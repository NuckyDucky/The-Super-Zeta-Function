import { createHash } from 'node:crypto';
import { closeSync, fstatSync, openSync, readFileSync } from 'node:fs';

const cutoff = 276824064;
const scoreDenominator = (2n ** 48n) ** 5n;
const rowCount = floorSqrt(cutoff);
const recordPattern = /^([1-9][0-9]*),(0|[1-9][0-9]*),(0|[1-9][0-9]*),(0|-?[1-9][0-9]*)$/;

function floorSqrt(n) {
  const root = Math.floor(Math.sqrt(n));
  if (!(root * root <= n && n < (root + 1) * (root + 1))) {
    throw new Error(`Could not verify the integer square root of ${n}`);
  }
  return root;
}

function stableSnapshot(path) {
  const handle = openSync(path, 'r');
  try {
    const before = fstatSync(handle, { bigint: true });
    const bytes = readFileSync(handle);
    const after = fstatSync(handle, { bigint: true });
    if (BigInt(bytes.length) !== before.size || before.size !== after.size ||
        before.mtimeNs !== after.mtimeNs || before.ctimeNs !== after.ctimeNs) {
      throw new Error('Checkpoint changed during the read');
    }
    if (bytes.length > 0 && bytes.at(-1) !== 10) {
      throw new Error('Checkpoint has an unterminated final record');
    }
    return { bytes, modifiedUtc: new Date(Number(after.mtimeMs)).toISOString() };
  } finally {
    closeSync(handle);
  }
}

function* expectedRecords(width) {
  for (let row = 1; row <= rowCount; row++) {
    const size = Math.min(row - 1, floorSqrt(cutoff - row * row));
    yield { row, offset: 0, length: 0, endsRow: size === 0 };
    for (let offset = 0; offset < size; offset += width) {
      const length = Math.min(width, size - offset);
      yield { row, offset, length, endsRow: offset + length === size };
    }
  }
}

function validate(bytes, width) {
  const lines = bytes.toString('utf8').split(/\r?\n/);
  lines.pop();
  let expectedCount = 0;
  let completeRows = 0;
  let sum = 0n;
  let lastRecord = null;
  let firstMissing = null;
  for (const { row, offset, length, endsRow } of expectedRecords(width)) {
    const coordinates = [row, offset, length];
    const line = lines[expectedCount++];
    if (line === undefined) {
      firstMissing ??= coordinates;
      continue;
    }
    const match = recordPattern.exec(line);
    if (!match) throw new Error(`Malformed CSV record at line ${expectedCount}`);
    if (match[1] !== String(row) || match[2] !== String(offset) || match[3] !== String(length)) {
      throw new Error(`Line ${expectedCount} has ${match.slice(1, 4).join(',')}, expected ${coordinates}`);
    }
    sum += BigInt(match[4]);
    lastRecord = coordinates;
    if (endsRow) completeRows++;
  }
  if (lines.length > expectedCount) throw new Error(`Unexpected record at line ${expectedCount + 1}`);
  return { records: lines.length, expectedCount, completeRows, sum, lastRecord, firstMissing };
}

const [path, widthText] = process.argv.slice(2);
try {
  if (process.argv.length !== 4 || !/^[1-9][0-9]*$/.test(widthText)) {
    throw new Error('Usage: node validate-paired-checkpoint.mjs CHECKPOINT WIDTH');
  }
  const width = Number(widthText);
  if (!Number.isSafeInteger(width)) throw new Error('WIDTH must be a safe positive integer');
  const { bytes, modifiedUtc } = stableSnapshot(path);
  const { records, expectedCount, completeRows, sum, lastRecord, firstMissing } = validate(bytes, width);
  const complete = firstMissing === null;
  const delta = complete ? 50n * sum - 7n * scoreDenominator : null;
  console.log(JSON.stringify({
    complete,
    cutoff,
    blockWidth: width,
    bytes: bytes.length,
    modifiedUtc,
    sha256: createHash('sha256').update(bytes).digest('hex'),
    completeRows,
    expectedRows: rowCount,
    records,
    expectedRecords: expectedCount,
    lastRecord,
    firstMissing,
    sumTicks: sum.toString(),
    scoreDenominator: scoreDenominator.toString(),
    thresholdDelta: delta?.toString() ?? null,
    exceedsSevenFiftieths: delta === null ? null : delta > 0n,
  }, null, 2));
  // 2 is an intact prefix. 3 is complete coverage with a nonpositive threshold margin.
  process.exitCode = !complete ? 2 : delta > 0n ? 0 : 3;
} catch (error) {
  console.error(error.message);
  process.exitCode = 1;
}

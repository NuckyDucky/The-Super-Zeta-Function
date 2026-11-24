import { performance } from 'node:perf_hooks';
import { pathToFileURL } from 'node:url';

const prime = 1414835497n;
const projection = 516876951n;
const nonresidue = 5n;

function square(value) {
  return value * value % prime;
}

function power(base, exponent) {
  let result = 1n;
  while (exponent > 0n) {
    if (exponent % 2n === 1n) result = result * base % prime;
    base = square(base);
    exponent /= 2n;
  }
  return result;
}

function repeatedSquare(value, count) {
  for (let i = 0; i < count; i++) value = square(value);
  return value;
}

let oddPart = prime - 1n;
let twoAdicOrder = 0;
while (oddPart % 2n === 0n) {
  oddPart /= 2n;
  twoAdicOrder++;
}
const nonresiduePower = power(nonresidue, oddPart);

// Tonelli–Shanks with target^oddPart already available from the sign check.
function squareRoot(target, oddPower) {
  let root = power(target, (oddPart + 1n) / 2n);
  let correction = nonresiduePower;
  let order = twoAdicOrder;
  while (oddPower !== 1n) {
    let index = 0;
    let current = oddPower;
    while (current !== 1n && index < order) {
      current = square(current);
      index++;
    }
    if (index === order) throw new Error(`Tonelli–Shanks failed for residue ${target}`);
    const factor = repeatedSquare(correction, order - index - 1);
    root = root * factor % prime;
    correction = square(factor);
    oddPower = oddPower * correction % prime;
    order = index;
  }
  return root <= prime - root ? root : prime - root;
}

function witness(residue) {
  if (residue === 0n) return 0n;
  let oddPower = power(residue, oddPart);
  const sign = repeatedSquare(oddPower, twoAdicOrder - 1);
  if (sign !== 1n && sign !== prime - 1n) {
    throw new Error(`Unexpected Euler value for residue ${residue}`);
  }
  const negative = sign === prime - 1n;
  const target = negative ? nonresidue * residue % prime : residue;
  if (negative) oddPower = oddPower * nonresiduePower % prime;
  const code = 2n * squareRoot(target, oddPower) + (negative ? 1n : 0n);

  const decodedTarget = code % 2n === 0n ? residue : nonresidue * residue % prime;
  if (square(code / 2n) !== decodedTarget) {
    throw new Error(`Invalid square-root witness for residue ${residue}`);
  }
  return code;
}

function natural(value, name) {
  if ((typeof value === 'bigint' && value >= 0n) ||
      (typeof value === 'number' && Number.isSafeInteger(value) && value >= 0) ||
      (typeof value === 'string' && /^[0-9]+$/.test(value))) {
    return BigInt(value);
  }
  throw new Error(`${name} must be a nonnegative integer`);
}

// Coordinates are physical, and each pair is ordered as (a,b), then (b,a).
export function makeWitnessPairs(a, first, length) {
  const row = natural(a, 'A');
  const firstB = natural(first, 'FIRST_B');
  const count = Number(natural(length, 'COUNT'));
  if (!Number.isSafeInteger(count)) throw new Error('COUNT exceeds the safe integer range');
  if (repeatedSquare(nonresiduePower, twoAdicOrder - 1) !== prime - 1n) {
    throw new Error('5 failed the nonresidue check');
  }

  const pairs = [];
  for (let i = 0, b = firstB; i < count; i++, b++) {
    const forward = witness((row + projection * b) % prime);
    const swapped = witness((b + projection * row) % prime);
    // The canonical root keeps every code at most prime.
    pairs.push([Number(forward), Number(swapped)]);
  }
  return pairs;
}

export function formatLeanPairs(pairs) {
  if (pairs.length === 0) return '[]\n';
  const lines = [];
  for (let start = 0; start < pairs.length; start += 4) {
    const entries = pairs.slice(start, start + 4).map(([forward, swapped]) => `(${forward}, ${swapped})`);
    lines.push(entries.join(', '));
  }
  return `[\n  ${lines.join(',\n  ')}\n]\n`;
}

export function formatLeanPacked(pairs) {
  const words = [];
  for (let i = pairs.length - 1; i >= 0; i--) {
    const [forward, swapped] = pairs[i];
    for (const code of [swapped, forward]) {
      if (!Number.isSafeInteger(code) || code < 0 || code >= 2 ** 32) {
        throw new Error('Witness code does not fit a 32-bit word');
      }
      words.push(code.toString(16).padStart(8, '0'));
    }
  }
  return '0x' + (words.join('') || '0');
}

function main(args) {
  const showStats = args.at(-1) === '--stats';
  if (showStats) args.pop();
  if (args.length !== 3) {
    throw new Error('Usage: node make-large-sign-witnesses.mjs A FIRST_B COUNT [--stats]');
  }
  const started = performance.now();
  const pairs = makeWitnessPairs(...args);
  const output = formatLeanPairs(pairs);
  const generationMs = performance.now() - started;
  process.stdout.write(output);
  if (showStats) {
    process.stderr.write(`${JSON.stringify({
      pairs: pairs.length,
      bytes: Buffer.byteLength(output),
      generationMs: Number(generationMs.toFixed(3)),
    })}\n`);
  }
}

if (process.argv[1] && pathToFileURL(process.argv[1]).href === import.meta.url) {
  try {
    main(process.argv.slice(2));
  } catch (error) {
    process.stderr.write(`${error.message}\n`);
    process.exitCode = 1;
  }
}

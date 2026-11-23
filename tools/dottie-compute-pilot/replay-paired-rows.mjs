import { spawn } from 'node:child_process';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { resolve } from 'node:path';

const cutoff = 276824064;
const rowCount = 16638;
const acceptedAxioms = new Set(['propext', 'Classical.choice', 'Quot.sound']);

function positiveInteger(value, label) {
  const number = Number(value);
  if (!/^[1-9][0-9]*$/.test(value) || !Number.isSafeInteger(number)) {
    throw new Error(`Invalid ${label}: ${value}`);
  }
  return number;
}

function selectedRows(checkpoint, first, last, width) {
  const rows = new Map();
  // The producer can be writing its last line. Check only complete records.
  const lines = checkpoint.slice(0, checkpoint.lastIndexOf('\n')).split(/\r?\n/);
  for (const line of lines) {
    const fields = line.split(',');
    const a = Number(fields[0]);
    if (a < first || a > last) continue;
    if (fields.length !== 4 || !/^-?\d+$/.test(fields[3])) {
      throw new Error(`Invalid score record for row ${a}`);
    }
    const contributions = rows.get(a) ?? new Map();
    const key = `${fields[1]},${fields[2]}`;
    if (contributions.has(key)) throw new Error(`Duplicate ${a},${key}`);
    contributions.set(key, BigInt(fields[3]));
    rows.set(a, contributions);
  }
  const selected = [];
  for (let a = first; a <= last; a++) {
    const contributions = rows.get(a);
    const size = Math.min(a - 1, Math.floor(Math.sqrt(cutoff - a * a)));
    const full = Math.floor(size / width);
    const remainder = size % width;
    const expected = [[0, 0]];
    for (let k = 0; k < full; k++) expected.push([k * width, width]);
    if (remainder > 0) expected.push([full * width, remainder]);
    if (!contributions || contributions.size !== expected.length ||
        expected.some(([lo, len]) => !contributions.has(`${lo},${len}`))) {
      throw new Error(`Row ${a} has incomplete or mismatched candidate coverage`);
    }
    selected.push({ a, width, full, remainder, contributions });
  }
  return selected;
}

function renderRow({ a, width, full, remainder, contributions }, mode, witness) {
  const index = a - 1;
  const name = `DottiePairedRow${a}`;
  const declaration = `dottiePairedRow${a}`;
  const entry = mode === 'witness' ? 'DottieWitnessPairBlocks' :
    mode === 'lookup' ? 'DottieStructuralPairBlocks' : 'DottiePairedRows';
  const lines = [
    'import ' + entry,
    '', 'open Finset', '', 'namespace QuarticModel', '',
    'set_option maxHeartbeats 30000000',
    ...(mode === 'witness' ? ['set_option maxRecDepth 12000'] : []), '',
    `private theorem firstTerms : dottiePairRowHead ${cutoff} dottieQuickWeightTicks ${index} =`,
    `    (${contributions.get('0,0')} : ℤ) := by decide +kernel`, '',
  ];
  function blockProof(lo, size) {
    if (mode === 'lookup') {
      return '\n  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq ' +
        `dottieQuickWeightTicks ${index} ${lo} ${size}).symm.trans (by decide +kernel)`;
    }
    if (mode === 'witness' && size > 0) {
      const packed = witness.formatLeanPacked(witness.makeWitnessPairs(a, lo + 1, size));
      return '\n  dottie_pair_block_of_packed_witness (packed := ' + packed + ')\n' +
        '    (by decide +kernel)';
    }
    return 'by decide +kernel';
  }
  const parts = [];
  for (let k = 0; k < full; k++) {
    const lo = k * width;
    const part = `block${k}`;
    lines.push(`private theorem ${part} : dottiePairRowBlock dottieQuickWeightTicks ${index} ${lo} ${width} =`,
      `    (${contributions.get(`${lo},${width}`)} : ℤ) := ${blockProof(lo, width)}`, '');
    parts.push(part);
  }
  const tailStart = full * width;
  const tail = contributions.get(`${tailStart},${remainder}`);
  lines.push(
    `private theorem lastTerms : dottiePairRowBlock dottieQuickWeightTicks ${index} ${tailStart} ${remainder} =`,
    `    (${remainder > 0 ? tail : 0n} : ℤ) := ${blockProof(tailStart, remainder)}`, '',
  );
  let total = 0n;
  for (const value of contributions.values()) total += value;
  lines.push(
    `theorem ${declaration} : dottiePairedRowSpan ${cutoff} dottieQuickWeightTicks ${index} 1 = (${total} : ℤ) := by`,
    '  rw [dottiePairedRowSpan_one, firstTerms, dottiePairRowBlock_eq_blocks]',
    `  have hdiv : dottiePairRowSize ${cutoff} ${index} / ${width} = ${full} := by decide +kernel`,
    `  have hmod : dottiePairRowSize ${cutoff} ${index} % ${width} = ${remainder} := by decide +kernel`,
    '  rw [hdiv, hmod]',
  );
  if (full > 0) {
    lines.push(`  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.zero_mul,`,
      `    ${parts.join(', ')}, lastTerms]`);
  } else {
    lines.push('  simp only [Finset.sum_range_zero, Nat.zero_mul, lastTerms]');
  }
  lines.push('  decide +kernel', '', `#print axioms ${declaration}`, '', 'end QuarticModel', '');
  const source = lines.join('\n').replace(/\b(firstTerms|lastTerms|block\d+)\b/g, part => `row${a}_${part}`);
  return { name, declaration, source };
}

async function compileBatch(lean, directory, rows, mode, witness) {
  const proofs = rows.map(row => renderRow(row, mode, witness));
  const name = rows.length === 1 ? proofs[0].name : `DottiePairedRows${rows[0].a}Through${rows.at(-1).a}`;
  const source = proofs[0].source + proofs.slice(1)
    .map(proof => proof.source.slice(proof.source.indexOf('\n'))).join('\n');
  await writeFile(resolve(directory, `${name}.lean`), source, 'utf8');
  const result = await new Promise((done, fail) => {
    const process = spawn(lean, ['-j', '1', '-s', '65536', '-DwarningAsError=true', '-o',
      `${name}.olean`, `${name}.lean`], { cwd: directory, windowsHide: true });
    let output = '';
    process.stdout.on('data', data => { output += data; });
    process.stderr.on('data', data => { output += data; });
    process.on('error', fail);
    process.on('close', status => done({ status, output }));
  });
  await writeFile(resolve(directory, `${name}.log`), result.output, 'utf8');
  if (result.status !== 0) throw new Error(`Lean rejected ${name}. See ${name}.log`);
  for (const { declaration } of proofs) {
    const axiomLine = result.output.match(new RegExp(`'QuarticModel\\.${declaration}' depends on axioms: \\[([^\\]]*)\\]`));
    if (!axiomLine || axiomLine[1].split(/,\s*/).some(axiom => !acceptedAxioms.has(axiom))) {
      throw new Error(`Unexpected axioms for ${declaration}. See ${name}.log`);
    }
    console.log(axiomLine[0]);
  }
}

const [checkpoint, output, lean, firstArg, lastArg, widthArg, ...flags] = process.argv.slice(2);
if (!widthArg || flags.some(flag => !['--lookup', '--witness', '--bundle'].includes(flag)) ||
    new Set(flags).size !== flags.length || (flags.includes('--lookup') && flags.includes('--witness'))) {
  throw new Error('Usage: node replay-paired-rows.mjs CHECKPOINT OUTPUT LEAN FIRST LAST WIDTH [--lookup | --witness] [--bundle]');
}
const first = positiveInteger(firstArg, 'first row');
const last = positiveInteger(lastArg, 'last row');
const width = positiveInteger(widthArg, 'block width');
if (first > last || last > rowCount) throw new Error('Invalid row bounds');
const directory = resolve(output);
const rows = selectedRows(await readFile(checkpoint, 'utf8'), first, last, width);
await mkdir(directory, { recursive: true });
const mode = flags.includes('--witness') ? 'witness' : flags.includes('--lookup') ? 'lookup' : 'original';
const witness = mode === 'witness' ? await import('./score-profile/make-large-sign-witnesses.mjs') : undefined;
const maxRows = flags.includes('--bundle') ? 16 : 1;
const maxWork = mode === 'witness' ? 12000 : 60000;
for (let start = 0; start < rows.length;) {
  let end = start + 1;
  let work = rows[start].full * width + rows[start].remainder;
  while (end < rows.length && end - start < maxRows) {
    const nextWork = rows[end].full * width + rows[end].remainder;
    if (work + nextWork > maxWork) break;
    work += nextWork;
    end++;
  }
  await compileBatch(resolve(lean), directory, rows.slice(start, end), mode, witness);
  start = end;
}

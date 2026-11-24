import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const cutoff = 276824064;
const tailFirst = 513;
const finalRow = 16638;
const prefix = {
  first: 1, last: 512, module: 'DottiePairedRowsThrough512',
  theorem: 'dottiePairedRows_1_512',
  ticks: -2194051408328389528095838244668709343406951250992555239349157224090040936n,
};
const candidateTicks = 303339834966217300615369504615526421285720775755844666418981971508403960n;

const length = span => span.last - span.first + 1;
const integer = value => `(${value} : ℤ)`;
const spanType = span =>
  `dottiePairedRowSpan ${cutoff} dottieQuickWeightTicks ${span.first - 1} ${length(span)} = ${integer(span.ticks)}`;

function joinTree(spans, lines) {
  if (spans.length === 1) return spans[0];
  const midpoint = Math.floor(spans.length / 2);
  const left = joinTree(spans.slice(0, midpoint), lines);
  const right = joinTree(spans.slice(midpoint), lines);
  if (left.last + 1 !== right.first) throw new Error('Assembly spans must be adjacent');
  const joined = {
    first: left.first, last: right.last, ticks: left.ticks + right.ticks,
    theorem: `span_${left.first - 1}_${length(left) + length(right)}`,
  };
  lines.push(
    `private theorem ${joined.theorem} :`,
    `    ${spanType(joined)} := by`,
    '  calc',
    `    _ = ${integer(left.ticks)} + ${integer(right.ticks)} := by`,
    `      rw [dottiePairedRowSpan_add ${cutoff} dottieQuickWeightTicks ${left.first - 1} ${length(left)} ${length(right)},`,
    `        ${left.theorem}, ${right.theorem}]`,
    '    _ = _ := by decide +kernel',
    '',
  );
  return joined;
}

function renderModule(spans, declaration, extraImports = [], extraTheorems = []) {
  const imports = [...extraImports, ...spans.map(span => span.module)];
  const lines = [...new Set(imports)].map(name => `import ${name}`);
  lines.push('', 'namespace QuarticModel', '');
  const result = joinTree(spans, lines);
  lines.push(
    `theorem ${declaration} :`,
    `    ${spanType(result)} :=`,
    `  ${result.theorem}`,
    '',
    ...extraTheorems,
    `#print axioms ${declaration}`,
    '',
    'end QuarticModel',
    '',
  );
  return { ...result, theorem: declaration, text: lines.join('\n') };
}

export function renderShard(records, { moduleForRow = row => `DottiePairedRow${row}`, declaration } = {}) {
  if (records.length === 0) throw new Error('Cannot assemble an empty shard');
  const spans = records.map(({ row, ticks }) => ({
    first: row, last: row, ticks: BigInt(ticks),
    module: moduleForRow(row), theorem: `dottiePairedRow${row}`,
  }));
  const first = spans[0].first;
  const last = spans.at(-1).last;
  const module = `DottieProductionRows${first}Through${last}`;
  return { ...renderModule(spans, declaration ?? `dottieProductionRows_${first}_${last}`), module };
}

function collectShards(input, downloads) {
  if (input.firstRow !== tailFirst || input.lastRow !== finalRow ||
      input.rows?.length !== finalRow - tailFirst + 1 ||
      !/^[a-f0-9]{40}$/.test(input.proofCommit) || !/^[a-f0-9]{40}$/.test(input.activationCommit)) {
    throw new Error('Expected a complete production receipt covering rows 513 through 16638');
  }
  const shards = [];
  for (const [index, record] of input.rows.entries()) {
    const row = tailFirst + index;
    const stem = `kernel/DottiePairedRow${row}`;
    const match = /^dottie-production-rows-([1-9]\d*)-([1-9]\d*)$/.exec(record.artifact);
    if (!match || record.row !== row || record.theorem !== `QuarticModel.dottiePairedRow${row}` ||
        record.source !== `${stem}.lean` || record.olean !== `${stem}.olean` ||
        record.log !== `${stem}.log` || typeof record.ticks !== 'string' || !/^-?\d+$/.test(record.ticks)) {
      throw new Error(`Invalid collected metadata at row ${row}`);
    }
    const first = Number(match[1]);
    const last = Number(match[2]);
    if (row === first && last >= first && last <= finalRow) {
      shards.push({ first, last, artifact: record.artifact, records: [] });
    }
    const shard = shards.at(-1);
    if (!shard || shard.artifact !== record.artifact || row > shard.last ||
        row !== shard.first + shard.records.length) {
      throw new Error(`Unexpected artifact boundary at row ${row}`);
    }
    shard.records.push(record);
  }
  if (shards.some(shard => shard.records.length !== length(shard))) throw new Error('Incomplete artifact range');
  return shards.map(shard => ({
    ...renderShard(shard.records),
    leanDirectory: resolve(downloads, shard.artifact, dirname(shard.records[0].olean)),
  }));
}

const fullTheorems = [
  'theorem dottieProductionFullSpan_eq_candidate :',
  '    dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 = dottiePairedCandidateTicks := by',
  '  simpa only [dottiePairedCandidateTicks] using dottieProductionFullSpan',
  '',
  'theorem dottieProductionQuickReferenceScore_eq_candidate :',
  '    dottieQuickReferenceScore = dottiePairedCandidateTicks :=',
  '  dottieQuickReferenceScore_eq_row_span.trans dottieProductionFullSpan_eq_candidate',
  '',
  'theorem dottieProductionCircleReference_pos : 0 < dottieCircleReference :=',
  '  dottieCircleReference_pos_of_candidate_equality dottieProductionFullSpan_eq_candidate',
  '',
  '#print axioms dottieProductionFullSpan_eq_candidate',
  '#print axioms dottieProductionQuickReferenceScore_eq_candidate',
  '#print axioms dottieProductionCircleReference_pos',
  '',
];

async function main() {
  if (process.argv.length !== 6) {
    throw new Error('Usage: node assemble-production-spans.mjs COLLECTOR_JSON DOWNLOAD_ROOT PREFIX_LEAN_DIR OUTPUT');
  }
  const [collector, downloads, prefixDir, destination] = process.argv.slice(2);
  const input = JSON.parse(await readFile(collector, 'utf8'));
  const shards = collectShards(input, downloads);
  const tailTicks = shards.reduce((total, shard) => total + shard.ticks, 0n);
  if (tailTicks.toString() !== input.tailTicks || prefix.ticks + tailTicks !== candidateTicks) {
    throw new Error('Collected ticks and the audited prefix do not match the exact reference candidate');
  }
  const top = {
    ...renderModule([prefix, ...shards], 'dottieProductionFullSpan', ['DottieReferenceCandidate'], fullTheorems),
    module: 'DottieProductionFull',
  };
  const output = resolve(destination);
  await mkdir(output);
  const buildOrder = [];
  for (const { module, text, first, last, ticks, theorem } of [...shards, top]) {
    const source = `${module}.lean`;
    await writeFile(join(output, source), text, 'utf8');
    buildOrder.push({ source, olean: `${module}.olean`, first, last, ticks: ticks.toString(),
      theorem: `QuarticModel.${theorem}` });
  }
  const manifest = {
    proofCommit: input.proofCommit, activationCommit: input.activationCommit,
    leanToolchain: 'leanprover/lean4:v4.33.1',
    mathlibCommit: '0df444a360eaa60ab8c11dca51a86af692955474',
    requiredImports: ['DottieReferenceCandidate', prefix.module],
    // Add the pinned proof project and package libraries to these directories.
    leanPath: [...new Set([output, resolve(prefixDir), ...shards.map(shard => shard.leanDirectory)])],
    compilerFlags: ['-j', '1', '-s', '65536', '-DwarningAsError=true'],
    buildOrder,
    candidateTicks: candidateTicks.toString(),
    circleReferenceTheorem: 'QuarticModel.dottieProductionCircleReference_pos',
  };
  await writeFile(join(output, 'build-manifest.json'), `${JSON.stringify(manifest, null, 2)}\n`, 'utf8');
}

if (process.argv[1] && pathToFileURL(process.argv[1]).href === import.meta.url) await main();

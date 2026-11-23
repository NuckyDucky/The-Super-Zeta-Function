import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const read = (directory, name) => readFile(join(directory, name), 'utf8');
const standardAxioms = new Set(['propext', 'Classical.choice', 'Quot.sound']);
const mathlib = '0df444a360eaa60ab8c11dca51a86af692955474';
const matrix = jobs => jobs.map(({ first, last, work }) => ({ first, last, work }));

export async function verifyShard(root, plan, job) {
  const artifact = `dottie-production-rows-${job.first}-${job.last}`;
  const directory = join(root, artifact);
  const receipt = JSON.parse(await read(directory, 'receipt.json'));
  if (receipt.sourceCommit !== plan.proofCommit || receipt.activationCommit !== plan.activationCommit ||
      receipt.firstRow !== job.first || receipt.lastRow !== job.last || receipt.work !== job.work ||
      receipt.cutoff !== 276824064 || receipt.blockWidth !== 1024 ||
      receipt.replayMode !== 'packed-witness' || receipt.mathlibCommit !== mathlib ||
      !receipt.leanVersion?.startsWith('Lean (version 4.33.1,')) {
    throw new Error(`Receipt does not match the plan for ${artifact}`);
  }

  const records = (await read(directory, 'rows.jsonl')).trimEnd().split(/\r?\n/).map(line => JSON.parse(line));
  const audits = (await read(directory, 'kernel-axioms.txt')).trimEnd().split(/\r?\n/);
  if (records.length !== job.last - job.first + 1 || audits.length !== records.length ||
      receipt.theorems?.length !== records.length) {
    throw new Error(`Missing row receipts in ${artifact}`);
  }
  const paths = new Set(['candidates.csv', 'kernel-axioms.txt', 'sources.sha256', 'receipt.json', 'rows.jsonl']);
  const rows = [];
  for (const [index, record] of records.entries()) {
    const row = job.first + index;
    const stem = `kernel/DottiePairedRow${row}`;
    const theorem = `QuarticModel.dottiePairedRow${row}`;
    if (record.row !== row || record.theorem !== theorem || receipt.theorems[index] !== theorem ||
        typeof record.ticks !== 'string' || !/^-?\d+$/.test(record.ticks) ||
        record.source !== `${stem}.lean` || record.olean !== `${stem}.olean` || record.log !== `${stem}.log`) {
      throw new Error(`Invalid row metadata for ${row}`);
    }
    const prefix = `'${theorem}' depends on axioms: [`;
    const audit = audits[index];
    if (!audit.startsWith(prefix) || !audit.endsWith(']') ||
        audit.slice(prefix.length, -1).split(/,\s*/).some(axiom => !standardAxioms.has(axiom))) {
      throw new Error(`Unexpected axiom audit for ${theorem}`);
    }
    paths.add(record.source).add(record.olean).add(record.log);
    rows.push({ ...record, artifact });
  }
  for (const line of (await read(directory, 'receipts.sha256')).trimEnd().split(/\r?\n/)) {
    const match = /^([0-9a-f]{64})  (.+)$/.exec(line);
    if (!match || !paths.delete(match[2])) throw new Error(`Unrecognized digest entry in ${artifact}`);
    const actual = createHash('sha256').update(await readFile(join(directory, match[2]))).digest('hex');
    if (actual !== match[1]) throw new Error(`Digest mismatch for ${artifact}/${match[2]}`);
  }
  if (paths.size !== 0) throw new Error(`Incomplete digest file in ${artifact}`);
  return { rows, sourceManifest: await read(directory, 'sources.sha256') };
}

async function main() {
  if (process.argv.length !== 3) throw new Error('Usage: node collect-packed-receipts.mjs DOWNLOAD_DIR');
  const root = resolve(process.argv[2]);
  const plan = JSON.parse(await read(join(root, 'dottie-production-plan'), 'plan.json'));
  const planner = fileURLToPath(new URL('./plan-packed-replay.mjs', import.meta.url));
  const expected = JSON.parse(execFileSync(process.execPath, [planner, '--json'], { encoding: 'utf8' }));
  if (!/^[a-f0-9]{40}$/.test(plan.proofCommit) || !/^[a-f0-9]{40}$/.test(plan.activationCommit) ||
      JSON.stringify(matrix(plan.jobs)) !== JSON.stringify(matrix(expected.jobs))) {
    throw new Error('Downloaded plan does not match the exact production matrix');
  }
  const rows = [];
  let sourceManifest;
  for (const job of expected.jobs) {
    const shard = await verifyShard(root, plan, job);
    sourceManifest ??= shard.sourceManifest;
    if (shard.sourceManifest !== sourceManifest) throw new Error('Source manifests differ between shards');
    rows.push(...shard.rows);
  }
  const tailTicks = rows.reduce((total, row) => total + BigInt(row.ticks), 0n);
  process.stdout.write(`${JSON.stringify({
    proofCommit: plan.proofCommit, activationCommit: plan.activationCommit,
    firstRow: 513, lastRow: 16638, tailTicks: tailTicks.toString(), rows,
  }, null, 2)}\n`);
}

if (process.argv[1] && pathToFileURL(process.argv[1]).href === import.meta.url) await main();

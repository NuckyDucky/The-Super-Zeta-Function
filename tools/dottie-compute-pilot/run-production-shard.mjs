import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { performance } from 'node:perf_hooks';
import { fileURLToPath } from 'node:url';

const mathlibCommit = '0df444a360eaa60ab8c11dca51a86af692955474';
const leanToolchain = 'leanprover/lean4:v4.33.1';
const cutoff = 276824064;
const width = 1024;
const replay = fileURLToPath(new URL('./replay-paired-rows.mjs', import.meta.url));
const pinFiles = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json'];
const proofSources = [
  'DottiePairedRows.lean',
  'DottieScoreCandidates.lean',
  'DottieWitnessPairBlocks.lean',
  'DottieLargeSignWitness.lean',
];

function run(command, args, cwd, { visible = false, env = process.env } = {}) {
  return execFileSync(command, args, {
    cwd,
    env,
    encoding: 'utf8',
    stdio: visible ? 'inherit' : ['ignore', 'pipe', 'pipe'],
    windowsHide: true,
  });
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

async function pinnedSources(project, commit) {
  const repo = dirname(project);
  const tree = run('git', ['ls-tree', '-rz', '--full-tree', commit, '--', 'lean-ideal73'], repo);
  const hashes = [];
  const imports = new Set();
  const paths = new Set();
  for (const record of tree.split('\0').filter(Boolean)) {
    const [entry, path] = record.split('\t');
    const [mode, type, objectId] = entry.split(' ');
    if (type !== 'blob' || !/^100(644|755)$/.test(mode)) continue;
    if (!path.endsWith('.lean') && !pinFiles.some(file => path === `lean-ideal73/${file}`)) continue;
    const bytes = await readFile(join(repo, path));
    const gitHash = createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex');
    if (gitHash !== objectId) throw new Error(`Source bytes differ from ${commit}: ${path}`);
    hashes.push(`${sha256(bytes)}  ${path}`);
    paths.add(path);
    if (path.endsWith('.lean')) {
      for (const match of bytes.toString('utf8').matchAll(
        /^[ \t]*(?:public[ \t]+)?import[ \t]+(Mathlib\.[A-Za-z0-9_.]+)/gm
      )) {
        imports.add(match[1]);
      }
    }
  }
  for (const file of [...pinFiles, ...proofSources]) {
    if (!paths.has(`lean-ideal73/${file}`)) throw new Error(`Missing pinned source ${file}`);
  }
  if (imports.size === 0) throw new Error('No Mathlib imports in the pinned source');
  for (const name of [
    'run-production-shard.mjs', 'activate-packed-production.mjs', 'plan-packed-replay.mjs',
    'replay-paired-rows.mjs', 'score-profile/make-large-sign-witnesses.mjs',
  ]) {
    const path = fileURLToPath(new URL(name, import.meta.url));
    hashes.push(`${sha256(await readFile(path))}  tools/dottie-compute-pilot/${name}`);
  }
  return { hashes, imports: [...imports].sort() };
}

const started = performance.now();
const [projectArg, commit, outputArg, firstArg, lastArg, workArg] = process.argv.slice(2);
if (process.argv.length !== 8) {
  throw new Error('Usage: node run-production-shard.mjs LEAN_PROJECT SOURCE_COMMIT OUTPUT FIRST LAST WORK');
}
if (!/^[a-f0-9]{40}$/.test(commit)) throw new Error('Use a full Git source commit SHA');
const activationCommit = process.env.DOTTIE_ACTIVATION_SHA;
if (!/^[a-f0-9]{40}$/.test(activationCommit)) throw new Error('Missing activation commit SHA');
const first = Number(firstArg);
const last = Number(lastArg);
const work = Number(workArg);
if (!/^[1-9][0-9]{0,4}$/.test(firstArg) || !/^[1-9][0-9]{0,4}$/.test(lastArg) ||
    !/^[1-9][0-9]*$/.test(workArg) || !Number.isSafeInteger(work) ||
    first < 513 || last > 16638 || first > last) {
  throw new Error('Invalid production row bounds or work count');
}
const project = resolve(projectArg);
const output = resolve(outputArg);
const checkpoint = join(output, 'candidates.csv');
const kernel = join(output, 'kernel');
const env = { ...process.env, LEAN_NUM_THREADS: '1' };
delete env.LEAN_PATH;
delete env.LEAN_SRC_PATH;

const { hashes, imports } = await pinnedSources(project, commit);
const toolchain = (await readFile(join(project, 'lean-toolchain'), 'utf8')).trim();
if (toolchain !== leanToolchain) throw new Error(`Expected ${leanToolchain}, found ${toolchain}`);
await mkdir(dirname(output), { recursive: true });
// The Lean candidate producer appends. Each shard must start with a new output directory.
await mkdir(output);
await writeFile(join(output, 'sources.sha256'), `${hashes.join('\n')}\n`);

console.log(`Rows ${first} through ${last}, ${work} paired positions, block width ${width}`);
const leanVersion = run('lake', ['env', 'lean', '--version'], project, { env }).trim();
if (!leanVersion.startsWith('Lean (version 4.33.1,')) {
  throw new Error(`Unexpected Lean compiler: ${leanVersion}`);
}
run('lake', ['exe', 'cache', 'get', ...imports], project, { env, visible: true });
const mathlibDir = join(project, '.lake', 'packages', 'mathlib');
const mathlib = run('git', ['rev-parse', 'HEAD'], mathlibDir).trim();
if (mathlib !== mathlibCommit) throw new Error(`Unexpected Mathlib revision: ${mathlib}`);
run('lake', ['build', '+DottiePairedRows:olean', '+DottieScoreCandidates:olean',
  '+DottieWitnessPairBlocks:olean'], project, { env, visible: true });
const leanPrefix = run('lake', ['env', 'lean', '--print-prefix'], project, { env }).trim();
const lean = join(leanPrefix, 'bin', process.platform === 'win32' ? 'lean.exe' : 'lean');
const setupSeconds = (performance.now() - started) / 1000;
console.log(`Setup, dependency cache and module build seconds: ${setupSeconds}`);

const candidateStart = performance.now();
run('lake', ['env', lean, '-j', '1', '-s', '65536', '-DwarningAsError=true', '--run',
  'DottieScoreCandidates.lean', 'paired', checkpoint, String(first), String(last + 1), String(width)],
  project, { env, visible: true });
const candidateSeconds = (performance.now() - candidateStart) / 1000;
console.log(`Candidate generation seconds: ${candidateSeconds}`);

const totals = new Map();
let candidateWork = 0;
for (const record of (await readFile(checkpoint, 'utf8')).trimEnd().split(/\r?\n/)) {
  const match = /^(\d+),(\d+),(\d+),(-?\d+)$/.exec(record);
  if (!match) throw new Error('Malformed candidate record');
  const row = Number(match[1]);
  if (row < first || row > last) throw new Error(`Unexpected candidate row ${row}`);
  candidateWork += Number(match[3]);
  totals.set(row, (totals.get(row) ?? 0n) + BigInt(match[4]));
}
if (candidateWork !== work || totals.size !== last - first + 1) {
  throw new Error('Candidate coverage disagrees with the weighted plan');
}

const replayStart = performance.now();
run('lake', ['env', process.execPath, replay, checkpoint, kernel, lean,
  String(first), String(last), String(width), '--witness'], project, { env, visible: true });
const kernelReplaySeconds = (performance.now() - replayStart) / 1000;
console.log(`Packed kernel replay seconds: ${kernelReplaySeconds}`);
const captured = ['candidates.csv', 'kernel-axioms.txt', 'sources.sha256', 'receipt.json', 'rows.jsonl'];
const theorems = [];
const axioms = [];
const rows = [];
for (let row = first; row <= last; row++) {
  const stem = `kernel/DottiePairedRow${row}`;
  const source = `${stem}.lean`;
  const olean = `${stem}.olean`;
  const log = `${stem}.log`;
  const theorem = `QuarticModel.dottiePairedRow${row}`;
  captured.push(source, olean, log);
  theorems.push(theorem);
  const audit = (await readFile(join(output, log), 'utf8')).split(/\r?\n/)
    .find(line => line.startsWith(`'${theorem}' depends on axioms: `));
  if (!audit) throw new Error(`Missing axiom audit for ${theorem}`);
  axioms.push(audit);
  rows.push(JSON.stringify({ row, ticks: totals.get(row).toString(), theorem, source, olean, log }));
}
await writeFile(join(output, 'kernel-axioms.txt'), `${axioms.join('\n')}\n`);
await writeFile(join(output, 'rows.jsonl'), `${rows.join('\n')}\n`);
await writeFile(join(output, 'receipt.json'), `${JSON.stringify({
  sourceCommit: commit,
  activationCommit,
  leanVersion,
  mathlibCommit: mathlib,
  nodeVersion: process.version,
  cutoff,
  firstRow: first,
  lastRow: last,
  work,
  blockWidth: width,
  replayMode: 'packed-witness',
  timingSeconds: { setup: setupSeconds, candidate: candidateSeconds, kernelReplay: kernelReplaySeconds },
  theorems,
}, null, 2)}\n`);
const artifactHashes = [];
for (const path of captured) {
  artifactHashes.push(`${sha256(await readFile(join(output, path)))}  ${path}`);
}
await writeFile(join(output, 'receipts.sha256'), `${artifactHashes.join('\n')}\n`);

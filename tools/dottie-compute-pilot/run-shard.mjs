import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const mathlibCommit = '0df444a360eaa60ab8c11dca51a86af692955474';
const leanToolchain = 'leanprover/lean4:v4.33.1';
const cutoff = 276824064;
const width = 1024;
const shardStride = 128;
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
    'run-shard.mjs', 'replay-paired-rows.mjs', 'score-profile/make-large-sign-witnesses.mjs',
  ]) {
    const path = fileURLToPath(new URL(name, import.meta.url));
    hashes.push(`${sha256(await readFile(path))}  tools/dottie-compute-pilot/${name}`);
  }
  return { hashes, imports: [...imports].sort() };
}

const [projectArg, commit, outputArg, firstArg, shardArg] = process.argv.slice(2);
if (process.argv.length !== 7) {
  throw new Error('Usage: node run-shard.mjs LEAN_PROJECT SOURCE_COMMIT OUTPUT LOWER_FIRST SHARD');
}
if (!/^[a-f0-9]{40}$/.test(commit)) throw new Error('Use a full Git source commit SHA');
const lowerFirst = Number(firstArg);
if (!/^[1-9][0-9]{0,4}$/.test(firstArg) || lowerFirst > 16509) {
  throw new Error('LOWER_FIRST must be an integer from 1 through 16509');
}
if (shardArg !== '0' && shardArg !== '1') throw new Error('SHARD must be 0 or 1');
const shard = Number(shardArg);
const first = lowerFirst + shard * shardStride;
const last = first + 1;
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

console.log(`Shard ${shard}: rows ${first} through ${last}, block width ${width}`);
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

run('lake', ['env', lean, '-j', '1', '-s', '65536', '-DwarningAsError=true', '--run',
  'DottieScoreCandidates.lean', 'paired', checkpoint, String(first), String(last + 1), String(width)],
  project, { env, visible: true });

const axioms = run('lake', ['env', process.execPath, replay, checkpoint, kernel, lean,
  String(first), String(last), String(width), '--witness'], project, { env });
process.stdout.write(axioms);
await writeFile(join(output, 'kernel-axioms.txt'), axioms);
const captured = ['candidates.csv', 'kernel-axioms.txt', 'sources.sha256', 'receipt.json'];
const theorems = [];
for (let row = first; row <= last; row++) {
  captured.push(`kernel/DottiePairedRow${row}.lean`, `kernel/DottiePairedRow${row}.log`);
  theorems.push(`QuarticModel.dottiePairedRow${row}`);
}
await writeFile(join(output, 'receipt.json'), `${JSON.stringify({
  sourceCommit: commit,
  leanVersion,
  mathlibCommit: mathlib,
  nodeVersion: process.version,
  cutoff,
  shard,
  firstRow: first,
  lastRow: last,
  blockWidth: width,
  replayMode: 'packed-witness',
  theorems,
}, null, 2)}\n`);
const artifactHashes = [];
for (const path of captured) {
  artifactHashes.push(`${sha256(await readFile(join(output, path)))}  ${path}`);
}
await writeFile(join(output, 'receipts.sha256'), `${artifactHashes.join('\n')}\n`);

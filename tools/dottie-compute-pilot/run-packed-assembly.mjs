import { execFileSync, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { appendFile, copyFile, mkdir, readFile, writeFile } from 'node:fs/promises';
import { delimiter, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { performance } from 'node:perf_hooks';
import { renderShard } from './assemble-production-spans.mjs';

const mathlib = '0df444a360eaa60ab8c11dca51a86af692955474';
const toolchain = 'leanprover/lean4:v4.33.1';
const prefixTicks = -2194051408328389528095838244668709343406951250992555239349157224090040936n;
const permitted = new Set(['propext', 'Classical.choice', 'Quot.sound']);
const here = name => fileURLToPath(new URL(name, import.meta.url));
const read = path => readFile(path, 'utf8');
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');

export function renderPackedPrefix(records) {
  const moduleForRow = row => {
    const first = 16 * Math.floor((row - 1) / 16) + 1;
    const last = Math.min(first + 15, records.at(-1).row);
    return first === last ? `DottiePairedRow${first}` : `DottiePairedRows${first}Through${last}`;
  };
  return renderShard(records, { moduleForRow, declaration: `dottiePairedRows_1_${records.length}` });
}

function run(command, args, cwd, env, live = false) {
  return execFileSync(command, args, {
    cwd, env, encoding: 'utf8', maxBuffer: 32 * 1024 * 1024,
    stdio: live ? 'inherit' : ['ignore', 'pipe', 'pipe'],
  });
}

function auditLine(log, theorem) {
  const prefix = `'${theorem}' depends on axioms: [`;
  const line = log.split(/\r?\n/).find(item => item.startsWith(prefix) && item.endsWith(']'));
  if (!line || line.slice(prefix.length, -1).split(/,\s*/).some(axiom => !permitted.has(axiom))) {
    throw new Error(`Missing or unexpected kernel audit for ${theorem}`);
  }
  return line;
}

async function main() {
  if (process.argv.length !== 8) {
    throw new Error('Usage: node run-packed-assembly.mjs LEAN_PROJECT DOWNLOAD_ROOT OUTPUT PRODUCTION_ID PROOF_SHA ACTIVATION_SHA');
  }
  const [projectArg, downloadsArg, outputArg, productionRun, proofCommit, activationCommit] = process.argv.slice(2);
  const [project, downloads, output] = [projectArg, downloadsArg, outputArg].map(path => resolve(path));
  if (!/^[1-9]\d*$/.test(productionRun) ||
      !/^[a-f0-9]{40}$/.test(proofCommit) || !/^[a-f0-9]{40}$/.test(activationCommit)) {
    throw new Error('Expected exact production run and source pins');
  }
  const env = { ...process.env, LEAN_NUM_THREADS: '1' };
  delete env.LEAN_PATH;
  delete env.LEAN_SRC_PATH;
  const git = (cwd, ...argv) => run('git', argv, cwd, env).trim();
  const lake = (args, live = false) => run('lake', args, project, env, live);
  if (git(project, 'rev-parse', 'HEAD') !== proofCommit ||
      (await read(join(project, 'lean-toolchain'))).trim() !== toolchain) {
    throw new Error('Proof checkout or Lean toolchain does not match the production pin');
  }

  const out = join(output, 'receipt');
  const prefixDir = join(output, 'prefix');
  const assembly = join(output, 'spans');
  await mkdir(output);
  await mkdir(out);
  await mkdir(prefixDir);
  const auditFile = join(out, 'kernel-audits.txt');
  const timing = [];
  const started = performance.now();

  const collected = run(process.execPath, [here('collect-packed-receipts.mjs'), downloads], project, env);
  const tail = JSON.parse(collected);
  if (tail.proofCommit !== proofCommit || tail.activationCommit !== activationCommit) {
    throw new Error('Downloaded artifact pins differ from the selected production run');
  }
  const collectorPath = join(output, 'collected.json');
  await writeFile(collectorPath, collected, 'utf8');
  const verifiedTime = performance.now();

  const imports = new Set();
  for (const file of git(project, 'ls-files').split(/\r?\n/).filter(name => name.endsWith('.lean'))) {
    const source = await read(join(project, file));
    for (const match of source.matchAll(/^[ \t]*(?:public[ \t]+)?import[ \t]+(Mathlib\.[\w.]+)/gm)) imports.add(match[1]);
  }
  if (imports.size === 0) throw new Error('No Mathlib sources found in the pinned proof project');
  lake(['exe', 'cache', 'get', ...[...imports].sort()], true);
  if (git(join(project, '.lake/packages/mathlib'), 'rev-parse', 'HEAD') !== mathlib) throw new Error('Mathlib pin mismatch');
  lake(['build', '+DottieWitnessPairBlocks:olean', '+DottieScoreCandidates:olean', '+DottieReferenceCandidate:olean'], true);
  const leanVersion = lake(['env', 'lean', '--version']).trim();
  if (!leanVersion.startsWith('Lean (version 4.33.1,')) throw new Error(`Unexpected Lean ${leanVersion}`);
  const lean = join(lake(['env', 'lean', '--print-prefix']).trim(), 'bin', 'lean');
  const paths = JSON.parse(lake(['env', process.execPath, '-p',
    'JSON.stringify({LEAN_PATH:process.env.LEAN_PATH, LEAN_SRC_PATH:process.env.LEAN_SRC_PATH, PATH:process.env.PATH})']));
  if (!paths.LEAN_PATH) throw new Error('Lake did not supply the proof search path');
  const prepTime = performance.now();

  const checkpoint = join(output, 'prefix-candidates.csv');
  lake(['env', lean, '-j', '1', '-s', '65536', '-DwarningAsError=true', '--run',
    'DottieScoreCandidates.lean', 'paired', checkpoint, '1', '513', '1024'], true);
  lake(['env', process.execPath, here('replay-paired-rows.mjs'), checkpoint, prefixDir, lean,
    '1', '512', '1024', '--witness', '--bundle'], true);
  const totals = new Map();
  for (const line of (await read(checkpoint)).trimEnd().split(/\r?\n/)) {
    const record = /^(\d+),(\d+),(\d+),(-?\d+)$/.exec(line);
    if (!record) throw new Error('Malformed prefix candidate');
    const row = Number(record[1]);
    totals.set(row, (totals.get(row) ?? 0n) + BigInt(record[4]));
  }
  const records = Array.from({ length: 512 }, (_, index) => ({ row: index + 1, ticks: totals.get(index + 1) }));
  const prefix = renderPackedPrefix(records);
  if (totals.size !== 512 || prefix.ticks !== prefixTicks) throw new Error('Checked prefix differs from the audited total');
  const prefixSource = 'DottiePairedRowsThrough512.lean';
  await writeFile(join(prefixDir, prefixSource), prefix.text, 'utf8');
  const prefixReplayTime = performance.now();

  run(process.execPath, [here('assemble-production-spans.mjs'), collectorPath, downloads, prefixDir, assembly], project, env);
  const manifest = JSON.parse(await read(join(assembly, 'build-manifest.json')));
  const nativeEnv = { ...env, ...paths, LC_ALL: 'C',
    LEAN_PATH: [...manifest.leanPath, paths.LEAN_PATH].join(delimiter) };

  async function compile(directory, source, olean, theorems) {
    const t0 = performance.now();
    const result = spawnSync('/usr/bin/time', ['-v', lean, ...manifest.compilerFlags, '-o', olean, source],
      { cwd: directory, env: nativeEnv, encoding: 'utf8', maxBuffer: 32 * 1024 * 1024 });
    if (result.error) throw result.error;
    const log = (result.stdout ?? '') + (result.stderr ?? '');
    await appendFile(join(out, 'build-log.txt'), `${source}\n${log}\n`, 'utf8');
    if (result.status !== 0) throw new Error(`Lean failed on ${source}. See build-log.txt`);
    const audits = theorems.map(theorem => auditLine(log, theorem));
    await appendFile(auditFile, `${audits.join('\n')}\n`, 'utf8');
    timing.push({ source, seconds: (performance.now() - t0) / 1000,
      peakRssKiB: Number(/Maximum resident set size \(kbytes\):\s*(\d+)/.exec(log)?.[1] ?? 0) });
    console.log(audits.join('\n'));
  }

  await compile(prefixDir, prefixSource, 'DottiePairedRowsThrough512.olean', ['QuarticModel.dottiePairedRows_1_512']);
  for (const module of manifest.buildOrder) {
    const theorems = [module.theorem];
    if (module.source === 'DottieProductionFull.lean') theorems.push(
      'QuarticModel.dottieProductionFullSpan_eq_candidate',
      'QuarticModel.dottieProductionQuickReferenceScore_eq_candidate',
      manifest.circleReferenceTheorem,
    );
    await compile(assembly, module.source, module.olean, theorems);
  }
  const attachments = ['DottieProductionFull.lean', 'DottieProductionFull.olean', 'build-manifest.json'];
  for (const file of attachments) await copyFile(join(assembly, file), join(out, file));
  await copyFile(join(prefixDir, prefixSource), join(out, prefixSource));
  const hashes = {};
  for (const file of [...attachments, prefixSource, 'build-log.txt', 'kernel-audits.txt']) {
    hashes[file] = sha256(await readFile(join(out, file)));
  }
  await writeFile(join(out, 'proof-receipt.json'), `${JSON.stringify({
    productionRun, proofCommit, activationCommit, leanVersion, mathlib,
    candidateTicks: manifest.candidateTicks, result: manifest.circleReferenceTheorem,
    timing, seconds: { artifactVerification: (verifiedTime - started) / 1000,
      dependencyBuild: (prepTime - verifiedTime) / 1000, prefixReplay: (prefixReplayTime - prepTime) / 1000,
      totalBeforeUpload: (performance.now() - started) / 1000 },
    hashes,
  }, null, 2)}\n`, 'utf8');
}

if (process.argv[1] && pathToFileURL(process.argv[1]).href === import.meta.url) await main();

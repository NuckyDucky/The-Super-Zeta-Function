import { execFileSync } from 'node:child_process';
import { appendFileSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const marker = '.github/dottie-packed-production.json';
const git = (...args) => execFileSync('git', args, { encoding: 'utf8' }).trim();
const [directory] = process.argv.slice(2);
const { DOTTIE_ACTIVATION_SHA, GITHUB_OUTPUT } = process.env;
if (!directory || !GITHUB_OUTPUT || !/^[a-f0-9]{40}$/.test(DOTTIE_ACTIVATION_SHA)) {
  throw new Error('Expected artifact directory, activation SHA, and GITHUB_OUTPUT');
}
const head = git('rev-parse', 'HEAD');
if (head !== DOTTIE_ACTIVATION_SHA) throw new Error('Checkout does not match the PR event head');
const parents = git('show', '-s', '--format=%P', head).split(' ');
const changes = parents.length === 1 && parents[0]
  ? git('diff-tree', '--no-commit-id', '--name-status', '--no-renames', '-r', parents[0], head)
  : '';
if (changes !== `A\t${marker}` && changes !== `M\t${marker}`) {
  appendFileSync(GITHUB_OUTPUT, 'enabled=false\n');
  console.log('Opt-in requires a marker-only commit. Production replay skipped.');
} else {
  const bytes = readFileSync(marker);
  const control = JSON.parse(bytes.toString('utf8'));
  const proof = parents[0];
  if (control.replay !== 'packed-witness-513-16638-v1' || control.proofCommit !== proof) {
    throw new Error('Marker must explicitly select the full packed replay and name its sole parent proof SHA');
  }
  const planner = fileURLToPath(new URL('./plan-packed-replay.mjs', import.meta.url));
  const plan = JSON.parse(execFileSync(process.execPath, [planner, '--json'], { encoding: 'utf8' }));
  if (plan.first !== 513 || plan.last !== 16638 || plan.jobs.length !== 36 ||
      plan.totalWork !== 108563533 || plan.maxParallel !== 18) {
    throw new Error('Planner produced an unexpected production workload');
  }
  const matrix = { include: plan.jobs.map(({ first, last, work }) => ({ first, last, work })) };
  mkdirSync(directory, { recursive: true });
  writeFileSync(join(directory, 'activation.json'), bytes);
  writeFileSync(join(directory, 'plan.json'), `${JSON.stringify({
    proofCommit: proof, activationCommit: head, ...plan,
  }, null, 2)}\n`);
  appendFileSync(GITHUB_OUTPUT, `enabled=true\nproof=${proof}\nmatrix=${JSON.stringify(matrix)}\n`);
}

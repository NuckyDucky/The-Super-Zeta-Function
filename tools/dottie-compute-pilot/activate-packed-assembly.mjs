import { execFileSync } from 'node:child_process';
import { appendFileSync, readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';

const marker = '.github/dottie-packed-assembly.json';
const workflow = '.github/workflows/dottie-packed-production.yml';
const git = (...args) => execFileSync('git', args, { encoding: 'utf8' }).trim();

export function validateProduction(markerData, repository, run, activation) {
  const { assembly, productionRunId, proofCommit, activationCommit } = markerData;
  if (assembly !== 'packed-witness-full-assembly-v1' || !Number.isSafeInteger(productionRunId) ||
      productionRunId < 1 || !/^[a-f0-9]{40}$/.test(proofCommit) || !/^[a-f0-9]{40}$/.test(activationCommit)) {
    throw new Error('Expected an explicit assembly marker with production run ID and two full SHAs');
  }
  if (run.id !== productionRunId || run.path?.split('@')[0] !== workflow || run.run_attempt !== 1 ||
      run.status !== 'completed' || run.conclusion !== 'success' || run.event !== 'pull_request' ||
      run.head_sha !== activationCommit || run.head_repository?.full_name !== repository) {
    throw new Error('Selected run is not a successful production replay at the requested activation SHA');
  }
  if (activation.sha !== activationCommit || activation.parents?.length !== 1 ||
      activation.parents[0].sha !== proofCommit) {
    throw new Error('Production activation does not descend directly from the requested proof SHA');
  }
}

function main() {
  const { GITHUB_OUTPUT, GITHUB_REPOSITORY, DOTTIE_ASSEMBLY_SHA } = process.env;
  const head = git('rev-parse', 'HEAD');
  if (!GITHUB_OUTPUT || !GITHUB_REPOSITORY || head !== DOTTIE_ASSEMBLY_SHA) {
    throw new Error('Assembly checkout does not match the PR event head');
  }
  const parents = git('show', '-s', '--format=%P', head).split(' ');
  const diff = parents.length === 1 && parents[0]
    ? git('diff-tree', '--no-commit-id', '--name-status', '--no-renames', '-r', parents[0], head)
    : '';
  if (diff !== `A\t${marker}` && diff !== `M\t${marker}`) {
    appendFileSync(GITHUB_OUTPUT, 'enabled=false\n');
    return;
  }
  const request = JSON.parse(readFileSync(marker, 'utf8'));
  const { productionRunId, proofCommit, activationCommit } = request;
  if (!Number.isSafeInteger(productionRunId) || productionRunId < 1 ||
      !/^[a-f0-9]{40}$/.test(activationCommit)) throw new Error('Invalid run ID or activation SHA');
  const api = path => JSON.parse(execFileSync('gh', [
    'api', '--method', 'GET', `repos/${GITHUB_REPOSITORY}/${path}`,
  ], { encoding: 'utf8' }));
  validateProduction(request, GITHUB_REPOSITORY, api(`actions/runs/${productionRunId}`),
    api(`git/commits/${activationCommit}`));
  appendFileSync(GITHUB_OUTPUT, `enabled=true\nrun_id=${productionRunId}\nproof=${proofCommit}\nactivation=${activationCommit}\n`);
}

if (process.argv[1] && pathToFileURL(process.argv[1]).href === import.meta.url) main();

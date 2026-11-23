import { parseArgs } from 'node:util';

const cutoff = 276824064;
const maxRow = floorSqrt(cutoff);
const calibration = { row: 11000, positions: 10999, seconds: 51.9001127 };

function floorSqrt(n) {
  const root = Math.floor(Math.sqrt(n));
  if (!(root * root <= n && n < (root + 1) * (root + 1))) {
    throw new Error(`Could not verify the integer square root of ${n}`);
  }
  return root;
}

function rowWork(row) {
  return Math.min(row - 1, floorSqrt(cutoff - row * row));
}

function positiveInteger(text, name, maximum) {
  const value = Number(text);
  if (!/^[1-9][0-9]*$/.test(text) || !Number.isSafeInteger(value) || value > maximum) {
    throw new Error(`${name} must be an integer from 1 through ${maximum}`);
  }
  return value;
}

function nearestCut(prefix, first, last, target, jobCount) {
  let low = first;
  let high = last;
  while (low < high) {
    const middle = Math.floor((low + high) / 2);
    if (jobCount * prefix[middle] < target) low = middle + 1;
    else high = middle;
  }
  const earlier = low - 1;
  if (earlier >= first &&
      Math.abs(jobCount * prefix[earlier] - target) <= Math.abs(jobCount * prefix[low] - target)) {
    return earlier;
  }
  return low;
}

function estimateSeconds(work) {
  return work * calibration.seconds / calibration.positions;
}

function makePlan(first, last, requestedJobs, maxParallel) {
  const rowCount = last - first + 1;
  const jobCount = Math.min(requestedJobs, rowCount);
  const prefix = [0];
  for (let row = first; row <= last; row++) prefix.push(prefix.at(-1) + rowWork(row));
  const totalWork = prefix.at(-1);

  const jobs = [];
  let previousCut = 0;
  for (let job = 1; job <= jobCount; job++) {
    // Scale the prefix and target by jobCount to compare exact integers.
    const cut = job === jobCount ? rowCount : nearestCut(
      prefix, previousCut + 1, rowCount - (jobCount - job), job * totalWork, jobCount,
    );
    const work = prefix[cut] - prefix[previousCut];
    jobs.push({
      job,
      wave: Math.floor((job - 1) / maxParallel) + 1,
      first: first + previousCut,
      last: first + cut - 1,
      work,
      estimatedSeconds: estimateSeconds(work),
    });
    previousCut = cut;
  }

  let nextRow = first;
  let coveredWork = 0;
  for (const job of jobs) {
    if (job.first !== nextRow || job.last < job.first || job.last > last) {
      throw new Error(`Invalid range coverage at job ${job.job}`);
    }
    nextRow = job.last + 1;
    coveredWork += job.work;
  }
  if (nextRow !== last + 1 || coveredWork !== totalWork) {
    throw new Error('The plan does not cover the requested rows and workload');
  }

  const waves = [];
  for (let start = 0; start < jobs.length; start += maxParallel) {
    const waveJobs = jobs.slice(start, start + maxParallel);
    waves.push({
      wave: waves.length + 1,
      first: waveJobs[0].first,
      last: waveJobs.at(-1).last,
      jobCount: waveJobs.length,
      work: waveJobs.reduce((sum, job) => sum + job.work, 0),
      estimatedSeconds: Math.max(...waveJobs.map(job => job.estimatedSeconds)),
    });
  }

  return {
    cutoff, first, last, rowCount, requestedJobs, jobCount, maxParallel, totalWork,
    timingProjection: {
      model: 'Linear replay estimate from paired positions',
      calibration,
      estimatedSerialSeconds: estimateSeconds(totalWork),
      estimatedWaveWallSeconds: waves.reduce((sum, wave) => sum + wave.estimatedSeconds, 0),
    },
    jobs,
    waves,
  };
}

function githubMatrix(jobs) {
  return { include: jobs.map(({ first, last, work }) => ({ first, last, work })) };
}

function main() {
  const { values } = parseArgs({
    options: {
      first: { type: 'string', default: '513' },
      last: { type: 'string', default: '16638' },
      jobs: { type: 'string', default: '36' },
      'max-parallel': { type: 'string', default: '18' },
      json: { type: 'boolean' },
      matrix: { type: 'boolean' },
      wave: { type: 'string' },
      help: { type: 'boolean' },
    },
  });
  if (values.help) {
    process.stdout.write(
      'Usage: node plan-packed-replay.mjs [--first N] [--last N] [--jobs N] [--max-parallel N]\n' +
      '                                  [--json | --matrix [--wave N]]\n' +
      'Defaults: rows 513 through 16638, up to 36 jobs, at most 18 per wave.\n' +
      'The default output is a full JSON plan. --matrix emits compact GitHub matrix JSON.\n',
    );
    return;
  }
  if (values.json && values.matrix) throw new Error('Choose --json or --matrix');
  if (values.wave !== undefined && !values.matrix) throw new Error('--wave requires --matrix');

  const first = positiveInteger(values.first, '--first', maxRow);
  const last = positiveInteger(values.last, '--last', maxRow);
  const requestedJobs = positiveInteger(values.jobs, '--jobs', 256);
  const maxParallel = positiveInteger(values['max-parallel'], '--max-parallel', 18);
  if (first > last) throw new Error('--first must not exceed --last');

  const plan = makePlan(first, last, requestedJobs, maxParallel);
  if (values.matrix) {
    const wave = values.wave === undefined ? null : positiveInteger(values.wave, '--wave', plan.waves.length);
    const jobs = wave === null ? plan.jobs : plan.jobs.filter(job => job.wave === wave);
    process.stdout.write(`${JSON.stringify(githubMatrix(jobs))}\n`);
    return;
  }
  process.stdout.write(`${JSON.stringify(plan, null, 2)}\n`);
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exitCode = 1;
}

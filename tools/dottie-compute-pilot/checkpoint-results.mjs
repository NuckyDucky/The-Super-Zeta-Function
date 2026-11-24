import { execFile } from 'node:child_process';
import { createHash, randomUUID } from 'node:crypto';
import { mkdir, readFile, readdir, rename, unlink, writeFile } from 'node:fs/promises';
import { basename, join, resolve } from 'node:path';
import { setTimeout as wait } from 'node:timers/promises';
import { pathToFileURL } from 'node:url';
import { promisify } from 'node:util';
import { gzipSync, gunzipSync } from 'node:zlib';

const execute = promisify(execFile);
const format = 'lean-proof-checkpoint-v1';
const prefix = 'lean-checkpoint-';
const archivePattern = /^lean-checkpoint-([0-9a-f]{64})\.json\.gz$/;
const filePattern = /^[A-Za-z0-9][A-Za-z0-9_.-]*\.(?:lean|olean|log|txt|json)$/;
const intervalMs = 180_000;
const hash = bytes => createHash('sha256').update(bytes).digest('hex');

async function atomicWrite(path, bytes) {
  const temporary = `${path}.${randomUUID()}.tmp`;
  await writeFile(temporary, bytes, { flag: 'wx', flush: true });
  try {
    await rename(temporary, path);
  } finally {
    await unlink(temporary).catch(error => {
      if (error.code !== 'ENOENT') throw error;
    });
  }
}

function requireDistinctNames(files) {
  const names = new Set();
  for (const file of files) {
    if (!filePattern.test(file.name) || names.has(file.name.toLowerCase())) {
      throw new Error(`Invalid or duplicate checkpoint member ${file.name}`);
    }
    names.add(file.name.toLowerCase());
  }
}

export async function sealCheckpoint(spool, paths) {
  if (paths.length === 0) throw new Error('A checkpoint needs at least one file.');
  const files = await Promise.all(paths.map(async path => {
    const bytes = await readFile(path);
    return { name: basename(path), sha256: hash(bytes), data: bytes.toString('base64') };
  }));
  requireDistinctNames(files);
  files.sort((left, right) => left.name.localeCompare(right.name, 'en'));
  const archive = gzipSync(JSON.stringify({ format, files }));
  const name = `${prefix}${hash(archive)}.json.gz`;
  await mkdir(spool, { recursive: true });
  const path = resolve(spool, name);
  await atomicWrite(path, archive);
  return path;
}

async function restoreCheckpoint(path, output) {
  const archive = await readFile(path);
  const digest = basename(path).match(archivePattern)?.[1];
  if (!digest || hash(archive) !== digest) throw new Error('Checkpoint archive checksum mismatch.');
  const packet = JSON.parse(gunzipSync(archive).toString('utf8'));
  if (packet.format !== format || !Array.isArray(packet.files) || packet.files.length === 0) {
    throw new Error('Unrecognized checkpoint data.');
  }
  requireDistinctNames(packet.files);
  const files = packet.files.map(file => {
    const bytes = Buffer.from(file.data, 'base64');
    if (hash(bytes) !== file.sha256) throw new Error(`Checkpoint checksum mismatch for ${file.name}`);
    return { name: file.name, bytes };
  });
  await mkdir(output, { recursive: true });
  for (const file of files) {
    const destination = join(output, file.name);
    try {
      await writeFile(destination, file.bytes, { flag: 'wx', flush: true });
    } catch (error) {
      if (error.code !== 'EEXIST' || !(await readFile(destination)).equals(file.bytes)) throw error;
    }
  }
  console.log(`Restored ${files.length} checked files to ${output}`);
}

async function github(args) {
  const result = await execute('gh', args, { windowsHide: true, timeout: 120_000, maxBuffer: 8 * 1024 ** 2 });
  return result.stdout;
}

async function releases(repo) {
  return JSON.parse(await github(['api', `repos/${repo}/releases?per_page=100`, '--paginate', '--slurp'])).flat();
}

async function assets(repo, releaseId) {
  return JSON.parse(await github(['api', `repos/${repo}/releases/${releaseId}/assets?per_page=100`, '--paginate', '--slurp'])).flat();
}

async function publishPending(spool, repo, tag) {
  await mkdir(spool, { recursive: true });
  const pending = (await readdir(spool)).filter(name => archivePattern.test(name)).sort();
  if (pending.length === 0) return;
  const visibility = (await github(['api', `repos/${repo}`, '--jq', '.visibility'])).trim();
  if (visibility !== 'private') throw new Error('Checkpoint destination must be the private backup repo.');
  const release = (await releases(repo)).find(candidate => candidate.tag_name === tag);
  if (!release) throw new Error(`Create checkpoint release ${tag} in ${repo} first.`);
  const uploaded = new Map((await assets(repo, release.id)).map(asset => [asset.name, asset]));

  for (const name of pending) {
    const path = resolve(spool, name);
    const checksum = archivePattern.exec(name)[1];
    if (hash(await readFile(path)) !== checksum) throw new Error(`Damaged local checkpoint: ${name}`);
    let asset = uploaded.get(name);
    if (!asset) {
      try {
        await github(['release', 'upload', tag, path, '--repo', repo]);
      } catch (error) {
        const match = (await assets(repo, release.id)).find(candidate => candidate.name === name);
        if (!match) throw error;
      }
      asset = (await assets(repo, release.id)).find(candidate => candidate.name === name);
    }
    if (asset?.state !== 'uploaded' || asset.digest !== `sha256:${checksum}`) {
      throw new Error(`GitHub did not confirm the checksum for ${name}. The local checkpoint is queued.`);
    }
    await atomicWrite(join(spool, `${name}.receipt.json`), JSON.stringify({ repo, tag, id: asset.id, sha256: checksum }));
    await unlink(path);
    console.log(`GitHub confirmed ${name}`);
  }
}

async function main([command, input, ...args]) {
  if (command === 'seal' && input && args.length > 0) {
    console.log(await sealCheckpoint(input, args));
    return;
  }
  if (command === 'restore' && input && args.length === 1) {
    await restoreCheckpoint(input, args[0]);
    return;
  }
  if (command === 'mirror' && input && (args.length === 2 || (args.length === 3 && args[2] === '--watch'))) {
    const [repo, tag, watch] = args;
    if (!/^[A-Za-z0-9][\w.-]*\/[A-Za-z0-9][\w.-]*$/.test(repo) || !/^[A-Za-z0-9][\w.-]*$/.test(tag)) {
      throw new Error('Invalid repo or release tag.');
    }
    if (!watch) {
      await publishPending(input, repo, tag);
      return;
    }
    for (;;) {
      const started = Date.now();
      try {
        await publishPending(input, repo, tag);
      } catch (error) {
        console.error(`Checkpoint mirror will retry: ${error.message}`);
      }
      await wait(Math.max(1000, intervalMs - (Date.now() - started)));
    }
  }
  throw new Error('Usage: checkpoint-results.mjs seal SPOOL FILE... | restore ARCHIVE OUT | mirror SPOOL OWNER/REPO TAG [--watch]');
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  main(process.argv.slice(2)).catch(error => {
    console.error(error.message);
    process.exitCode = 1;
  });
}

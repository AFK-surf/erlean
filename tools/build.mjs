// Serialize module compilation, including native objects, to bound peak memory.
import { readdirSync, readFileSync, mkdirSync, openSync, writeSync, closeSync, unlinkSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';

mkdirSync('.lake', { recursive: true });
const lock = '.lake/erlean-build.lock';
let descriptor;
try {
  descriptor = openSync(lock, 'wx');
} catch (error) {
  if (error.code !== 'EEXIST') throw error;
  const owner = Number(readFileSync(lock, 'utf8'));
  if (!Number.isSafeInteger(owner) || owner <= 0) throw new Error(`Inspect invalid build lock: ${lock}`);
  try {
    process.kill(owner, 0);
    throw new Error(`Another build owns ${lock} (PID ${owner})`);
  } catch (probe) {
    if (probe.code !== 'ESRCH') throw probe;
  }
  unlinkSync(lock);
  descriptor = openSync(lock, 'wx');
}
writeSync(descriptor, String(process.pid));
closeSync(descriptor);

function scan(directory) {
  return readdirSync(directory, { withFileTypes: true }).flatMap(entry => {
    const path = join(directory, entry.name);
    return entry.isDirectory() ? scan(path) : path.endsWith('.lean') ? [path] : [];
  });
}

function run(args) {
  const result = spawnSync('lake', args, { stdio: 'inherit', timeout: 180000 });
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(`lake ${args.join(' ')} failed (${result.status ?? result.signal})`);
}

try {
  const files = [...scan('Erlean'), 'Erlean.lean', 'Main.lean'];
  const modules = new Map(files.map(path => [path.replace(/\.lean$/, '').replaceAll('/', '.'), path]));
  const built = new Set();
  const visiting = new Set();
  function build(name) {
    if (built.has(name) || !modules.has(name)) return;
    if (visiting.has(name)) throw new Error(`Cyclic repository import: ${name}`);
    visiting.add(name);
    const text = readFileSync(modules.get(name), 'utf8');
    for (const line of text.split('\n')) {
      const match = line.match(/^\s*import\s+([A-Za-z][A-Za-z0-9_.]*)\s*$/);
      if (match) build(match[1]);
    }
    console.log(`Building ${name} sequentially...`);
    run(['build', `+${name}:o`]);
    visiting.delete(name);
    built.add(name);
  }
  for (const name of modules.keys()) build(name);
  run(['build', 'erlean']);
} finally {
  unlinkSync(lock);
}

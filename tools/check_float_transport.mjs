// Bit-preserving float transport checks; no floating-point computation proof.
import assert from 'node:assert/strict';
import { normalizeTermJson as normalize } from './term_json.mjs';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const flags = new Set(process.argv.slice(2));
assert.ok([...flags].every(flag => flag === '--skip-export'), 'Unknown float transport option');
const source = 'tests/fixtures/erlang/float_transport.erl';
const directory = 'tests/fixtures/erlang/float_transport';
const artifact = join(directory, 'core.json');
const exporter = 'tools/export_core.escript';
const executable = '.lake/build/bin/erlean';
const env = { ...process.env, ASDF_ERLANG_VERSION: '29.0.6', ERL_FLAGS: '+S 2:2 +SDcpu 1 +SDio 1' };
const temporary = mkdtempSync(join(tmpdir(), 'erlean-float-transport-'));
function invoke(command, args) {
  const result = spawnSync(command, args,
    { env, encoding: 'utf8', timeout: 30000, maxBuffer: 16 * 1024 * 1024 });
  if (result.error) throw result.error;
  return result;
}
function run(command, args) {
  const result = invoke(command, args);
  assert.equal(result.status, 0, `${command}: ${result.stderr}`);
  return result.stdout;
}
const hash = path => createHash('sha256').update(readFileSync(path)).digest('hex');
const manifest = JSON.parse(readFileSync(join(directory, 'manifest.json'), 'utf8'));
assert.equal(manifest.otp_version, '29.0.6');
assert.equal(manifest.source, source);
assert.deepEqual(manifest.compiler_options,
  ['to_core', 'binary', 'no_copt', 'deterministic', 'return_errors', 'return_warnings']);
assert.equal(manifest.source_sha256, hash(source));
assert.equal(manifest.core_sha256, hash(artifact));
assert.equal(manifest.exporter_sha256, hash(exporter));
if (!flags.has('--skip-export')) {
  for (const attempt of ['first', 'second']) {
    const destination = join(temporary, attempt);
    run('asdf', ['exec', 'escript', exporter, source, destination]);
    for (const name of ['core.json', 'manifest.json', 'inventory.json']) {
      assert.deepEqual(readFileSync(join(destination, name)), readFileSync(join(directory, name)),
        `Reproducible float transport ${name}`);
    }
  }
}
const report = JSON.parse(run(executable, ['inspect', artifact]));
assert.equal(report.module, 'erlean_float_transport');
assert.deepEqual(report.rejected, []);

const atom = value => ({ tag: 'atom', value });
const float = bits => ({ tag: 'float', bits });
const map = (...entries) => ({ tag: 'map', entries });
const tuple = (...items) => ({ tag: 'tuple', items });
const nil = { tag: 'nil' };
const cons = (head, tail) => ({ tag: 'cons', head, tail });
const samples = [
  '0000000000000000', // Positive zero.
  '8000000000000000', // Negative zero: transport must retain its sign bit.
  '0000000000000001', // Smallest positive subnormal.
  '8000000000000001', // Smallest negative subnormal.
  '0010000000000000', // Smallest positive normal.
  '7fefffffffffffff', // Largest finite positive value.
  'ffefffffffffffff', // Largest finite negative magnitude.
  '3ff8000000000000', // 1.5.
  'c004000000000000', // -2.5.
];
const cases = [];
const add = (fn, args, value) => cases.push({ function: fn, arguments: args,
  expected: { status: 'returned', values: [value] } });
add('literal', [], map([atom('payload'), float('3ff8000000000000')]));
for (const bits of samples) {
  const value = float(bits);
  add('identity', [value], value);
  add('wrap', [value], cons(value, cons(tuple(atom('payload'), value), nil)));
  add('nested', [value], map([atom('outer'), map([atom('payload'), value])]));
  add('put_get', [value, map([atom('other'), float('3ff0000000000000')])], value);
}
// The payload itself may contain floats behind several container boundaries.
const nested = map([atom('items'), cons(float(samples[1]), cons(float(samples[2]), nil))]);
// CLI input uses its existing list codec, while expected results use cons cells.
const nestedInput = map([atom('items'), { tag: 'list',
  items: [float(samples[1]), float(samples[2])], tail: nil }]);
add('identity', [nestedInput], nested);
add('put_get', [nestedInput, map()], nested);
const casesPath = join(temporary, 'cases.json');
writeFileSync(casesPath, JSON.stringify(cases));
const actual = JSON.parse(run(executable, ['run-batch', artifact, casesPath, '10000']));
assert.ok(Array.isArray(actual));
assert.equal(actual.length, cases.length);
for (const [index, test] of cases.entries()) {
  const oracle = JSON.parse(run('asdf', ['exec', 'escript', 'tools/otp_oracle.escript',
    source, test.function, JSON.stringify(test.arguments)]));
  assert.deepEqual(normalize(actual[index]), normalize(oracle), `Float differential ${index}: ${test.function}`);
  assert.deepEqual(normalize(actual[index]), normalize(test.expected), `Float bits preserved at case ${index}`);
}

function reject(fn, args, diagnostic) {
  const result = invoke(executable, ['run', artifact, fn, JSON.stringify(args), '10000']);
  assert.equal(result.status, 1, `Unsupported float operation ${fn} must fail closed`);
  assert.match(result.stderr, diagnostic);
  assert.equal(result.stdout.trim(), '', 'Rejected operation must not emit a semantic result');
}
for (const fn of ['plus', 'minus', 'multiply']) {
  reject(fn, [float(samples[7]), float(samples[8])], /unsupported/i);
  reject(fn, [float(samples[7]), { tag: 'integer', value: '1' }], /unsupported/i);
  reject(fn, [{ tag: 'integer', value: '1' }, float(samples[7])], /unsupported/i);
}
for (const fn of ['equal', 'exact_equal']) {
  reject(fn, [float(samples[0]), float(samples[1])], /unsupported/i);
  reject(fn, [nestedInput, nestedInput], /unsupported/i);
}
reject('key', [float(samples[7])], /unsupported|outside.*profile/i);
for (const bits of ['7ff0000000000000', 'fff0000000000000', '7ff8000000000000',
  '7ff0000000000001', '123', 'zzzzzzzzzzzzzzzz']) {
  reject('identity', [float(bits)], /float|finite|hex/i);
}
console.log(`Float transport checks passed: ${cases.length} bit-exact OTP 29.0.6 cases plus explicit unsupported-operation and malformed/nonfinite-input rejections. No numeric or float-equality semantics are claimed.`);

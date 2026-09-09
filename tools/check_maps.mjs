// Compatibility checks for the finite data-map profile, not a universal proof.
import assert from 'node:assert/strict';
import { normalizeTermJson as normalize } from './term_json.mjs';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const flags = new Set(process.argv.slice(2));
assert.ok([...flags].every(flag => flag === '--skip-export'), 'Unknown check_maps option');
const source = 'tests/fixtures/erlang/maps.erl';
const directory = 'tests/fixtures/erlang/maps';
const artifact = join(directory, 'core.json');
const exporter = 'tools/export_core.escript';
const executable = '.lake/build/bin/erlean';
const env = { ...process.env, ASDF_ERLANG_VERSION: '29.0.6', ERL_FLAGS: '+S 2:2 +SDcpu 1 +SDio 1' };
const temporary = mkdtempSync(join(tmpdir(), 'erlean-maps-'));

function run(command, args) {
  const result = spawnSync(command, args, { env, encoding: 'utf8', timeout: 30000, maxBuffer: 16 * 1024 * 1024 });
  if (result.error) throw result.error;
  assert.equal(result.status, 0, `${command} ${args.slice(0, 3).join(' ')}: ${result.stderr}`);
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
        `Reproducible maps ${name}`);
    }
  }
}
const report = JSON.parse(run(executable, ['inspect', artifact]));
assert.equal(report.module, 'erlean_maps');
assert.deepEqual(report.rejected, [], 'The complete fixture must lower without rejected functions');

const atom = value => ({ tag: 'atom', value });
const integer = value => ({ tag: 'integer', value: String(value) });
const tuple = (...items) => ({ tag: 'tuple', items });
const nil = { tag: 'nil' };
const list = (...items) => ({ tag: 'list', items, tail: nil });
const map = (...entries) => ({ tag: 'map', entries });
const a = atom('a');
const b = atom('b');
const empty = map();
const one = map([a, integer(1)]);
const two = map([a, integer(1)], [b, integer(2)]);
const reordered = map([b, integer(2)], [a, integer(1)]);
const cases = [];
const add = (fn, args, expected) => cases.push({ function: fn, arguments: args, expected });
const returned = value => ({ status: 'returned', values: [value] });
const raised = reason => ({ status: 'raised', class: 'error', reason });

add('literal', [], returned(map([atom('answer'), integer(42)],
  [atom('nested'), map([atom('items'), list(a, b)])], [integer(1), atom('integer_key')])));
add('construct', [a, integer(1), a, integer(2)], returned(map([a, integer(2)])));
add('construct', [integer(1), a, atom('1'), b], returned(map([integer(1), a], [atom('1'), b])));
add('construct', [tuple(a, integer(1)), one, list(a), two]);
for (const key of [nil, integer(-7), tuple(), list(a, b),
  { tag: 'list', items: [a], tail: b },
  { tag: 'bitstring', bits: '3', hex: 'a0' }]) {
  add('construct', [key, integer(1), key, integer(2)], returned(map([key, integer(2)])));
  add('get', [key, map([key, two])], returned(two));
}
add('assoc', [one, b, integer(2)], returned(two));
add('assoc', [two, a, integer(3)], returned(map([a, integer(3)], [b, integer(2)])));
add('exact', [two, a, integer(3)], returned(map([a, integer(3)], [b, integer(2)])));
add('exact', [empty, a, integer(3)], raised(tuple(atom('badkey'), a)));
add('mixed', [empty, a, integer(1), a, integer(2)]);
add('exact_then_assoc', [empty, a, integer(1), a, integer(2)]);
add('ambiguous_exact', [map([atom('z'), integer(0)], [a, integer(0)])],
  returned(map([atom('z'), integer(1)], [a, integer(2)])));
add('ambiguous_exact', [one], raised(tuple(atom('badkey'), atom('z'))));
add('mixed', [one, b, integer(2), a, integer(3)]);
for (const fn of ['assoc', 'exact']) add(fn, [atom('bad'), a, integer(1)], raised(tuple(atom('badmap'), atom('bad'))));
for (const value of [map([atom('answer'), one]), one, atom('bad')]) add('literal_pattern', [value]);
add('nested_pattern', [map([atom('outer'), map([atom('inner'), two])])], returned(tuple(atom('found'), two)));
add('nested_pattern', [map([atom('outer'), atom('bad')])], returned(atom('absent')));
for (const [value, outcome] of [
  [{ tag: 'bitstring', bits: '40', hex: '7265616479' }, 'ready'],
  [{ tag: 'bitstring', bits: '3', hex: 'a0' }, 'partial'],
  [{ tag: 'bitstring', bits: '8', hex: 'a0' }, 'absent'],
  [{ tag: 'bitstring', bits: '48', hex: '726561647900' }, 'absent'],
  [atom('ready'), 'absent'], [map(), 'absent']]) {
  add('packed_pattern', [map([atom('status'), value])], returned(atom(outcome)));
}
for (const value of [empty, two, atom('bad')]) {
  add('empty_pattern', [value], returned(atom(value.tag === 'map' ? 'matched' : 'absent')));
}
for (const [key, value] of [[a, one], [b, one], [a, atom('bad')]]) add('guard_lookup', [key, value]);
add('exact_equal', [two, reordered], returned(atom('true')));
add('exact_equal', [one, two], returned(atom('false')));
add('exact_equal', [map([a, two]), map([a, reordered])], returned(atom('true')));
// Loose and exact equality agree only within this float-free data profile.
for (const [left, right, same] of [[two, reordered, true], [one, two, false],
  [integer(1), atom('1'), false], [list(a), list(a), true],
  [map([a, two]), map([a, reordered]), true]]) {
  add('equal', [left, right], returned(atom(String(same))));
  add('not_equal', [left, right], returned(atom(String(!same))));
  add('exact_not_equal', [left, right], returned(atom(String(!same))));
}
for (const [value, accepted] of [
  [{ tag: 'bitstring', bits: '0', hex: '' }, false],
  [{ tag: 'bitstring', bits: '8', hex: '00' }, true],
  [{ tag: 'bitstring', bits: '16', hex: '0102' }, true],
  [{ tag: 'bitstring', bits: '3', hex: 'a0' }, false], [a, false], [one, false]]) {
  add('binary_id', [value], returned(atom(accepted ? 'accepted' : 'rejected')));
}
for (const value of [empty, two, atom('bad'), nil]) add('is_map_value', [value], returned(atom(value.tag === 'map' ? 'true' : 'false')));
for (const fn of ['get', 'has_key', 'library_get', 'library_find', 'library_remove', 'library_take']) {
  for (const [key, value] of [[a, two], [atom('missing'), two], [a, atom('bad')]]) add(fn, [key, value]);
}
add('size', [two], returned(integer(2)));
add('size', [atom('bad')], raised(tuple(atom('badmap'), atom('bad'))));
add('library_put', [a, integer(4), two], returned(map([a, integer(4)], [b, integer(2)])));
add('library_put', [a, integer(4), atom('bad')], raised(tuple(atom('badmap'), atom('bad'))));
add('library_update', [a, integer(4), two], returned(map([a, integer(4)], [b, integer(2)])));
add('library_update', [atom('missing'), integer(4), two], raised(tuple(atom('badkey'), atom('missing'))));
add('library_update', [a, integer(4), atom('bad')], raised(tuple(atom('badmap'), atom('bad'))));
add('library_get_default', [a, one, atom('default')], returned(integer(1)));
add('library_get_default', [b, one, atom('default')], returned(atom('default')));
add('library_get_default', [a, atom('bad'), atom('default')], raised(tuple(atom('badmap'), atom('bad'))));
add('library_merge', [one, map([a, integer(3)], [b, integer(2)])], returned(map([a, integer(3)], [b, integer(2)])));
add('library_merge', [atom('bad'), one], raised(tuple(atom('badmap'), atom('bad'))));
add('library_merge', [one, atom('bad')], raised(tuple(atom('badmap'), atom('bad'))));
for (const fn of ['key_order', 'value_order', 'pair_order', 'exact_value_order']) {
  for (const value of [empty, atom('bad')]) add(fn, [value]);
}
add('base_order', []);

const casesPath = join(temporary, 'cases.json');
writeFileSync(casesPath, JSON.stringify(cases));
const actual = JSON.parse(run(executable, ['run-batch', artifact, casesPath, '10000']));
assert.ok(Array.isArray(actual));
assert.equal(actual.length, cases.length);
for (const [index, test] of cases.entries()) {
  const oracle = JSON.parse(run('asdf', ['exec', 'escript', 'tools/otp_oracle.escript',
    source, test.function, JSON.stringify(test.arguments)]));
  assert.deepEqual(normalize(actual[index]), normalize(oracle), `Map differential ${index}: ${test.function}`);
  if (test.expected !== undefined) {
    assert.deepEqual(normalize(actual[index]), normalize(test.expected), `Independent map expectation ${index}`);
  }
}
// Multiple absent exact-update keys are an explicit model boundary, not an
// omitted compatibility case. Record OTP's result without adopting its key order.
const ambiguousOracle = JSON.parse(run('asdf', ['exec', 'escript', 'tools/otp_oracle.escript',
  source, 'ambiguous_exact', JSON.stringify([empty])]));
assert.equal(ambiguousOracle.status, 'raised');
assert.equal(ambiguousOracle.class, 'error');
assert.equal(ambiguousOracle.reason.tag, 'tuple');
assert.deepEqual(ambiguousOracle.reason.items[0], atom('badkey'));
assert.ok(['a', 'z'].includes(ambiguousOracle.reason.items[1].value));
const ambiguousModel = spawnSync(executable,
  ['run', artifact, 'ambiguous_exact', JSON.stringify([empty]), '10000'],
  { env, encoding: 'utf8', timeout: 30000, maxBuffer: 16 * 1024 * 1024 });
if (ambiguousModel.error) throw ambiguousModel.error;
assert.equal(ambiguousModel.status, 1, 'Ambiguous exact-map failure must be a model fault');
assert.match(ambiguousModel.stderr, /Ambiguous exact-map update failure/);
assert.equal(ambiguousModel.stdout.trim(), '', 'Rejected map execution must not emit a semantic outcome');
console.log(`Explicit map boundary: OTP ambiguous exact update ${JSON.stringify(ambiguousOracle)}; model rejects it.`);
console.log(`Map checks passed: ${cases.length} OTP 29.0.6 cases covering updates, nested map values, exact data keys, literal-key patterns, BIFs, and error evaluation order. Testing is not a correctness proof.`);

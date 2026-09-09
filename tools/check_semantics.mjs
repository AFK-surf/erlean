import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';

// Both sides consume the same tagged inputs, including arbitrary precision integers.
const integer = value => ({ tag: 'integer', value: String(value) });
const atom = value => ({ tag: 'atom', value });
const nil = { tag: 'nil' };
const list = (items, tail = nil) => ({ tag: 'list', items, tail });
const tuple = items => ({ tag: 'tuple', items });
const source = 'tests/fixtures/erlang/sequential.erl';
const artifact = 'tests/fixtures/erlang/sequential/core.json';
const executable = '.lake/build/bin/erlean';

function run(command, args) {
  const result = spawnSync(command, args, { encoding: 'utf8', timeout: 30000 });
  if (result.error) throw result.error;
  return result;
}

const emitted = run(executable, ['emit', 'tests/fixtures/erlang/identity/core.json']);
assert.equal(emitted.status, 0, emitted.stderr);
assert.equal(emitted.stdout, readFileSync('Erlean/Examples/ImportedIdentity.lean', 'utf8'),
  'Proof fixture must be the exact AST emitted from the retained OTP artifact');

const cases = [
  ['reverse', [nil]],
  ['reverse', [atom('bad')]],
  ['reverse', [list([integer(1)], atom('improper'))]],
  ['reverse', [list([integer(1), atom('two'), tuple([integer(3)])])]],
  ['reverse', [list(Array.from({ length: 30 }, (_, i) => integer(i))) ]],
  ['append', [nil, atom('improper_tail')]],
  ['append', [integer(1), nil]],
  ['append', [list([integer(1), integer(2)]), list([integer(3)])]],
  ['append', [list([integer(1)]), atom('improper_tail')]],
  ['classify', [integer(42)]],
  ['classify', [atom('hello')]],
  ['classify', [nil]],
  ['classify', [tuple([integer(1)])]],
  ['arithmetic', [integer(7), integer(-4)]],
  ['arithmetic', [integer('123456789012345678901234567890'), integer('-987654321098765432109876543210')]],
  ['arithmetic', [atom('bad'), integer(2)]],
  ['arithmetic', [integer(2), nil]],
  ['context', [integer(99)]],
  ['context', [list([atom('original')], atom('tail'))]],
  ['identity', [integer('-999999999999999999999999999999999999')]],
  ['tuple_order', []],
  ['cons_order', []],
];

function differential(input, compiled, name, values) {
  const args = JSON.stringify(values);
  const lean = run(executable, ['run', input, name, args]);
  assert.equal(lean.status, 0, `Lean ${name}: ${lean.stderr}`);
  const otp = run('asdf', ['exec', 'escript', 'tests/semantics/oracle.escript', compiled, name, args]);
  assert.equal(otp.status, 0, `OTP ${name}: ${otp.stderr}`);
  assert.deepEqual(JSON.parse(lean.stdout), JSON.parse(otp.stdout), `${name}(${args})`);
}

for (const [name, values] of cases) differential(artifact, source, name, values);

const closureCases = [
  ['capture', [integer(10), integer(7)]],
  ['capture', [integer(-20), integer(7)]],
  ['capture', [atom('bad'), integer(7)]],
  ['nested', [integer(10), integer(20), integer(30)]],
  ['named_sum', [integer(5), nil]],
  ['named_sum', [integer(5), list([integer(1), integer(2), integer(3)])]],
  ['named_sum', [integer(0), list([integer(1)], atom('improper'))]],
  ['map_add', [integer(10), nil]],
  ['map_add', [integer(10), list([integer(1), integer(2), integer(3)])]],
  ['map_add', [integer(-2), list([integer(0), integer(2), integer(5)])]],
];
for (const [name, values] of closureCases) differential(
  'tests/fixtures/erlang/closures/core.json', 'tests/fixtures/erlang/closures.erl', name, values);

const languageCases = [
  ['identity', [{ tag: 'bitstring', bits: '3', hex: 'a0' }]],
  ['identity', [{ tag: 'bitstring', bits: '0', hex: '' }]],
  ['identity', [{ tag: 'bitstring', bits: '16', hex: 'aff0' }]],
  ['identity', [integer('987654321012345678909876543210')]],
  ['identity', [tuple([atom('nested'), list([integer(1)], atom('tail'))])]],
  ['pair', [atom('first'), integer(-2)]],
  ['empty', []],
  ['prepend', [tuple([integer(1)]), list([atom('tail')])]],
  ['prepend', [integer(1), atom('improper')]],
];
for (const [language, compiled] of [
  ['elixir', 'tests/fixtures/elixir/identity/module.beam'],
  ['gleam', 'tests/fixtures/gleam/identity/generated/_gleam_artefacts/gleam_identity.erl'],
]) {
  const input = `tests/fixtures/${language}/identity/core.json`;
  for (const [name, values] of languageCases) differential(input, compiled, name, values);
}

const unsupported = run(executable, ['run', artifact, 'module_info', '[]']);
assert.equal(unsupported.status, 1, 'Unsupported runtime operation must fail');
assert.match(unsupported.stderr, /unsupported.*get_module_info/s);
const exhausted = run(executable, ['run', artifact, 'loop', '[]', '50']);
assert.equal(exhausted.status, 2, 'Fuel exhaustion has its own exit status');
assert.match(exhausted.stderr, /Fuel exhausted/);
console.log(`Sequential checks passed: ${cases.length + closureCases.length + 2 * languageCases.length} OTP 29.0.6 differential cases across Erlang, Elixir, and Gleam; unsupported runtime fault; fuel exhaustion.`);

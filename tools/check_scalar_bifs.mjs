// Run serially from the repository root. --skip-export reuses the retained
// artifact while still checking its pinned provenance.
//
// The differential corpus below only exercises the implemented profile.
// Integer comparisons and min/max deliberately stop at the integer domain,
// and the type predicates, byte accounting, and iolist flattening raise badarg
// exactly where OTP raises badarg. Cases outside that profile are asserted
// against the model in tests/semantics/Regression.lean instead.
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdtempSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const flags = new Set(process.argv.slice(2));
assert.ok([...flags].every(flag => flag === '--skip-export'), 'Unknown check_scalar_bifs option');
const source = 'tests/fixtures/erlang/scalar_bifs.erl';
const directory = 'tests/fixtures/erlang/scalar_bifs';
const artifact = join(directory, 'core.json');
const exporter = 'tools/export_core.escript';
const executable = '.lake/build/bin/erlean';
const env = { ...process.env, ERL_FLAGS: '+S 2:2 +SDcpu 1 +SDio 1', LEAN_NUM_THREADS: '1' };
function run(command, args) {
  const result = spawnSync(command, args, { encoding: 'utf8', env, timeout: 30000, maxBuffer: 16 * 1024 * 1024 });
  if (result.error) throw result.error;
  assert.equal(result.status, 0, `${command} ${args.slice(0, 3).join(' ')}: ${result.stderr}`);
  return result.stdout;
}
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const manifest = JSON.parse(readFileSync(join(directory, 'manifest.json'), 'utf8'));
assert.equal(manifest.otp_version, '29.0.6');
assert.deepEqual(manifest.compiler_options,
  ['to_core', 'binary', 'no_copt', 'deterministic', 'return_errors', 'return_warnings']);
assert.equal(manifest.source_sha256, digest(readFileSync(source)));
assert.equal(manifest.core_sha256, digest(readFileSync(artifact)));
assert.equal(manifest.exporter_sha256, digest(readFileSync(exporter)));
if (!flags.has('--skip-export')) {
  const temporary = mkdtempSync(join(tmpdir(), 'erlean-scalar-bifs-'));
  for (const attempt of ['first', 'second']) {
    const destination = join(temporary, attempt);
    run('asdf', ['exec', 'escript', exporter, source, destination]);
    for (const name of ['core.json', 'manifest.json', 'inventory.json']) {
      assert.deepEqual(readFileSync(join(destination, name)), readFileSync(join(directory, name)),
        `Reproducible scalar BIF ${name}`);
    }
  }
}

const integer = value => ({ tag: 'integer', value: String(value) });
const atom = value => ({ tag: 'atom', value });
const float = hex => ({ tag: 'float', bits: hex });
const nil = { tag: 'nil' };
const list = items => ({ tag: 'list', items, tail: nil });
const improper = (items, tail) => ({ tag: 'list', items, tail });
const binary = text => {
  const bytes = Buffer.from(text, 'utf8');
  return { tag: 'bitstring', bits: String(bytes.length * 8), hex: bytes.toString('hex') };
};
const emptyBinary = { tag: 'bitstring', bits: '0', hex: '' };
const big = 9007199254740993n;

// [function, arguments, label]
const cases = [
  ['less', [integer(1), integer(2)], 'left operand below'],
  ['less', [integer(2), integer(2)], 'equal operands are not less'],
  ['less', [integer(-5), integer(5)], 'negative left operand'],
  ['greater', [integer(2), integer(1)], 'left operand above'],
  ['greater', [integer(1), integer(2)], 'left operand below'],
  ['greater', [integer(big), integer(1)], 'large left operand'],
  ['at_least', [integer(2), integer(2)], 'equality satisfies at_least'],
  ['at_least', [integer(1), integer(2)], 'smaller operand fails at_least'],
  ['at_least', [integer(big + 1n), integer(big)], 'large bounded comparison'],
  ['minimum', [integer(3), integer(5)], 'minimum selects the smaller'],
  ['minimum', [integer(5), integer(-3)], 'minimum accepts a negative winner'],
  ['maximum', [integer(3), integer(5)], 'maximum selects the larger'],
  ['maximum', [integer(big), integer(1)], 'maximum preserves large integers'],
  ['either', [atom('false'), atom('true')], 'or accepts a true right operand'],
  ['either', [atom('true'), atom('false')], 'or accepts a true left operand'],
  ['either', [atom('false'), atom('false')], 'or rejects two false operands'],
  ['negate', [atom('true')], 'not negates true'],
  ['negate', [atom('false')], 'not negates false'],
  ['list_shape', [list([integer(1), integer(2)])], 'proper list'],
  ['list_shape', [nil], 'empty list'],
  ['list_shape', [improper([integer(1)], atom('tail'))], 'improper list'],
  ['list_shape', [atom('a')], 'atom is not a list'],
  ['boolean_shape', [atom('true')], 'true is a boolean'],
  ['boolean_shape', [atom('false')], 'false is a boolean'],
  ['boolean_shape', [atom('nil')], 'the atom nil is not a boolean'],
  ['boolean_shape', [integer(1)], 'integer is not a boolean'],
  ['float_shape', [float('3ff0000000000000')], 'binary64 one is a float'],
  ['float_shape', [float('0000000000000000')], 'positive zero is a float'],
  ['float_shape', [integer(1)], 'integer is not a float'],
  ['float_shape', [atom('a')], 'atom is not a float'],
  ['byte_count', [binary('ab')], 'two bytes'],
  ['byte_count', [emptyBinary], 'empty binary'],
  ['byte_count', [binary('é')], 'non-ASCII byte accounting'],
  ['element_count', [list([integer(1), integer(2), integer(3)])], 'three elements'],
  ['element_count', [nil], 'empty list count'],
  ['byte_values', [binary('AB')], 'byte extraction order'],
  ['byte_values', [emptyBinary], 'empty binary extraction'],
  ['byte_values', [binary('é')], 'non-ASCII byte extraction'],
  ['flatten', [list([integer(65), binary('B')])], 'nested binary element'],
  ['flatten', [list([integer(65), list([integer(66)])])], 'nested list element'],
  ['flatten', [nil], 'empty iolist'],
  ['flatten', [emptyBinary], 'binary outside a list'],
  ['flatten', [list([])], 'nested empty list'],
];

for (const [name, values, label] of cases) {
  const argumentsJson = JSON.stringify(values);
  const lean = JSON.parse(run(executable, ['run', artifact, name, argumentsJson, '200000']));
  const otp = JSON.parse(run('asdf', ['exec', 'escript', 'tools/otp_oracle.escript',
    source, name, argumentsJson]));
  assert.deepEqual(lean, otp, `OTP differential: ${name} / ${label}`);
  assert.equal(lean.status, 'returned', `${name} / ${label}`);
}

// Both engines must reject the same unsupported operands with error:badarg.
const invalidCases = [
  ['either', [atom('nil'), atom('true')], 'non-boolean left operand'],
  ['either', [integer(1), integer(2)], 'non-boolean operands'],
  ['negate', [atom('nil')], 'non-boolean operand'],
  ['negate', [integer(1)], 'non-boolean integer operand'],
  ['byte_count', [integer(1)], 'byte_count rejects a non-binary'],
  ['byte_count', [atom('a')], 'byte_count rejects an atom'],
  ['element_count', [improper([integer(1)], atom('tail'))], 'length rejects an improper list'],
  ['element_count', [atom('a')], 'length rejects an atom'],
  ['byte_values', [integer(1)], 'binary_to_list rejects a non-binary'],
  ['flatten', [atom('a')], 'iolist_to_binary rejects an atom'],
  ['flatten', [list([integer(256)])], 'iolist_to_binary rejects an out-of-range byte'],
  ['flatten', [list([integer(-1)])], 'iolist_to_binary rejects a negative byte'],
  ['flatten', [improper([integer(65)], atom('tail'))], 'iolist_to_binary rejects an improper tail'],
];
for (const [name, values, label] of invalidCases) {
  const argumentsJson = JSON.stringify(values);
  const lean = JSON.parse(run(executable, ['run', artifact, name, argumentsJson]));
  const otp = JSON.parse(run('asdf', ['exec', 'escript', 'tools/otp_oracle.escript',
    source, name, argumentsJson]));
  assert.deepEqual(lean, otp, `Invalid scalar BIF input differential: ${label}`);
  assert.deepEqual(lean, { status: 'raised', class: 'error', reason: atom('badarg') }, label);
}
console.log(`Scalar BIF checks passed: ${cases.length} results and ${invalidCases.length} rejected inputs against OTP 29.0.6, plus provenance. Compatibility evidence is not a proof of equivalence with OTP.`);

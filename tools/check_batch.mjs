// CLI batching preserves single-call results and publishes no partial output.
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const executable = '.lake/build/bin/erlean';
const sequential = 'tests/fixtures/erlang/sequential/core.json';
const identity = 'tests/fixtures/erlang/identity/core.json';
const temporary = mkdtempSync(join(tmpdir(), 'erlean-batch-'));
const casesPath = join(temporary, 'cases.json');
const atom = value => ({ tag: 'atom', value });
const integer = value => ({ tag: 'integer', value: String(value) });
const tuple = (...items) => ({ tag: 'tuple', items });
const returned = value => ({ status: 'returned', values: [value] });

function invoke(args) {
  const result = spawnSync(executable, args, { encoding: 'utf8', timeout: 30000 });
  if (result.error) throw result.error;
  return result;
}

function batch(artifact, cases, fuel) {
  writeFileSync(casesPath, JSON.stringify(cases));
  return invoke(['run-batch', artifact, casesPath, ...(fuel === undefined ? [] : [String(fuel)])]);
}

function successful(result) {
  assert.equal(result.status, 0, result.stderr);
  assert.equal(result.stderr, '');
  return JSON.parse(result.stdout);
}

function failed(result, code, diagnostic) {
  assert.equal(result.status, code, result.stderr);
  assert.equal(result.stdout, '', 'A failed batch must not print earlier successful results');
  assert.match(result.stderr, diagnostic);
}

try {
  const payload = tuple(atom('payload'), integer(9007199254740993123456789n));
  const identities = [payload, atom('again')].map(value => ({ function: 'identity', arguments: [value] }));
  assert.deepEqual(successful(batch(identity, identities)),
    [returned(payload), returned(atom('again'))]);
  assert.deepEqual(successful(batch(identity, [])), []);

  const cases = [
    { function: 'identity', arguments: [payload], expected: 'Additional metadata is ignored' },
    { function: 'classify', arguments: [integer(3)] },
    { function: 'arithmetic', arguments: [integer(2), integer(4)] },
    { function: 'tuple_order', arguments: [] },
    { function: 'identity', arguments: [atom('after_exception')] },
  ];
  const results = successful(batch(sequential, cases, 1000));
  assert.deepEqual(results, [returned(payload), returned(atom('integer')), returned(integer(10)),
    { status: 'raised', class: 'error', reason: atom('first') }, returned(atom('after_exception'))]);
  for (const [index, test] of cases.entries()) {
    assert.deepEqual(results[index], successful(invoke([
      'run', sequential, test.function, JSON.stringify(test.arguments), '1000',
    ])), `Batch result ${index} must match the existing single-call command`);
  }

  failed(batch(sequential, [cases[0], { function: 'identity' }]), 1, /arguments/);
  failed(batch(sequential, [cases[0], { function: 7, arguments: [] }]), 1, /erlean:/);
  failed(batch(sequential, [cases[0], { function: 'identity', arguments: 'not_an_array' }]), 1, /erlean:/);
  failed(batch(sequential, {}), 1, /erlean:/);
  writeFileSync(casesPath, '[invalid JSON');
  failed(invoke(['run-batch', sequential, casesPath]), 1, /erlean:/);
  failed(batch(sequential, [cases[0], { function: 'module_info', arguments: [] }]),
    1, /Batch case 1.*Model fault/);
  failed(batch(sequential, [cases[0], { function: 'loop', arguments: [] }], 100),
    2, /Batch case 1.*Fuel exhausted/);
  failed(batch(identity, identities, 0), 2, /Fuel exhausted after 0 steps/);
  failed(batch(identity, identities, 'invalid'), 1, /Fuel must be a natural number/);
  console.log('Batch CLI checks passed: ordered results, raised outcomes, input validation, model faults, per-case fuel, and atomic stdout.');
} finally {
  rmSync(temporary, { recursive: true, force: true });
}

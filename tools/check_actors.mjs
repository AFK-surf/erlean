// Compare selected deterministic model executions with isolated OTP scenarios.
// This does not enumerate schedules or prove an actor protocol invariant.
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync, mkdtempSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const atom = value => ({ tag: 'atom', value });
const integer = value => ({ tag: 'integer', value: String(value) });
const nil = { tag: 'nil' };
const tuple = items => ({ tag: 'tuple', items });
const list = items => ({ tag: 'list', items, tail: nil });
const returned = value => ({ status: 'returned', values: [atom(value)] });
const exited = value => ({ status: 'exited', reason: atom(value) });
const executable = '.lake/build/bin/erlean';
const digest = path => createHash('sha256').update(readFileSync(path)).digest('hex');

for (const module of ['actor_protocol', 'actor_lifecycle']) {
  const path = `tests/fixtures/erlang/${module}`;
  const manifest = JSON.parse(readFileSync(`${path}/manifest.json`));
  assert.equal(manifest.otp_version, '29.0.6');
  assert.equal(manifest.source_sha256, digest(`${path}.erl`));
  assert.equal(manifest.core_sha256, digest(`${path}/core.json`));
  assert.equal(manifest.exporter_sha256, digest('tools/export_core.escript'));
  assert.deepEqual(manifest.compiler_options,
    ['to_core', 'binary', 'no_copt', 'deterministic', 'return_errors', 'return_warnings']);
}

function invoke(command, args, label) {
  const result = spawnSync(command, args, { encoding: 'utf8', timeout: 20000 });
  if (result.error) throw result.error;
  assert.equal(result.status, 0, `${label}: ${result.stderr}`);
  return JSON.parse(result.stdout);
}

let checks = 0;
function differential(module, fn, args, expected) {
  const path = `tests/fixtures/erlang/${module}`;
  const encoded = JSON.stringify(args);
  const label = `${module}:${fn}(${encoded})`;
  const lean = invoke(executable, ['actor-run', `${path}/core.json`, fn, encoded], `Lean ${label}`);
  const otp = invoke('asdf', ['exec', 'escript', 'tests/semantics/actor_oracle.escript',
    `${path}.erl`, fn, encoded], `OTP ${label}`);
  assert.deepEqual(lean, otp, label);
  if (expected) assert.deepEqual(otp, expected, `Expected lifecycle behavior: ${label}`);
  checks++;
}

for (const [fn, expected] of [
  ['monitor_normal', returned('normal')],
  ['monitor_kill', returned('killed')],
  ['demonitor_before_exit', returned('removed')],
  ['normal_signal_ignored', returned('survived')],
  ['linked_normal', returned('survived')],
  ['linked_failure', exited('boom')],
  ['unlink_failure', returned('survived')],
  ['link_dead', returned('noproc')],
  ['self_normal', exited('normal')],
]) differential('actor_lifecycle', fn, [], expected);

for (const value of [integer(42), integer('123456789012345678901234567890'),
  tuple([atom('payload'), list([integer(1), integer(2)])]), nil]) {
  differential('actor_protocol', 'exchange', [value]);
}
differential('actor_protocol', 'poll', [], returned('empty'));
differential('actor_protocol', 'wait_only', [integer(0)], returned('elapsed'));
for (const value of [integer(-1), atom('invalid_timeout')]) {
  differential('actor_protocol', 'wait_only', [value],
    { status: 'raised', class: 'error', reason: atom('timeout_value') });
}

console.log(`Actor checks passed: ${checks} OTP 29.0.6 differential scenarios.`);
const directory = mkdtempSync(join(tmpdir(), 'erlean-actor-replay-'));
const trace = join(directory, 'schedule.json');
const input = JSON.stringify([integer(42)]);
const artifact = 'tests/fixtures/erlang/actor_protocol/core.json';
const first = invoke(executable, ['actor-run', artifact, 'exchange', input, trace], 'trace recording');
const replayed = invoke(executable, ['actor-replay', artifact, 'exchange', input, trace], 'trace replay');
assert.deepEqual(first, replayed);
assert.ok(JSON.parse(readFileSync(trace)).some(choice => 'deliver' in choice));
const invalid = join(directory, 'invalid.json');
writeFileSync(invalid, JSON.stringify([{ deliver: 999 }]));
const rejected = spawnSync(executable, ['actor-replay', artifact, 'exchange', input, invalid],
  { encoding: 'utf8', timeout: 20000 });
assert.equal(rejected.status, 1);
assert.match(rejected.stderr, /Invalid replay choice/);
console.log('CLI schedule recording, replay, and invalid-choice rejection passed.');
console.log('Results cover the selected bounded scheduler, not all possible schedules.');

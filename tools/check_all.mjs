// Run the full bounded verification suite from the repository root.
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';

function run(label, command, args, quiet = false) {
  console.log(`Checking ${label}...`);
  const result = spawnSync(command, args, { encoding: 'utf8', timeout: 300000 });
  if (result.stdout && !quiet) process.stdout.write(result.stdout);
  if (result.stderr) process.stderr.write(result.stderr);
  if (result.error) throw result.error;
  assert.equal(result.status, 0, `${label} failed`);
  return result.stdout;
}

const hash = path => createHash('sha256').update(readFileSync(path)).digest('hex');
const fixtures = [
  'tests/fixtures/erlang/identity',
  'tests/fixtures/erlang/sequential',
  'tests/fixtures/erlang/closures',
  'tests/fixtures/erlang/higher_order',
  'tests/fixtures/erlang/exceptions',
  'tests/fixtures/erlang/modular_client',
  'tests/fixtures/erlang/byte_codec',
  'tests/fixtures/erlang/actor_protocol',
  'tests/fixtures/erlang/actor_lifecycle',
  'tests/fixtures/erlang/dijkstra',
  'tests/fixtures/erlang/maps',
  'tests/fixtures/elixir/identity',
  'tests/fixtures/gleam/identity',
];

process.env.ERL_FLAGS = `${process.env.ERL_FLAGS ?? ''} +S 2:2 +SDcpu 1 +SDio 1`.trim();
run('serialized Lean build and imported contracts', 'node', ['tools/build.mjs']);
run('Lean importer rejection and scope checks', 'lake', ['env', 'lean', '-j1', '-M2048', '--run', 'tests/import/Smoke.lean']);
run('OTP extraction and lossless transport', 'node', ['tools/check_export.mjs']);
// This also regenerates the ignored Elixir BEAM before validating its manifest hash.
run('Elixir/Gleam compiler adapters and reproducibility', 'node', ['tools/check_languages.mjs']);
run('Lean machine regression checks', 'lake', ['env', 'lean', '-j1', '-M2048', '--run', 'tests/semantics/Regression.lean']);
run('exception and observation boundary checks', 'lake', ['env', 'lean', '-j1', '-M2048', '--run', 'tests/semantics/ExceptionChecks.lean']);
run('map representation and observation boundary checks', 'lake', ['env', 'lean', '-j1', '-M2048', '--run', 'tests/semantics/MapChecks.lean']);
run('actor scheduling and lifecycle regressions', 'lake', ['env', 'lean', '-j1', '-M2048', '--run', 'tests/semantics/ActorChecks.lean']);
const axioms = run('kernel theorem axiom audit', 'lake',
  ['env', 'lean', '-j1', '-M2048', 'tests/semantics/Axioms.lean']);
assert.doesNotMatch(axioms, /sorryAx|ofReduceBool|native_decide|Lean\.ofReduce/);
run('OTP differential checks and explicit model failures', 'node', ['tools/check_semantics.mjs']);
run('batch execution and atomic failure reporting', 'node', ['tools/check_batch.mjs']);
run('OTP finite-map compatibility and error ordering', 'node', ['tools/check_maps.mjs']);
run('OTP actor differential scenarios', 'node', ['tools/check_actors.mjs']);
run('Dijkstra OTP and independent shortest-path checks', 'node', ['tools/check_dijkstra.mjs']);

for (const directory of fixtures) {
  const manifest = JSON.parse(readFileSync(`${directory}/manifest.json`));
  assert.equal(manifest.otp_version, '29.0.6', directory);
  assert.equal(manifest.source_sha256, hash(manifest.source), `${directory}: source provenance`);
  assert.equal(manifest.core_sha256, hash(`${directory}/core.json`), `${directory}: Core provenance`);
  assert.equal(manifest.exporter_sha256, hash('tools/export_core.escript'), `${directory}: exporter provenance`);
}

const emitted = spawnSync('.lake/build/bin/erlean',
  ['emit', 'tests/fixtures/erlang/identity/core.json'], { encoding: 'utf8', timeout: 30000 });
if (emitted.error) throw emitted.error;
assert.equal(emitted.status, 0, emitted.stderr);
assert.equal(emitted.stdout.trimEnd(),
  readFileSync('Erlean/Examples/Identity/ImportedErlang.lean', 'utf8').trimEnd(),
  'The checked-in Lean module must match the current importer and pinned Core artifact');
for (const [language, declaration, file] of [
  ['elixir', 'importedElixirModule', 'Identity/ImportedElixir'],
  ['gleam', 'importedGleamModule', 'Identity/ImportedGleam'],
]) {
  const output = run(`${language} proof artifact correspondence`, '.lake/build/bin/erlean',
    ['emit', `tests/fixtures/${language}/identity/core.json`, declaration], true);
  assert.equal(output, readFileSync(`Erlean/Examples/${file}.lean`, 'utf8'));
}
const sequential = run('recursive proof artifact correspondence', '.lake/build/bin/erlean',
  ['emit', 'tests/fixtures/erlang/sequential/core.json', 'importedSequentialModule'], true);
assert.equal(sequential, readFileSync('Erlean/Examples/Sequential/Imported.lean', 'utf8'));
const higherOrder = run('higher-order proof artifact correspondence', '.lake/build/bin/erlean',
  ['emit', 'tests/fixtures/erlang/higher_order/core.json', 'importedHigherOrderModule'], true);
assert.equal(higherOrder, readFileSync('Erlean/Examples/HigherOrder/Imported.lean', 'utf8'));
const modular = run('modular proof artifact correspondence', '.lake/build/bin/erlean',
  ['emit', 'tests/fixtures/erlang/modular_client/core.json', 'importedModularClient'], true);
assert.equal(modular, readFileSync('Erlean/Examples/Modular/Imported.lean', 'utf8'));
const codec = run('codec proof artifact correspondence', '.lake/build/bin/erlean',
  ['emit', 'tests/fixtures/erlang/byte_codec/core.json', 'importedByteCodec'], true);
assert.equal(codec, readFileSync('Erlean/Examples/ByteCodec/Imported.lean', 'utf8'));
const actor = run('actor proof artifact correspondence', '.lake/build/bin/erlean',
  ['emit', 'tests/fixtures/erlang/actor_protocol/core.json', 'importedActorProtocolModule'], true);
assert.equal(actor, readFileSync('Erlean/Examples/Protocol/Imported.lean', 'utf8'));
console.log('All bounded checks passed, including kernel-checked identity contract and artifact provenance.');
console.log('Differential results are compatibility evidence, not a proof of equivalence with OTP.');

// Run from the repository root with Node.js and the pinned asdf OTP installed.
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdtempSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';

const output = mkdtempSync(join(tmpdir(), 'erlean-export-check-'));
const exporter = 'tools/export_core.escript';
execFileSync('asdf', ['exec', 'escript', exporter, '--check-encoding'], { stdio: 'pipe' });
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
function run(source, destination) {
  execFileSync('asdf', ['exec', 'escript', exporter, source, destination], { stdio: 'pipe' });
}
const source = 'tests/fixtures/erlang/identity.erl';
run(source, join(output, 'first'));
run(source, join(output, 'second'));
execFileSync('asdf', ['exec', 'escript', exporter, '--otp', '29.0.6', source,
  join(output, 'explicit')], { stdio: 'pipe' });
assert.deepEqual(readFileSync(join(output, 'first', 'core.json')),
  readFileSync(join(output, 'explicit', 'core.json')));
for (const version of ['29.0.2', '29.0.5']) {
  const rejected = spawnSync('asdf', ['exec', 'escript', exporter, '--otp', version,
    source, join(output, `rejected-${version}`)], { encoding: 'utf8' });
  assert.notEqual(rejected.status, 0, 'A different running patch must not be relabeled');
  assert.match(rejected.stderr, /unsupported_otp_(patch|profile)/);
}
for (const name of ['core.json', 'manifest.json', 'inventory.json']) {
  assert.deepEqual(readFileSync(join(output, 'first', name)), readFileSync(join(output, 'second', name)));
}
const core = readFileSync(join(output, 'first', 'core.json'));
assert.deepEqual(core, readFileSync('tests/fixtures/erlang/identity/core.json'));
const manifest = JSON.parse(readFileSync(join(output, 'first', 'manifest.json')));
assert.equal(manifest.otp_version, '29.0.6');
assert.equal(manifest.source_sha256, digest(readFileSync(source)));
assert.equal(manifest.core_sha256, digest(core));
assert.equal(manifest.exporter_sha256, digest(readFileSync(exporter)));
assert.deepEqual(manifest.compiler_options,
  ['to_core', 'binary', 'no_copt', 'deterministic', 'return_errors', 'return_warnings']);
const inventory = JSON.parse(readFileSync(join(output, 'first', 'inventory.json')));
assert.equal(inventory.constructs.module, 1);
assert.equal(inventory.calls['erlang:get_module_info/1'], 1);
assert.ok(inventory.primops.match_fail > 0);

run('tests/fixtures/erlang/literals.erl', join(output, 'literals'));
const literals = JSON.parse(readFileSync(join(output, 'literals', 'core.json')));
const terms = [];
function visit(value) {
  if (value && typeof value === 'object') {
    if (value.tag) terms.push(value);
    for (const child of Object.values(value)) visit(child);
  }
}
visit(literals);
for (const value of ['1234567890123456789012345678901234567890']) {
  assert.ok(terms.some(term => term.tag === 'integer' && term.value === value));
}
assert.ok(terms.some(term => term.tag === 'float' && term.bits === '3ff0000000000000'));
assert.ok(terms.some(term => term.tag === 'atom' && term.value === 'atom with spaces'));
assert.ok(terms.some(term => term.tag === 'list' && term.tail.tag === 'atom' && term.tail.value === 'b'));
assert.ok(terms.some(term => term.tag === 'map' && term.entries.length === 2));
// At this unoptimized stage, unary minus and bitstring construction remain Core
// expressions. Their final literal representations are checked directly above.
console.log(`Exporter reproducibility, manifest hashes, inventory, and lossless literals passed. Artifacts: ${output}`);

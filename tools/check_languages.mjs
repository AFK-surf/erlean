// Regenerate the documented fixture locations twice and check stable artifacts.
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';

const paths = ['elixir', 'gleam'].flatMap(language =>
  ['core.json', 'manifest.json', 'inventory.json'].map(name =>
    `tests/fixtures/${language}/identity/${name}`));
const before = paths.map(path => readFileSync(path));
for (let iteration = 0; iteration < 2; iteration++) {
  execFileSync('node', ['tools/export_languages.mjs'], { stdio: 'pipe' });
  paths.forEach((path, index) => assert.deepEqual(readFileSync(path), before[index], path));
}
const hash = path => createHash('sha256').update(readFileSync(path)).digest('hex');
for (const [language, version] of [['elixir', '1.20.0'], ['gleam', '1.18.1']]) {
  const directory = `tests/fixtures/${language}/identity`;
  const manifest = JSON.parse(readFileSync(`${directory}/manifest.json`));
  assert.equal(manifest.otp_version, '29.0.6');
  assert.equal(manifest.source_language, language);
  assert.equal(manifest.source_compiler_version, version);
  assert.equal(manifest.source_sha256, hash(manifest.source));
  assert.equal(manifest.core_sha256, hash(`${directory}/core.json`));
  assert.equal(manifest.exporter_sha256, hash('tools/export_core.escript'));
  assert.equal(manifest.adapter_sha256, hash('tools/export_languages.mjs'));
  for (const intermediate of manifest.intermediates) {
    assert.equal(intermediate.sha256, hash(`${directory}/${intermediate.file}`));
  }
}
console.log('Elixir/Gleam exact compiler pins, byte reproducibility, and provenance hashes passed.');

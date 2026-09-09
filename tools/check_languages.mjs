// Regenerate the documented fixture locations twice and check stable artifacts.
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync, mkdtempSync, mkdirSync, copyFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname } from 'node:path';

const paths = ['elixir', 'gleam'].flatMap(language =>
  ['core.json', 'manifest.json', 'inventory.json'].map(name =>
    `tests/fixtures/${language}/identity/${name}`));
const before = paths.map(path => readFileSync(path));
for (let iteration = 0; iteration < 2; iteration++) {
  execFileSync('node', ['tools/export_languages.mjs'], { stdio: 'pipe' });
  paths.forEach((path, index) => assert.deepEqual(readFileSync(path), before[index], path));
}
const hash = path => createHash('sha256').update(readFileSync(path)).digest('hex');
// A different checkout root must not change debug info or companion BEAM hashes.
const relocated = mkdtempSync(join(tmpdir(), 'erlean-language-relocation-'));
try {
  for (const file of ['.tool-versions', 'tools/export_languages.mjs',
    'tools/export_core.escript', 'tools/elixir_forms.exs',
    'tests/fixtures/elixir/identity.ex', 'tests/fixtures/gleam/gleam.toml',
    'tests/fixtures/gleam/src/gleam_identity.gleam']) {
    const destination = join(relocated, file);
    mkdirSync(dirname(destination), { recursive: true });
    copyFileSync(file, destination);
  }
  execFileSync('node', ['tools/export_languages.mjs'], { cwd: relocated, stdio: 'pipe' });
  for (const path of [...paths, 'tests/fixtures/elixir/identity/abstract.etf',
    'tests/fixtures/elixir/identity/module.beam']) {
    assert.deepEqual(readFileSync(join(relocated, path)), readFileSync(path),
      `${path}: checkout-independent compilation`);
  }
} finally {
  rmSync(relocated, { recursive: true, force: true });
}
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
console.log('Elixir/Gleam exact pins, byte reproducibility across checkout roots, and provenance hashes passed.');

// Reproducible, dependency-free fixture adapters. Run from the repository root.
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { delimiter, join } from 'node:path';

const otp = execFileSync('asdf', ['where', 'erlang'], { encoding: 'utf8' }).trim();
const env = { ...process.env, PATH: join(otp, 'bin') + delimiter + process.env.PATH };
const run = (...args) => execFileSync('asdf', ['exec', ...args], { env, encoding: 'utf8', stdio: 'pipe' });
const hash = path => createHash('sha256').update(readFileSync(path)).digest('hex');
const outRoot = process.argv[2] || 'tests/fixtures';
const exporter = 'tools/export_core.escript';

function provenance(output, source, language, compiler, version, options, intermediates) {
  const path = join(output, 'manifest.json');
  const manifest = JSON.parse(readFileSync(path));
  manifest.otp_compiler_version = manifest.source_compiler_version;
  manifest.source = source;
  manifest.source_sha256 = hash(source);
  manifest.source_language = language;
  manifest.source_compiler = compiler;
  manifest.source_compiler_version = version;
  manifest.source_compiler_options = options;
  manifest.intermediates = intermediates.map(file => ({ file: file.name, sha256: hash(file.path) }));
  manifest.adapter_sha256 = hash('tools/export_languages.mjs');
  if (language === 'elixir') manifest.forms_adapter_sha256 = hash('tools/elixir_forms.exs');
  writeFileSync(path, JSON.stringify(manifest) + '\n');
}

const elixirSource = 'tests/fixtures/elixir/identity.ex';
const elixirOutput = join(outRoot, 'elixir', 'identity');
mkdirSync(elixirOutput, { recursive: true });
run('elixir', 'tools/elixir_forms.exs', elixirSource, elixirOutput);
run('escript', exporter, '--forms', join(elixirOutput, 'abstract.etf'), elixirOutput);
provenance(elixirOutput, elixirSource, 'elixir', 'Elixir', '1.20.0',
  ['debug_info=true', 'docs=false', 'Code.compile_file', 'debug_info:erlang_v1'],
  [{ name: 'abstract.etf', path: join(elixirOutput, 'abstract.etf') },
   { name: 'module.beam', path: join(elixirOutput, 'module.beam') }]);

const gleamVersion = run('gleam', '--version').trim();
if (gleamVersion !== 'gleam 1.18.1') throw new Error(`Expected gleam 1.18.1, received ${gleamVersion}`);
const gleamOutput = join(outRoot, 'gleam', 'identity');
const generated = join(gleamOutput, 'generated');
mkdirSync(generated, { recursive: true });
run('gleam', 'compile-package', '--target', 'erlang', '--package', 'tests/fixtures/gleam',
  '--out', generated, '--lib', generated, '--no-beam');
const erlangSource = join(generated, '_gleam_artefacts', 'gleam_identity.erl');
run('escript', exporter, erlangSource, gleamOutput);
provenance(gleamOutput, 'tests/fixtures/gleam/src/gleam_identity.gleam', 'gleam', 'Gleam', '1.18.1',
  ['compile-package', '--target=erlang', '--no-beam', 'no dependencies'],
  [{ name: 'generated/_gleam_artefacts/gleam_identity.erl', path: erlangSource },
   { name: '../gleam.toml', path: 'tests/fixtures/gleam/gleam.toml' }]);
console.log(`Exported Elixir 1.20.0 and Gleam 1.18.1 fixtures through OTP 29.0.6 to ${outRoot}`);

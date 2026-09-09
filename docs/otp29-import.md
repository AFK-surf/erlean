# OTP 29 Core import profile

The initial extraction profile pins Erlang/OTP **29.0.6** through `.tool-versions`
and asdf. It exports compiler trees without claiming executable support for every
exported construct. The manifest profile `raw-only-v1` means transport coverage,
not semantic compatibility.

## Runtime and extraction

Install the pinned runtime with the asdf Erlang plugin:

```sh
asdf plugin add erlang https://github.com/asdf-vm/asdf-erlang.git
KERL_CONFIGURE_OPTIONS='--without-javac --without-wx --without-odbc' KERL_BUILD_DOCS=no asdf install erlang 29.0.6
asdf exec escript tools/export_core.escript tests/fixtures/erlang/identity.erl tests/fixtures/erlang/identity
```

Skip plugin installation when it is already installed. The omitted applications
are irrelevant to this extraction profile. The exporter checks the full
`releases/29/OTP_VERSION` value, since `system_info(otp_release)` only reports 29.
It fails for another patch release.

Extraction uses `compile:noenv_file/2` with these exact options, in order:

```erlang
[to_core, binary, no_copt, deterministic, return_errors, return_warnings]
```

The `noenv_file` entry point avoids implicit `ERL_COMPILER_OPTIONS`. Source compile
attributes still belong to the input and are covered by its hash. Imports with
parse transforms, includes, or external dependencies need an extended manifest
before they can claim a reproducible build; this initial fixture has none.

The selected stage is after `v3_core`, with Core optimization passes disabled,
and before `sys_core_bsm` and Core-to-SSA. This follows the `core_passes` and
`kernel_passes` definitions in the
[pinned OTP compiler source](https://github.com/erlang/otp/blob/OTP-29.0.6/lib/compiler/src/compile.erl).
`to_core` alone would allow optimization; the exporter must retain `no_copt`.
This stage can contain lowered receive operations; it is not the historical Core
language specification.

Run from the repository root using the documented relative source path. Core
annotations can retain source paths, so moving a source or changing its argument
spelling can change the artifact. No annotations are erased for reproducibility.

## RawCore version 1

`core.json` is a UTF-8 JSON object with:

| Field | Value |
| --- | --- |
| `format` | `"erlean.raw-core"` |
| `version` | JSON integer `1` |
| `otp_version` | `"29.0.6"` |
| `module` | Module atom as a UTF-8 string |
| `core` | Tagged Erlang term described below |

The encoding is lossless for accepted Erlang terms. Language integers are decimal
strings, never JSON numbers. Empty lists have a separate representation. Nonempty
lists flatten their cons prefix and explicitly retain the final tail, including
improper tails.

| Erlang term | JSON shape |
| --- | --- |
| atom | `{"tag":"atom","value":"ok"}` |
| integer | `{"tag":"integer","value":"-123"}` |
| float | `{"tag":"float","bits":"3ff0000000000000"}` |
| nil | `{"tag":"nil"}` |
| nonempty list | `{"tag":"list","items":[TERM],"tail":TERM}` |
| tuple | `{"tag":"tuple","items":[TERM]}` |
| map | `{"tag":"map","entries":[[KEY,VALUE]]}` |
| bitstring | `{"tag":"bitstring","bits":"3","hex":"a0"}` |

Float bits are the big-endian 64-bit IEEE representation. Bitstring bytes are in
source bit order, padded with zero bits at the right to a byte boundary; `bits`
records the original length. Hex strings are lowercase. Map entries are sorted
by OTP term ordering for stable output. Maps are represented as entry arrays so
keys retain Erlang identity. Pids, ports, references, fun values, and other terms
without a declared encoding cause an explicit export failure.

Core records are ordinary encoded tuples. Every record starts with its record
tag atom and annotations list; remaining fields use the order in the
[OTP 29.0.6 record declarations](https://github.com/erlang/otp/blob/OTP-29.0.6/lib/compiler/src/core_parse.hrl).
The initially accepted record layouts are:

| Record | Fields after tag and annotations |
| --- | --- |
| `c_alias` | var, pat |
| `c_apply` | op, args |
| `c_binary` | segments |
| `c_bitstr` | val, size, unit, type, flags |
| `c_call` | module, name, args |
| `c_case` | arg, clauses |
| `c_catch` | body |
| `c_clause` | pats, guard, body |
| `c_cons` | hd, tl |
| `c_fun` | vars, body |
| `c_let` | vars, arg, body |
| `c_letrec` | defs, body |
| `c_literal` | val |
| `c_map` | arg, es, is_pat |
| `c_map_pair` | op, key, val |
| `c_module` | name, exports, attrs, defs |
| `c_primop` | name, args |
| `c_receive` | clauses, timeout, action |
| `c_seq` | arg, body |
| `c_try` | arg, vars, body, evars, handler |
| `c_tuple` | es |
| `c_values` | es |
| `c_var` | name |

Definitions and attributes are lists of pairs encoded as two-element tuples.
Variable names can be atoms, integers, or function-name/arity tuples; a decoder
must not coerce them all to strings. The exporter rejects OTP 29 native record
nodes and opaque nodes until their import contract is specified. Record-shaped
tuples inside literals remain literal terms and must not be interpreted as syntax.

## Manifest and inventory

The Lean execution profile accepts integer, atom, list, tuple, canonical bitstring,
and finite-map literals. It also supports alias patterns, finite closures, and
the restricted binary segments described in the design tracker. Finite binary64
floats can be transported without arithmetic or observable equality. Unlisted
runtime operations remain unsupported. Literal transport is broader
than executable semantics.

Float inputs use exactly sixteen hexadecimal digits in the RawCore `bits` field.
The model retains negative zero and subnormal encodings. NaNs and infinities are
rejected. Returned floats use sixteen lowercase digits. No host decimal conversion
occurs. Float literal patterns, including floats nested in literal containers,
are unsupported. Variable and wildcard patterns can carry float payloads.

Maps use canonical unique data keys. Keys can be integers, atoms, lists, tuples,
bitstrings, pids, or references. Map, float, and function keys are unsupported,
including those nested in composite keys. Values can contain maps and functions.
Function-containing maps cannot participate in observable equality.
Literal-key map patterns match a subset of fields. Bound-variable keys remain
unsupported. Associative and exact updates evaluate all Core operands before
checking the base and keys. Multiple missing exact keys are explicitly rejected
because the current profile does not model the compiler's key-failure ordering.
Canonical storage order does not specify Erlang term order or map iteration.

Elixir metadata functions are retained whole. Their structural import does not
imply that their runtime BIF dependencies are implemented; these remain visible
call obligations. See the design tracker for verified entry points and limitations.

The companion `manifest.json` records exact OTP patch, compiler options, stage,
source path, source SHA-256, exact `core.json` byte SHA-256, exporter SHA-256,
platform architecture and endianness, and compiler warnings. This initial adapter
records Erlang as source language; Elixir/Gleam adapters must additionally retain
their source compiler and original-source provenance.

`inventory.json` counts Core node kinds, statically named module calls (including
arity), primop names, and dynamic call sites. An inventory entry is not a semantic
support assertion. Unknown semantic operations must still fail explicitly in the
Lean feature profile. Generated `module_info` calls are intentionally retained.

Hashes identify concrete artifacts and tooling, but neither hashing nor successful
differential tests prove compiler correctness or OTP correspondence.

## Checks performed

Run `node tools/check_export.mjs` from the repository root. It uses the asdf pin,
exports twice, checks byte reproducibility and the checked-in Core artifact,
verifies manifest hashes, and checks inventory entries and lossless term encoding.
The literal fixture exercises integers beyond IEEE double precision, float bit
encoding, improper lists, and distinct integer/float map keys. Direct term checks
exercise negative integers, non-byte-aligned bitstrings, and negative zero:
unoptimized Core can retain their source expressions instead of folding literals.
Temporary output directories are reported and retained for inspection.

These checks passed on OTP 29.0.6 installed with asdf on x86_64 Linux. Running the
exporter under the separately installed asdf OTP 29.0.1 failed as intended with an
`unsupported_otp_patch` diagnostic. This is extraction validation only; execution
and semantic coverage are separate obligations.

## Elixir and Gleam adapters

The repository pins **Elixir 1.20.0** and **Gleam 1.18.1** in asdf alongside OTP.
These versions were already installed locally; a fresh checkout can install them
with `asdf install elixir 1.20.0` and `asdf install gleam 1.18.1` after adding their
asdf plugins. `node tools/export_languages.mjs` regenerates both fixtures using
the exact pins; `node tools/check_languages.mjs` verifies repeatability and hashes.
Node.js is orchestration tooling, not part of the semantic model.

Elixir uses `Code.compile_string` with an explicit repository-relative filename,
`debug_info=true`, `docs=false`, and `ERL_COMPILER_OPTIONS=[deterministic]`, then the
BEAM debug-info backend's `erlang_v1` callback to recover the compiler's Erlang
abstract forms. This callback is implemented in the
[pinned Elixir compiler source](https://github.com/elixir-lang/elixir/blob/v1.20.0/lib/elixir/src/elixir_erl.erl).
The forms are serialized as `abstract.etf` and passed to `compile:noenv_forms`
with the same OTP options as the Erlang adapter. The companion BEAM is also
retained as generated output. This is reconstruction through the compiler's
debug-info facility, not a claim that the recovered forms are independently
proved equivalent to the BEAM. ETF input to `--forms` must be trusted local
compiler output: the exporter does not sandbox arbitrary ETF data.

Deterministic BEAM compilation excludes checkout-specific compiler metadata.
The language adapter overrides ambient Erlang compiler options with the recorded
option above. Reproducibility checks repeat extraction in a temporary checkout
root and compare both artifacts and intermediates, including the companion BEAM.

Gleam invokes `compile-package --target erlang --no-beam` on the dependency-free
fixture package. The actual generated `_gleam_artefacts/gleam_identity.erl` is
then passed through the existing OTP source exporter. This interface is described
in the [Gleam CLI reference](https://gleam.run/documentation/command-line-reference/).
The package manifest and generated Erlang source are hashed alongside original
Gleam source. Gleam compiler cache files are ignored.

Both manifests preserve the OTP compiler version separately, original language
compiler version and options, adapter hashes, and intermediate artifact hashes.
The fixtures provide identity, pair, empty-list, and prepend functions. Compiler
generated introspection functions remain in the Core and inventory.

Repeatability currently means the same repository location and documented path
arguments. Elixir can retain absolute source paths in its forms, and Gleam Core
can retain the generated Erlang path. Moving the checkout or choosing a different
output directory can therefore change bytes. No source annotations are normalized
away. These adapters cover one dependency-free module each; multi-module projects,
macros with external inputs, dependencies, and build-system configuration need
additional provenance before their builds can claim reproducibility.

## Full bounded verification command

Run `node tools/check_all.mjs` from the repository root after installing the pinned
toolchains. It builds the Lean executable and imported identity contract, runs
importer and machine regression checks, executes all adapter and differential
tests, checks fixture provenance, and compares the emitted Lean module with the
module used by the identity theorem. Every stage must succeed; failures stop the
command. The theorem remains scoped to the implemented value and execution profile.

The Elixir `module.beam` is ignored by Git because it is generated output. The
language reproducibility check regenerates it before verifying its recorded hash;
the full suite therefore also works when the BEAM is absent after a clean clone.
The tracked abstract-form ETF is a retained import intermediate. Neither should
be accepted from an untrusted producer without a separate input-security review.

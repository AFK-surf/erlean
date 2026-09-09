# erlean
Core Erlang executable semantics in Lean 4

The target runtime is **Erlang/OTP 29**. The project aims to verify compiled
Erlang, Elixir, and Gleam modules using executable semantics and proofs in Lean.

The initial slice imports real modules from all three languages, proves their
identity functions for arbitrary modeled values, proves list reversal and a
higher-order map example, and reuses a dependency contract across linked modules.
Captured closures, recursive groups, and class/reason exception handlers execute;
71 OTP differential cases pass. Stacktrace inspection and actor semantics remain
outside the validated profile.

See the [design document](docs/design.md) for the architecture, trust boundary,
verification interfaces, and implementation milestones.

All repository content is maintained in English.

## Development

Install the pinned Lean toolchain with elan and OTP with asdf. The Erlang asdf
plugin must be available before running `asdf install erlang 29.0.6`.

```sh
node tools/build.mjs
node tools/check_all.mjs
lake exe erlean inspect tests/fixtures/erlang/identity/core.json
lake exe erlean run tests/fixtures/erlang/identity/core.json answer '[]'
```

`run` accepts a JSON array of tagged RawCore argument terms and an optional fuel
budget. `inspect` reports rejected functions and call obligations. `emit` produces
an auditable Lean module literal for proofs; the exporter/importer are not verified
compilers. See the [OTP import notes](docs/otp29-import.md) for the schema.
`run-linked MODULE FUNCTION JSON_ARGUMENTS ARTIFACTS...` executes an explicit set
of linked modules and rejects duplicate module names.

Implementation coverage and the next work items are tracked in the
[design document](docs/design.md#implementation-tracker).

Builds are serialized by the build script, and each Lean process is limited to
one thread and 2 GiB. Run only one verification suite at a time; subagents must
not launch overlapping builds. The full suite also limits Erlang scheduler counts.

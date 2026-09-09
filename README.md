# erlean
Core Erlang executable semantics in Lean 4

The target runtime is **Erlang/OTP 29**. The project aims to verify compiled
Erlang, Elixir, and Gleam modules using executable semantics and proofs in Lean.

See the [design document](docs/design.md) for the architecture, trust boundary,
verification interfaces, and implementation milestones.

All repository content is maintained in English.

## Development

Install the pinned Lean toolchain with elan and OTP with asdf. The Erlang asdf
plugin must be available before running `asdf install erlang 29.0.6`.

```sh
lake build
node tools/check_export.mjs
lake env lean --run tests/import/Smoke.lean
lake exe erlean inspect tests/fixtures/erlang/identity/core.json
lake exe erlean run tests/fixtures/erlang/identity/core.json answer '[]'
```

`run` accepts a JSON array of tagged RawCore argument terms and an optional fuel
budget. `inspect` reports rejected functions and call obligations. `emit` produces
an auditable Lean module literal for proofs; the exporter/importer are not verified
compilers. See the [OTP import notes](docs/otp29-import.md) for the schema.

Implementation coverage and the next work items are tracked in the
[design document](docs/design.md#implementation-tracker).

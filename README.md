# erlean
Core Erlang executable semantics in Lean 4

The target runtime is **Erlang/OTP 29**. The project aims to verify compiled
Erlang, Elixir, and Gleam modules using executable semantics and proofs in Lean.

The initial slice imports real modules from all three languages, proves their
identity functions for arbitrary modeled values, proves list reversal and a
higher-order map example, and reuses a dependency contract across linked modules.
Captured closures, recursive groups, and class/reason exception handlers execute;
The byte codec has a bounded-input round-trip proof. The restricted actor runtime
supports explicit scheduling, signal delivery, receive, monitor/link lifecycle,
and replay. Tests include 91 sequential cases and 17 actor scenarios against OTP;
local lexical preservation is proved. Schedule-independent protocol proofs remain
in progress; testing is compatibility evidence, not OTP equivalence.

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
`actor-run ARTIFACT FUNCTION JSON_ARGUMENTS [TRACE_FILE]` uses a bounded debugging
scheduler; `actor-replay ARTIFACT FUNCTION JSON_ARGUMENTS TRACE_FILE` validates a
saved JSON schedule. See the design tracker for lifecycle and timing restrictions.

Implementation coverage and the next work items are tracked in the
[design document](docs/design.md#implementation-tracker).

Builds are serialized by the build script, and each Lean process is limited to
one thread and 2 GiB. Run only one verification suite at a time; subagents must
not launch overlapping builds. The full suite also limits Erlang scheduler counts.

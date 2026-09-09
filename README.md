# erlean
Core Erlang executable semantics in Lean 4

The target runtime is **Erlang/OTP 29**. The project aims to verify compiled
Erlang, Elixir, and Gleam modules using executable semantics and proofs in Lean.

The initial slice imports real modules from all three languages, proves their
identity functions for arbitrary modeled values, proves list reversal and a
higher-order map example, and reuses a dependency contract across linked modules.
Captured closures, recursive groups, and class/reason exception handlers execute.
The byte codec has a bounded-input round-trip proof. The restricted actor runtime
supports explicit scheduling, signal delivery, receive, monitor/link lifecycle,
and replay. Tests include 91 sequential cases and 17 actor scenarios against OTP;
local lexical preservation and actor cursor/signal bounds are proved. The imported
closed request/reply exchange has safety proofs over every finite accepted schedule:
a finished root returns the original payload, and pending replies preserve its
reference and payload. This does not prove termination or OTP equivalence.

See the [design document](docs/design.md) for the architecture, trust boundary,
verification interfaces, and implementation milestones.

All repository content is maintained in English.

## Verified Dijkstra example

[dijkstra.erl](tests/fixtures/erlang/dijkstra.erl) implements Dijkstra using a
sorted list queue and consumes outgoing edges when a vertex is settled. Its API
is `dijkstra:distances(Source, [{From, To, Weight}, ...])`, returning reachable
`{Vertex, Distance}` pairs. Vertex identifiers and weights are nonnegative
arbitrary-precision integers; malformed or negative inputs raise `badarg`.

[dijkstra_total_correct](Erlean/Examples/Dijkstra.lean) proves total correctness
of the actual imported OTP 29.0.6 Core implementation for **every finite graph**
in that input domain. Each returned distance is attained and minimal among all
finite walks; every omitted vertex is unreachable. The proof includes zero-weight
cycles, parallel edges, and disconnected components without a graph-size bound.
It does not require a successful execution or checked certificate as a premise.
The source/compiler/import trust boundary remains as documented in the design.

```erlang
dijkstra:distances(0, [{0,1,9}, {0,2,2}, {2,1,3}]).
%% [{0,0},{2,2},{1,5}]
```

Run `node tools/check_dijkstra.mjs` after building for reproducible extraction,
17 graph checks against OTP and independent BigInt Bellman-Ford, and 11 invalid
input checks. These tests supplement the universal proof; they are not its basis.

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

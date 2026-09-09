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

## Usage tutorial

Run all commands below from the repository root in a POSIX shell.

### 1. Install dependencies and build

Install Git, a C compiler toolchain, Node.js (tested with 20.19.2), and
[elan](https://github.com/leanprover/elan#installation). There are no npm packages
or external Lean libraries to install. To build and use the retained Core JSON
fixtures, you do not need Erlang, Elixir, or Gleam installed:

```sh
elan toolchain install leanprover/lean4:v4.33.1
node tools/build.mjs
```

The repository's `lean-toolchain` selects the pinned Lean version. The build
checks the proofs and produces `.lake/build/bin/erlean`. Use this binary in the
following commands to avoid triggering another build.

Fresh source imports and the full compatibility suite also require
[asdf](https://asdf-vm.com/guide/getting-started.html) and the versions in
`.tool-versions`: Erlang/OTP 29.0.6, Elixir 1.20.0, and Gleam 1.18.1. Add only
plugins that are not already installed:

```sh
asdf plugin add erlang https://github.com/asdf-vm/asdf-erlang.git
asdf plugin add elixir https://github.com/asdf-vm/asdf-elixir.git
asdf plugin add gleam https://github.com/vic/asdf-gleam.git
```

Install your platform's
[Erlang build prerequisites](https://github.com/asdf-vm/asdf-erlang#before-asdf-install)
before installing OTP. These options omit applications unnecessary for this
profile:

```sh
KERL_CONFIGURE_OPTIONS='--without-javac --without-wx --without-odbc' KERL_BUILD_DOCS=no asdf install erlang 29.0.6
asdf install elixir 1.20.0
asdf install gleam 1.18.1
export ERL_FLAGS='+S 2:2 +SDcpu 1 +SDio 1'
```

Manage OTP through asdf, not a separate system installation. Exporters check the
exact patch version, not merely the major release number.

### 2. Inspect and execute a compiled module

Start with the retained artifact for
[identity.erl](tests/fixtures/erlang/identity.erl):

```sh
.lake/build/bin/erlean inspect tests/fixtures/erlang/identity/core.json
.lake/build/bin/erlean run tests/fixtures/erlang/identity/core.json answer '[]'
.lake/build/bin/erlean run tests/fixtures/erlang/identity/core.json identity '[{"tag":"integer","value":"42"}]'
```

Both executions return the modeled integer `42`. `inspect` lists accepted and
rejected functions and call obligations; an imported call is not automatically
a supported BIF or a verified dependency.

Arguments are a JSON array of tagged RawCore terms. Integers use decimal
**strings** to preserve arbitrary precision; atoms use
`{"tag":"atom","value":"ok"}`, tuples use `{"tag":"tuple","items":[...]}`,
and lists use `{"tag":"list","items":[...],"tail":{"tag":"nil"}}`.
The empty list is `{"tag":"nil"}`. Returned nonempty lists are printed as nested
`cons` objects, rather than the flattened input representation. See the
[term schema](docs/otp29-import.md#rawcore-version-1) for details; transport support
for a term does not imply executable support.

`run ARTIFACT FUNCTION JSON_ARGUMENTS [FUEL]` defaults to 100000 machine steps.
An exhausted budget is inconclusive, not proof of divergence. Read the outcome:
a modeled Erlang exception is distinct from an unsupported semantic operation.

### 3. Run Dijkstra and use its universal theorem

This runs the three-edge example above inside the Lean executable semantics:

```sh
.lake/build/bin/erlean run tests/fixtures/erlang/dijkstra/core.json distances '[
  {"tag":"integer","value":"0"},
  {"tag":"list","items":[
    {"tag":"tuple","items":[{"tag":"integer","value":"0"},{"tag":"integer","value":"1"},{"tag":"integer","value":"9"}]},
    {"tag":"tuple","items":[{"tag":"integer","value":"0"},{"tag":"integer","value":"2"},{"tag":"integer","value":"2"}]},
    {"tag":"tuple","items":[{"tag":"integer","value":"2"},{"tag":"integer","value":"1"},{"tag":"integer","value":"3"}]}
  ],"tail":{"tag":"nil"}}
]'
```

The returned list encodes `[{0,0},{2,2},{1,5}]`. This execution is only an example;
the correctness theorem quantifies over every finite graph in the stated domain.
To use the theorem in Lean, run `mkdir -p build/tutorial` and save the following
as `build/tutorial/CheckDijkstra.lean`:

```lean
import Erlean.Examples.Dijkstra

open Erlean Erlean.Examples
open Erlean.Core Erlean.Semantics Erlean.Logic
open DijkstraCertificate Dijkstra

example (source : Nat) (graph : Graph) :
    ∃ result,
      Evaluates (stepLocal world)
        (initialCall "dijkstra" "distances" [encodeNat source, encodeGraph graph])
        (.returned [encodeQueue result]) ∧
      DijkstraAlgorithm.ResultCorrect graph source result :=
  dijkstra_terminates_correct source graph

#check dijkstra_total_correct
#print axioms dijkstra_total_correct
```

Check it with:

```sh
lake env lean -j1 -M2048 build/tutorial/CheckDijkstra.lean
```

`Graph` is a list of directed edges with natural-number endpoints and weights.
`ResultCorrect` states that each reported distance is attained and minimal, and
an omitted vertex is unreachable. The example proves execution and correctness
for arbitrary `source` and `graph`, not a fixed test graph. The axiom audit lists
only standard Lean axioms (`propext`, `Classical.choice`, and `Quot.sound`), with
no `sorryAx`. Negative weights are outside this theorem's domain.

### 4. Import source and generate a Lean module literal

With the pinned OTP installed, export a fresh copy into an ignored build directory:

```sh
asdf exec escript tools/export_core.escript tests/fixtures/erlang/identity.erl build/tutorial/identity
.lake/build/bin/erlean inspect build/tutorial/identity/core.json
.lake/build/bin/erlean run build/tutorial/identity/core.json answer '[]'
.lake/build/bin/erlean emit build/tutorial/identity/core.json importedTutorialModule > build/tutorial/ImportedTutorial.lean
lake env lean -j1 -M2048 build/tutorial/ImportedTutorial.lean
```

The exporter writes `core.json`, `manifest.json`, and `inventory.json`. The manifest
records OTP 29.0.6, source provenance, and the compiler options
`[to_core, binary, no_copt, deterministic, return_errors, return_warnings]`.
Keep these files together. Substitute your own `.erl` path to try another module;
unsupported constructs are reported, and partially lowered modules cannot be
executed or emitted. Includes, parse transforms, and external dependencies need
additional provenance beyond this fixture profile.

`emit` creates an auditable syntax literal, not a correctness proof. Proving your
own module requires an explicit input contract, postcondition, and proof about
that literal in the implemented semantics. Start with
[Identity.lean](Erlean/Examples/Identity.lean) and
[the existing example proofs](Erlean/Examples). The source compiler and importer
remain outside the verified trust boundary. The
[import notes](docs/otp29-import.md) also describe the Elixir and Gleam adapters.

### 5. Linked modules and actor replay

Supply each dependency explicitly for a linked call:

```sh
.lake/build/bin/erlean run-linked modular_client relay '[{"tag":"integer","value":"42"}]' tests/fixtures/erlang/modular_client/core.json tests/fixtures/erlang/identity/core.json
```

This returns `42`; duplicate module names are rejected. To record and replay the
restricted actor request/reply example:

```sh
mkdir -p build/tutorial
.lake/build/bin/erlean actor-run tests/fixtures/erlang/actor_protocol/core.json exchange '[{"tag":"atom","value":"hello"}]' build/tutorial/exchange.json
.lake/build/bin/erlean actor-replay tests/fixtures/erlang/actor_protocol/core.json exchange '[{"tag":"atom","value":"hello"}]' build/tutorial/exchange.json
```

The debugging scheduler is bounded; replay validates one schedule, not all
possible schedules. The protocol's separate arbitrary-schedule safety theorem
does not establish eventual delivery or termination. See the design document
for actor lifecycle and timing restrictions.

### 6. Run validation

After building and installing all pinned source-language toolchains:

```sh
node tools/check_all.mjs
```

For just the Dijkstra extraction and differential checks, use
`node tools/check_dijkstra.mjs`. Testing supplements the Lean proofs and does
not establish compiler correctness or full OTP compatibility.

Implementation coverage and the next work items are tracked in the
[design document](docs/design.md#implementation-tracker).

Builds are serialized by the build script, and each Lean process is limited to
one thread and 2 GiB. Run only one verification suite at a time; subagents must
not launch overlapping builds. The full suite also limits Erlang scheduler counts.

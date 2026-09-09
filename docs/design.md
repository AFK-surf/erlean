# Design: Executable Core Erlang Semantics in Lean 4

Status: implementation started. The architecture below is the target; the tracker
records actual coverage and must not be read as a full compatibility claim.

Target: Erlang/OTP 29. Each supported build profile must pin an exact OTP patch
release, compiler options, and Core extraction stage. Lean 4 and source-language
compiler versions must also be pinned when the implementation is bootstrapped.

## Implementation tracker

This document is the authoritative design and progress record. Update this section
at each validated checkpoint. Detailed technical notes may live elsewhere, but
milestone status, design changes, limitations, and the next work item belong here.

### Overall objective

Verify real Erlang, Elixir, and Gleam Core artifacts targeting OTP 29 in Lean 4.
The first end-to-end success criterion remains reproducible import, executable
evaluation, an arbitrary-input contract, and differential execution for a module
from each language. Sequential milestones precede actor-system verification.

### Current checkpoint: three-language verification slice (2026-09-09)

| Milestone | Status | Evidence / remaining work |
| --- | --- | --- |
| M0: reproducible input | Complete for the fixture profile | Reproducible real imports from all three languages, manifests, inventories, and rejection diagnostics pass. |
| M1: sequential verification | In progress | Three imported universal identity contracts and 40 differential cases pass; recursive contracts, closures, handlers, and preservation remain open. |
| M2: modular proofs | Not started | Depends on linked execution and function contracts. |
| M3: actor verification | Not started | Depends on sequential and runtime request interfaces. |

The first end-to-end success criterion is met for small identity modules from all
three source languages. This is a restricted sequential slice, not completion of
the broader M1 language coverage or general module verification.

Recovery note: the user reported an OOM kill during parallel implementation.
Subagent builds are paused. Verification now runs serially through
`node tools/build.mjs`, with a build lock, one Lean worker per process, and a 2 GiB
Lean memory limit. The exact killed process was not established from available
logs. Recovery and the complete test suite passed with these limits. Parallel
implementation may resume on independent files, but builds and test suites remain
serialized through the primary agent.

### Decision log

- 2026-09-09: Target OTP 29; pin the precise patch after checking an available
  runtime and its compiler output. No claim that all OTP 29 constructs work.
- 2026-09-09: Pin Lean to `leanprover/lean4:v4.33.1`, already available in the
  development environment. Start without external Lean library dependencies.
- 2026-09-09: Keep design and progress in this one document rather than create a
  second potentially divergent roadmap.
- 2026-09-09: Pin OTP `29.0.6` using asdf. Extraction uses `compile:noenv_file`
  with `[to_core, binary, no_copt, deterministic, return_errors, return_warnings]`,
  after `v3_core` and before `sys_core_bsm`. See [import notes](otp29-import.md).
- 2026-09-09: Use tagged JSON preserving the raw OTP Core record tree. Language
  integers are decimal strings; raw floating-point bits and bitstrings are retained
  even when the sequential value profile cannot execute them.
- 2026-09-09: Reject execution/emission of partially lowered modules. Coverage
  reports preserve rejected function signatures and original exports, preventing
  a missing implementation from silently becoming an Erlang `undef` result.
- 2026-09-09: Initial function values represent named local functions only; closures,
  `letrec`, external fun creation, and fun introspection are deferred.
- 2026-09-09: Pin asdf Elixir `1.20.0` and Gleam `1.18.1`. Elixir uses its debug-info
  backend to recover Erlang forms; Gleam produces generated Erlang. Both flow into
  the same pinned OTP extraction stage and retain intermediate provenance hashes.
- 2026-09-09: Normalize `match_fail` function-clause descriptors to the observable
  `function_clause` atom. Differential execution exposed the incorrect metadata
  tuple result; argument metadata belongs to the unmodeled stacktrace.
- 2026-09-09: Add canonical bitstring literal values (`List Bool`) and alias
  patterns to retain Elixir's generated `__info__/1` intact. Padding must be zero;
  bit-segment construction/matching and bitstring BIFs are still unsupported.
- 2026-09-09: Use focused simplification for the Elixir identity execution proof.
  Eager `cbv` expanded unrelated metadata and hit the heartbeat budget; focused
  rewriting checks in approximately two seconds under the same memory cap.

### Validation and limitations

- `node tools/check_all.mjs` passes the full bounded suite after OOM recovery.
  `node tools/build.mjs` compiles modules and native objects in dependency order;
  the final library, executable, and all example proofs build successfully.
- `lake env lean --run tests/import/Smoke.lean` passes malformed-input, precision,
  lexical scope, unsupported-feature, and real OTP fixture checks.
- `node tools/check_export.mjs` checks reproducible extraction, hashes, operation
  inventory, and lossless literals using asdf-managed OTP 29.0.6.
- `Erlean.Examples.identity_totalCorrect` proves total correctness for every Value
  input of the actual emitted Erlang identity AST. Its axiom audit reports only
  `propext` and `Quot.sound`; no `sorry`, custom axiom, or native execution axiom.
- `gleam_identity_totalCorrect` and `elixir_identity_totalCorrect` prove the same
  contract against exact emitted modules. The Elixir proof additionally uses
  Lean's standard `Classical.choice`. The suite prints all three axiom sets and
  checks that generated Lean fixtures exactly match current importer output.
- `node tools/check_languages.mjs` checks reproducibility and source/intermediate
  provenance for the Elixir and Gleam artifacts.
- Kernel-checked generic execution results: step determinism, finite evaluation
  soundness/completeness, budget splitting, and stability under additional fuel.
- Forty differential cases pass against OTP 29.0.6, including recursive list
  functions, arbitrary-precision arithmetic, exceptions, operand order, context
  restoration, and all three source-language identities and constructors.
- Machine regressions check multiple values, invalid arities/scope, guard fallback,
  unsupported faults, fuel resumption, and bounded stack use for tail calls.
- Scope and pattern checks cover integers, atoms, lists, tuples, alias bindings,
  and bitstring literals. `Module.check` establishes lexical/signature checks,
  not complete Core arity validation or guard-grammar validity.
- Machine support includes multi-values, binding, sequencing, construction,
  named calls, cases/guards, selected integer BIFs, and `match_fail/1`. Exceptions
  expose class/reason only; stack inspection and handlers are not yet implemented.
- Unknown BIFs, unlinked dependencies, and other unsupported operations report
  model faults. Generated `module_info` calls remain visible obligations.
- No full OTP compatibility, closure support, actor execution, or completed M1
  claim is made. State preservation and recursive-function contracts remain open.

### Next work

1. Prove a recursive list-function contract against imported Core, beginning with
   accumulator-based reversal; provide reusable frame and call proof rules.
2. Strengthen accepted-Core invariants and prove local state preservation.
3. Add captured closures and `letrec`, then a higher-order map contract.
4. Extend exception handlers and the codec-required map/bitstring operations.
5. Progress to M2 dependency-contract reuse before starting M3 actor semantics.

### Commit checkpoints

- `a9c21be`: design, repository instructions, and buildable Lean bootstrap; pushed
  to `origin/main`.
- `78c590a`: three source exporters, OTP import, first local machine, CLI,
  generic runner proofs, and the imported Erlang identity contract; pushed.
- Current checkpoint: three-language contracts, 40 differential cases, canonical
  bitstring literals, alias patterns, and resource-bounded serial verification.
  The commit carrying this tracker update records the exact revision.

## 1. Purpose and success criteria

erlean will provide an executable, proof-oriented semantics for Core Erlang in
Lean 4. The intended users verify properties of Erlang, Elixir, and Gleam modules
after compilation to a supported OTP 29 Core artifact.

The first end-to-end milestone is:

1. Import a real compiled module from each source language.
2. Execute representative exported functions in Lean.
3. Prove a function contract for arbitrary inputs satisfying its precondition.
4. Compare concrete executions with the corresponding OTP 29 execution.

The architecture must support later actor-system verification without requiring
a replacement of the sequential semantics.

Initial non-goals are full BEAM emulation, a verified compiler, distributed Erlang,
hot code loading, complete OTP library coverage, and precise runtime resource or
performance modeling. Native functions, ports, IO, ETS, floating-point operations,
and other runtime facilities enter through explicit supported models or remain
unsupported. Merely declaring a value constructor does not imply support for all
operations over that value.

## 2. Verification boundary

The initial theorem states:

> This imported Core artifact satisfies property P under the declared runtime
> model, feature profile, and dependency assumptions.

It does not independently establish source compiler correctness or equivalence
with a deployed BEAM artifact. Transferring the result to a source program relies
on the source compiler, extraction pipeline, Core-to-BEAM compiler, and runtime
faithfully implementing the relevant semantics.

Each imported artifact should have a manifest containing:

- Source and Core artifact hashes.
- Source-language compiler version and build configuration.
- Exact OTP 29 patch version, compilation options, and extraction stage.
- Import format version and importer version.
- erlean semantic profile and dependency artifact identifiers.
- Relevant target-platform assumptions, such as native bit-segment endianness.

Hashes associate proofs with artifacts; they do not prove translation correctness.
Lean checks theorems about the embedded AST. An unverified exporter can still
export the wrong AST, even if the AST passes structural validation.

The preferred proof path uses definitions and proof terms checked by the Lean
kernel. Native execution is useful for testing and exploration; any proof facility
that adds trust in native compilation must declare that additional trust explicitly.

## 3. OTP 29 compatibility profile

Core Erlang is an implementation-facing intermediate representation. OTP documents
that primops may change between major releases. Older Core specifications are
useful background but are not the complete acceptance contract for this project.

Compatibility is defined by a named profile, for example `otp29-sequential-v1`,
whose manifest specifies accepted constructs, primops, BIFs, annotations, runtime
operations, and platform assumptions. Exact names are provisional.

The initial extraction investigation must identify and pin one reproducible Core
stage before committing to a concrete compiler hook. Optimized and unoptimized
Core are distinct inputs: optimizations can change generated operations and
observable exception details. We must not silently switch stages.

The importer must emit a coverage report before verification. Every encountered
operation must be implemented, covered by an explicit environment contract, or
reported as unsupported. Unknown constructs must never be erased or treated as
successful no-ops. Where dynamic calls prevent a complete static coverage check,
execution and proof rules must preserve that obligation.

Modern receive lowering is part of the design from the beginning. EEP 52 describes
the introduction of operations such as `recv_peek_message`, `recv_next`,
`remove_message`, and `recv_wait_timeout`. The implementation must inventory the
actual OTP 29 operations and annotations rather than assume that this historical
list is exhaustive.

## 4. Import pipeline

```text
Erlang / Elixir / Gleam source
             |
     source compiler adapter
             |
  pinned OTP 29 Core extraction
             |
       versioned RawCore
             |
   decoding and scope validation
             |
         semantic Core AST
             |
   execution and module contracts
```

Source adapters converge at Core; the semantic engine does not interpret three
source languages separately. The exact Elixir and Gleam integration hooks are
implementation investigation items. Support initially applies to reproducible
source builds, not arbitrary BEAM binaries without recoverable intermediate data.

Use two representations:

| Representation | Responsibility |
| --- | --- |
| `RawCore` | Preserve compiler structure, names, literals, annotations, and source locations. |
| `Core` | Resolve bindings and represent validated input for the semantic machine. |

Prefer an OTP-side exporter with a small versioned interchange schema over a
handwritten parser for pretty-printed Core. The encoding must preserve arbitrary
integers, atom identity, float bits, and bitstring lengths without lossy host
conversions. The schema and exporter are part of the auditable import boundary.

Use unique variable identifiers and finite environments internally. Provide
explicit well-scopedness and structural validity predicates, with executable
checks and correctness lemmas. Avoid making the whole AST intrinsically typed in
the first implementation.

Preserve annotations until their semantic relevance has been classified. Maintain
source provenance separately where possible. Name resolution should not perform
unnecessary optimization, receive reconstruction, or closure conversion. Any
later semantic transformation needs a preservation theorem or an explicitly
documented extension of the trusted translation boundary.

## 5. Syntax and runtime values

The semantic AST must preserve distinctions between:

- `call`, `apply`, and `primop`.
- A single Erlang term and a Core sequence of returned values.
- `let`, `letrec`, function construction, and function references.
- Pattern matching and guard evaluation.
- Normal evaluation, exception raising, and exception handlers.
- Map and bitstring construction and matching.

Evaluation order must follow the selected Core stage and OTP 29 behavior. It must
not be chosen incidentally by the order of Lean function arguments.

### Values

Represent Erlang values explicitly. The intended universe includes integers,
atoms, nil and cons, tuples, maps, bitstrings, floating-point values, local and
external funs, process identifiers, references, and eventually ports.

Important representation decisions:

- Use mathematical `Int` for arbitrary-precision integers.
- Represent cons cells explicitly, including improper lists.
- Represent bitstrings with an explicit bit length; byte arrays alone are
  insufficient.
- Keep Core multiple values outside the Erlang term datatype.
- Define exact equality, numeric equality, and term ordering separately.
- Define map key equivalence using Erlang semantics, not generic Lean equality.
- Preserve floating-point bits during import. Arithmetic requires a separately
  specified model; initial profiles may reject unsupported operations.

Executable comparison procedures need correctness results against their semantic
relations. Data structure optimizations must preserve these relations.

### Closures and recursive bindings

Closures are data containing a code identifier and captured values, not Lean
functions. Code lives in an immutable code world for the initial static-linking
profile.

Represent a `letrec` group by a group descriptor and its outer captured
environment. Calling a group member reconstructs the recursive bindings from the
descriptor, avoiding cyclic inductive Lean values. Establish well-formedness
invariants for captured environments and code lookup.

Internal allocation identifiers must not accidentally define observable Erlang
fun equality. Fun equality and introspection need a specified model or explicit
profile restrictions.

## 6. Sequential machine

Use a small-step machine with explicit continuation frames. Its conceptual state
is:

```text
LocalState = control + environment + continuation + process-local state

Control = evaluate expression
        | return Core values
        | raise exception
        | await runtime response
```

Frames record pending argument evaluation, binding, branch selection, call return,
and exception handling. Tail calls must not accumulate ordinary return frames.
Stacktrace representation needs separate care because stacktraces are observable
values, not just debugging metadata.

The following signatures are interface sketches, not compilable declarations:

```lean
stepLocal : CodeWorld → LocalState → LocalProgress
runLocal  : Nat → CodeWorld → LocalState → RunResult
```

`LocalProgress` distinguishes a next state, a suspended runtime request, a terminal
outcome, and a model fault. A terminal outcome is a normal return or an uncaught
Erlang exception. The local runner stops at unresolved runtime requests; a system
runner or concrete runtime model can resume them.

`stepLocal` is a total definition. Program recursion unfolds across machine steps;
the runner uses structural recursion over fuel. Do not make ordinary opaque
`partial def` evaluation the central proof interface.

The result types must distinguish:

| Result | Meaning |
| --- | --- |
| Returned | The program produced values. |
| Raised | The program produced an uncaught Erlang exception. |
| Suspended or blocked | The program requires a runtime response or cannot currently proceed. |
| Fuel exhausted | The runner reached its execution budget; execution can resume. |
| Unsupported | The model has no implementation for an encountered feature. |
| Invalid | Input or machine invariants were violated. |

Fuel exhaustion is neither divergence nor an Erlang timeout. Unsupported behavior
is not an Erlang exception and must not become catchable by the program.

### Proof relation

Define local `Step` from the graph of the executable transition and derive
multi-step reachability and execution traces from it. Expose readable rule lemmas
for each construct rather than maintain two independent complete semantics.

Foundational results should include local determinism, preservation of machine
invariants, runner correspondence with finite steps, and fuel extension or
resumption properties. Relating a runner to its own step graph establishes
internal consistency, not correspondence with OTP; that requires separate
semantic justification and compatibility evidence.

### Patterns, guards, and exceptions

Pattern matching must handle binding scope, clause order, map keys, and bitstring
segment constraints. Guard failure must follow OTP rules rather than uniformly
propagate ordinary expression exceptions. Preserve `error`, `exit`, and `throw`
classes and implement handler unwinding explicitly.

If exact stacktrace construction is deferred, the supported profile must restrict
stacktrace observation or declare an abstraction with an appropriate justification.
An arbitrary placeholder stacktrace is not an exact semantics.

## 7. Built-ins, modules, and effects

Separate three kinds of operation:

| Kind | Execution | Proof use |
| --- | --- | --- |
| Pure BIF | Explicit executable definition | Rewriting and BIF correctness lemmas |
| Imported module function | Execute linked Core | Apply a proved function contract |
| Runtime or external operation | Explicit request handled by a model | Apply a model rule or declared environment contract |

The code world resolves modules, exports, and arities. Missing exports and invalid
applications must produce the appropriate modeled Erlang behavior when supported,
not be confused with missing implementation support.

A proved dependency contract is a proof shortcut, not permission for the concrete
interpreter to invent a result. External contracts can describe several possible
results and effects. Concrete execution then requires an implementation, a
declared test stub, or an explicit choice accepted by the model.

Contracts need to express exceptions, effects, and state changes where relevant.
A postcondition about return values alone is insufficient for effectful calls.

## 8. Actor-system semantics

The concurrent layer extends the local machine with explicit system state:

```text
SystemState = processes
            + in-flight signals
            + mailboxes and receive cursors
            + logical time and timers
            + fresh identity supply
            + supported runtime resources
```

Use an executable transition with explicit nondeterministic choices:

```lean
stepSystem : CodeWorld → SystemState → Choice → Except ChoiceError SystemState
```

Choices include executing a process, delivering an eligible signal, and advancing
time subject to the timing model. The transition validates each choice. Existential
quantification over accepted choices defines the system transition relation.
Proofs quantify over that relation; a particular scheduler is only an execution
strategy. Exhaustive finite exploration is possible only for suitably bounded
instances, not arbitrary open environments or unbounded time domains.

Required design constraints:

- Separate signal sending from delivery and enforce OTP's applicable signal
  ordering guarantees without imposing a total order between unrelated senders.
- Model selective receive with a scan cursor and precise removal behavior;
  unmatched messages retain their relative order.
- Give lowered receive primops explicit transitions and invariants, including
  their interaction with newly delivered messages.
- Track timeout deadlines and legal expiration events separately from execution
  fuel. State the timing abstraction used by any timed theorem.
- State scheduling and delivery fairness assumptions explicitly for liveness
  proofs. Safety proofs must not silently inherit a single scheduler's behavior.
- Extend link, monitor, and process exit through the signal layer.

The first actor profile is single-node and may exclude newer runtime features
such as priority messages until modeled. Rejection or declared abstraction must
make such exclusions visible. Every profile must state whether it is an exact
restricted model or a justified over-approximation; omitted behaviors must not
silently strengthen verification claims.

## 9. Module verification interface

Users should prove contracts about exported functions, with fuel hidden from
ordinary specifications. Provide:

- Partial correctness: all reachable states remain within the supported model,
  and terminating outcomes and relevant effects satisfy the contract. Divergence
  is permitted.
- Total correctness: additionally establish termination under the stated
  environment assumptions. Actor liveness requires its own explicit assumptions.

A representative intended interface is:

```lean
-- Interface sketch: names and encodings remain to be implemented.
theorem reverse_correct :
  TotalCorrect world ⟨"demo", "reverse", 1⟩
    (fun args => ∃ xs, args = [encodeList xs])
    (fun args result =>
      ∀ xs, args = [encodeList xs] →
        result = .returned [encodeList xs.reverse])
```

For sequential functions, termination can be expressed through finite reachability
of a terminal outcome; general recursive proofs use well-founded induction or
another explicit termination argument. For actors, provide invariant and trace
properties separately from function return contracts.

Develop proof automation in this order:

1. Simplification lemmas for values, patterns, frames, and pure BIFs.
2. Symbolic stepping through concrete Core structure.
3. Application of previously proved module contracts.
4. Recursive-function induction support.
5. Reflection for closed, bounded computations with kernel-checkable evidence.

Language-specific adapters can supply encoders, decoders, and representation
invariants for Gleam and Elixir data. Source types and specifications may suggest
preconditions, but are not automatically proof evidence.

## 10. Validation strategy

Maintain a corpus of small source modules and their reproducibly extracted Core.
Run concrete cases both in erlean and on the pinned OTP 29 runtime. Include all
three source languages early, so the design encounters real generated idioms.

High-value cases include argument evaluation order, recursive closures, tail calls,
Core multiple values, improper lists, exact versus numeric equality, map keys,
bitstring boundaries, guard failures, and exception propagation. Actor cases add
unmatched messages, receive scans, timeout boundaries, and signal ordering.

Compare values and supported observable outcomes. Any normalization of identities,
stacktraces, or traces must have an explicit rationale and must not conceal a
distinction observable by the property being checked. Concurrent testing should
check allowed outcomes and ordering constraints rather than demand identical
uncontrolled schedules on BEAM and the model.

Differential testing detects mismatches; it does not prove the semantics agrees
with OTP. Preserve minimized counterexamples as regression fixtures. Unsupported
operations and failed coverage checks count as incomplete coverage, not passes.

## 11. Proposed repository layout

The following is a planned layout, not a list of existing modules:

```text
Erlean/
  Core/           -- Syntax, values, scope checks, artifact metadata
  Import/         -- Interchange decoding and validation
  Semantics/      -- Frames, local machine, transitions, exceptions
  Runtime/        -- BIFs, runtime operations, actor system, profiles
  Logic/          -- Reachability, contracts, invariants, proof rules
  Tactic/         -- Symbolic execution and contract application
  Examples/       -- Verified imported modules
tools/            -- OTP and source-language extraction adapters
tests/            -- Compatibility fixtures and differential harness
docs/             -- Design and supported-profile documentation
```

Keep IO and tool invocation outside the semantic definitions. Executable drivers
may use Lean IO; the transition functions and proof interfaces remain pure.

All repository content, including comments, documentation, and test descriptions,
is written in English regardless of the language used in project discussions.

## 12. Milestones and acceptance criteria

### M0: Reproducible input

Pin toolchains and the OTP 29 Core stage. Export one small module from each source
language, retain artifact manifests, and generate a construct/BIF/primop inventory.
Acceptance requires a reproducible import with actionable unsupported-feature
diagnostics. This milestone determines the concrete initial support profile.

### M1: Sequential verification

Implement the local machine, recursion and closures, matching and guards,
exceptions, required pure BIFs, and the map/bitstring subset needed by the examples.
Prove machine invariants and runner correspondence. Complete universal-input
contracts for list reversal, a higher-order map example, and a small codec as
coverage permits. Meet the three-language end-to-end success criterion from
Section 1 and pass the corresponding differential corpus.

### M2: Modular proofs

Add linked-module execution, proved dependency contracts, representation lemmas,
and basic symbolic execution. Acceptance requires a multi-module proof that reuses
a dependency theorem rather than unfolding its implementation at every call.
Unproved external assumptions must be visible in the theorem interface.

### M3: Actor verification

Implement a documented single-node profile for spawn, send, lowered receive, and
timeouts, followed by monitor and link support. Prove a request/reply protocol
invariant over all allowed schedules, and state the extra assumptions needed for
any progress result. Retain executable traces for debugging and replay.

## 13. Decisions deferred to implementation evidence

The architecture commits to OTP 29, explicit machine state, total executable steps,
and visible verification assumptions. The following choices require inspection of
actual compiler artifacts before being finalized:

- Exact OTP 29 patch release, extraction stage, and source compiler hooks.
- Interchange encoding and annotation classification.
- Initial BIF and primop inventory, including receive optimization operations.
- Exact fun equality and stacktrace support in the first profile.
- Floating-point, native-endian, and timing model scope.
- The first practical Elixir and Gleam examples and their required dependencies.

These are tracked compatibility decisions, not permission to substitute unspecified
behavior during execution or proof.

## References

- [OTP compiler documentation](https://www.erlang.org/doc/apps/compiler/compile.html):
  Core integration, primop stability, and compiler behavior. The live documentation
  can advance; implementation work must retain references for its pinned OTP 29 build.
- [EEP 52](https://www.erlang.org/eeps/eep-0052): changes to Core binary matching
  and receive lowering introduced in OTP 23.
- [OTP process documentation](https://www.erlang.org/doc/system/ref_man_processes.html):
  signals, process communication, and ordering guarantees.
- [A Formalisation of Core Erlang, a Concurrent Actor Language](https://arxiv.org/abs/2311.10482):
  prior machine-checked work using modular frame-stack semantics. It is a design
  reference, not evidence of OTP 29 compatibility.
- [Lean recursive definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/):
  total definitions, recursion, and executable proof-facing definitions.

# Design: Executable Core Erlang Semantics in Lean 4

Status: initial milestones implemented for the restricted profiles in the
tracker. The broader architecture is a target, not a full compatibility claim.

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

### Current work: Cue controller verification support (2026-09-09)

Cue will consume Erlean through a pinned Git dependency to prove its production
Agent Loop kernel. Add explicit OTP `29.0.2` import support alongside the existing
`29.0.6` fixture profile. Export requires the exact selected runtime patch and
never relabels another patch. The default toolchain and fixtures stay unchanged.
The actual Cue kernel exports and lowers under asdf OTP `29.0.2` without rejected
functions. Its control data needs only existing tuple, atom, reference, and
integer operations. No business-specific semantic rule is added.

New comparable-data equality reflection and finite controller trace lemmas have
passed the serialized Lean build. Function identity remains unsupported. Trace
lifting requires an actual one-step implementation refinement and does not prove
external effect execution, truthful storage responses, or infinite-schedule
liveness. The full regression suite and axiom audit passed, including 91
sequential differential cases, 17 actor scenarios, and 28 graph/input checks.
The new lemmas use only standard kernel axioms. Re-exported fixture manifests
refresh exporter provenance without changing Core literals. Explicit profile
selection and rejection of unsupported or mismatched patches pass. Next, pin
this library checkpoint in Cue and check its universal compiled-controller proofs.
The Cue plan and production adapter obligations live in that repository at
`docs/salix/agent-loop-kernel-verification.md`.

Cue's differential gate needs repeated calls against one large imported module.
The generic `run-batch` CLI imports once and evaluates independent cases with a
per-case fuel budget. It publishes one ordered result array only after every
case succeeds. Raised Erlang exceptions remain observable results. Model faults,
malformed cases, and exhaustion fail without partial standard output. This is a
runner optimization, not a semantic extension. The full serialized suite passed,
including batch ordering, raised outcomes, malformed input, late model faults,
and per-case exhaustion with atomic output. The original single-call CLI checks
and all artifact, differential, and theorem checks still pass. Cue's Round,
Dependency, Ownership, and Policy modules have passed kernel checking.

Cue now pins `d1ee8a67c22d2aecc5ff4ec2d8f3408eb6c166a8` through a real public
Git dependency. Its complete proof gate passed, including two exact OTP 29.0.2
exports, emitted-syntax correspondence, 241 batch differential cases, and an
allowlisted final axiom audit. Its full Agent Loop application suite passed
1763 tests with 2 existing skips and 42 excluded live-LLM cases. All 65 retained
TLC configurations produced their expected outcomes, including 42 deliberate
violations. The production integration is open as
[Cue PR #1581](https://github.com/AFK-surf/Cue/pull/1581). Cue's tracker records
the exact theorem domains, synchronous-adapter obligations, reference abstraction,
and unchanged durable protocol mappings. No whole-actor, compiler, storage,
or global-liveness proof is claimed. The library's
hosted full suite also passed at this pin:
[run 34349033714](https://github.com/AFK-surf/erlean/actions/runs/34349033714).

### Previous checkpoint: GitHub Actions verification (2026-09-09)

GitHub Actions now runs a single Ubuntu 24.04 job on pull requests, pushes to
`main`, and manual dispatch. It installs the pinned Lean toolchain and manages
OTP/Elixir/Gleam through asdf and `.tool-versions`. The cold serialized build runs
before the complete suite to avoid the suite's shorter per-stage timeout. Lean
outputs are not cached; source-language installations are cached against the
toolchain and workflow definitions. Permissions are read-only, action references
are commit-pinned, superseded runs are cancelled, and asdf compilation is capped
at two workers alongside the existing one-worker/2 GiB Lean limits. Workflow
lint passed. Review caught checkout-specific
metadata in the Elixir companion BEAM. The adapter now uses an explicit relative
filename and deterministic BEAM compilation, records those compiler options, and
tests byte equality after relocating the fixture inputs to a temporary root.
Relocation checks and the full local suite passed with refreshed artifact
provenance. The emitted executable Elixir module literal is unchanged. The
fresh hosted workflow also passed: [run 34332011416](https://github.com/AFK-surf/erlean/actions/runs/34332011416)
at `d59ad64` completed in 8m53s, including toolchain installation, cold kernel
checking, the complete suite, and a clean retained-artifact diff. GitHub emitted
a non-fatal Node 20 action-runtime deprecation notice; these pinned actions ran
successfully under the runner's Node 24 compatibility behavior. Future action
updates should select native Node 24 releases and rerun the same checks.

### Validated example layout

Example sources now live in topic directories: `Identity`, `Sequential`,
`HigherOrder`, `Modular`, `ByteCodec`, `Protocol`, and `Dijkstra`. Each directory
keeps its imported artifact literals with its contracts and supporting proofs;
filenames describe their role without repeating the directory name. Lean imports,
artifact-correspondence checks, and README links follow the new paths. Public
declaration namespaces and generated literal contents remain unchanged, so this
is a module-path reorganization, not a semantics or theorem API change. The
dependency-ordered build and complete compatibility suite passed, including all
kernel axiom audits, 91 sequential cases, 17 actor scenarios, and 17 graph plus
11 invalid-input checks. All 31 moved files preserve content outside imports.
Source-import existence and README link checks also passed, independently of
cached build artifacts; the updated README contract snippet kernel-checks.

The previous documentation checkpoint is recorded below for context.

The README now provides an English walkthrough of dependency setup, retained
artifact execution, identity function contract reuse, fresh OTP import and Lean
literal emission, linked calls, actor recording/replay, and validation. It
distinguishes the minimal Lean/Node setup from source-language dependencies and
keeps the existing semantic and compiler trust boundaries explicit. Following
user feedback, algorithm-specific walkthroughs were removed from the README;
Dijkstra is now a peer link alongside the other examples. The replacement
arbitrary-value identity contract snippet passed kernel checking with one worker
and a 2 GiB cap; its axiom audit reports only `propext` and `Quot.sound`. Local
README link targets and `git diff --check` also passed. No implementation changed.

At the preceding tutorial checkpoint, documentation checks passed: all tutorial
execution commands, a fresh OTP 29.0.6
identity export, generated literal kernel checking, the arbitrary-graph Lean
proof snippet and axiom audit, linked execution, actor recording/replay, local
Markdown link targets, and `git diff --check`. Lean checks ran serially with one
worker and a 2 GiB cap. Dependency installation was not repeated, and the full
compatibility suite was not rerun for this documentation-only change; its most
recent full result remains the universal Dijkstra checkpoint below. No semantics
or proof claims changed. Next implementation work remains the explicitly scoped
extensions in "Next work beyond the initial milestones".

| Milestone | Status | Evidence / remaining work |
| --- | --- | --- |
| M0: reproducible input | Complete for the fixture profile | Reproducible real imports from all three languages, manifests, inventories, and rejection diagnostics pass. |
| M1: sequential verification | Complete for the restricted profile | Imported reversal, higher-order identity-map, byte codec, runner correspondence, and full local lexical preservation are proved. General maps/bitstrings and stacktraces remain excluded. |
| M2: modular proofs | Complete for tail delegation | Real imported client reuses a dependency contract in an explicit linked world; arbitrary continuation lifting remains future work. |
| M3: actor verification | Complete for the closed-exchange profile | Runtime/lifecycle/replay execute; actual imported request/reply safety is proved for every finite accepted schedule. Progress assumptions are explicit; no liveness theorem is claimed. |

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

- 2026-09-09: Add a real list-based Erlang Dijkstra example for finite directed
  graphs with natural-number vertex identifiers and nonnegative integer weights.
  The user requires a universal algorithm termination/refinement theorem, not
  just certificate-conditioned correctness or representative executions. Prove
  the pure algorithm for arbitrary graphs, then connect the actual imported
  Core implementation to it for arbitrary inputs and continuations. The
  certificate soundness theorem is a supporting lemma, not the acceptance gate.
  Consume outgoing edges when their source is first settled: queue length plus
  remaining-edge count decreases on every search iteration, giving a proved
  graph-size resource bound without bounding the accepted input graph.
  The only planned BIF extension is integer `erlang:'=<'/2`; other term-order
  comparisons remain unsupported rather than using an incorrect ordering.
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
  `letrec`, external fun creation, and fun introspection were initially deferred.
- 2026-09-09: Pin asdf Elixir `1.20.0` and Gleam `1.18.1`. Elixir uses its debug-info
  backend to recover Erlang forms; Gleam produces generated Erlang. Both flow into
  the same pinned OTP extraction stage and retain intermediate provenance hashes.
- 2026-09-09: Normalize `match_fail` function-clause descriptors to the observable
  `function_clause` atom. Differential execution exposed the incorrect metadata
  tuple result; argument metadata belongs to the unmodeled stacktrace.
- 2026-09-09: Add canonical bitstring literal values (`List Bool`) and alias
  patterns to retain Elixir's generated `__info__/1` intact. Padding must be zero;
  bit-segment construction/matching was deferred at that checkpoint; the later
  fixed unsigned-byte decision extends it without enabling general bitstring BIFs.
- 2026-09-09: Use focused simplification for the Elixir identity execution proof.
  Eager `cbv` expanded unrelated metadata and hit the heartbeat budget; focused
  rewriting checks in approximately two seconds under the same memory cap.
- 2026-09-09: Add finite closures as module-local code references, captured values,
  and recursive-group descriptors. The importer extracts nested code into a table,
  reserves recursive slots before lowering members, and resolves lexical function
  names before module references. This code extraction is inside the unverified
  importer boundary; no translation-preservation theorem is claimed.
- 2026-09-09: Reconstruct recursive bindings on application without cyclic values.
  Capture all ambient lexical bindings initially. Structural closure comparison is
  only internal machinery; OTP-observable fun equality/introspection remain unsupported.
- 2026-09-09: Model Core try/catch and raise with class/reason and opaque internal
  exception information. Protect tokens from BIF observation, pattern inspection,
  and public serialization. Legacy catch of errors and stacktrace construction
  remain unsupported; legacy throw/exit catch is supported. Model faults bypass
  language handlers. Compiler-generated after cleanup uses ordinary continuations.
- 2026-09-09: Separate internal `TotalCorrect` from `ObservableTotalCorrect`.
  Public contracts additionally require supported observation at the boundary;
  arbitrary internal Value quantification must not imply public token transport.
- 2026-09-09: Reuse dependency contracts through checked common-entry prefixes in
  the same linked code world. This supports tail delegation without assuming
  that extending or replacing a world preserves an earlier theorem.
- 2026-09-09: Restrict executable binary segments to literal size 8, unit 1,
  unsigned big-endian integer fields. Construction preserves the low eight bits
  for every integer; patterns consume exactly the expected bytes, with no trailing
  bits. Other sizes, units, types, flags, and dynamic sizes are explicitly rejected.
  The codec needs no map operations; maps remain outside this profile.
- 2026-09-09: Add runtime suspension to the local machine. Sequential execution
  reports a model fault on suspended operations; the actor driver supplies effects.
  Pids/references are fresh counters within a closed initial system, not BEAM
  identity encodings. External injection of identities requires explicit assumptions.
- 2026-09-09: Actor choices separate process steps, per-pair FIFO signal delivery,
  and logical millisecond time advances. Receive uses a mailbox scan cursor and a
  persistent deadline. A ready mailbox entry wins over timeout at a wait step;
  this is a declared timing abstraction, not a wall-clock OTP equivalence claim.
- 2026-09-09: Monitor/link registration and removal travel through the signal
  layer. Immediate owner-side cancellation suppresses stale DOWN/link-exit signals;
  already queued DOWN messages remain. Link generations prevent reactivation by
  stale signals. Self exit/2, normal exit, kill, and synchronous local link failure
  retain their distinct OTP 29 behaviors.
- 2026-09-09: Keep lifecycle limitations explicit: no trap_exit, priority signals,
  distributed/registered destinations, monitor options, exit_signal/2, or full
  simultaneous opposite-endpoint link handshake. Observed uncaught error/throw
  process termination requires unmodeled stacktraces and faults rather than
  fabricating a notification reason. Any model fault stops system execution.

### Validation and limitations

- `Dijkstra.dijkstra_total_correct source graph` is kernel checked for every
  finite directed graph with natural-number vertex identifiers and nonnegative
  integer weights. It proves total correctness of the actual imported OTP 29.0.6
  `dijkstra:distances/2` implementation, including source validation, sorted queue
  operations, consumed-edge expansion, recursive search, and final reversal.
  Returned distances are attained and minimal over all finite walks; missing
  vertices are unreachable. There is no accepted-run, certificate-check, fixed
  interpreter budget, or bounded-graph premise in the final theorem.
- `DijkstraAlgorithm.distances_total` proves the mathematical algorithm terminates
  within `|E| + 1` queue removals. This is not a bound on Core machine steps or a
  complexity claim. Generic arbitrary-stack refinement lemmas prove each source
  helper terminates and compose a finite Core execution for every input graph.
  The proof allows parallel edges, self-loops, zero-weight cycles, disconnected
  components, and unbounded integer magnitudes. The result specification is about
  the distance lookup relation; no separate list-order or list-uniqueness theorem
  is claimed. The source queue tie convention remains deterministic.
- Dijkstra source/artifact reproduction and 17 graph scenarios pass against OTP
  and independent BigInt Bellman-Ford. Eleven malformed/negative input scenarios
  agree on `error:badarg`. These checks supplement, rather than discharge, the
  universal theorem. Full-suite revalidation and the final axiom audit passed.
- `node tools/check_all.mjs` passes the full bounded suite after OOM recovery.
  `node tools/build.mjs` compiles modules and native objects in dependency order;
  the final library, executable, and all example proofs build successfully.
- `reverse_totalCorrect` proves termination and reversal for every finite list of
  modeled values against the retained OTP sequential artifact. The proof composes
  a 20-step entry prefix, 22-step recursive worker prefixes, and a 12-step base
  case using list induction. It does not assume a fixed total execution budget.
- `Erlean.Logic.Rules` exposes finite-prefix execution composition for reuse in
  recursive and modular proofs. The suite checks the exact emitted recursive
  proof artifact and audits the theorem's standard Lean axioms.
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
- Ninety-one sequential differential cases pass against OTP 29.0.6, including recursive list
  functions, arbitrary-precision arithmetic, exceptions, operand order, context
  restoration, and all three source-language identities and constructors.
- Closure cases cover capture, nested captures, returned closures used by callers,
  named recursive sum, and recursive map capturing a second closure. The importer
  rejects incomplete code tables, and the module checker validates capture scopes
  and recursive code references. `map_identity_totalCorrect` proves the actual
  imported higher-order callback example for every finite list of modeled values.
  Its inductive return lemma accepts arbitrary continuation stacks.
- `modular_relay_totalCorrect` verifies the emitted client and identity dependency
  together. The client theorem applies the dependency contract without unfolding
  its body. CLI `run-linked` executes explicit artifact sets and rejects duplicate
  module names. Kernel axiom audits cover both new contracts.
- Exception regressions cover handler frame removal, rethrow, lexical context,
  opaque-token observation, malformed arities, and unsupported fault propagation.
- `byte_roundtrip_totalCorrect` proves the actual imported byte codec returns its
  input for every integer in [0,256). The stronger execution theorem normalizes
  every integer modulo 256. `byte_roundtrip_observableTotalCorrect` checks the
  public observation boundary too. Byte conversion and all example theorem axioms
  are audited by the full suite.
- Seventeen actor differential scenarios compare the selected bounded scheduler
  against isolated OTP processes. Separate regressions exercise FIFO rejection,
  selective-receive retention, persistent timeouts, stale lifecycle signals, and
  replay. These tests do not prove safety for arbitrary schedules or fairness.
- `actor-run` can retain JSON choices, and `actor-replay` checks a supplied trace
  against the same pure transition. Invalid choices are not language exceptions.
  The default scheduler advances time only when no process/delivery can progress;
  it is a debugging strategy, not an assumption silently imported into proofs.
- `Erlean.Core.Environment` proves lookup/key correspondence, environment extension,
  parameter-zip coverage under arity agreement, and successful-pattern coverage.
- `stepLocal_preserves_lexical_scope` now covers every local control/frame branch
  under an immutable checked code world. The invariant uses static scopes covered
  by dynamic environments, including saved frames and finite closure descriptors.
  `runLocal_preserves_lexical_scope` lifts it through every finite successful prefix;
  `initialCall_reachable_variable_not_unbound` excludes the unbound-variable fault
  when the next expression is a variable. This is lexical availability, not general
  fault freedom, dynamic arity correctness, or an OTP translation theorem.
- Protocol proof rules connect accepted choices to replay, prove FIFO eligibility
  of delivered signals, and link the actual imported server/client handlers to
  exact reference/payload-preserving send and return prefixes. Generic pure-segment
  boundary lemmas hide intermediate Core frames without assuming protocol safety.
  The complete closed-exchange phase simulation is now proved over the actual
  imported module and system transition, not a separate macro-model.
- Machine regressions check multiple values, invalid arities/scope, guard fallback,
  unsupported faults, fuel resumption, and bounded stack use for tail calls.
- Scope and pattern checks cover integers, atoms, lists, tuples, alias bindings,
  and bitstring literals. `Module.check` establishes lexical/signature checks,
  not complete Core arity validation or guard-grammar validity.
- Machine support includes multi-values, binding, sequencing, construction,
  named calls, cases/guards, selected integer BIFs, and `match_fail/1`. Exceptions
  expose class/reason only; handlers are implemented but stack inspection is not.
- Unknown BIFs, unlinked dependencies, and other unsupported operations report
  model faults. Generated `module_info` calls remain visible obligations.
- Actor cursor bounds and pending-signal identifier bounds are proved for every
  accepted system transition and finite replay from the initial system, including
  lifecycle requests and signal handlers. The next signal identifier is fresh
  relative to the pending queue. Both modules passed the resource-bounded serial
  build; these facts do not establish protocol correctness or OTP equivalence.
- Exact runtime-boundary states and receive-loop equalities for the imported
  request/reply client and server are kernel checked for every public payload.
  Boundary searches have explicit failure, with no fallback state. Staged
  normal-form equalities avoid repeatedly expanding earlier execution segments;
  their build passed in 20 seconds under the existing 2 GiB compiler cap.
- `exchange_allSchedules` proves the complete closed-exchange invariant after
  every finite accepted schedule from `actor_protocol:exchange/1`, for every
  public modeled payload. The invariant tracks both processes' real Core
  continuations, selected mailbox messages, allowed network payloads, and
  allocation counters. It includes pure steps, runtime requests, ordinary
  delivery, normal termination, and arbitrary increasing logical-time choices.
- `exchange_reply_correct` proves that a finished root has returned exactly
  `{ok, Payload}` with the original payload. `exchange_pendingRepliesAuthentic`
  proves every pending signal to the root is an ordinary reply with the expected
  reference and payload. These are conditional safety properties, not eventual
  termination, message-count uniqueness, or open-environment authentication.
- M0 through M3 acceptance criteria are met for the explicitly restricted
  profiles above. There is no claim of full OTP compatibility, compiler
  correctness, general module verification, or liveness. The endpoint search's
  128-step bound is a local proof-construction bound, not a bound on the schedules
  quantified by the protocol theorem. Final full-suite revalidation passed.

### Next work beyond the initial milestones

1. The requested universal Dijkstra implementation proof is complete for its
   natural-number vertex/weight API. Further graph-algorithm work should choose
   explicit requirements such as generic vertex encodings, path reconstruction,
   heap-based queues, or a different algorithm for negative weights. These are
   future extensions, not hidden assumptions in the completed theorem.
2. Generalize tail-delegation rules to arbitrary continuations when that client
   requires them; retain world compatibility obligations explicitly.
3. Extend protocol proofs to multiple outstanding requests and open environments
   with explicit rely/guarantee assumptions. The current theorem starts with the
   specified closed initial system and does not assume hostile message injection.
4. If eventual-reply or timeout progress is required, formalize the execution and
   fairness assumptions in Section 8 before proving it. No liveness theorem
   follows merely from the debugging scheduler or differential corpus.

### Commit checkpoints

- `a9c21be`: design, repository instructions, and buildable Lean bootstrap; pushed
  to `origin/main`.
- `78c590a`: three source exporters, OTP import, first local machine, CLI,
  generic runner proofs, and the imported Erlang identity contract; pushed.
- `64a7760`: three-language contracts, 40 differential cases, canonical bitstring
  literals, alias patterns, and resource-bounded serial verification; pushed.
- `cbbab32`: imported arbitrary-list reversal and reusable finite-prefix composition
  rules; full bounded suite passed and commit was pushed.
- `1f1d2cf`: finite closures, recursive groups, code references, environment lemmas,
  and 50 differential cases; full bounded suite passed and commit was pushed.
- `b659a78`: higher-order map, exception observation boundaries, linked dependency
  reuse, and 71 differential cases; full suite passed and commit was pushed.
- `b55fddc`: imported byte-codec contracts and explicit actor runtime,
  including lifecycle signals, 91 sequential cases and 17 actor scenarios. The
  complete bounded suite passed and the commit was pushed.
- `05ca217`: full local lexical preservation, reachable variable safety, and
  imported protocol-handler/pure-segment proof rules; complete suite passed and pushed.
- `b053016`: arbitrary-schedule actor cursor and signal bounds, plus exact
  imported protocol boundary/loop equations. The full serialized suite and kernel
  axiom audit passed; pushed to `origin/main`.
- `7820028`: imported client/server runtime preservation, all accepted
  schedule induction, exact root result, and pending-reply authenticity. The
  complete serialized suite passed under the same 2 GiB limit: 91 sequential
  differential cases, 17 actor scenarios, replay, importer/rejection and
  artifact-correspondence checks. The final theorem audit uses only `propext`,
  `Classical.choice`, and `Quot.sound`, with no `sorryAx` or native execution
  oracle; pushed to `origin/main`.
- `99a492c`: real Dijkstra source and reproducible Core artifact,
  integer-order extension, universally correct mathematical model, and generic
  Core helper refinements. Dependency-ordered builds, the machine regression
  checks, model/helper axiom audit, and 17 graph plus 11 invalid-input differential
  checks passed; pushed. The final universal Core entry contract was still pending
  at that checkpoint.
- `0b48115`: arbitrary-input Core edge expansion and source validation,
  search-loop refinement, and the universal `dijkstra_total_correct` contract.
  All proof modules passed kernel checking without increasing the 2 GiB memory
  cap. The complete suite passed: 91 existing sequential differential cases,
  17 actor scenarios, 17 Dijkstra graphs, 11 invalid Dijkstra inputs, importer
  rejection checks, recording/replay, and source/artifact correspondence.
  The final implementation theorem depends only on `propext`, `Classical.choice`,
  and `Quot.sound`; there are no custom axioms, `sorryAx`, or native execution
  oracles; pushed to `origin/main`.
- `afd188b`: English README usage tutorial with executed CLI examples,
  fresh import/emission, and a kernel-checked arbitrary-graph proof snippet.
  Pushed to `origin/main`.
- `81e77c3`: generic README workflow using an identity contract, with
  specialized examples reduced to links. The replacement proof snippet, axiom
  audit, local links, and whitespace checks passed; no full-suite rerun was
  needed for this documentation-only revision; pushed to `origin/main`.
- `db1633a`: move 31 example modules into topic directories and update
  all source imports, artifact check paths, and documentation. Preserve theorem
  declaration names and generated artifact contents.
- `f22f33f`: GitHub Actions configuration for cold kernel checking,
  complete compatibility tests, and retained-artifact reproducibility.
- `d59ad64`: deterministic, checkout-independent language extraction
  with a relocation regression and refreshed provenance. Workflow lint and the
  complete local suite and hosted CI run 34332011416 passed.
- Current checkpoint: record successful cold hosted verification. No workflow,
  source, artifact, or proof changes beyond the validated `d59ad64` checkpoint.

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

### Safety and progress assumptions for the closed exchange

The first protocol target is the actual imported `actor_protocol:exchange/1`
entry point in a closed world containing that module. Its initial system has one
root process, empty mailboxes and signal queues, no links or monitors, and the
specified fresh-identity counters. The payload must satisfy the model's public
value predicate; opaque exception information is not an admissible payload.
Safety is quantified over every finite accepted schedule, including arbitrary
interleavings of pure steps, runtime requests, eligible deliveries, and logical
time advances. It does not assume fairness and does not promise termination.

A future eventual-reply theorem additionally needs an infinite, non-stuttering
execution (or an appropriate maximal-execution definition), fair scheduling of
continuously enabled process steps, and eventual delivery of each persistently
eligible signal to a live endpoint. The closed environment must not add external
messages, terminate endpoints, replace code, or exhaust resources. Infinite
logical-time-only steps cannot substitute for process or delivery fairness.
The exchange uses an infinite receive timeout, so its progress claim would not
need clock divergence. A finite-timeout progress theorem would also need
unbounded logical time and fair execution of enabled timeout transitions; neither
would establish a wall-clock deadline on OTP. No liveness theorem is currently
provided, and the bounded debugging scheduler proves none of these assumptions.

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
  Examples/       -- Verified imported modules, grouped by topic
    Identity/     -- Erlang, Elixir, and Gleam identity contracts
    Sequential/   -- Recursive list-processing examples
    HigherOrder/  -- Higher-order function contracts
    Modular/      -- Cross-module contract reuse
    ByteCodec/    -- Byte codec and observable contracts
    Protocol/     -- Actor protocol execution and safety proofs
    Dijkstra/     -- Graph model, refinement, and correctness
tools/            -- OTP and source-language extraction adapters
tests/            -- Compatibility fixtures and differential harness
docs/             -- Design and supported-profile documentation
```

Keep IO and tool invocation outside the semantic definitions. Executable drivers
may use Lean IO; the transition functions and proof interfaces remain pure.

The example topic directories above are implemented. Keep generated `Imported`
modules beside the proofs that use them; name handwritten modules by role, such
as `Contract`, `Model`, or `Correctness`. The identity imports distinguish their
source languages. Add new examples in a topic directory, not directly under
`Erlean/Examples/`. Module paths follow the layout; existing declaration names
remain stable independently of these paths.

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

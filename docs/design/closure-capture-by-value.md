# Closures capture by value

Updated: 2026-11-03.

solcore-rs issue #120 compared Rust and Lean on two closure programs. The
maintainers decided that captured variables are passed by value, and Lean
follows Rust. This note records the probe of the pinned Rust paths, the Lean
probe, the design chosen for the source semantics and the source-to-Core
lowering, and the alternatives.

## The rule

A closure captures the values its captured variables have when the closure is
created:

1. a later assignment in the enclosing scope does not reach the closure;
2. an assignment inside the body does not reach the enclosing scope;
3. each call starts again from the creation-time values, so an assignment
   inside the body does not carry over to the next call of the same closure;
4. a closure that captures another closure captures that closure value, which
   keeps its own creation-time values.

Rust passes captured values as ordinary runtime arguments of the lifted
lambda (the module comment of `crates/specialize/src/evaluate/closures.rs` in
upstream main), which gives rule 3.

## Probe of the pinned Rust paths

A probe compiled hand-written contracts through checked Hull export, Sonatina
O0 and O2 and Yul (`export-rust-yul.py` with solc 0.8.35), ran them on Anvil
and in the Lean Hull runner (`rust-hull-scenario`), at twelve inputs each,
against a Python model of rule 1 to 4. `x0` below is the input's low byte.

| Program | Model | O0 | O2 | Yul | Hull runner |
| --- | --- | --- | --- | --- | --- |
| #120's first program, `x = 99` after the capture | `x0 + 42` | match | match | match | match |
| #120's second program, `x = 42` in the body | `42 + x0 + 41` | match | match | match | match |
| two calls of `lam () { x = x + 1; return x; }`, `a * 10 + b + x * 100` | `11 (x0 + 1) + 100 x0` (11 at `x0 = 0`) | match | match | match | match |
| a closure calling a mutating closure twice, then `x = 7` | rule 4 | match | match | match | match |
| a closure created in a loop body, writing a loop-carried local | rules 1–3 | match | match | match | match |
| a counter returned by a function, called twice | `seed + 2`, then `seed + 3` | match | match | match | match |
| an uninitialized local captured, assigned later, read in the body | `0` | match | match | match | match |
| an uninitialized local captured and assigned in the body before a read | rules 1–3 | match | match | match | match |
| an uninitialized local captured but never read | rules 1–3 | match | match | match | match |

At `x0 = 0` the repeated-call program gives 11. A closure with private state
across calls would give 12, and shared cells 212. All Rust paths agree, so
these results are the specification.

- Rust reads an uninitialized local as zero, also through a capture. Lean
  faults on every read of an uninitialized local (`uninitializedLocal`); this
  is an existing difference that does not depend on captures, and capture by
  value keeps it. Lean keeps this fault by decision rather than defining a
  zero value for every type. Lean and Rust therefore disagree on any program
  that reads a local before assigning it, directly or through a capture, and
  such a program is not a comparison case.
- Rust rejects a polymorphic local lambda used at two types (`SC0201`), so
  Lean's generalized local closures have no Rust counterpart. They follow the
  same rule.

Lean's source-to-Core API gave 101, 84 and 212 on the first three programs
before this change, from shared cells. On solcore-rs #123,
`let x: Word = 1; if (true) { let x: Word = 2; } return x;` already gives 1
in Lean, also when the inner `x` is then assigned, so #123 needs no Lean
change.

The upstream fixture `control-flow-capture-identity`, unchanged except for its
pragma between the pin and upstream main, encodes the same rule:
`branch(true, 3)` gives `3 + 10 = 13`.

## Candidates

**A. Snapshot cells.** The lambda rule copies the captured cells into fresh
closure-private cells and the closure keeps their locations. Each application
copies those cells again into fresh cells before binding the parameters.
Nothing writes a snapshot cell after the lambda rule, because the body only
sees the per-call copies.

**B. Carried values.** The closure keeps the captured cells' contents, and
each application allocates fresh cells for them, as for parameters.

B keeps the lambda rule free of heap effects, but the closure then contains
values, so `Value`, `Closure`, `Cell` and `GeneralizedClosure` become one
nested inductive. Closure typing would type captured values recursively, and
every source-to-Core value relation (`Represents` and its variants) would
relate captured values to Core values recursively instead of relating
locations through the location map. In Core, B loads the captured cells at
creation and allocates cells per call; the closure keeps plain values.

A keeps `Value` and closures unchanged: a closure still holds an
`Environment` of locations, and every location-based relation (`Captures`,
`EnvRepresents`, the location map, the allocation ledger) still applies, now
to snapshot cells. What changes is the lambda rule, which now allocates, and
the application rules, which copy before binding parameters. In Core, A
allocates the snapshot cells at creation and the copies at each call.

A is chosen. Its changes are local to closure formation and closure
application, on both sides and in lockstep, while B changes the carrier of
every source value.

## Which bindings are copied

Both sides decide with one function of the closure's source,
`SourceSemantics.CaptureBinders.copiedBinder? source id`
(`Solcore/SourceSemantics/CaptureBinders.lean`): a binding is copied when its
identifier has exactly one declaration among the source's inputs, lambda
parameters and `let`, `for` and `match` binders, and that declaration is
monomorphic. Every other binding is shared:

- a generalized local has a polymorphic declaration, and its cell holds an
  immutable principal (no rule writes such a cell: place resolution's
  `RootInitialValue` and the empty-mapping read both require an ordinary
  cell), so sharing it is the same as copying it;
- a hidden match scrutinee slot has no declaration; it exists only in Core and
  the source environment has no binding for it.

Because the source semantics and the lowering use the same function of the same
source, no invariant relating a scope to its environment is needed: a source
binding and its Core slot are copied together or shared together. A compiler
view of the source (`LambdaMetadataViews.MetadataView`) declares the same
binders, so it makes the same decision.

## Source semantics

`Dynamic/Heap.lean` gains:

- `Heap.AllocatesCopy`, which appends an exact copy of a cell;
- `EnvironmentCopies source environment before copies after`, which walks the
  environment from its most recent binding. A binding that `copiedBinder?`
  selects gets a fresh cell holding an exact copy of its cell, and `copies`
  binds the same identifier to it; any other binding keeps its location.

`Dynamic/Evaluation.lean` and `Dynamic/Fault.lean`:

- `ExpressionFormEvaluates.lambda` takes `EnvironmentCopies source environment
  before captured after`, stores `captured`, and ends in `after`.
- `CallableApplies.closure` and `closureUnit` take `EnvironmentCopies
  function.source function.captured before entry copied` and allocate the
  parameters on top of `entry` from `copied`. `CallableFaults.closureBody` and
  `closureControlEscape` do the same.
- `StatementExecutes.letInitializedGeneralized` and
  `ForItemExecutes.letInitializedGeneralized` copy the environment first; the
  principal captures the copies, and every materialized instance shares them.

A copy of an uninitialized cell is uninitialized: the capture itself never
faults, a read in the body faults as any read of an uninitialized local does,
and an assignment in the body initializes only that call's copy. A copied
closure value keeps its own snapshot locations, and nothing writes them, so a
closure that captures another closure needs no deeper copy. Retained closures
in public sessions, session snapshots and checkpoints hold the snapshot cells
like any other cells. Copying a cell exactly keeps the heap typing and the
lexical agreement of the copies without any further fact about the closure's
context.

## Lowering

The Core lowering mirrors the source rules allocation by allocation.

- Copies are marked source allocations made through the profile's allocator
  (`SourceCoreSourceCells`), so the allocation ledger knows them. A copy loads
  the slot's optional payload and allocates an uninitialized or an initialized
  marked cell in the two branches of a `caseE`; its marker captures the
  scope's original slots, and its frame-reference index follows the
  convention of named inputs (`copyReferences`). Without an allocator, the copy
  is a plain `newCell` of the loaded payload.
- At creation, the lowered lambda is preceded by one copy for each copied
  scope slot, and the lambda expression is renamed so that those slots refer
  to the copies. The closure's environment, the lambda manifest's captures and
  the indexed frame snapshot therefore hold the snapshot cells.
- At each call, the raw lambda body copies the captured slots after the
  manifest and before parameter binding, and the body is renamed so that
  scope slots refer to these copies.
- A generalized declaration copies the scope around its bundle and its binder
  allocation, so the bundle's instance closures and the binder's marker
  capture the snapshot cells, which is what the ledger restores the principal
  from. Instances of a generalized local take no snapshot of their own
  (`Policy.snapshotLambda` is false for the initializer).

This changes neither Core's syntax nor its semantics, the Hull importer or the
shared contract runtime.

A prototype that copied with plain unmarked cells gave 42, 83 and 11 through
the public API and ran the public execution test up to its first shared-capture
expectation, but `Session.snapshot` then failed with the ledger's
`unknownCaptureLocation`: every capture in a marker must be a marked cell.
Copies are therefore marked allocations.

## Proofs and tests

Theorem statements that mention the lambda rule's unchanged heap, or a closure
whose captured environment is its creation environment, change to the snapshot
environment and the extended heaps; other statements stay unchanged.

- `CaptureCopies.copies_prefix` (plain copies) and
  `CaptureCopies.marked_copies_prefix` (marked copies through the indexed
  allocator) relate the copies of a represented scope to the source copies:
  the heap relation extends, the scope's canonical slots point at the copies,
  slots past the scope keep their values, the frame cell is only read, and the
  copies agree with their continuation in both directions, with sizes.
- `DataHeap.EnvRepresentsIn.internal` describes an internal slot by its typed
  Core cell. A Core copy of an internal slot, which can occur only when a
  hidden identifier also has a declaration, is then still an internal slot.
- Formation: `CallableIndexedLambdaValues.formation` gives a `Formed` record
  (the source copies, the closure's capture layout over them, the extended heap
  relation and the Core evaluation); the families build their closure
  relations from it. The non-indexed families (`FunctionValues`,
  `ContractedFunctionValues`) state formation over the creation environment.
- A formed closure lives in the formed state, so formation lemmas conclude
  `∃ formed`, members and associations are stated for `formed.closure` at
  `formed.finalMap` and `formed.finalWorld`, and a caller's protocol state is
  carried to the formed state by its administrative transport (for example
  `formedState` in the selected-call modules). A consumer that needs a record
  takes one as an argument or obtains one from an existence lemma such as
  `CallableIndexedOwnedLambdaFormationReceipts.formation_exists`; premises that
  used to name the formed closure now quantify over every formed record. A
  compiler-qualification premise stated for the creation code now holds for
  the code recaptured at any environment (`qualified`), and the source
  liftings of generalized declarations take the protocol's `Bindings` to
  rebind the copied scope.
- Calls: the indexed parameter entry (`CallableIndexedLambdaViewPrefix.Entry`
  and its siblings) copies the captured cells and then binds the parameters,
  recording the copy for the source call. The entry's canonical environment is
  the parameters followed by the copied slots, which agree with the closure's
  canonical environment past the scope. Protected-state protocols cross the
  copies by administrative transport and are rebound to the copied slots
  (`ProtectedStateTransition.Rebinds`).
- Generalized `let`: `CellAwareGeneralizedSnapshotCode` gives the lowered
  snapshot around the bundle and its binder allocation, and
  `CellAwareNamedGeneralizedPrefix.complete` follows it over the source copies.
  The protocol state is rebound over the whole copied scope by
  `ProtectedStateTransition.Bindings.rebind`, using the protocol's
  administrative transitions (`ProtectedStateRebinding`).

The runtime tests expect the by-value results, including #120's programs, the
repeated call, a loop-carried capture and the adapted
`control-flow-capture-identity` fixture. The 109 runtime tests written for
shared cells now expect the by-value results:

- a retained closure that assigns a captured local returns the same value at
  every call (the projected bit-not factory returns the complement twice
  instead of restoring the entry), and closures created together or by
  different calls no longer share a capture cell;
- a closure that reaches itself through a local assigned after its creation
  (`let f: F; f = lam(…) { … f(…) … };`) copies that local while it is still
  uninitialized, so the recursive call faults with `uninitializedLocal`;
- tests that observed evaluation order only through a closure assigning a
  captured local keep their by-value results, and where an exact heap or a
  call copy still shows the order, they check that instead.

A copy is a marked allocation of three native store cells (the allocator's
entry, the marker and the payload) and a ledger row of the copied binder, so
every recorded native heap size grows by them at each closure creation and
each call, and reconstructed source heaps hold the snapshot and the per-call
copies before later cells.

Closures in Hull (`Solcore/Frontend/RustHull/`) are Rust's lifted lambdas and
are out of scope. The generated closure profiles already capture before the
outer assignments, and every path agrees on them.

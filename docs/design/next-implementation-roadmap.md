# Next implementation roadmap

Updated: 2026-11-21. Where the work stands, and the order of the next work, as the user approved
it from 2026-11-17 to 2026-11-21. solcore-rs is pinned at `d1b5ac28`.

## Status at a glance

Core typing is proved for admitted programs. Source-emitter preservation, native Source
whole-compiler preservation and the remaining Hull public connections are separate proof
obligations. None follows from agreement in a test corpus.

### Done

- **Three-way differential testing.** Generated programs run as the original Core program, as EVM
  bytecode from the pinned Rust compiler (Sonatina O0 or O2, or Yul through solc), and as the Rust
  compiler's Hull imported into Core. The default suite has 66 profiles, 34 pure and 32 stateful.
  Yul runs every pure profile and 30 stateful ones; `stateful-calls` and
  `stateful-forwarded-value` stay on Sonatina.
  [SEMANTIC_DIFFERENTIAL.md](../../scripts/SEMANTIC_DIFFERENTIAL.md) describes each profile.
- **Runners.** A saved case replays strictly, and a campaign reduces a failure and keeps its
  classification. The suite runs fixed corpora and recorded random seeds under shared time and disk
  limits. The fuzz driver repeats random suites with advancing seeds. It counts findings by
  signature, so recorded upstream findings with stable signatures and recorded mismatch classes
  count as known.
- **Pinned fixtures.** All 184 end-to-end fixtures of solcore-rs at `d1b5ac28` compile on Hull, O0,
  O2 and Yul, and their recorded steps agree on every path. Mutants of their derived ADT arguments,
  call sequences and sources run too. The fixtures have no original Core, so only the compiled
  paths are compared. The comparison runs only locally, standalone or as the fuzz driver's opt-in
  run kind.
- **Runtime operations.** The fourteen raw `std.opcodes` operations of the
  [mapping table](../../scripts/SEMANTIC_DIFFERENTIAL.md#runtime-operation-mappings) render in
  the generated sources.
- **Generated grammar.** Call graphs, bounded loops and recursion, loop closures, recursive loops,
  aggregates, generics, inline Yul with loops and memory, enums, traits and trait hierarchies,
  memory values and calls, revert data, halts, checked arithmetic, shifts, memory arrays and their
  ABI, and closure captures and factories. G0 revision four is the random default for the
  seventeen G0-based pure profiles.
- **State and ABI.** The stateful profiles cover storage and loops over it, logs, call value,
  dynamic ABI values, mappings, malformed calldata, several methods, returned values, constructor
  arguments, and return data across calls. All of them compare the contracts' whole committed
  storage on all three paths.
- **Source emitter proofs** for fifteen emitters
  ([source emitter meaning](scalar-emitter-meaning.md)).
- **The re-pins to `e2eef194`** (`4da119798`) **and `d1b5ac28`** (row 8). Neither found a new
  upstream defect.
- **Upstream rows 1 to 7** in Lean, row 4 for memory arrays in functions: see
  [the upstream table](#following-upstreams-semantics-the-next-units).
- **Closures capture by value** (solcore-rs #120), in Lean and in the closure capture and closure
  factory profiles ([source semantics](../guide/source-semantics.md#closures-capture-by-value)).

### In progress

- **Native Source goal two**: complete accepted-body preservation, with every actual pass
  connected to the public session
  ([Core runtime unification](core-runtime-unification.md#remaining-work-for-the-second-goal)).
  - Done: statement closure over the actual compiler tree; a first expression subset and
    statement shape for named rows, connected to the unchanged public root; one concrete instance
    (`AcceptedTick` in `Generalized/Export`); direct calls and the builtin conversions at any
    expression position, closed by one size induction over a family of rows; call authority from
    a complete inventory; and the public root in both directions for call-containing rows
    (`CellAwarePublicAcceptedCallRoot`), with their original traces lifted and instances at a
    call, a nested call, a conversion and `Typedef.rep` of a conversion (`Accepted/OneCall`).
  - Remaining: the remaining expression and statement forms, fault lifting, a richer instance
    and chained public calls.
- **Hull public connections** ([Hull meaning preservation](hull-meaning-preservation.md)).
  - Connected: recursive functions, loops, language faults, memory, storage, logs, return data, all
    four message-call modes, root reentry and account destruction; the identity, SHA-256 and
    RIPEMD-160 precompiles; refused CREATE and CREATE2 attempts and admitted ones without an init
    frame, with the init-template catalog premise of the public theorems; Hull's explicit revert;
    and inline Yul statement lists with `let`, assignment, nested blocks, `if`, `switch`, the
    memory and termination builtins and `add`, `sub`, `lt`, `gt`, `eq` and `iszero`.
  - Remaining: further state operations, ECRECOVER and P256VERIFY, init frames and public
    deployment, the rest of inline Yul, object linking, and then divergence and reverse
    correspondence.
- **Upstream row 13**: Lean follows upstream's superclass obligations
  ([the upstream table](#following-upstreams-semantics-the-next-units)).
- **Lean's native frontend as a fourth path**: the harness and the fuzz driver's `native` run kind
  compare the admitted pure cases with direct Core, memory arrays with their slices and memrefs
  among them. Native `std.opcodes` is next.

### Open

- **Emitter proofs** for the other emitters. The unproved ones that render with `AggregateRenderer`
  are the closure, comptime, module, storage mapping, sender-keyed ledger, dynamic array, dynamic
  bytes, long bytes, call value, contract call and forwarded value emitters.
- **The fixed suite's budget.** At fifty-five profiles the default fixed suite ran locally within
  its documented 7,200 seconds and 1 GiB on Sonatina O0, and its twenty-six pure profiles on Yul.
  With the profiles added since, the O0 fixed suite would now take more than its 7,200 seconds.
  Splitting the fixed CI job by `--profile`, already open, would keep each job within it.
- **Not built** in the generators: `bytes` returns beyond 64 bytes; returned enums, enum arguments,
  enum arrays, array returns, constructor arguments, call returns, call sequences and call branches
  beyond the recorded shapes; and other dynamic return values.

### Known upstream findings

The ignored `questions.md` records the evidence for each:

- Q013's `usize` overflow at O2 and in inline Yul on O0, O2 and Yul, and its `sar` wrong code at O2;
- the O2 `signextend` overflow on `stateful-adt-storage`;
- solc's `StackTooDeepError` on the exported Yul of specialized trait methods;
- `SC0401` through two superclass bounds;
- std's mapping slot order;
- Hull memory's range on a store at `2^256 - 1` that solc removes;
- Sonatina's first allocation, at `0x200` on O0 and at `0x140` on O2;
- the frontend's `SC0299` on two near spellings of row 4's forms, `new uint256[](uint256(2))` and
  `Typedef.rep(s[0])` for a literal index of a slice or a calldata array;
- the frontend's `SC0422` on closure forms that the pin cannot lower: it lowers only closures that
  are statically one lambda.

The last two are recorded without investigation, and the generators avoid them.

## Priorities

### Now

1. **Upstream's new trait coherence rules** (row 13). The re-pin and rows 9 to 12 are done, and
   Lean's trait search takes a goal from a body's `where` predicates at any depth. Next, Lean
   uses no default once an ordinary impl's head matches the goal, which the rest of row 13
   builds on: a `where` predicate then gives its superclasses, and each impl proves its
   superclasses at its declaration (`SC0248`) instead of restating them. Lean keeps ignoring
   `#[derive]`. Then Lean follows upstream in three more places:
   - a match's exhaustiveness: today Lean counts constructors only for a scrutinee of a nominal
     type, so an exhaustive match over a pair needs a `_` arm;
   - a literal `lidx` index, which gets `uint256` as a read's index does;
   - the Patterson, coverage and closed-default conditions (`SC0213`, `SC0212`, `SC0219`), with
     upstream's two pragmas.
2. **Meaning proofs.** Row 1's leftovers: `<<=`, `>>=` and in-place `~` at the twelve types
   ([what remains](integer-types-unchecked-shifts.md#what-remains)). Then the rest of native
   Source goal two.
3. **Lean's native frontend as a fourth differential path.** The harness runs the admitted pure
   cases through the native pipeline, alone or as the fuzz driver's `native` run kind, memory
   arrays with their slices and memrefs among them. Lean's imports follow upstream's `SC0108`
   and `SC0110`, an unknown module is refused at the import, and of two imports that bind one
   name from one module the first is kept. Next is native `std.opcodes`. Then the remaining
   import differences follow upstream: `SC0117`, `SC0120` for unused names, `SC0121` and the
   export checks.

### Then

4. Row 4 in the meaning proofs: a unit that relates array objects to their Core cells
   ([decision 6](memory-arrays-slices.md#6-meaning-proofs)).
5. The remaining Hull public connections and emitter proofs.
6. Deferred type resolution at finalization. It would lift row 4's differences 14, 15, 18, 19 and
   22 to 24 and the open `Typedef` call. It is unscheduled.

### Later

7. The fuzzing leftovers.
8. Generic code over the twelve integer types, `where` with builtin `Int`, `comptime<T>` locals and
   contract storage at the twelve types.
9. Storage and calldata arrays, which first need native contract storage and a calldata ABI.

CI has no passing hosted run, and its automatic triggers are disabled: the
[workflow](../../.github/workflows/semantic.yml) runs only on manual dispatch.

## Following upstream's semantics: the next units

The re-pin keeps every comparison working. These rows bring to Lean's source language the features
that upstream added between the pins. A row needs work in some of these layers:

- the parser (`Solcore/Syntax`);
- typing (`Solcore/TypeSystem`, `Solcore/Frontend/SourceInference`);
- the source semantics (`Solcore/SourceSemantics`);
- the lowering to Core (`Solcore/Frontend/SourceCore*`);
- the Hull importer (`Solcore/Frontend/RustHull`);
- the generators (`Solcore/Synthesis`).

Core needs nothing in any row. Checks, panics and wrapping are ordinary Core over Words, row 4's
arrays are Core cells and ordered mappings, and the Hull importer's byte memory is ordinary Core
code.

| Row | Upstream change | Status | Fixtures |
| ---: | --- | --- | --- |
| 1 | Checked integer types and literal defaulting (#95): `uint8` to `uint256` and `int8` to `int256`, checked `+ - * / %` that panic with `0x11` or `0x12`, unary negation, range-checked literals, ABI validation of narrow integers, and an unconstrained literal defaulting to `uint256` instead of `word` | **Done.** The twelve types are builtins with comparisons, bitwise operators, checked and unchecked arithmetic, shifts and their compound forms, range-checked literals, the `uint256` default, the constructors from `word`, and `Typedef.abs` and `Typedef.rep` where the call's type is known. `<<=`, `>>=` and in-place `~` at the twelve types are compiled but outside the meaning proofs, and four differences from upstream remain ([integer note](integer-types-unchecked-shifts.md#semantics-in-lean), [differences](integer-types-unchecked-shifts.md#differences-from-upstream)). | `checked-arith`, `int-ops`, `issue92-checked-defaults`, `shift-operators`, `mini-erc20`, `deposit` |
| 2 | `unchecked` blocks (#119): `+ - * / %` inside a block resolve to `std.unchecked`'s wrapping instances, lexically | **Done** for `word` and the twelve types. `+ - * / %` and their compound forms wrap to the type's width, and `/ %` panic with `0x12` on a zero divisor ([unchecked blocks](integer-types-unchecked-shifts.md#unchecked-blocks-as-implemented)). | `unchecked-scope`, `shift-operators` |
| 3 | Shift operators (#129): `<<` and `>>` with `Shl`, `Shr` and `ShiftAmount`, arithmetic `>>` for signed types, no revert, amounts of at least the width giving 0 or -1 | **Done** for `word` and the twelve types: `<<`, `>>`, `<<=` and `>>=` by a `word` or unsigned amount ([shifts](integer-types-unchecked-shifts.md#shifts-as-implemented)). | `shift-operators` |
| 4 | Memory arrays, slices and panic codes (#145): `T[]`, `new T[](n)` zeroed, `a.length` and methods on any receiver, `a[i]` through a checked `memref`, read-only slices `a[s:e]`, memory arrays in the public ABI, `Panic(0x32)` for indices and slice bounds, `Panic(0x31)` for an empty pop, `Panic(0x41)` for allocation overflow | **Done for memory arrays in functions.** `T[]`, `new`, literals, reads, element writes and compound assignments, lengths, slices, `toArray(s)`, `memref<T>`, `lidx(a, i)`, `CanStore.load(r)` and `CanStore.store(r, v)` are typed, have their source semantics and compile through the compatible profile, outside the meaning proofs. A compound assignment evaluates its element place once, by the user's decision, where upstream evaluates it twice. Storage and calldata arrays and `T[]` in the ABI wait for native contract storage and a calldata ABI ([memory arrays note](memory-arrays-slices.md), [differences](memory-arrays-slices.md#differences-from-upstream-that-lean-would-keep)). | `array-syntax`, `mem-array`, `array-slice`, `calldata-slice`, `memory-array-abi`, `user-collection-index`, `memory-allocation-bounds`, `allocator-bounds`, `abi-sum-padding`, `array-ops` |
| 5 | `pragma solcore;` (#141): required first in every file, once, without arguments | **Done.** Every emitter prints the pragma. Lean's loader rejects a file without it, with it after another declaration, twice, or with arguments, as upstream's `SC0002` does; the parser reads it as an ordinary pragma. | every fixture |
| 6 | Compiler fixes #130 to #133: recursive layouts rejected with `SC0420`, canonical ABI outputs of memory dynamic arrays, frontend diagnostics before specialization, inline Yul calls to Hull functions qualified with `usr$` | **Done.** The recursive-layout gate and the records of the three fixtures that Q008 and Q010 admitted follow upstream, and the importer accepts a plain-name Hull call from inline Yul as upstream's checker resolves it (Q006). Lean's catalogs refuse a non-regular recursive layout at once, as upstream's Hull emitter does with `SC0420`, and a nominal instantiation of more than 4096 nodes, the default of upstream's `--pe-max-type-nodes`, which upstream applies only where it specializes. Lean keeps accepting and running the regular recursive layouts that upstream's backends refuse with `SC0420`, a limit of their lowering rather than of the language, and the mutually recursive data types that upstream's name resolution refuses for now (`SC0203`). | `storage-array`, `ufcs-array`, `module-local-function-evidence`, `storage-adt-recursive-ok`, `asm-substitution` |
| 7 | Closure factories (`bf7114a8`, `ad1f49cf`): captures resolved in the factory's own scope, a factory's runtime effects kept | **Done where the native pipeline runs the fixture.** Captures resolve in the factory's own scope, and a factory's body runs when it is called, as upstream now does; Lean's typing, source semantics and lowering needed no change. Calls that use contract storage or inline assembly wait for them ([closures](../guide/source-semantics.md#closures-capture-by-value)). | `closure-parameters` (36 → 49 calls) |
| — | `msgSender` (#142) and contract-declared struct state (#138) | **Nothing to do.** #142 uses std's existing `msgSender` in examples, and #138 changes only examples. | `msg-context` |
| 8 | Re-pin to `d1b5ac28` (#146, #155; #147 and #148 change only the playground) | **Done.** Upstream's Hull format and backends are unchanged, so the importer and the harness took only the new commit, and every existing expectation holds. | `abi-layout-through-reexport` (new), `superclass-default-through-subtrait` (new), `abi-raw-default-codec` (6 → 8 calls), `abi-word-custom-codec` |
| 9 | Impl method constraints (`81afb96b`, `SC0249`): each constraint of an impl method is one of its trait method's, its impl's conditions or its head's direct superclasses, and an entailed one is refused | **Done.** Lean accepts the omitted, reordered, repeated and restated constraints that its equality refused, and refuses an undeclared or entailed one, as upstream does. The method's body sees only its declared constraints. | uitest `impl_method_extra_constraint` |
| 10 | No default for a type-parameter goal (`1c7fe983`, `SC0207`) | **Done.** Lean's checker refuses a generic whose body needs a default for a goal on its type parameter, or on a product whose first component is one, called or not, and accepts the goal from a `where` predicate, as upstream does. Where Lean's search lacks upstream's superclass projection, it keeps the default it used before rather than refuse what upstream accepts. | uitest `default_not_used_for_type_parameter`, `default_not_used_for_tuple_of_type_parameter` |
| 11 | Overlapping unconditional defaults (`4f22ddb0`, `SC0247`) | **Done.** Lean refuses a default implementation whose subject unifies with an earlier default of the same trait when either has no `where` predicates, comparing only subjects, as upstream's `SC0247` does. Two conditional defaults, a default with an ordinary implementation, and defaults whose subjects don't unify stay accepted. | uitest `overlapping_unconditional_default` |
| 12 | The orphan rule (`02456cee`, `282cb2c8`, `SC0246`): an impl sits next to its trait or its type, std counting as one unit and a tuple as its first element | **Done.** Lean refuses an implementation that sits neither in its trait's module nor in the module of the type at its subject's head, a product counting as its first component, nor in a module that sees that module and is seen by it through imports and re-exports, as upstream's `SC0246` does. Two tests now implement the imported trait for the consumer's own type. Upstream's two `invokable` uitests have no Lean form. | uitest `orphan_*`; the six rewritten e2e fixtures |
| 13 | Superclass obligations (`6e3c4d3c`, `7bdd9a0a`, `SC0248`): each impl proves its superclasses at declaration, and a given entails its superclasses | **In progress.** Lean's trait search decides a goal equal to one of the body's `where` predicates by that given at any depth, before any impl, as upstream ranks its local givens. Lean still restates superclass predicates in each impl and never projects. Once its default tier follows upstream's, it will refuse an impl whose superclass has no impl, and accept the impls without the restatement and the projections that it refuses today. | `superclass-default-through-subtrait`; uitest `missing_superclass_instance`; the solver fixtures |
| — | Impls through re-exports (`9286baea`), std's generic impls (`ad8f003f`), `SC0416` (`86d7bc02`), derive checks (`ba16e8e5`) | **Nothing to do.** Lean's impls are visible everywhere, so neither re-export visibility nor a goal with two impls in different places arises. std's changes reach the importer through the Hull. Lean ignores `#[derive]`, so `SC0230`'s check waits for derive itself. | `abi-layout-through-reexport` |

The new `evm-word-boundaries` fixture checks the `word` operations at their extremes, which the
scalar meaning already covers.

## Handoff rules

- Follow the order above. Finish each operational connection before the next large expansion. An
  ambiguous comparison or a confirmed defect can justify a narrow proof or implementation fix
  sooner: record why, then return to the order.
- Keep existing profile behavior and saved-case semantics stable, or version a deliberate change
  explicitly.
- Use separate commits for a coherent operational change and for its validation.
- Keep `questions.md` ignored and uncommitted. Put confirmed regressions and public limitations in
  tracked tests and documentation.
- When a gate is actually complete, update its status here in a sentence or two. Commands, counts,
  seeds and timings stay out of this file.
- Delete disposable exports and validation caches once their evidence is saved.

Delivery records up to 2026-11-17 are in git history at `049f8ce1f`.

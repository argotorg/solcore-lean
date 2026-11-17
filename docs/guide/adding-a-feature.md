# Adding a language feature

This page walks through adding a feature to Lean's source language, from the design note to the
docs. It is for anyone who adds a construct or changes what one means. A feature crosses several
areas, and each area's page has the recipe for its part: [Syntax](syntax.md),
[Foundations](foundations.md), [Source semantics](source-semantics.md), [Frontend](frontend.md),
[Core](core.md), [Core lowering](core-lowering.md) and [Tests](tests.md).

- **Worked example:** the shift operators `<<`, `>>`, `<<=` and `>>=` on `word`.
- **Contrasts:** `unchecked` blocks, added by a pass around the parser, and closures that capture
  by value, a change of meaning without new syntax.

## Before code

**Follow upstream at the pin.** Lean follows the semantics of `argotorg/solcore-rs` at the revision
given in README and in [`scripts/SEMANTIC_DIFFERENTIAL.md`](../../scripts/SEMANTIC_DIFFERENTIAL.md).
Where Lean decides to differ, the design note says so, and the affected programs are not comparison
cases (see the [rules](differential-testing.md#rules)).

**Probe the pinned Rust paths.** For shifts and `unchecked` blocks (the integer note's
[probe](../design/integer-types-unchecked-shifts.md#probe-of-the-pinned-rust-paths)):
- hand-written contracts were compiled through checked Hull export
  ([`export-rust-hull.py`](../../scripts/export-rust-hull.py)), Sonatina O0 and O2, and Yul
  ([`export-rust-yul.py`](../../scripts/export-rust-yul.py) with solc), and run on Anvil and in the
  Lean Hull runner, against a model read from std, the compiler crates and upstream's fixtures;
- a compile probe recorded which sources the frontend accepts, and the code of each rejection.

When every path agrees with the model, the results are the specification and the tests' expected
values. The pinned checkouts live under `.upstream/`, which Git ignores; [Workflow](workflow.md)
says how to prepare them.

**Write the design note.** Commit the design before any code, with a roadmap entry, as the
[integer note](../design/integer-types-unchecked-shifts.md) was. Its main sections:

| Section | Contents |
| --- | --- |
| Lean today | How the frontend handles the construct before the change |
| Upstream's semantics | What std, the compiler and the fixtures define at the pin |
| Probe | The calls compared on each path, and the accepted and rejected sources |
| Design | One part per layer: Syntax, Typing, Source semantics, Lowering, Public API |
| Alternatives | Each rejected design, with the reason |
| Order and commits | One commit per feature, each with public-API tests whose expectations come from the probe and the fixtures |
| As implemented | Added with each feature: what was done, and where it departs from the design |

## The layers, with shifts

The shift commit left Core, ContractRuntime, the Hull importer, TypeSystem and Synthesis unchanged.
This is what it changed, in pipeline order; each layer's recipe is on its area's page.

| Layer | What shifts changed | Recipe |
| --- | --- | --- |
| Syntax | `shiftLeft` and `shiftRight` in `BinaryOp` and `ValueAssignOp`; a shift layer at precedence 7 (`* / %` 9, `+ -` 8) in the parser and the grammar, which decode through the same `BinaryOp.at?` and `ValueAssignOp.at?`. Tokens and the lexer did not change: `<<` is two adjacent `<` tokens, so `Box<Box<Word>>` still closes with two `>` tokens | [Syntax](syntax.md#an-operator-or-a-spelling-made-of-existing-tokens) |
| Typing | Nothing in TypeSystem. `inferBinaryOperator` types a shift (`isShiftOperator`) before any dispatch, and `inferBinaryOperator_shift_result` and `inferBinaryOperator_shift_projection` state that branch once, for every proof to use | [Frontend](frontend.md#a-new-construct-in-the-native-compiler) |
| Source semantics | `ShiftBinaryOperator` and `BinaryOperatorHasType.wordShift`; `BinaryPrimitiveApplies.wordShiftLeft` and `wordShiftRight`, defined by Core's `Word.shiftLeft` and `Word.shiftRight`; `IntegerStrictBinaryOperator`, the strict operators other than shifts; operand faults (`WordBinaryOperator`). No preservation statement changed | [Source semantics](source-semantics.md#add-a-primitive-operator) |
| Compilation | `SourceCorePrimitive.strictBinaryBody` lowers shifts to `wordShl` and `wordShr`, and `SourceCoreInteger.strictBinaryBody` has a placeholder, since typing never puts a shift at `integer`; `wordOnly?` and `wordOnlyCompound` lower a compound shift of a local; the data places map the compound shifts and refuse them at `integer` leaves; `directBinary` maps them too | [Frontend](frontend.md#a-new-construct-in-the-native-compiler) |
| Core | Nothing: `wordShl` and `wordShr` were already Core operations | [Core](core.md#add-an-operator) |
| Core lowering | A one-line case per shift in `PrimitiveExpressions.strict_binary_value`, since the semantics and Core apply the same `Word` function; the conjunct `operator.wordOnly = false` in the assignment profile | [Core lowering](core-lowering.md#making-changes) |
| Fragments | The historical strict-`word` evaluators leave shifts out; their soundness proofs gained the cases | [Frontend](frontend.md#fragments) |
| Public API | Nothing | [Frontend](frontend.md#a-new-public-entry-point) |

A new constructor reaches every match on its type, including the paths that must refuse it.

- **Core conventions.** Core's compound assignment, `Core.LocalAssignment.compound`, has no shift
  operator. Rather than extend it and its laws, `wordOnlyCompound` copies its shape in the
  frontend. The roadmap plans no Core change for the whole integer unit: checks, panics and
  wrapping are ordinary Core over words.
- **The public API** changes when callers see new values, errors or behaviour: `unchecked` blocks
  added the load error `ProgramLoadError.uncheckedBlock`, panics the diagnostic
  `RuntimeError.panic`, the conversions the diagnostic `RuntimeError.dirtyHigherBitsForInteger`
  with upstream's revert data `0x6cc54a63`, and the twelve integer types the error
  `nonCanonicalSourceValue`, which every public encoder raises for an argument that is not
  canonical for its type.
- **Tests.** `Tests.SourceCoreShiftExecution`, in `Foundations/Execution` and registered in
  [`Tests/Main.lean`](../../Tests/Main.lean), runs the probe's results and the rejected programs
  (`a < < b`, `a > >= b`, a shift of or by a `Bool`). The `example` in
  `Tests.SourceCorePrimitiveExpressions` runs every `StrictBinaryOperator` through the lowering
  theorem, so it covers shifts. No parser test was added: the public test checks precedence by its
  results and adjacency by `checkProgram`'s rejections.

## After the Lean side

**The differential-testing profile.** These profiles compare the Rust paths with a Core reference of
their own and do not go through Lean's source frontend, so they can land first, and for shifts they
did: `runtime-checked-arithmetic` and `runtime-shifts`, in
[`Synthesis/Internal/Integers.lean`](../../Solcore/Synthesis/Internal/Integers.lean).
[Synthesis](synthesis.md#add-a-profile) gives the steps, and
[Differential testing](differential-testing.md) the comparison model.

**Docs.** With the feature, update the design note's "as implemented" section (as in
[shifts as implemented](../design/integer-types-unchecked-shifts.md#shifts-as-implemented)), and in
the roadmap the row's status in the table "Following upstream's semantics: the next units" and the
unit's status paragraph. Update README when public behaviour changes: the closure work rewrote
README's account of closures, and shifts needed no README change. Update the guide pages and module
docs of what you touched ([Conventions](conventions.md#documentation)). When the unit is done, move
what stays true into this guide or the module docs, and delete the note.

## Two contrasts

| Layer | Shifts | `unchecked` blocks | Closures by value |
| --- | --- | --- | --- |
| Syntax | operators, a parser layer, grammar, parser proofs | a pass around the parser; parser, grammar and their proofs unchanged | nothing |
| Typing | a shift branch in inference | three operators, dispatched on declared types to `UncheckedAdd`, `UncheckedSub` and `UncheckedMul` | nothing |
| Source semantics | primitive, fault and typing rules | `wordUnchecked` typing and primitive rules | the lambda rule and closure calls copy captured cells |
| Lowering to Core | `wordShl` and `wordShr` | as the checked operators on `word` | marked copies at creation and at each call |
| CoreLowering | new cases, and a conjunct in the assignment profile | `wordOnly` replaces `isShift` | closure formation and call theorems restated over the copies |
| Tests | a new public test | a new public test | a new semantics test; runtime tests changed their expected results |

**`unchecked` blocks: a pass around the parser.** A statement form would have reached every proof
that matches statement forms exhaustively, inference's included, though no typed program keeps it;
operators are matched in far fewer places. So `Syntax/Unchecked` works around the parser, and from
there the operators cross the other layers as shifts did
([Syntax](syntax.md#a-form-that-a-pass-around-the-parser-can-handle)). In a block, `/ % /= %=`
panic with `0x12` on a zero divisor.

**Closures by value: a change of meaning.** Nothing changed in Syntax, TypeSystem,
`SourceInference` or Core; the semantics and the lowering changed in lockstep. A closure copies the
captured cells when it is created and again at each call. Carrying values in closures was rejected
because it would change the carrier of every source value. One function,
`CaptureBinders.copiedBinder?`, decides which bindings are copied, for both sides, so no invariant
has to relate a scope to its environment. [Source
semantics](source-semantics.md#closures-capture-by-value) states the rule, and
[Core lowering](core-lowering.md#closures-by-value) the lowering and its proofs.

## Checklist

- [ ] Probe the pinned Rust paths; record upstream's semantics and any deliberate difference.
- [ ] Before any code, commit a design note under `docs/design/` (a part per layer, the
  alternatives) and the roadmap entry.
- [ ] Syntax: operators or AST, parser and grammar, with soundness, totality and outcome proofs.
- [ ] Typing: inference and dispatch, their invariants, and soundness against the declarative rule.
- [ ] Source semantics: typing, evaluation and fault rules, and the preservation cases.
- [ ] Compilation: every lowering path that can meet the construct, including those that refuse it.
- [ ] Core: reuse existing operations and conventions where they compute what the semantics defines.
- [ ] CoreLowering: the new cases, with any changed profile passed through.
- [ ] Public-API tests with the probe's expected values, registered in `Tests/Main.lean`, and the
  checks in [Workflow](workflow.md#before-you-commit).
- [ ] A differential-testing profile, if none covers the construct.
- [ ] The note's "as implemented" section, the roadmap row, README if public behaviour changed, and
  the guide pages; when the unit is done, the guide takes what stays true and the note goes.

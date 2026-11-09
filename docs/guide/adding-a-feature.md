# Adding a language feature

This page walks through adding a feature to Lean's source language, from the design note to the
docs. It is for anyone who adds a construct or changes what one means. A feature crosses several
areas, each with its own page: [Syntax](syntax.md), [Foundations](foundations.md),
[Source semantics](source-semantics.md), [Frontend](frontend.md), [Core](core.md),
[Core lowering](core-lowering.md) and [Tests](tests.md).

- **Worked example:** the shift operators `<<`, `>>`, `<<=` and `>>=` on `word` (commit 5b8c6e96d).
- **Contrasts:** `unchecked` blocks (e8d28e957), added by a pass around the parser, and closures
  that capture by value (7ac75aea3), a change of meaning without new syntax.

These commits predate the layout refactor (f820cc25f) and name old modules. The paths below are
current; [Conventions](conventions.md#following-older-notes) explains how to map an old module.

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
values. The closure work probed the same paths. The pinned checkouts live under `.upstream/`, which
Git ignores; [Workflow](workflow.md) says how to prepare them.

**Write the design note.** The design was committed before any code, with a roadmap entry: fee885b47
added the [integer note](../design/integer-types-unchecked-shifts.md), and 43956742b the closure
note, removed once the work was done (Git history keeps it). The integer note's main sections:

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
Its changes fall into these layers, in pipeline order.

### Syntax

| File | What shifts added |
| --- | --- |
| [`Syntax/Operator.lean`](../../Solcore/Syntax/Operator.lean) | `shiftLeft` and `shiftRight` in `BinaryOp` and `ValueAssignOp`; the precedence ladder renumbered (`* / %` 9, `+ -` 8, shifts 7); `secondSymbol?` and `tokenCount`; the decoders `BinaryOp.at?` and `ValueAssignOp.at?`, with `at?_cases`, `at?_bound` and `tokenCount_pos` |
| [`Syntax/Parser/Terms.lean`](../../Solcore/Syntax/Parser/Terms.lean) | `binaryAtPrecedence?` and `valueAssignAt?` decode with `at?`; `consumeBinary` advances by `tokenCount`; `expressionLayer` gains a shift layer at 7 |
| [`Grammar/Expressions.lean`](../../Solcore/Syntax/Grammar/Expressions.lean), [`Grammar/Statements.lean`](../../Solcore/Syntax/Grammar/Statements.lean) | `BinaryOperatorAtPrecedenceParses`, `ValueAssignOperatorParses` and their `AbsentAt` forms decode with the same `at?`, with new `unique` and `not_absent` lemmas; `ExpressionLayerParses` and `ExpressionLayerRejects` gain the layer |

The tokens, the lexer and the node types of the AST (`Syntax/Term.lean`) did not change; only the
operator types they carry did. `<<` is two adjacent `<` tokens, so `Box<Box<Word>>` still closes
with two `>` tokens. A new token would change `Syntax/Token.lean` and the lexer, whose output
`Lexer/Contract` states and `Lexer/Properties` proves.

**Proofs that changed**, in `Syntax/Parser/Internal/` and `Syntax/Internal/`:
- Soundness got shorter. The parser and the grammar call one decoder, so
  `consumeBinary_success_sound_of_binaryAtPrecedence?_some` and `binaryAtPrecedence?_none_absentAt`
  (`OperatorSoundness`) reduce to it, and the per-token helper lemmas were deleted.
- An operator may span two tokens. The state-shape and validity lemmas (`ExpressionProofs`,
  `SimpleStatementSoundness`) advance the cursor by `tokenCount`, bound it with `at?_bound`, keep
  progress strict with `tokenCount_pos`, and validate a two-token span with
  `SourceSpan.cover_validFor`.
- Totality, trace and outcome proofs (`ExpressionTotality`, `PostfixTrace`, `TermTotality`,
  `ExpressionOutcomes`, `StatementOutcomes`) case on the decoder, use `unique` and `not_absent`,
  and follow the renumbered ladder. The new layer reuses the generic left-associative parser and
  its lemmas at precedence 7.

### Typing

Shifts needed nothing in TypeSystem, whose builtin types are `TypeSystem.BuiltinType`
([`TypeSystem/Type.lean`](../../Solcore/TypeSystem/Type.lean)). Inference types them:
- In [`SourceInference/Resolution.lean`](../../Solcore/Frontend/SourceInference/Resolution.lean),
  `inferBinaryOperator` types a shift (`isShiftOperator`) before any dispatch: the value and then
  the amount unify with `word`, and the result is `word`, with no requirements.
  `binaryOperatorDispatch` maps shifts to no trait method.
- In [`SourceInference/Expression.lean`](../../Solcore/Frontend/SourceInference/Expression.lean),
  `inferBinaryOperator_shift_result` and `inferBinaryOperator_shift_projection` state that branch
  once, for every proof to use.

**Proofs that changed:**
- Proofs that unfold `inferBinaryOperator` split on `isShiftOperator`, close the shift branch with
  these lemmas, rewrite with `if_neg` and go on as before. They are in
  `Frontend/SourceInference/Internal/ExpressionProperties.lean` and in `SourceSemantics/Internal/`
  (`Inference`, `Privacy`, `Formation`, `Selected`). Proofs that list compound operators gained
  two cases.
- In `SourceSemantics/Internal/Inference/Soundness.lean`, `inferBinaryOperator_success_case` types
  a shift by `BinaryOperatorHasType.wordShift`. The literal-only case
  `BinaryOperatorInferenceCase.literalFallback` gained a `not_shift` field for its staged `integer`
  typing, `binaryInteger_hasType`: shifts have no `integer` typing.

### Source semantics and preservation

| File | What shifts added |
| --- | --- |
| [`SourceSemantics/Expressions.lean`](../../Solcore/SourceSemantics/Expressions.lean) | `ShiftBinaryOperator`; the typing rule `BinaryOperatorHasType.wordShift`, with `word` operands and result and no requirements; the shifts in `WordCompoundAssignmentOperator` |
| [`Dynamic/Primitive.lean`](../../Solcore/SourceSemantics/Dynamic/Primitive.lean) | the shifts in `StrictBinaryOperator`; `BinaryPrimitiveApplies.wordShiftLeft` and `wordShiftRight`, defined by Core's `Word.shiftLeft` and `Word.shiftRight`; `IntegerStrictBinaryOperator`, the strict operators other than shifts |
| [`Dynamic/Evaluation.lean`](../../Solcore/SourceSemantics/Dynamic/Evaluation.lean) | `AssignmentValueApplies.shiftLeft` and `shiftRight` |
| [`Dynamic/Fault.lean`](../../Solcore/SourceSemantics/Dynamic/Fault.lean) | `WordPair`, `WordBinaryOperator` and `BinaryPrimitiveOperandsInvalid.word`: a shift of anything but two words is an operand fault |

**Proofs that changed.** No preservation statement changed. `PrimitiveBinaryHasType` gained a
`wordShift` constructor, and each `cases` over the operator typing gained a case: `sourceTyping`,
`preserves` and `wordCompoundPreserves` in `Dynamic/Preservation.lean`, and matches in
`Dynamic/WholeLanguagePreservation.lean`, the staging preservation files and
`Internal/Substitution/StructuralLaws.lean`.
[Source semantics](source-semantics.md#add-a-primitive-operator) lists every place.

### Compilation to Core

| File | What shifts added |
| --- | --- |
| [`Frontend/SourceCore/Lowering.lean`](../../Solcore/Frontend/SourceCore/Lowering.lean) | `SourceCorePrimitive.strictBinaryBody` lowers shifts to `wordShl` and `wordShr`; `SourceCoreInteger.strictBinaryBody` has a placeholder, since typing never puts a shift at `integer`; `SourceCoreAssignments.wordOnly?` and `wordOnlyCompound` lower a compound shift of a local |
| [`SourceCore/DataPlaces.lean`](../../Solcore/Frontend/SourceCore/DataPlaces.lean), [`SourceCore/Compatible.lean`](../../Solcore/Frontend/SourceCore/Compatible.lean) | `binaryOperator` maps the compound shifts to `wordShl` and `wordShr`; `lower` refuses them at `integer` leaves |
| [`Frontend/SourceCoreElaboration.lean`](../../Solcore/Frontend/SourceCoreElaboration.lean) | `directBinary` maps the shifts too |
| `Frontend/Fragments/Internal/` | The historical strict-`word` evaluators leave shifts out; their soundness proofs gained the cases |

A new constructor reaches every match on its type, including the paths that must refuse it.
(`wordOnly?` and `wordOnlyCompound` were `shift?` and `shiftCompound` until the unchecked commit.)

### Core conventions

Core did not change. `wordShl` and `wordShr` were already Core operations
([`Core/Syntax.lean`](../../Solcore/Core/Syntax.lean), evaluated by `Core.BinaryOp.apply` in
[`Core/Primitive.lean`](../../Solcore/Core/Primitive.lean)). Core's compound assignment,
`Core.LocalAssignment.compound` in [`Core/Conventions.lean`](../../Solcore/Core/Conventions.lean),
has no shift operator. Rather than extend it and its laws in `Core/Internal/ConventionLaws.lean`,
`wordOnlyCompound` copies its shape in the frontend. The roadmap plans no Core change for the whole
integer unit: checks, panics and wrapping are ordinary Core over words.

### The CoreLowering correspondence

In `SourceSemantics/CoreLowering/Internal/`, most changed files changed by a line or two. A
predicate that classifies operators (`IntegerStrictBinaryOperator`, or `ValueAssignOp.isShift`, now
`wordOnly`) carries each exclusion:
- **Expression primitives.** `PrimitiveExpressions.strict_binary_value`
  (`Foundations/PrimitiveExpressions.lean`) gained a one-line case per shift, because the semantics
  and Core apply the same `Word` function. The `integer` case of
  `CompatibleExpressionPrimitives.BinaryProfile` (`Compatible/ExpressionPrimitives.lean`) now
  takes `IntegerStrictBinaryOperator`, so the integer bodies never meet a shift.
- **Compound assignment.** The data-place theorems share an assignment profile, of the form
  `operator = .equal ∨ T = .word ∨ T = .integer` for the leaf type `T`. Its last disjunct gained
  `∧ operator.isShift = false`, now `operator.wordOnly = false`; proofs that destructure the
  profile pass the conjunct on. `DataPlaceModifier.integer_success` (`Data/PlaceReflection.lean`)
  takes the conjunct as a premise and refutes the shift cases, and `word_success` gained them. The
  receipts in [`AcceptedTrees.lean`](../../Solcore/SourceSemantics/CoreLowering/AcceptedTrees.lean)
  carry the profile in `operatorType`.

### The public API

The public API in [`Frontend/SourceCompiler.lean`](../../Solcore/Frontend/SourceCompiler.lean),
which re-exports `SourceCoreExecution`, did not change for shifts, nor did the checker
`checkProgram` ([`Frontend/ProgramChecking.lean`](../../Solcore/Frontend/ProgramChecking.lean)).
They change when callers see new values, errors or behaviour: `unchecked` blocks added the load
error `ProgramLoadError.uncheckedBlock`, panics the diagnostic `RuntimeError.panic`, and the twelve
integer types the error `nonCanonicalSourceValue`, which every public encoder raises for an argument
that is not canonical for its type.

### Tests

| Layer | Test |
| --- | --- |
| Whole pipeline | `Tests.SourceCoreShiftExecution` in [`Foundations/Execution.lean`](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean), registered in [`Tests/Main.lean`](../../Tests/Main.lean): the probe's results for `word` shifts, amounts at and past 256, a precedence ladder, compound shifts of a local and of a mapping element, a `Box<Box<Word>>` parameter, and rejected programs (`a < < b`, `a > >= b`, a shift of or by a `Bool`) |
| Lowering correspondence | The `example` in `Tests.SourceCorePrimitiveExpressions` ([`Foundations/Statements.lean`](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Statements.lean)) runs every `StrictBinaryOperator` through the compiler and `PrimitiveExpressions.lowerExpression_preserves`, so it covers shifts |
| Existing tests | Tests that list operators or use a changed signature were adjusted, such as `Tests.SourceCoreCompatibleAssignment.staged_modifier` |
| Parser | None added: the public test checks precedence by its results and adjacency by `checkProgram`'s rejections. Parser tests live in `Solcore/Test/Syntax/` |

## After the Lean side

**The differential-testing profile.** These profiles compare the Rust paths with a Core reference of
their own and do not go through Lean's source frontend, so they can land first, and for these rows
they did. acadc607a recorded their probe and definitions in the roadmap, 6b2f86b99 added the
`runtime-checked-arithmetic` and `runtime-shifts` profiles, and eab3114ec and 57b9c55c3 recorded
and documented the results. The profile commit has the parts a profile needs:

| Part | Where |
| --- | --- |
| Plans, Core reference, reductions, emitter and cases | [`Synthesis/Internal/Integers.lean`](../../Solcore/Synthesis/Internal/Integers.lean) |
| Case-tool commands (`shift-generate`, `shift-emit`, …) | [`Tests/SemanticCaseTool.lean`](../../Tests/SemanticCaseTool.lean) |
| Adapter, campaign and suite | `scripts/semantic-differential.py`, `semantic-campaign.py` and `semantic-suite.py`, with their `scripts/test-semantic-*.py` |
| Lean test with golden fixtures | `Tests.SourceIntegerCases` in [`Test/Synthesis/Scalars.lean`](../../Solcore/Test/Synthesis/Scalars.lean) |
| Fixed corpus and its validator | `scripts/semantic-shift-corpus.json` and `Tests/scripts/test-semantic-shift-corpus.py` |

[Synthesis](synthesis.md#add-a-profile) gives the steps, and
[Differential testing](differential-testing.md) the comparison model.

**Docs.** With the feature, update the design note's "as implemented" section (as in
[shifts as implemented](../design/integer-types-unchecked-shifts.md#shifts-as-implemented)), and in
the roadmap the row's status in the table "Following upstream's semantics: the next units" and the
unit's status paragraph. Update README when public behaviour changes: the closure commit rewrote
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
operators are matched in far fewer places. So
[`Syntax/Unchecked.lean`](../../Solcore/Syntax/Unchecked.lean) works around the parser:
- `prepare` finds each `unchecked` at a statement start followed by `{` and blanks the keyword's
  bytes. The parser reads a plain block, and every span stays the same.
- `mark` then turns `+ - * / %` and `+= -= *= /= %=` in each recorded block into unchecked
  operators, which only this pass produces. Lambda bodies start outside any block. From there the
  operators cross the other layers as shifts did. `/ % /= %=` were a load error until panics
  (9597a7771); now they panic with `0x12` on a zero divisor.
- `parseWorkspaceFile` in
  [`Frontend/ProgramInterfaces.lean`](../../Solcore/Frontend/ProgramInterfaces.lean) runs both
  steps. A nested block is a load error (`Syntax.Unchecked.Error`).

**Closures by value: a change of meaning.** Nothing changed in Syntax, TypeSystem, `SourceInference`
or Core; the semantics and the lowering changed in lockstep. [Source
semantics](source-semantics.md#closures-capture-by-value) states the rule.
- A closure copies the captured cells when it is created and again at each call. Carrying values in
  closures was rejected because it would change the carrier of every source value.
- One function, `CaptureBinders.copiedBinder?`
  ([`SourceSemantics/CaptureBinders.lean`](../../Solcore/SourceSemantics/CaptureBinders.lean)),
  decides which bindings are copied. `Dynamic.EnvironmentCopies` (`Dynamic/Heap.lean`) and
  `SourceCoreSourceCells` (`Frontend/SourceCore/Lowering.lean`) both use it, so no invariant has to
  relate a scope to its environment.
- `ExpressionFormEvaluates.lambda`, `CallableApplies.closure` and `closureUnit`,
  `CallableFaults.closureBody` and `closureControlEscape`, and the generalized `let` rules take an
  `EnvironmentCopies` premise. The Core copies are marked allocations: the allocation ledger
  rejects a capture cell it does not record (`unknownCaptureLocation`).
- Theorems about closure formation and calls were restated over the copies, through
  `CaptureCopies.copies_prefix`, `CaptureCopies.marked_copies_prefix` and
  `CallableIndexedLambdaValues.formation`. Runtime tests written for shared cells now expect
  by-value results; `Tests.SourceCoreExecution` runs the programs of solcore-rs #120.

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

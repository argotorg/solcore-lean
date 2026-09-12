# ADR-0296: original closed unary primitive evaluation

## Status

Accepted for bounded prototype implementation after independent design review.
Implementation, consumer review and kernel verification remain required.
Baseline is completed ADR-0295 at
`80ad278d16fd882bcd35903547800a0ca7e5d8f8`; its complete-array final audit is
`51df726be98f7820994c07754670617c6bbf11cbc1d8c9050579f590a8c0f932`.
Canonical Rust remains fixed at 18fd9f75d290df0070e21ee56e0a5691f232596f.
Diagnostics/parser proofs remain paused.

## Decision and limits

Extend the same original closed expression/body judgment and depth-bounded runner
with logical-not on an actual Bool and bit-not on an actual Core.Word.
Keep the original source, outer/operator spans, operand, owner, complete ordered
names/captures and entire actual entry/final stores. No projection, typing,
store-validity, callback or heap snapshot premise is added.
Use existing Bool negation and Core.Word.bitNot; do not add a primitive definition.
No Bool-literal or binary rule, Core/host dispatch, mutation or coercion is added.

These are the existing fixed Lean primitive operations. At the pinned Rust
revision, ! resolves through the name not and ~ through BitNot.bnot; specialization
may fold known operands later. This increment does not implement or prove that
name/class dispatch, selected instance, staging or canonical execution agreement.

Both seven-form ClosedSourceDataExpression and ClosedSourceDataBody gates remain
byte-identical. All existing ADR-0293/0294/0295 production correspondence proofs
must rebuild without source changes. Successful unary execution alone does not
make a unary body/argument eligible for those data gates.

## Literal public laws

Exactly four new ordinary laws in Solcore.Frontend, in one new
Solcore/Frontend/ClosedSourceUnaryProperties.lean file, below 300 lines.
Only existing ClosedSourceEvaluation and ClosedSourceEvaluator imports are needed.
All helpers, if any, remain private.

```lean
theorem closedSourceExpressionEvaluates_logicalNot_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {operand : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ value finalStore ↔
    ∃ operandValue : Bool,
      ClosedSourceExpressionEvaluates owner names captured initialStore
        operand (.bool operandValue) finalStore ∧
      value = .bool (!operandValue)

theorem closedSourceExpressionEvaluates_bitNot_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {captured : Resolved.LocalScope RuntimeValue}
    {initialStore finalStore : List RuntimeValue}
    {span operatorSpan : Syntax.SourceSpan}
    {operand : Syntax.Expr} {value : RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names captured initialStore
      ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ value finalStore ↔
    ∃ operandValue : Core.Word,
      ClosedSourceExpressionEvaluates owner names captured initialStore
        operand (.word operandValue) finalStore ∧
      value = .word operandValue.bitNot

theorem evaluateClosedSourceExpression?_logicalNot
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (operand : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ =
    (do
      let (.bool value, finalStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore operand | none
      return (.bool (!value), finalStore))

theorem evaluateClosedSourceExpression?_bitNot
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (initialStore : List RuntimeValue)
    (span operatorSpan : Syntax.SourceSpan) (operand : Syntax.Expr) :
    evaluateClosedSourceExpression? (budget + 1) owner names captured initialStore
      ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ =
    (do
      let (.word value, finalStore) ←
        evaluateClosedSourceExpression? budget owner names captured initialStore operand | none
      return (.word value.bitNot, finalStore))
```

## Exact semantic additions

Append exactly these two expression constructors after the ten existing
expression clauses and before the unchanged nine-body family. The old nineteen
clauses, order and both family headers remain literal. Update only the expression
constructor-count comment.

```lean
  | logicalNot {owner names captured initialStore finalStore}
      {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr} {value : Bool}
      (child : ClosedSourceExpressionEvaluates owner names captured
        initialStore operand (.bool value) finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩ (.bool (!value)) finalStore
  | bitNot {owner names captured initialStore finalStore}
      {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr} {value : Core.Word}
      (child : ClosedSourceExpressionEvaluates owner names captured
        initialStore operand (.word value) finalStore) :
      ClosedSourceExpressionEvaluates owner names captured initialStore
        ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩ (.word value.bitNot) finalStore
```

Insert exactly these cases in the existing successor expression match before
the lambda-shape fallback. Preserve every old branch and the entire body-runner
suffix. The operand receives precisely the predecessor depth; zero is unchanged.

```lean
      | ⟨_, .unary ⟨_, .logicalNot⟩ operand⟩ => do
          let (.bool value, finalStore) ←
            evaluateClosedSourceExpression? n owner names captured store operand | none
          return (.bool (!value), finalStore)
      | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ => do
          let (.word value, finalStore) ←
            evaluateClosedSourceExpression? n owner names captured store operand | none
          return (.word value.bitNot, finalStore)
```

None still conflates exhausted depth, unsupported paths, absent lookup and wrong
actual operand shape. No public classifier or termination claim is introduced.

## Explicit old-source mutation boundary

Only these seven old production files may change:
ClosedSourceEvaluation, ClosedSourceEvaluator, ClosedSourceEvaluationCompatibility,
ClosedSourceEvaluationProperties, ClosedSourceEvaluatorSoundnessProperties,
ClosedSourceEvaluatorCompletenessProperties and
ClosedSourceEvaluatorMonotonicityProperties (all under Solcore/Frontend).

Beyond the two definitions, edits only add the two necessary expression cases to
four proof inductions: compatibility, determinism, soundness and completeness,
plus the simultaneous one-step monotonicity proof. Preserve all old cases,
body cases/suffixes, imports and sixteen ordinary production headers literally.
Threshold and conditional wrappers, the local/Core/Resolved semantics, RuntimeValue,
source closure semantics, Word match and data correspondence files stay unchanged.

Three old consumer files may change, only as follows:
- FrontendClosedSourceBoundaryProperties: add the two operand-IH cases to store
  invariance; retain all eight public headers and every other proof.
- FrontendClosedSourceDataBoundaryProperties: in
  singleton_and_negation_are_outside_data retain gate exclusions, resolution and
  local negation evidence; replace only universal closed negation impossibility
  by exact original Bool-negation success for arbitrary choice and full mapped
  original store. Singleton tuples remain excluded.
- FrontendExpectedDataLambdaBoundaryProperties: in
  checked_unary_body_is_outside_closed_gate and
  checked_unary_argument_is_outside_closed_gate retain all lets, checking,
  resolution/lowering, Core witnesses and gate exclusions. Replace only the
  universal closed-body/argument impossibility with exact original success for
  both Bool choices under the same parameter/reference rows and arbitrary full
  raw store. Update their obsolete comments. All other helpers/theorems stay literal.

Do not rescue false old negatives with extra assumptions or erase their fixtures.
New successful witnesses must precede runners/new iff use and be built directly
from reference, unary and body constructors. The direct ADR-0295 application law
still excludes ungated arguments. Its invocation law can use a supplied actual
unary argument derivation when all its unchanged saved-body/image premises hold.
Historical ADR-0293/0295 remain historical; new status text explicitly supersedes
only raw unary execution impossibility, not their gate boundaries.

## Generated declarations and preservation

Completed295 has 439 production roots/456 dependency files, public359/1935 and
consumer363/1932, with 3965 tracked Solcore Lean sources. Preserve all old bytes
outside the ten-file allowlist and separately reviewed final publication.
Protect the nineteen old constructor clauses and sixteen old production headers
with literal before/after extraction; also subtract approved inserted cases to
recover old source where possible. This is a source audit, not a formal
cross-version conservativity theorem.

The selected generated manifest467 (91 parents/55 files) contains no entry from
ClosedSourceEvaluation. Keep that full selection unchanged, not 467→469.
Separately enumerate both judgment parents, old19/new2 constructors and both
families' rec/recOn/casesOn types and axioms; actual generated suffix inventory
must be checked too. Their mutual eliminator types intentionally change even
though all body constructor clauses stay literal. No generated audit is implied
by only checking selected467. Existing IO-generated audits stay separate.
New public selection adds only the four ordinary laws; final consumer counts
are fixed after frozen independent consumer design and source inventories.

## Independent consumers and verification

Use distinct new consumer modules below 300 lines without cross-imports.
Symbolic tests retain arbitrary owners/spans, scalar values, full mixed rows and
stores. Construct independent operand/reference/call derivations first, then
consume both iff directions for every actual output and full final store.
Include arbitrary unary nesting, Bool choices, Word zero/maximum/arbitrary value,
wrong scalar/Unit/pair/source closure, missing lookup and nested mismatch.
Unread capture/store rows may contain source closures, opaque Core closures,
hosts and cells. Whole input projection is not an admission condition.

Parsed tests retain actual original unary/group/call ASTs, all spans, empty
diagnostics and EOF. Cover direct/nested operators and operands that invoke an
actual returned source closure whose saved owner/rows conflict with caller rows.
Reuse the actual returned closure and call-entry store, never a reconstructed
Core closure. Build source evidence independently before runner/law answers.

Keep closed depth distinct from Core transition cost. For n wrappers over an
independently successful depth-one/cost-one leaf, show depth n+1 versus Core cost
2*n+1 with original paths. Grouped/call operands keep their own depth accounting.
No universal source-size cutoff, fuel equality or canonical operator claim follows.

First freeze this design after independent review. Prototype the affected proof
family in isolated scratch modules using unchanged common dependencies, then
review and port exact changes. Freeze all source bytes before reviewer reads.
Run focused/direct builds, all old consumers, actual parsed IO, full tests,
exact ordinary/generated kernel and standard-axiom checks after stable builds,
whole dependency/byte-allowlist checks, raw policy/metadata/whitespace checks.
Publish imports/tests/status only after semantic review, in small commits.

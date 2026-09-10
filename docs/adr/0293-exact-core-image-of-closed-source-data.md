# ADR-0293: exact Core image of closed source data expressions

## Status

Accepted after two independent design reviews of the complete literal contract.
Implementation follows the declarations and validation boundaries below.
Base is completed ADR-0292 at 1175f35bca6f486045c0063837218f80a6e88a7e.
Its complete audit is .lake/trace-audits/ADR0292FinalAudit.json, SHA256
37442da54f6ac1449a21daa4446e11400d1ebc3ca0fbab084a2f52d691918504.

## Context and decision

The callback-free original evaluator now has soundness, finite completeness and
exact successful-depth thresholds, but it is not yet related to the older local
expression semantics. Add an exact bridge for their common data/conditional syntax.
Do not duplicate either evaluator or evaluation judgment, change any old contract,
or infer primitive operator semantics from spelling.

Introduce a pure syntax-only proposition with seven constructors. It preserves all
original ranges, recurses on the original right-associated tuple suffix, and checks
all three original conditional children. It has no names, environment, value, type,
cost, depth or successful-resolution index. Literal syntax is permitted as a shape;
successful Word meaning remains exclusively the existing WordLiteralDenotes relation.
Thus malformed/overflowing/string literals may satisfy the shape gate while having
no successful derivation. Identifier spellings such as true remain ordinary lookups.
Singleton tuple syntax, unary/binary operations, lambdas, calls, arrays, projections
and indexing are outside this gate. The gate is not a well-typedness or success test.
The gate is sufficient, not necessary, for raw overlap: an unselected lambda can
coexist with successful raw evaluation but remains outside the whole syntax gate.

Under this gate, prove the full actual-output iff below. Inputs are arbitrary Core
values embedded componentwise while retaining the entire ordered environment and raw
store. Outputs on the closed side remain arbitrary mixed values/stores, not assumed
to project successfully and not fixed to embedded endpoints in advance. The
existential conclusion must identify all actual fields and the whole final store.
No uniqueness, freshness, ownership, runtime typing, store validity or closure-body
assumption may be added. Duplicated names/IDs and foreign-owner rows remain legal.

Prove reflection and embedding by induction on the independent syntax gate, using
private first-match value-map lookup transport/reflection. Recursively reflect each
actual intermediate store before proceeding to the next child. For a conditional
guard, use existing RuntimeValue.ofCore_injective to recover the exact Core Bool.
Only the selected evaluation branch is used, despite the gate covering both branches.
All helper declarations remain private. The raw proof must not use the new Core
bridge or an executable evaluator to reconstruct its conclusion.

Compose the raw iff with existing ResolvesLocalExpression.core_evaluates_iff for
the Core bridge. Both whole original resolution and lowering against the exact
runtime identity order are explicit. Equal environment lengths are insufficient.
No source typing is required for this relational correspondence.

## Frozen declarations

Add two production modules: ClosedSourceDataExpression (the seven-constructor gate)
and ClosedSourceDataExpressionProperties (two ordinary public iff theorems).
The gate and these two theorems are the only new ordinary public declarations.
Its seven constructor names belong to the new gate; no existing generated recursor
or constructor is changed. No extra public helper, filtered evaluator or body family.
Each new module and each consumer must stay below 300 lines.

```lean
inductive ClosedSourceDataExpression : Syntax.Expr → Prop where
  | reference {span : Syntax.SourceSpan} {name : Syntax.Identifier} :
      ClosedSourceDataExpression ⟨span, .identifier name⟩
  | literal {span : Syntax.SourceSpan} {literal : Syntax.CoreLiteral} :
      ClosedSourceDataExpression ⟨span, .literal literal⟩
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr}
      (child : ClosedSourceDataExpression inner) :
      ClosedSourceDataExpression ⟨span, .group inner⟩
  | unit {span tupleSpan : Syntax.SourceSpan} :
      ClosedSourceDataExpression ⟨span, .tuple ⟨tupleSpan, []⟩⟩
  | pair {span tupleSpan : Syntax.SourceSpan} {left right : Syntax.Expr}
      (leftSyntax : ClosedSourceDataExpression left)
      (rightSyntax : ClosedSourceDataExpression right) :
      ClosedSourceDataExpression ⟨span, .tuple ⟨tupleSpan, [left, right]⟩⟩
  | many {span tupleSpan : Syntax.SourceSpan} {first second third : Syntax.Expr}
      {rest : List Syntax.Expr}
      (headSyntax : ClosedSourceDataExpression first)
      (tailSyntax : ClosedSourceDataExpression
        ⟨span, .tuple ⟨tupleSpan, second :: third :: rest⟩⟩) :
      ClosedSourceDataExpression ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩
  | conditional {span question colon : Syntax.SourceSpan}
      {condition thenBranch elseBranch : Syntax.Expr}
      (conditionSyntax : ClosedSourceDataExpression condition)
      (thenSyntax : ClosedSourceDataExpression thenBranch)
      (elseSyntax : ClosedSourceDataExpression elseBranch) :
      ClosedSourceDataExpression
        ⟨span, .conditional condition question thenBranch colon elseBranch⟩

theorem ClosedSourceDataExpression.local_evaluates_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {source : Syntax.Expr} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataExpression source) :
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      LocalExpressionEvaluates names environment initialStore source value finalStore

theorem ClosedSourceDataExpression.core_evaluates_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {source : Syntax.Expr} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataExpression source)
    {resolved : Resolved.Expr} {core : Core.Expr}
    (resolution : ResolvesLocalExpression names source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core) :
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore
```

## Evidence and boundaries

Existing LocalExpressionEvaluationRules, LocalExpressionEvaluationProperties,
RuntimeValueProperties and the closed source judgment provide the needed unchanged
rules. ADR-0288's sourceComputationBodyEvaluates_ofCore_inputs_iff requires child
image correspondence for every source: this gated theorem cannot silently satisfy
that premise for the unrestricted closed evaluator. Body extension is separate.

The raw bridge does not need whole resolution. A selected successful c ? x : missing
can have a gate and both raw derivations, but no whole resolution. Even successful
resolution can fail lowering if an unselected identity is absent from the runtime
identity order. An operator such as !c may have old local evaluation and resolution,
but no closed evaluation rule; resolution success is not a replacement for the gate.
A source closure can be created from embedded inputs outside the Core image. A source
call may even return embedded unit without an old local derivation. Restricting only
the endpoint image does not solve either problem. A mixed initial store outside the
Core image cannot imply that the entire final store is in that image.

Canonical evidence remains pinned to 18fd9f75d290df0070e21ee56e0a5691f232596f.
Original conditional branch selection and ordered/right-associated tuple behavior
are relevant; operator dispatch, typing and the whole compiler correspondence are not
claimed here. In particular &&/|| resolve as ordinary named calls at the pinned target,
so the old specialized local short-circuit rules must not be generalized to that target.

## Consumers and validation

Build independent original closed and local derivations before executable evaluation.
Use arbitrary inert Core payloads, including full closure captures, host functions,
tags and dangling/raw cells, with duplicate and foreign lexical rows and raw stores.
Symbolic consumers exercise reference/group/unit/pair/many/conditional, both actual
Bool choices, unselected failure boundaries and all actual endpoint reflection.

A parsed consumer must reuse the original AST, retain punctuation/source spans, and
first build independent certificates. It must pass actual returned closed evaluator
values/stores through the new iff and compare with actual old/Core results; it must
not assume the returned mixed value's projection in advance. Explicit resolution and
lowering witnesses or actual checker successes are required only at the Core boundary.
Depth and old Core execution cost remain separate; groups already distinguish them.
Consumer imports may not depend on other consumer modules.

Freeze and independently review prototypes before mechanical namespace/import ports.
All earlier source bytes, ordinary headers, constructor clauses, generated recursors,
production import closures and old consumer selections remain unchanged. Only normal
umbrella imports, consumer registration and bounded status/plan/matrix publication
may change. Keep paused diagnostics/parser work and all unrelated files untouched.
Run focused/direct checks, exact public-header and full global public/consumer axiom
checks, aggregate/runtime tests, metadata/kernel checks and dependency/source audits.
No proof placeholders, nonstandard axioms, unsafe/native shortcuts or totality claims.
Use only .lake/trace-audits for scratch. Commit small exact frozen changes; no push.

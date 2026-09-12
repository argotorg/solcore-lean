# ADR-0297: recursive unary data-image bridges

## Status

Accepted design after independent production and consumer design review.
Formal adoption, final consumer review and aggregate kernel verification are
separate required gates, not implied by prototype compilation.
Baseline is completed ADR-0296 at
`a6ebcf88fac3317ec88dbfe67a98a7572a68132b`; its complete-array final audit is
`db572c3f2acc7874332f0f9b51dc95c420457dea4a7870c92dfd3c9014fe56a9`.
Canonical Rust remains fixed at 18fd9f75d290df0070e21ee56e0a5691f232596f.
Diagnostics/parser proofs remain paused.

## Decision and deliberate expansion

Extend existing ClosedSourceDataExpression from seven to nine recursive forms.
Keep its original seven clauses, order and source spans. The unchanged seven
ClosedSourceDataBody forms admit the new expressions in recursive child positions.
This is an intentionally broader admission predicate, not old-gate equivalence.
It establishes neither successful evaluation nor runtime typing: !Word and ~Bool
may be admitted but fail, while unary over calls or lambda creation stays outside.
Use the existing fixed Bool-not/Word-bitNot semantics from ADR-0296. This does not
implement Rust's named not/BitNot.bnot dispatch, instance selection or staging.

Only two existing production files change, with no new ordinary law or module.
Append exactly these clauses to ClosedSourceDataExpression.lean:

```lean
  | logicalNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (child : ClosedSourceDataExpression operand) :
      ClosedSourceDataExpression ⟨span, .unary ⟨operatorSpan, .logicalNot⟩ operand⟩
  | bitNot {span operatorSpan : Syntax.SourceSpan} {operand : Syntax.Expr}
      (child : ClosedSourceDataExpression operand) :
      ClosedSourceDataExpression ⟨span, .unary ⟨operatorSpan, .bitNot⟩ operand⟩
```

ClosedSourceDataExpressionProperties.lean adds two cases each to private reflect
and embed. Reflection inverts the actual unary judgment, applies the child
hypothesis to its full value/store and identifies the Core scalar by
RuntimeValue.ofCore_injective. Embedding uses the independent old local unary
constructor. Impossible source-creation alternatives are discharged by shape.
All existing imports, helpers, public headers and public proof bodies stay literal.
Deleting exactly the new clauses/cases must recover both baseline sources.
The other four body/invocation/application bridge files remain whole-byte exact;
closed evaluation, runners, depth properties and their 58-name mutual family
also remain unchanged.

## Three legacy gate-conjunct migrations

Keep all ten old public names in the two existing data-boundary consumer files.
Only these conjuncts, their obsolete comments and their contradiction subproofs change:

- singleton_and_negation_are_outside_data: admit negated span with .logicalNot .reference.
- checked_unary_body_is_outside_closed_gate: admit b with .expression (.logicalNot .reference).
- checked_unary_argument_is_outside_closed_gate: admit neg s (ref s) with .logicalNot .reference.

The singleton exclusion, seven other complete headers and all other proof bytes
stay literal. Preserve every existing arbitrary-Bool and entire raw RuntimeValue
store success clause introduced in ADR-0296, including its quantified types.
Historical identifiers remain intentionally unchanged. This supersedes only the
older unary data-gate exclusions, not the retained execution or checking results.

## Six unchanged public theorem headers (namespace Solcore.Frontend)

These headers end at := by; their old proof bodies are retained whole, not replaced by this draft.
Solcore/Frontend/ClosedSourceDataExpressionProperties.lean:
```lean
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
      LocalExpressionEvaluates names environment initialStore source value finalStore := by
```
Solcore/Frontend/ClosedSourceDataExpressionProperties.lean:
```lean
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
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
```
Solcore/Frontend/ClosedSourceDataBodyProperties.lean:
```lean
theorem ClosedSourceDataBody.local_evaluates_iff
    {owner : Resolved.DeclarationId} {names : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataBody body) :
    ClosedSourceBodyEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) body actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      ComputationReturnTreeEvaluates LocalExpressionEvaluates owner names environment
        initialStore body value finalStore := by
```
Solcore/Frontend/ClosedSourceDataBodyProperties.lean:
```lean
theorem ClosedSourceDataBody.core_evaluates_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore : Core.Store}
    {body : Syntax.Block} {actualValue : RuntimeValue} {actualFinal : List RuntimeValue}
    (fragment : ClosedSourceDataBody body)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateComputationReturnTree? elaborateLocalExpression?
      types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context) :
    ClosedSourceBodyEvaluates owner inputs.names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (initialStore.map RuntimeValue.ofCore) body actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore := by
```
Solcore/Frontend/ExpectedDataLambdaInvocationProperties.lean:
```lean
theorem closedSourceExpectedDataLambda_invocation_core_iff
    {types : TypeNameTable} {savedOwner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {savedEnvironment : Resolved.Environment}
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {parameterType returnType : Core.Ty} {bodyCore : Core.Expr}
    (shape : SourceUnaryLambdaShape source name body)
    (fragment : ClosedSourceDataBody body)
    (checked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types savedOwner inputs source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore))
    (sameSavedIds : Resolved.LocalScope.ids savedEnvironment =
      Resolved.LocalScope.ids inputs.context)
    {callerOwner : Resolved.DeclarationId} {callerNames : LocalNameTable}
    {callerCaptured : List (Resolved.LocalId × RuntimeValue)}
    {initialStore calleeStore : List RuntimeValue}
    {callSpan argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
    {argumentValue : Core.Value} {bodyStore : Core.Store}
    (calleeEvaluation : ClosedSourceExpressionEvaluates callerOwner callerNames
      callerCaptured initialStore callee
      (.sourceClosure source savedOwner inputs.names
        (savedEnvironment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))) calleeStore)
    (argumentEvaluation : ClosedSourceExpressionEvaluates callerOwner callerNames
      callerCaptured calleeStore argument (RuntimeValue.ofCore argumentValue)
      (bodyStore.map RuntimeValue.ofCore))
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured initialStore
      ⟨callSpan, .call callee ⟨argumentsSpan, [argument]⟩⟩ actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (argumentValue :: Resolved.LocalScope.values savedEnvironment)
        bodyStore bodyCore value finalStore := by
```
Solcore/Frontend/ExpectedDataLambdaApplicationProperties.lean:
```lean
theorem closedSourceExpectedDataLambda_application_core_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {inputs : LocalTypeInputs} {environment : Resolved.Environment}
    {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
    {parameterType returnType : Core.Ty} {bodyCore : Core.Expr}
    (shape : SourceUnaryLambdaShape source name body)
    (fragment : ClosedSourceDataBody body)
    (checked : elaborateExpectedComputationLambda? elaborateLocalExpression?
      types owner inputs source (.function parameterType returnType) =
        some (.lambda parameterType returnType bodyCore))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    {argument : Syntax.Expr} {resolvedArgument : Resolved.Expr} {argumentCore : Core.Expr}
    (argumentFragment : ClosedSourceDataExpression argument)
    (argumentResolution : ResolvesLocalExpression inputs.names argument resolvedArgument)
    (argumentLowering : Resolved.Lowers (Resolved.LocalScope.ids environment)
      resolvedArgument argumentCore)
    {initialStore : Core.Store} {callSpan argumentsSpan : Syntax.SourceSpan}
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ClosedSourceExpressionEvaluates owner inputs.names
      (environment.map (fun row => (row.1, RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore)
      ⟨callSpan, .call source ⟨argumentsSpan, [argument]⟩⟩ actualValue actualFinal ↔
    ∃ value finalStore,
      actualValue = RuntimeValue.ofCore value ∧
      actualFinal = finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore
        (.apply (.lambda parameterType returnType bodyCore) argumentCore) value finalStore := by
```

## Independent consumers

Adopt exactly five new consumer files, each below 300 lines and importing no other
consumer. Complete literal public headers, private fixtures and import-reversal
maps are frozen before formal adoption; final audits retain these bytes in full.
The ordinary inventory is seven, in namespace Tests:

- ClosedSourceUnaryDataImages.mixed_nesting_original_and_all_actual_images.
- ExpectedBoolUnaryDataImages.body_original_and_all_actual_images.
- ExpectedBoolUnaryDataImages.calls_original_and_all_actual_images.
- ExpectedWordUnaryDataImages.body_original_and_all_actual_images.
- ExpectedWordUnaryDataImages.calls_original_and_all_actual_images.
- frontendParsedExpectedBoolUnaryDataBridgeTests : IO Unit.
- frontendParsedExpectedWordUnaryDataBridgeTests : IO Unit.

Expression certificates retain arbitrary nesting, spans, owners, scalar values,
opaque Core payloads, complete ordered rows and stores. All-output clauses quantify
the actual RuntimeValue and entire final list, not just successful projections.
Body/call certificates retain original typed shadow initialization before binding,
saved owner/captures, actual unary arguments and independent Core execution paths.
Recover index witnesses from existing lookup/alignment facts. Saved IDs are unique
as a consequence of LocalTypeInputs and exact alignment, not an added hypothesis.
Raw expression/caller rows may have duplicate or foreign IDs; no row is sanitized.
Opaque q need not have its declared Unit runtime shape. No store-validity premise.
Bool fixture contracts explicitly mention a private Frame; Word uses explicit
arguments and existential indices. Neither is advertised as a private-free API.
Each applicable local/Core image law is consumed in both directions, after
independent original/local/Core witnesses, preserving full actual endpoint images.

Parsed companions retain actual grouped source ASTs, all ranges and SourceIds,
diagnostics zero and EOF. Compare Bool choices and Word zero/one/maximum across
empty and opaque nonempty stores. Use the actual returned source closure AND
creation store to begin the saved invocation; pass actual callee/argument stores
and values through subsequent runs without reconstructing their runtime inputs.
Use invocation for grouped and saved calls, application for a separate constructed
direct AST. Do not describe the latter as the parsed grouped call.
Expression image laws apply only to Core-image environments, not mixed caller rows;
saved invocation uses actual prefix evidence and the checked saved-body image.
Derive closed depth and Core transition cost independently: argument D2/K3,
shadow body D4/K10, whole call D5/K17. Exercise distinct boundary budgets
0, bound-1, bound, bound+3; report prefix-only runs separately where applicable.
Prove wrong-scalar all-output impossibility or nongated-call exclusion before
bounded rejection checks. Bool's missing-callee example is not universal call failure.

## Publication, generated declarations and completion

Preserve all completed296 sources/import edges and full ordered catalog arrays.
Only production2, legacy2, new consumer5, Tests/Main.lean, the three status documents
and this ADR may change. No Solcore/Frontend.lean import is added.
Register five test imports and two IO calls exactly once; retain all old suites.
Publication explicitly supersedes the old seven-form expression boundary while
retaining milestone history and the unchanged seven-form body shape.

Append only logicalNot then bitNot to the selected generated rows under parent
Solcore.Frontend.ClosedSourceDataExpression in its existing source file:
467 becomes 469, retaining all old rows, 91 parents and 55 parent files.
Only that parent source may differ; the other 54 parent files remain literal.
Public catalog becomes 360 files/1941 names; consumer catalog 374 files/1947 names.
Retain the entire four ordered arrays and inherited/new generated lists, not counts.

Separately enumerate the actual nonmutual expression/body gate family: 44 becomes
48, including the two new below constructors which are NOT selected public rows.
Compare full old/new names, raw types, flags and axioms under identical imports.
Old direct constructor types remain unchanged; some expression eliminator types
deliberately expand. Exact alias/hygiene rules must be reviewed, never inferred
from counts. The distinct closed-evaluation mutual family stays at 58 unchanged.
Audit every module-owned private/public/compiler declaration and logical dependency
closure. Preserve generated partial wrappers as visible, individually checked
records; their exclusion from logical proof dependencies is not a claim about
runtime replacement metadata. Accept only the standard three axioms or subsets.

Before completion run focused/direct-client builds, old and new parsed IO,
aggregate frontend/syntax/tests builds, full tests, policy/metadata/whitespace checks,
all selected public/consumer axiom checks and complete source/edge preservation.
Freeze and independently review the new audit helpers/config before execution.
Independent executions must agree on full results. Record bounded failures without
rewriting old evidence, then commit exact approved paths in small coherent units.
No whole-frontend totality, canonical agreement or source/Core closure identity
follows from this bounded bridge expansion.

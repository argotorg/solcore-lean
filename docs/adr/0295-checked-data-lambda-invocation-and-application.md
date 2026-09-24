# ADR-0295: checked data-lambda invocation and application

## Status

Accepted after independent literal-contract and consumer design reviews.
Baseline is completed ADR-0294 at
`b55dcc059c0ad19aec0ac61539ee21a3bdb12588`; its full-array final audit is
`f3cf9b7f9d012bfcd1681197ab3ffea3c8223b3c6439cebb9982babae8062d57`.
Implementation follows the two literal contracts below.
Canonical Rust remains fixed at 18fd9f75d290df0070e21ee56e0a5691f232596f.
Diagnostics/parser proofs remain paused.

## Decision

Connect existing expected-type unary lambda checking to actual original source
calls with data bodies, then to direct Core application. Add exactly two proof
modules and two public iff theorems. Do not change any old judgment, evaluator,
syntax gate, checker, constructor, generated recursor, ordinary header or proof.

This is a bridge for the explicit existing Lean profile, not general closure
conversion, a complete source call checker or canonical Rust execution agreement.
The intermediate sourceClosure is genuinely not an ofCore image of the compiled
Core closure. It must never be replaced by one to reuse the data-expression gate.

## Literal public contracts

Names are in Solcore.Frontend. All original source spans and bodies are retained.
Use the existing SourceUnaryLambdaShape to name the original parameter/body.
The existing whole expected checker supplies annotation meanings, well-formed
component types, parameter scope, body checking and exact expected codomain.
No additional public header record or relation is introduced.

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
        bodyStore bodyCore value finalStore

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
        (.apply (.lambda parameterType returnType bodyCore) argumentCore) value finalStore
```

The first law retains actual caller-side callee and argument derivations. Their
contexts can differ completely from the saved lexical context. It neither assumes
the result of the source body nor accepts a callback correspondence obligation.
The second law eliminates these dynamic prefix premises for a direct source
lambda callee and an original gated argument whose whole resolution/lowering is
supplied. Neither law asserts that the argument has the function's domain type.

The shape premise is used to name the original body and parameter; it is not a
substitute for the successful whole expected checker. Inferred and unmarked typed
parameters are both supported. Omitted return annotations retain the expected
codomain; explicit annotations must have the existing structural meaning.

## Proof obligations

First prove a private checker decomposition using the existing expected-checker
iff and header provenance. It must recover the exact old shared body checker
success at inputs.bindFresh savedOwner name.value parameterType, for the original
body, exact bodyCore and returnType. Recover the parameter/body identity from
the independent original shape; do not assume a header-specific checker result.

Private source-shape uniqueness may reuse the exact existing executable shape
iff. LocalTypeInputs.names_ids/context_ids and bindFresh laws equate the runtime
names-only parameter ID with the declared parameter ID. Extend the entire
sameSavedIds list equality after prepending the actual argument row. Preserve all
original captures, including duplicate spellings and foreign IDs.

Instantiate ADR-0294 at this exact parameter-extended environment, with the
embedded actual argument and entire body-entry store. The source runtime map of
the prepended environment must be shown literally equal, not merely equivalent
under lookups. Source freshness is not recomputed from the caller's rows.

For invocation forward, invert the original call evaluation. Use unchanged closed
callee determinism to identify the complete saved source/owner/names/captures and
callee store with the supplied actual prefix. Use argument determinism to identify
the actual argument and full body-entry store. Align the original shape, then
apply the body image iff to the actual result and full final store.
Reverse starts from the Core body derivation, uses the reverse body image iff,
and builds the original source call from the supplied actual prefixes.

For direct application, original creation captures exactly the input rows and
does not snapshot or modify the heap. Reflect the actual argument through
ADR-0293 before applying invocation; do not project first or assume its image.
The Core target is exactly apply of the checked lambda and argumentCore.
Use the unchanged lambda/apply rules in both directions, with exact argument and
body stores. Core lambda inversion determines its full capture environment.
Do not identify a source closure value with its compiled Core closure.

Every helper is private. No runtime typing, inhabitation, store validity, world,
owner-equality, lookup-only alignment, new cost or evaluator success assumption
may be substituted for the literal hypotheses. If a proposed header is false or
unreasonably redundant, resolve it in design review before implementation.

## Boundary and independent consumers

The saved runtime identities must equal all ordered unique IDs of the supplied
LocalTypeInputs. Thus environment-only rows, missing or reordered rows, duplicate
runtime IDs and fresh-ID collisions are not positive Core fixtures. The theorem
still allows duplicate spellings, foreign owners/IDs, arbitrary opaque Core
closures/hosts/cells, untyped argument payloads and arbitrary complete Core stores.
Caller mixed rows remain unconstrained by saved-ID alignment.

Construct original source and Core derivations independently before applying either
new law or running evaluators. Cover saved owner/capture different from caller,
callee lookup versus original grouped creation, caller-side argument lookup,
parameter shadowing, names-only freshness and full preserved capture suffixes.
Successful endpoints must consume both iff directions, including their entire
actual stores, with opaque returned payloads and nonempty unrelated store rows.

Keep raw success versus checked admission separate: unknown parameter/return
annotation, marked or multiple parameter shape, wrong expected codomain, missing
or reordered saved identities, unselected invalid body/pattern and nongated
created/returned/discarded source closure must not be silently admitted.
Use existing gates and checking rules; do not weaken their whole-written-branch
or then-only name-protection conditions.

Separately test a checked Word-to-Word identity with an actual Unit argument and
Unit result: the operational iff holds without whole-call typing. A checked but
nongated original unary body and direct argument isolate the syntax-gate premises
from checker rejection. These are negative coverage fixtures, not new operators.

Parsed consumers keep the actual original call AST, diagnostics, EOF and spans.
If the parser returns a grouped lambda callee, retain that group and consume
invocation with original group/creation evidence; never replace the parsed call
callee by its child to fit the direct-only application theorem.
Both expected checking and argument resolution/lowering must be actual old
executable/relational evidence for those original children.

Connect actual closed runner outputs using old soundness, before projection.
Compare actual old Core application execution through old soundness and independent
finite witnesses; do not extract existential Prop witnesses into IO data.
Keep closed depth distinct from Core transition cost. Finite budget observations
do not imply failure classification, universal exact bounds or termination.

Suggested production files:
- Solcore/Frontend/ExpectedDataLambdaInvocationProperties.lean
- Solcore/Frontend/ExpectedDataLambdaApplicationProperties.lean

Use separate symbolic and parsed consumer files, splitting each below 300 lines
when needed. Consumers never import each other. Final exact public/consumer names
and counts are fixed by frozen source scans, not provisional file estimates.

## Exclusions and verification

No recursively mixed source/Core value relation, arbitrary sourceClosure capture,
returned-created-closure conversion, general lambda-let-spine simulation, Core or
host invocation from the closed runner, mutation, staging, global resolution,
general expected-type propagation, well-typed generation or totality is added.
Source operator name/class resolution remains separate from fixed Core operations.

The completed294 baseline and independent literal/consumer design reviews are
recorded before adoption. Prototype and freeze before independent full proof
review and mechanical porting. All new files stay below 300 lines; every
public declaration uses only standard axioms. Existing implementation bytes,
full public/consumer selections and generated names are retained.
Run focused and direct checks, actual parsed tests, aggregate and full tests, exact selected-name
axiom audits, whole-dependency and old-byte checks, and kernel-policy and whitespace checks
and small separate commits. Preserve full catalog file/name arrays in final audit.

The exact baseline has437 production roots/454 dependencies,357 public files/1933
selected names,357 consumer files/1916 selected names and467 selected generated
names in91 parent declarations across55 files. The two new ordinary proof laws
add no generated declarations: planned production439/456 and public359/1935.
Old3957 tracked Solcore Lean files and all old implementation/dependency bytes
remain protected, apart from the separately reviewed final umbrella registration.

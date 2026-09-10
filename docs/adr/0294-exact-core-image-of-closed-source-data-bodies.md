# ADR-0294: exact Core image of closed source data bodies

## Status

Accepted after two independent design reviews; implementation follows this contract.
Baseline is completed ADR-0293 at
`0dcbff3f1317ae42c665053bd848ce54ece73a45`; its full-array final audit is
`f3aab61b38003e544952ccb1210c9ad91d902ed57ce5b0cbe130f892278bc5e9`.
Canonical Rust stays fixed at `18fd9f75d290df0070e21ee56e0a5691f232596f`.

## Scope and decision

ADR-0293 identifies every actual closed expression result and whole final store
with an old local result on an independent common data-syntax gate. Extend that
image correspondence to the existing original terminal-body profile, without
changing any expression/body evaluator, judgment, selector, checker or old proof.
The old raw body target is exactly ComputationReturnTreeEvaluates specialized to
LocalExpressionEvaluates, not the larger LocalComputationReturnTreeEvaluates.

Add a pure original-block syntax gate and two iff theorems. Raw correspondence
keeps arbitrary names, runtime rows, Core payloads and stores. The Core theorem
separately consumes an actual existing shared whole-body checker success at the
local-expression child specialization, plus exact ordered runtime/context IDs.
This stronger static boundary is explicit; it is not ADR-0293's resolution-only
and lowering-only Core contract extended to arbitrary raw body environments.

## Literal public contracts

Names below are in Solcore.Frontend. The gate has no owner, scope, result, store,
typing, success, resolution, cost or depth index. All declarations are literal;
implementation may not silently strengthen premises or trim match coverage.

```lean
inductive ClosedSourceDataBody : Syntax.Block → Prop where
  | bare {blockSpan returnSpan : Syntax.SourceSpan} :
      ClosedSourceDataBody ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩
  | expression {blockSpan returnSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      (child : ClosedSourceDataExpression source) :
      ClosedSourceDataBody ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩
  | block {outerSpan innerSpan : Syntax.SourceSpan} {statements : List Syntax.Statement}
      (child : ClosedSourceDataBody ⟨innerSpan, statements⟩) :
      ClosedSourceDataBody ⟨outerSpan, [⟨innerSpan, .block statements⟩]⟩
  | binding {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
      {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {rest : List Syntax.Statement}
      (initializerSyntax : ClosedSourceDataExpression initializer)
      (tailSyntax : ClosedSourceDataBody ⟨blockSpan, rest⟩) :
      ClosedSourceDataBody
        ⟨blockSpan, ⟨letSpan, .letDecl name annotation (some initializer)⟩ :: rest⟩
  | discard {blockSpan statementSpan : Syntax.SourceSpan} {source : Syntax.Expr}
      {rest : List Syntax.Statement}
      (child : ClosedSourceDataExpression source)
      (tailSyntax : ClosedSourceDataBody ⟨blockSpan, rest⟩) :
      ClosedSourceDataBody
        ⟨blockSpan, ⟨statementSpan, .expression source true⟩ :: rest⟩
  | conditional {blockSpan ifSpan : Syntax.SourceSpan} {condition : Syntax.Expr}
      {thenBody elseBody : Syntax.Block}
      (conditionSyntax : ClosedSourceDataExpression condition)
      (thenSyntax : ClosedSourceDataBody thenBody)
      (elseSyntax : ClosedSourceDataBody elseBody) :
      ClosedSourceDataBody
        ⟨blockSpan, [⟨ifSpan, .ifThen condition thenBody (some elseBody)⟩]⟩
  | wordMatch {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
      {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block}
      (scrutineeSyntax : ClosedSourceDataExpression scrutinee)
      (branches : ∀ arm ∈ cases, ClosedSourceDataBody arm.value.body)
      (fallback : ∀ source ∈ defaultBody.toList, ClosedSourceDataBody source) :
      ClosedSourceDataBody
        ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩
          ⟨armsSpan, ⟨cases, defaultBody⟩⟩⟩]⟩

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
        initialStore body value finalStore

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
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore
```

Seven syntax forms account for all nine unchanged successful body rules:
optional annotation combines typed/inferred binding, and conditional combines
the two actual Bool choices. Keep all original spans, statement tails, single
scrutinee wrappers, case order and optional defaults. Every written expression
child uses ADR-0293's gate; both conditional bodies and all match/default bodies
use the body gate. All unselected syntax remains present.

No empty-body implicit return, uninitialized let, expression without its discard
semicolon, nonterminal explicit block/if/match, extra scrutinee, source closure
creation/call or excluded expression operator gains a form. Annotations and
patterns have no validity premise in the gate. Existing Word meanings and
actual selector derivations determine successful evaluation, not shape admission.
The gate is sufficient, not necessary, for raw overlap and guarantees no success.

## Reuse without weakening the old child contract

ADR-0288's global childExact over every source cannot be instantiated with
unrestricted ClosedSourceExpressionEvaluates from a syntax-conditional theorem.
Use private conjunction aliases only: gate and LocalExpressionEvaluates; gate
and ClosedSourceExpressionEvaluates. These are not new public judgments or
evaluator functions; they do not transform or replace the original source syntax.
ADR-0293 then proves the unchanged global all-actual-output childExact for those
aliases. Preserve both whole endpoint equalities and all original input indices.

Private body adapters add/remove the expression-gate conjunct under the separate
body gate. Compose original closed-body compatibility, the mixed adapter,
ADR-0288's exact body image theorem and the old adapter under the existential.
The existing bridge reflects actual initializer/discard/guard/scrutinee values
and complete middle stores before continuing; endpoint-only admission is not
an acceptable replacement for this intermediate-value evidence.

For match, retain fallback/wildcard/hit/miss and actual selected original body.
If using gate induction, transport the entire generalized induction property
through choice with a private arbitrary Block predicate helper. Merely finding
the selected body's gate does not justify a recursive theorem call. Evaluation
induction carrying a gate is an equivalent implementation choice. Non-Word
wildcard/default and unvisited malformed patterns retain their existing meaning.

Initializers evaluate before binding. Fresh IDs use only current name-row IDs;
embedding values changes neither that expression nor the exact prepended rows.
The raw bridge imposes no global freshness, owner alignment or row uniqueness:
duplicate spellings/IDs, foreign rows and environment-only fresh-ID collisions
remain allowed, as do arbitrary Core closure bodies/captures, hosts and raw cells.
No typing, inhabitation, world or store-validity premise is added to raw results.

## Explicit Core boundary

Reuse ComputationReturnTreeElaborates.evaluates_iff with the actual child-checker
equation as ChildElab, LocalExpressionEvaluates as ChildEval, and the existing
Core local fragment. Actual whole acceptance supplies elaboration via
elaborateComputationReturnTree?_iff with reflexive child correctness.
Discharge its four unchanged child contracts with existing local-fragment
membership, weakening, exact insertion and local-expression/Core correspondence.
Compose only the final old-evaluation conjunct of the raw image existential.
Do not add another body lowerer, checker, execution engine or proof callback
to either public header.

LocalTypeInputs derives names and context from one unique-ID bindings list.
Exact sameIds aligns that entire ordered list with runtime IDs. Thus this Core
law excludes duplicate runtime IDs, missing/reordered rows and environment-only
extra rows. Duplicate spellings and foreign IDs remain possible; actual values
and stores need not satisfy the checker context or any runtime typing judgment.
This input restriction belongs to the Core bridge, never the raw theorem.

Whole acceptance retains existing annotation interpretation, child checking,
both conditional arm checks/equal result types, then-only ComputationNamesProtected,
all original match patterns/bodies and the existing ordered coverage fold.
Explicit blocks and match arms remain scope barriers. Do not strengthen the
then-only guard to both branches or remove it. The older TypedLetReturnTree
checker has distinct unused-spelling restrictions and is not substituted here.
Pinned body_resolver.rs lines32-134 and928-968 confirm initializer-before-binding,
sequential bare-if traversal, explicit block/match-arm scopes and overwriting
registration. This evidence bounds the unchanged profile; it proves neither
whole canonical resolution nor whole-compiler correctness.

## Files, consumers and verification

Use exactly ClosedSourceDataBody.lean and ClosedSourceDataBodyProperties.lean,
each below300 lines. Only the gate and two iff theorems are ordinary public
declarations; additionally select all seven new constructor names for audit.
Keep adapters, conjunction aliases and selector transports private. No existing
production file or old consumer is modified except final umbrella registration.
Retain all old435 production roots/452 union dependencies, public355/1923,
consumer353/1904 and all460 selected generated names/parent sources. New public
selection should be357 files/1933 names, with old imports and all old recursors
unchanged; no exemptions for generated mutual recursors are needed.

Independent symbolic consumers construct original Closed and generic-Local
derivations before the new laws: arbitrary binding prefixes and pre-shadow
lookup, optional annotations, both Bool branches, all ordered match choices,
opaque payloads and whole stores. Include raw duplicate/environment-only
collision witnesses separately from successful unique-aligned Core fixtures.
Negative boundaries include a discarded source closure yielding image Unit,
unknown annotation, exposed then-side shadow versus terminal explicit block,
unselected missing names/IDs and unvisited invalid pattern/body distinctions.

Parsed consumers use actual original blocks, empty diagnostics, EOF and spans;
independent original certificates precede either new iff or semantic search.
Actual closed outputs enter image laws before projection. Actual whole checking
and actual Core execution must be connected by old soundness/independent
derivations, without extracting existential Prop witnesses into IO data.
Keep observed closed depth separate from existing exact Core transition costs.
Split consumers as necessary so each remains below300 lines and no consumer
imports another consumer; do not create a new shared public testing framework.

Freeze prototypes before independent full review and mechanical namespace/import
porting. Run focused builds, direct Lean, actual parsed IO, aggregate/full tests,
all exact public/consumer names with standard-only axioms, full dependency/old-byte
audits, kernel/metadata/EOF/whitespace checks and small commits. Final audit must
retain full selected file/name arrays, not only counts. Diagnostics/parser proof
development remains paused. No new termination, totality, runtime safety, source
closure conversion, operator semantics or whole-language correctness is claimed.

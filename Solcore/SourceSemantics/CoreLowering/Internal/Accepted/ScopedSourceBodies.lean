import Solcore.SourceSemantics.CoreLowering.EmittedMatchCatalogCoupledExtraction
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaSupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSyntaxFacts
import Solcore.SourceSemantics.CoreLowering.GenericMatchScopedContexts
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentRoute
import Lean
import Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition
import Solcore.Frontend.SourceCoreLocalPolymorphism
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralIssuedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedRecipes

/-!
# Scoped Source bodies

Admission, stopping and typing of scoped Source bodies, their matches and `for` items, and the support of prepared lambda bodies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyStaticReceipts
/-! Exact compiler trees keep their original occurrence evidence. The prepared
alternative interprets only authentic operand and unary tokens; projection
failures remain indexed by the actual reached state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyStaticReceipts
open Core Frontend SourceInference
open GenericImperativeMatch

/-- Only original value-assignment occurrences request an operand token law. -/
def OperandLaw (source : TypedSource)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {site assignment operator rhs},
    AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs →
    (operator = .equal ∨ assignment.target.type = .word) →
    AssignmentOperandDiagnostics.OperandsLaw faults operator
      (invalidOperand site assignment.target.root operator)

/-- Original unary occurrences retain their actual diagnostic token. -/
def UnaryLaw (source : TypedSource)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (faults : FunctionCalls.FaultRep) : Prop :=
  ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs source site assignment →
    assignment.target.type = .word →
    faults (.invalidUnaryOperand .bitNot) (invalidUnary site assignment.target.root)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- The tree is fixed before a receiving registry or fault interpretation is
chosen. Place diagnostics retain preparation instead of a uniform fault law. -/
structure PreparedExtraction
    (layouts : SourceCoreAllocationLayouts.Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (invalidUnary invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (position : Position) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop where
  tree : Tree layouts owner active frame globals onError values source expressionSyntax certificates
    definitions administrative context scope position expected type code
  sites : ∀ registry faults, OperandLaw source invalidOperand faults → UnaryLaw source invalidUnary faults →
    PreparedBranchingCatalogSites.CatalogSites invalidProjection missingDefault registry faults tree


end Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyStaticReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodySupport
/-! The selected physical closure keeps its actual compiler flow and reached
place receipts. The older ordinary support retains its original contract. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedContextualLambdaProvenance (BinderPolicy)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

abbrev Produced := @CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Produced

/-- One accepted body keeps both its actual compiler callback and original
Source tree. Capture replacement changes none of these static witnesses. -/
structure Body {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (namedCompilation : Compilation compiled.indexed named diagnostics namedCode)
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative) (program : Program)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (invalidUnary invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    extends CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code where
  frame : Dynamic.ClosureFrame program function
  readFuel : Nat
  flow : Expr
  projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
    code.compilation.internalReason code.compilation.internalReason
  valid : CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source
  syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (expressionSyntax function.source)
    context (.statements true function.body) function.resultType
  shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body
  view : code.view = function.source
  recipe : BodyRecipe namedCompilation code
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy (bodyPolicy namedCompilation code) code.fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow
  extraction : PreparedLambdaBodyStaticReceipts.PreparedExtraction compiled.indexed.layouts code.compilation.owner code.active
    compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
    (.initial compiled.compatible.checked) function.source invalidOperand invalidUnary invalidProjection missingDefault
    (expressionSyntax function.source) (certificates readFuel function.source)
    compiled.indexed.layouts.definitions administrative context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- Every field belongs to this literal Code and genuine owning Source. -/
structure Support (code : Code compiled.indexed function scope administrative) where
  caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  namedCode : Expr
  namedCompilation : Compilation compiled.indexed caller.named diagnostics namedCode
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  source : function.source = CallableIndexedNamedGeneration.source caller.named
  compilation : code.compilation = CallableIndexedNamedGeneration.context compiled.indexed caller.named
  active : code.active = []
  issued : IssuedSource compiled code.compilation.owner function.source
  diagnosticPolicy : AssignmentDiagnosticPolicy
  body : Body namedCompilation code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
    issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault

variable (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : Compilation compiled.indexed caller.named diagnostics namedCode)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
  (site : Site compiled.indexed caller.named parameters result statements context evidence environment scope administrative)

/-- Independent same-Site static body and issuance construct support directly. -/
def Support.of_site
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (issued : IssuedSource compiled site.code.compilation.owner (CallableIndexedNamedGeneration.source caller.named))
    (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (body : Body namedCompilation site.code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
      issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault) :
    Support site.code :=
  ⟨caller, diagnostics, namedCode, namedCompilation, expressionSyntax, certificates, rfl, site.compilation, site.active,
    issued, diagnosticPolicy, body⟩

variable {code : Code compiled.indexed function scope administrative} (support : Support code)

include support in
/-- Source attribution follows from the retained actual Header. -/
theorem Support.source_receipt :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source := by
  rw [support.compilation, support.active, support.source]
  exact .original (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)

include support in
theorem Support.unique : NodeOccurrencesUnique function.source := support.body.unique

/-- Static body, recipe and prepared packet keep their identical indices. -/
def Support.recapture (environment : Dynamic.Environment) :
    Support (RecursiveNamedLambdaFormationHeads.recaptureCode (values := .initial compiled.compatible.checked)
      (indexed := compiled.indexed) code environment) where
  caller := support.caller
  diagnostics := support.diagnostics
  namedCode := support.namedCode
  namedCompilation := support.namedCompilation
  expressionSyntax := support.expressionSyntax
  certificates := support.certificates
  source := support.source
  compilation := support.compilation
  active := support.active
  issued := support.issued
  diagnosticPolicy := support.diagnosticPolicy
  body := {
    toContext := RecursiveNamedLambdaFormationHeads.recaptureContext (values := .initial compiled.compatible.checked) code support.body.toContext environment
    frame := RecursiveNamedLambdaFormationHeads.recaptureFrame support.body.frame environment
    readFuel := support.body.readFuel, flow := support.body.flow, projection := support.body.projection
    emitted := support.body.emitted, valid := support.body.valid
    unique := support.body.unique, syntaxTree := support.body.syntaxTree, shape := support.body.shape
    view := support.body.view, recipe := support.body.recipe, generated := support.body.generated
    extraction := support.body.extraction }

/-- Captured history keeps its full original compiler seed. -/
structure SourceOrigin (history : History code) : Prop where
  metadata : history.metadata = state support.caller.named

/-- Output indices keep the exact seed; no Site is reconstructed from Code. -/
inductive PreparedAt : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) → Support code → Prop where
  | recaptured
      (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
      {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
      (compilation : Compilation compiled.indexed caller.named diagnostics namedCode)
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
      {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      (site : Site compiled.indexed caller.named parameters result statements context evidence [] scope administrative)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
      (issued : IssuedSource compiled site.code.compilation.owner (CallableIndexedNamedGeneration.source caller.named))
      (diagnosticPolicy : AssignmentDiagnosticPolicy)
      (body : Body compilation site.code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
        issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault)
      (binderPolicy : BinderPolicy caller.named site.code)
      (compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained caller.named site.code)
      (issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained caller.named site.code)
      (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView site.code)
      (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons site.code caller.named)
      (declarations : CompatibleExpressionReads.ScopeDeclarations
        (CallableIndexedNamedGeneration.source caller.named) scope context)
      (environment : Dynamic.Environment) :
      PreparedAt (RecursiveNamedLambdaFormationHeads.recaptureCode (values := .initial compiled.compatible.checked)
        (indexed := compiled.indexed) site.code environment)
        ((Support.of_site caller compilation site expressionSyntax certificates issued diagnosticPolicy body).recapture environment)

/-- Genuine seed policy and Source metadata identify this ordered binder row. -/
theorem PreparedAt.projected_bindings (receipt : PreparedAt code support) :
    ∀ binding ∈ code.receipt.loweredParameters,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment =>
    exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings site binderPolicy body.extended

end Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodySupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyStopping
/-! Finite stopping receipts refer only to original statement forms. Independent
Source typing supplies every prefix and branch context and raw result fact. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyStopping
open Frontend SourceInference ReachableStatementContinuations

inductive ReturnStopped (source : TypedSource) : List StatementId → Prop where
  | returning {id node value rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt value) :
      ReturnStopped source (id :: rest)
  | block {id node body rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .block body)
      (inner : ReturnStopped source body) : ReturnStopped source (id :: rest)
  | conditional {id node condition left right rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .ifThen condition left (some right))
      (first : ReturnStopped source left) (second : ReturnStopped source right) :
      ReturnStopped source (id :: rest)
  | matching {id node resolution fallback rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .matchWith resolution)
      (present : resolution.defaultBody = some fallback)
      (arms : ∀ arm ∈ resolution.cases, ReturnStopped source arm.body)
      (default : ReturnStopped source fallback) : ReturnStopped source (id :: rest)
  | prefix {id rest} (remaining : ReturnStopped source rest) : ReturnStopped source (id :: rest)

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by
        intro item member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail item member⟩

/-- The budget controls this finite form inspection. A failed earlier candidate
may still be followed by an actual stopped suffix. -/
def returnStopped? (source : TypedSource) : (fuel : Nat) → (statements : List StatementId) →
    Option (PLift (ReturnStopped source statements))
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, id :: rest =>
    let tail := do
      let ⟨stopped⟩ ← returnStopped? source fuel rest
      pure ⟨ReturnStopped.prefix stopped⟩
    match found : source.lookupStatement? id with
    | none => tail
    | some node =>
      match form : node.form with
      | .returnStmt _value => some ⟨.returning found form⟩
      | .block body =>
        match returnStopped? source fuel body with
        | some ⟨inner⟩ => some ⟨.block found form inner⟩
        | none => tail
      | .ifThen _condition left (some right) =>
        match returnStopped? source fuel left, returnStopped? source fuel right with
        | some ⟨first⟩, some ⟨second⟩ => some ⟨.conditional found form first second⟩
        | _, _ => tail
      | .matchWith resolution =>
        match present : resolution.defaultBody with
        | none => tail
        | some fallback =>
          match allProof? (fun arm : TypedMatchCase => ReturnStopped source arm.body)
              (fun arm => returnStopped? source fuel arm.body) resolution.cases,
              returnStopped? source fuel fallback with
          | some ⟨arms⟩, some ⟨default⟩ => some ⟨.matching found form present arms default⟩
          | _, _ => tail
      | _ => tail

theorem ReturnStopped.nonempty {source statements} (stopped : ReturnStopped source statements) :
    statements ≠ [] := by cases stopped <;> simp

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts ∧
      facts.control = (if rest.isEmpty then headFacts.control else headFacts.control.sequence tailFacts.control) ∧
      facts.sawReturn = (headFacts.sawReturn || tailFacts.sawReturn) := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _, rfl, by simp [BodyFacts.singleton, BodyFacts.empty]⟩
  | cons head tail => exact ⟨_, _, _, head, tail, rfl, rfl⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementControlFormTyping source control context node.form facts := by
  obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.controlFormTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact formTyped

private theorem head_stops {source : TypedSource} {id : StatementId} {rest : List StatementId}
    {head tail summary : ControlSummary}
    (stopped : StoppingStatement source id head)
    (same : summary = if rest.isEmpty then head else head.sequence tail) :
    StoppingStatements source (id :: rest) summary := by
  have sequence : head.sequence tail = head := by
    have absent := stopped.no_fallthrough
    cases head
    simp_all [ControlSummary.sequence, ControlSummary.canFallthrough]
  rw [sequence] at same
  simp only [ite_self] at same
  exact same ▸ .stop stopped

private theorem cases_stopping {source : TypedSource} {cases : List TypedMatchCase}
    (bodies : ∀ arm ∈ cases, ∀ {control : ControlContext}
      {context final : SourceSemantics.Context} {facts : BodyFacts},
      StatementsHaveType source control context arm.body final facts →
      StoppingStatements source arm.body facts.control ∧ facts.sawReturn = true)
    {control : ControlContext} {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {facts : List BodyFacts}
    (typed : MatchCasesHaveType source control context type cases facts) :
    (∀ arm fact, (arm, fact) ∈ cases.zip facts →
      StoppingStatements source arm.body fact.control) ∧ allBodiesSawReturn facts = true := by
  induction cases generalizing facts with
  | nil =>
    cases typed
    refine ⟨?_, rfl⟩
    intro arm fact member
    cases member
  | cons arm rest ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | intro pattern extended body =>
        obtain ⟨stops, returns⟩ := bodies arm List.mem_cons_self body
        obtain ⟨tails, allReturn⟩ := ih (fun candidate member => bodies candidate (List.mem_cons_of_mem _ member)) tail
        refine ⟨?_, ?_⟩
        · intro candidate fact member
          rcases List.mem_cons.mp member with same | member
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
            exact stops
          · exact tails candidate fact member
        · simp only [allBodiesSawReturn, List.all_cons, returns, Bool.true_and]
          exact allReturn

private theorem ReturnStopped.typed {source statements} (stopped : ReturnStopped source statements)
    (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    StoppingStatements source statements facts.control ∧ facts.sawReturn = true := by
  induction stopped generalizing control context final facts with
  | returning found form =>
    obtain ⟨_, _, _, head, _, same, returned⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | returnUnit => exact ⟨head_stops (.returnUnit found form) same, by simpa using returned⟩
    | returnValue => exact ⟨head_stops (.returnValue found form) same, by simpa using returned⟩
  | block found form inner ih =>
    obtain ⟨_, _, _, head, _, same, returned⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | block body =>
      obtain ⟨stops, returns⟩ := ih body
      exact ⟨head_stops (.block found form stops) same, by simpa [returns] using returned⟩
  | conditional found form first second firstIH secondIH =>
    obtain ⟨_, _, _, head, _, same, returned⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | ifWithElse condition left right =>
      obtain ⟨firstStop, firstReturn⟩ := firstIH left
      obtain ⟨secondStop, secondReturn⟩ := secondIH right
      exact ⟨head_stops (.conditional found form firstStop secondStop) same,
        by simpa [firstReturn, secondReturn] using returned⟩
  | matching found form present arms default armIH defaultIH =>
    obtain ⟨_, _, _, head, _, same, returned⟩ := head_tail typed
    have original := form_at unique found head
    rw [form] at original
    cases original with
    | matchWithoutDefault absent scrutinee casesTyped exhaustive merged =>
      simp [present] at absent
    | matchWithDefault actual scrutinee casesTyped defaultTyped merged =>
      cases Option.some.inj (actual.symm.trans present)
      obtain ⟨armStops, armReturns⟩ := cases_stopping armIH casesTyped
      obtain ⟨defaultStops, defaultReturns⟩ := defaultIH defaultTyped
      exact ⟨head_stops (.matchDefault found form present casesTyped defaultTyped merged armStops defaultStops) same,
        by simpa [armReturns, defaultReturns] using returned⟩
  | «prefix» remaining ih =>
    cases typed with
    | singleton head => exact False.elim (remaining.nonempty rfl)
    | cons head tail =>
      obtain ⟨stops, returns⟩ := ih tail
      obtain ⟨node, contains, _⟩ := Dynamic.StatementHasType.controlFormTyping head
      exact ⟨.prefix (lookupStatement?_complete unique contains) head stops,
        by simp [BodyFacts.cons, returns]⟩

/-- Stopping is justified at the original typed contexts. Its exact summary and
return annotation are retained independently of compiled native types. -/
theorem ReturnStopped.facts {source statements} (stopped : ReturnStopped source statements)
    (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    StoppingStatements source statements facts.control ∧ facts.sawReturn = true ∧
      facts.type = control.returnType := by
  obtain ⟨stops, returns⟩ := stopped.typed unique typed
  exact ⟨stops, returns, RecursiveNamedStatementSyntaxFacts.returned_type typed returns⟩

theorem ReturnStopped.stopped {source statements} (stopped : ReturnStopped source statements)
    (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    GenericLexicalStatements.Stopped source statements :=
  GenericLexicalStatements.Stopped.of_source (stopped.facts unique typed).1

/-- Every original arm and the present default retain genuine Source stopping.
The actual typed case row supplies its full ordered branch facts. -/
theorem ReturnStopped.match_default {source : TypedSource} {id : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {fallback : List StatementId}
    (arms : ∀ arm ∈ resolution.cases, ReturnStopped source arm.body)
    (default : ReturnStopped source fallback)
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (present : resolution.defaultBody = some fallback)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : StatementFacts}
    (typed : StatementHasType source control context id final facts) :
    ReachableMatchContinuations.DefaultStopped source id resolution := by
  have receipt : ReturnStopped source [id] := .matching found form present arms default
  have stops := (receipt.facts unique (.singleton typed)).1
  have head_only : ∀ {summary}, StoppingStatements source [id] summary →
      ∃ head, StoppingStatement source id head := by
    intro summary stopped
    cases stopped with
    | stop head => exact ⟨_, head⟩
    | «prefix» _ _ tail => cases tail
  obtain ⟨_, head⟩ := head_only stops
  exact RecursiveNamedStatementSyntaxFacts.stopped_match found form head

end Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyStopping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
/-! Original match typing fixes each arm's full lexical context. The hidden
scrutinee is a compiler cell, so it is excluded from these Source contexts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
open Frontend SourceInference

private theorem binders_unique {owner : Resolved.DeclarationId}
    {context first second : SourceSemantics.Context} {binders : List TypedBinder}
    (left : BindersExtend owner context binders first)
    (right : BindersExtend owner context binders second) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons head tail ih =>
    cases head
    cases right with
    | cons head tail => cases head; exact ih tail

theorem case_typing {source : TypedSource} {control : ControlContext}
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {cases : List TypedMatchCase} {facts : List BodyFacts} {arm : TypedMatchCase}
    (typed : MatchCasesHaveType source control context type cases facts)
    (member : arm ∈ cases) :
    ∃ binders arity armContext final bodyFacts,
      TypedMatchPatternHasType context arm.pattern type binders arity ∧
      BindersExtend source.owner context binders armContext ∧
      StatementsHaveType source control armContext arm.body final bodyFacts := by
  induction cases generalizing facts with
  | nil => cases member
  | cons first rest ih =>
    cases typed with
    | cons head tail =>
      rcases List.mem_cons.mp member with rfl | member
      · cases head with
        | intro pattern extended body => exact ⟨_, _, _, _, _, pattern, extended, body⟩
      · exact ih tail member

/-- A compiler request's native scope cannot substitute for the original
pattern binders. The two genuine typing derivations determine equal contexts. -/
theorem request_typing {source : TypedSource} {control : ControlContext}
    {context child : SourceSemantics.Context} {type : TypeSystem.Ty}
    {cases : List TypedMatchCase} {facts : List BodyFacts}
    {fallback : Option (List StatementId)} {request : GenericMatchChildren.Request}
    (typed : MatchCasesHaveType source control context type cases facts)
    (defaultTyped : ∀ statements, fallback = some statements →
      ∃ final bodyFacts, StatementsHaveType source control context statements final bodyFacts)
    (selected : GenericMatchChildren.ContextFor source context type cases fallback request child) :
    ∃ final bodyFacts, StatementsHaveType source control child request.statements final bodyFacts := by
  cases selected with
  | arm member same pattern extended =>
    obtain ⟨binders, arity, armContext, final, bodyFacts, original, extension, body⟩ :=
      case_typing typed member
    have sameBinders := (CompatiblePatternSourceBinders.pattern_binders original).symm.trans
      (CompatiblePatternSourceBinders.pattern_binders pattern)
    cases sameBinders
    have sameContext := binders_unique extension extended
    cases sameContext
    exact ⟨final, bodyFacts, same ▸ body⟩
  | default same => exact defaultTyped _ same

private theorem defined_ordinary {source : TypedSource} {node : Node}
    {localId : Resolved.LocalId} (ownership : LocalIdentityOwnership source)
    (member : node ∈ source.nodes) (defined : localId ∈ node.definedLocalIds) :
    source.inputs.any (fun input => decide (input.id = localId)) = false := by
  have inNodes : localId ∈ source.nodes.flatMap Node.definedLocalIds :=
    List.mem_flatMap.mpr ⟨node, member, defined⟩
  have disjoint := (List.nodup_append.mp (show
    (source.inputs.map (·.id) ++ source.nodes.flatMap Node.definedLocalIds).Nodup from
    by simpa only [definedLocalIds, ← flatMapNodeDefinedLocalIds_eq_carrier] using ownership.unique)).2.2
  apply Bool.eq_false_iff.mpr
  intro present
  obtain ⟨input, member, same⟩ := List.any_eq_true.mp present
  exact disjoint input.id (List.mem_map.mpr ⟨input, member, rfl⟩)
    localId inNodes (of_decide_eq_true same)

theorem ordinary_bindings {source : TypedSource} {id : StatementId}
    {node : StatementNode} {resolution : MatchResolution}
    (ownership : LocalIdentityOwnership source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution) :
    source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false ∧
    ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
      source.inputs.any (fun input => decide (input.id = binder)) = false := by
  have member := (lookupStatement?_sound found).1
  constructor
  · apply defined_ordinary ownership member
    simp [Node.definedLocalIds, StatementForm.definedLocalIds, form]
  · intro arm present binder bound
    apply defined_ordinary ownership member
    simp only [Node.definedLocalIds, StatementForm.definedLocalIds, form, List.mem_cons]
    exact .inr (List.mem_flatMap.mpr ⟨arm, present, bound⟩)

theorem statement_type {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (typed : StatementHasType source control context id final facts) :
    node.type = .unit ∨ node.type = control.returnType := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all only [reduceCtorEq]
  all_goals
    split at * <;> simp_all

/-- Match arms restore the parent context. The default and every pattern body
keep the original control context, including its actual enclosing loop depth. -/
theorem statement_sites {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {facts : StatementFacts}
    {scrutinee : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutinee)
    (typed : StatementHasType source control context id final facts) :
    final = context ∧ ∃ caseFacts,
      ExpressionHasType source context resolution.scrutinee scrutinee.type ∧
      MatchCasesHaveType source control context scrutinee.type resolution.cases caseFacts ∧
      (∀ statements, resolution.defaultBody = some statements →
        ∃ last bodyFacts, StatementsHaveType source control context statements last bodyFacts) := by
  obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases same
  rw [form] at formTyped
  have core : final = context ∧ ∃ type caseFacts,
      ExpressionHasType source context resolution.scrutinee type ∧
      MatchCasesHaveType source control context type resolution.cases caseFacts ∧
      (∀ statements, resolution.defaultBody = some statements →
        ∃ last bodyFacts, StatementsHaveType source control context statements last bodyFacts) := by
    cases formTyped with
    | matchWithoutDefault absent value casesTyped =>
      exact ⟨rfl, _, _, value, casesTyped, fun statements present => by simp_all⟩
    | matchWithDefault present value casesTyped defaultTyped =>
      exact ⟨rfl, _, _, value, casesTyped, fun statements selected => by
        cases Option.some.inj (present.symm.trans selected)
        exact ⟨_, _, defaultTyped⟩⟩
  obtain ⟨sameContext, type, caseFacts, value, casesTyped, defaultTyped⟩ := core
  obtain ⟨stored, contains, sameType⟩ := value.stored_type
  have sameNode := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans scrutineeFound)
  cases sameNode
  exact ⟨sameContext, caseFacts, sameType ▸ value, sameType ▸ casesTyped, defaultTyped⟩

end Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ScopedSourceForItemsAdmission
/-! Original for-item certificates thread the exact lexical context recovered
from genuine Source typing. The accepted compiler supplies these finite receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceForItemsAdmission
open Core Frontend SourceInference

inductive Scan (source : TypedSource) (approved : ExpressionId → Prop) : List ForItemForm → Prop where
  | nil : Scan source approved []
  | absent {binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Scan source approved rest) : Scan source approved (.letDecl binder none :: rest)
  | initialized {binder expression expressionNode rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (found : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = binder.scheme.body) (value : approved expression)
      (remaining : Scan source approved rest) : Scan source approved (.letDecl binder (some expression) :: rest)
  | discard {expression expressionNode rest}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : approved expression) (remaining : Scan source approved rest) :
      Scan source approved (.expression expression :: rest)
  | assign {assignment operator rhs rhsNode binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (targetType : binder.scheme.body = assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type) (value : approved rhs)
      (remaining : Scan source approved rest) : Scan source approved (.assignValue assignment operator rhs :: rest)
  | bitNotProjected {assignment binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (route : AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type)
      (profile : assignment.target.type = .word)
      (projected : assignment.target.projections ≠ [])
      (keys : ∀ key ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections, approved key)
      (remaining : Scan source approved rest) : Scan source approved (.assignBitNot assignment :: rest)
  | assignProjected {assignment operator rhs rhsNode binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (route : AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (projected : assignment.target.projections ≠ [])
      (keys : ∀ key ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections, approved key)
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type) (value : approved rhs)
      (remaining : Scan source approved rest) : Scan source approved (.assignValue assignment operator rhs :: rest)
  | bitNot {assignment binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (targetType : binder.scheme.body = assignment.target.type)
      (profile : assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (remaining : Scan source approved rest) : Scan source approved (.assignBitNot assignment :: rest)

theorem Scan.map {source : TypedSource} {approved other : ExpressionId → Prop} {items : List ForItemForm}
    (scan : Scan source approved items) (mapped : ∀ id, approved id → other id) : Scan source other items := by
  induction scan with
  | nil => exact .nil
  | absent declaration mono ordinary _ ih => exact .absent declaration mono ordinary ih
  | initialized declaration mono ordinary found type value _ ih => exact .initialized declaration mono ordinary found type (mapped _ value) ih
  | discard found value _ ih => exact .discard found (mapped _ value) ih
  | assign declaration target profile bare found type value _ ih => exact .assign declaration target profile bare found type (mapped _ value) ih

  | assignProjected declaration route profile projected keys found type value _ ih =>
      exact .assignProjected declaration route profile projected (fun key member => mapped key (keys key member)) found type (mapped _ value) ih
  | bitNotProjected declaration route profile projected keys _ ih =>
      exact .bitNotProjected declaration route profile projected (fun key member => mapped key (keys key member)) ih
  | bitNot declaration target profile bare _ ih => exact .bitNot declaration target profile bare ih

theorem Scan.shape {source approved items} (scan : Scan source approved items) :
    CallableIndexedOwnedPreparedStagedBranchingTree.ItemShape items := by
  induction scan with
  | nil => exact .nil
  | absent _ _ _ _ ih => exact .absent ih
  | initialized _ _ _ _ _ _ _ ih => exact .initialized ih
  | discard _ _ _ ih => exact .discard ih
  | assign _ _ profile bare _ _ _ _ ih => exact .assign profile bare ih

  | assignProjected _ _ profile projected _ _ _ _ _ ih => exact .assignProjected profile projected ih
  | bitNotProjected _ _ profile projected _ _ ih => exact .bitNotProjected profile projected ih
  | bitNot _ _ profile bare _ ih => exact .bitNot profile bare ih

private theorem expression_at {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) : ExpressionHasType source context id node.type := by
  obtain ⟨original, contains, same⟩ := typed.stored_type
  cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact same ▸ typed

/-- Original assignment typing supplies the actual writable root and raw RHS type.
The bare path keeps this fact on the declared binder used by the compiler. -/
theorem assignment_facts {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp}
    {rhs : ExpressionId} {binder : TypedBinder}
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (targetType : binder.scheme.body = assignment.target.type)
    (bare : assignment.target.projections = [])
    (typed : SourceAssignmentHasType source context assignment operator rhs) :
    (∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
      SourceProjectionsHaveType source context actual.scheme.body assignment.target.projections assignment.target.type) ∧
    (∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
      WritableLocal context assignment.target.root actual.scheme.body) ∧
    ExpressionHasType source context rhs assignment.target.type ∧
    (operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false) := by
  have original : ∃ type, SourcePlaceHasType source context assignment.target type ∧
      ExpressionHasType source context rhs type ∧ (operator = .equal ∨ type = .word) := by
    cases typed with
    | equal place value _ => exact ⟨_, place, value, .inl rfl⟩
    | wordCompound _ place value _ => exact ⟨_, place, value, .inr rfl⟩
  obtain ⟨type, place, value, profile⟩ := original
  cases place with
  | intro writable projections target =>
      refine ⟨?_, ?_, target.symm ▸ value, ?_⟩
      · intro actual actualFound
        cases Except.ok.inj (declaration.symm.trans actualFound)
        rw [targetType, bare]
        exact .nil _
      · intro actual actualFound
        cases Except.ok.inj (declaration.symm.trans actualFound)
        rw [bare] at projections
        cases projections
        exact targetType.symm ▸ target.symm ▸ writable
      · rcases profile with equal | word
        · exact .inl equal
        · exact .inr (.inl (by rw [target, word]; rfl))

/-- Mapping paths derive the writable declaration from the original key types. -/
theorem projected_assignment_facts {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp}
    {rhs : ExpressionId} {binder : TypedBinder}
    (unique : NodeOccurrencesUnique source)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (route : AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type)
    (typed : SourceAssignmentHasType source context assignment operator rhs) :
    (∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
      SourceProjectionsHaveType source context actual.scheme.body assignment.target.projections assignment.target.type) ∧
    (∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
      WritableLocal context assignment.target.root actual.scheme.body) ∧
    ExpressionHasType source context rhs assignment.target.type ∧
    (operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false) := by
  have original : ∃ type, SourcePlaceHasType source context assignment.target type ∧
      ExpressionHasType source context rhs type ∧ (operator = .equal ∨ type = .word) := by
    cases typed with
    | equal place value _ => exact ⟨_, place, value, .inl rfl⟩
    | wordCompound _ place value _ => exact ⟨_, place, value, .inr rfl⟩
  obtain ⟨type, place, value, profile⟩ := original
  cases place with
  | intro writable projections target =>
      have atLeaf := target.symm ▸ projections
      have same := route.root_type unique atLeaf
      refine ⟨?_, ?_, target.symm ▸ value, ?_⟩
      · intro actual actualFound
        cases Except.ok.inj (declaration.symm.trans actualFound)
        exact same ▸ atLeaf
      · intro actual actualFound
        cases Except.ok.inj (declaration.symm.trans actualFound)
        exact same ▸ writable
      · rcases profile with equal | word
        · exact .inl equal
        · exact .inr (.inl (by rw [target, word]; rfl))

/-- Actual original unary typing supplies the declared writable root. -/
theorem bitNot_facts {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {binder : TypedBinder}
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (targetType : binder.scheme.body = assignment.target.type)
    (bare : assignment.target.projections = [])
    (typed : SourceBitNotAssignmentValid source context assignment) :
    ∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
      WritableLocal context assignment.target.root actual.scheme.body := by
  cases typed with
  | intro place _ =>
    cases place with
    | intro writable projections target =>
      intro actual actualFound
      cases Except.ok.inj (declaration.symm.trans actualFound)
      rw [bare] at projections
      cases projections
      exact targetType.symm ▸ target.symm ▸ writable

/-- Original unary typing and the accepted mapping route identify the declared root. -/
theorem projected_bitNot_facts {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {binder : TypedBinder}
    (unique : NodeOccurrencesUnique source)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (route : AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type)
    (typed : SourceBitNotAssignmentValid source context assignment) :
    (∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
      SourceProjectionsHaveType source context actual.scheme.body assignment.target.projections assignment.target.type) ∧
    (∀ actual, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok actual →
      WritableLocal context assignment.target.root actual.scheme.body) := by
  cases typed with
  | intro place _ =>
    cases place with
    | intro writable projections target =>
      have atLeaf := target.symm ▸ projections
      have same := route.root_type unique atLeaf
      constructor
      · intro actual actualFound
        cases Except.ok.inj (declaration.symm.trans actualFound)
        exact same ▸ atLeaf
      · intro actual actualFound
        cases Except.ok.inj (declaration.symm.trans actualFound)
        exact same ▸ writable

theorem Scan.syntax {source approved items} (scan : Scan source approved items)
    (unique : NodeOccurrencesUnique source) {control : ControlContext}
    {context final : SourceSemantics.Context}
    (typed : ForItemsHaveType source control context items final) :
    GenericForHeader.PreparedSyntax source approved context items := by
  induction scan generalizing context final with
  | nil => exact .nil
  | absent declaration monomorphic ordinary remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | letUninitialized _ _ extended => exact .uninitialized declaration monomorphic extended ordinary (ih tail)
  | initialized declaration monomorphic ordinary found valueType value remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | letInitialized actual _ _ extended =>
          exact .initialized declaration monomorphic extended ordinary found valueType
            (expression_at unique found actual) value (ih tail)
        | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly monomorphic)
  | discard found value remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | expression actual => exact .discard found (expression_at unique found actual) value (ih tail)
  | assign declaration targetType profile bare rhsFound rhsType value remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | assignValue assignment =>
          obtain ⟨sourceTyped, writable, rightTyped, numeric⟩ :=
            assignment_facts declaration targetType bare assignment
          apply GenericForHeader.PreparedSyntax.assign sourceTyped writable rightTyped numeric
          · intro child member
            simp only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
            subst child
            exact ⟨value, _, rhsFound, expression_at unique rhsFound rightTyped⟩
          · exact ih tail

  | assignProjected declaration route profile projected keys rhsFound rhsType value remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | assignValue assignment =>
          obtain ⟨sourceTyped, writable, rightTyped, numeric⟩ :=
            projected_assignment_facts unique declaration route assignment
          apply GenericForHeader.PreparedSyntax.assign sourceTyped writable rightTyped numeric
          · intro child member
            rcases List.mem_cons.mp member with equal | member
            · subst child
              exact ⟨value, _, rhsFound, expression_at unique rhsFound rightTyped⟩
            · obtain ⟨node, found, typed⟩ := route.key_typed unique (sourceTyped _ declaration) member
              exact ⟨keys child member, node, found, typed⟩
          · exact ih tail

  | bitNotProjected declaration route profile projected keys remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | assignBitNot assignment =>
          obtain ⟨sourceTyped, writable⟩ := projected_bitNot_facts unique declaration route assignment
          apply GenericForHeader.PreparedSyntax.bitNotProjected sourceTyped writable projected (.inl (by rw [profile]; rfl))
          · intro child member
            obtain ⟨node, found, typed⟩ := route.key_typed unique (sourceTyped _ declaration) member
            exact ⟨keys child member, node, found, typed⟩
          · exact ih tail

  | bitNot declaration targetType profile bare remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | assignBitNot assignment =>
          exact .bitNot (bitNot_facts declaration targetType bare assignment) bare
            (.inl (by rw [profile]; rfl)) (ih tail)


private theorem binder_final {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binder : TypedBinder} (first : BinderExtends owner context binder left)
    (second : BinderExtends owner context binder right) : left = right := by
  cases first
  cases second
  rfl

/-- A header's actual typing fixes the context at its continuation. -/
theorem initializers {source : TypedSource} {approved : ExpressionId → Prop}
    {context final : SourceSemantics.Context} {control : ControlContext}
    {items : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
    {body : List StatementId} {expected : TypeSystem.Ty}
    (tree : GenericForHeader.PreparedSyntax source approved context items)
    (typed : ForItemsHaveType source control context items final)
    (next : GenericImperativeMatch.PreparedSyntax source approved final (.initializers [] condition post body) expected) :
    GenericImperativeMatch.PreparedSyntax source approved context (.initializers items condition post body) expected := by
  induction tree generalizing final with
  | nil => cases typed; exact next
  | uninitialized declaration monomorphic extended ordinary remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | letUninitialized _ _ other =>
          have same := binder_final extended other
          subst_vars
          exact .initializerUninitialized declaration monomorphic extended ordinary (ih tail next)
  | initialized declaration monomorphic extended ordinary found sourceType child value remaining ih =>
      cases typed with
      | cons head tail =>
        cases head with
        | letInitialized _ _ _ other =>
          have same := binder_final extended other
          subst_vars
          exact .initializerInitialized declaration monomorphic extended ordinary found sourceType child value (ih tail next)
        | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly monomorphic)
  | discard found child value remaining ih =>
      cases typed with
      | cons head tail =>
        cases head
        exact .initializerDiscard found child value (ih tail next)
  | assign sourceTyped writable rightTyped profile children remaining ih =>
      cases typed with
      | cons head tail =>
        cases head
        exact .initializerAssign sourceTyped writable rightTyped profile children (ih tail next)
  | bitNotProjected sourceTyped writable projected profile children remaining ih =>
      cases typed with
      | cons head tail =>
        cases head
        exact .initializerBitNotProjected sourceTyped writable projected profile children (ih tail next)
  | bitNot writable bare profile remaining ih =>
      cases typed with
      | cons head tail =>
        cases head
        exact .initializerBitNot writable bare profile (ih tail next)

end Solcore.SourceSemantics.CoreLowering.ScopedSourceForItemsAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
/-! Finite original statement admission separates syntax from lexical typing.
The same scan yields the accepted body shape and recovers changing contexts
from independent Source statement typing, including loop control contexts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
open Core Frontend SourceInference

inductive Scan (source : TypedSource) (approved : ExpressionId → Prop)
    (expected : TypeSystem.Ty) : Bool → List StatementId → Prop where
  | nil {mode} (allowed : mode = false ∨ expected = .unit) : Scan source approved expected mode []
  | breaking {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .breakStmt) : Scan source approved expected mode (id :: rest)
  | continuing {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .continueStmt) : Scan source approved expected mode (id :: rest)
  | returnUnit {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none)
      (sourceType : node.type = .unit) (result : expected = .unit) :
      Scan source approved expected mode (id :: rest)
  | returning {mode id node expression expressionNode} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (sourceType : node.type = expected)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected) (value : approved expression) :
      Scan source approved expected mode (id :: rest)
  | tail {id node expression expressionNode}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (sourceType : node.type = expected)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected) (value : approved expression) :
      Scan source approved expected true [id]
  | absent {mode id node binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | initialized {mode id node binder expression expressionNode rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some expression))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = binder.scheme.body) (value : approved expression)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | discard {mode id node expression expressionNode semicolon rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (continuing : semicolon = true ∨ mode = false)
      (sourceType : node.type = if semicolon then .unit else expressionNode.type)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : approved expression) (remaining : Scan source approved expected mode rest) :
      Scan source approved expected mode (id :: rest)
  | block {mode id node body rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .block body)
      (inner : Scan source approved expected false body)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | conditional {mode id node condition conditionNode thenBody elseBody rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
      (sourceType : node.type = .unit ∨ node.type = expected)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool) (value : approved condition)
      (left : Scan source approved expected false thenBody)
      (right : Scan source approved expected false (elseBody.getD []))
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | whileLoop {mode id node condition conditionNode body rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition body)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool) (value : approved condition)
      (inner : Scan source approved expected false body)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | matching {mode id node resolution scrutineeNode rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (value : approved resolution.scrutinee)
      (hiddenOrdinary : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
      (armsOrdinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
        source.inputs.any (fun input => decide (input.id = binder)) = false)
      (arms : ∀ arm ∈ resolution.cases, Scan source approved expected false arm.body)
      (fallback : ∀ statements, resolution.defaultBody = some statements → Scan source approved expected false statements)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | forLoop {mode id node initializer condition conditionNode post body rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initializer condition post body)
      (sourceType : node.type = .unit)
      (initial : ScopedSourceForItemsAdmission.Scan source approved initializer)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool) (value : approved condition)
      (inner : Scan source approved expected false body)
      (after : ScopedSourceForItemsAdmission.Scan source approved post)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)
  | assign {mode id node assignment operator rhs rhsNode binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (targetType : binder.scheme.body = assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type) (value : approved rhs)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)

  | bitNotProjected {mode id node assignment binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (route : AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type)
      (profile : assignment.target.type = .word)
      (projected : assignment.target.projections ≠ [])
      (keys : ∀ key ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections, approved key)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)

  | assignProjected {mode id node assignment operator rhs rhsNode binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (route : AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (projected : assignment.target.projections ≠ [])
      (keys : ∀ key ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections, approved key)
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type) (value : approved rhs)
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)

  | bitNot {mode id node assignment binder rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (targetType : binder.scheme.body = assignment.target.type)
      (profile : assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (remaining : Scan source approved expected mode rest) : Scan source approved expected mode (id :: rest)

  | terminalBlock {mode id node body rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .block body)
      (sourceType : node.type = expected)
      (inner : Scan source approved expected false body)
      (stops : ScopedSourceBodyStopping.ReturnStopped source body)
      (remaining : CallableIndexedOwnedPreparedStagedBranchingTree.Shape source mode rest) :
      Scan source approved expected mode (id :: rest)
  | terminalConditional {mode id node condition conditionNode leftBody rightBody rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition leftBody (some rightBody))
      (sourceType : node.type = expected)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool) (value : approved condition)
      (left : Scan source approved expected false leftBody)
      (right : Scan source approved expected false rightBody)
      (first : ScopedSourceBodyStopping.ReturnStopped source leftBody)
      (second : ScopedSourceBodyStopping.ReturnStopped source rightBody)
      (remaining : CallableIndexedOwnedPreparedStagedBranchingTree.Shape source mode rest) :
      Scan source approved expected mode (id :: rest)
  | terminalMatch {mode id node resolution scrutineeNode defaultBody rest}
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (sourceType : node.type = expected)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (value : approved resolution.scrutinee)
      (hiddenOrdinary : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
      (armsOrdinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
        source.inputs.any (fun input => decide (input.id = binder)) = false)
      (arms : ∀ arm ∈ resolution.cases, Scan source approved expected false arm.body)
      (fallback : ∀ statements, resolution.defaultBody = some statements → Scan source approved expected false statements)
      (present : resolution.defaultBody = some defaultBody)
      (stoppedArms : ∀ arm ∈ resolution.cases, ScopedSourceBodyStopping.ReturnStopped source arm.body)
      (stoppedDefault : ScopedSourceBodyStopping.ReturnStopped source defaultBody)
      (remaining : CallableIndexedOwnedPreparedStagedBranchingTree.Shape source mode rest) :
      Scan source approved expected mode (id :: rest)

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact original

private theorem expression_at {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) : ExpressionHasType source context id node.type := by
  obtain ⟨original, contains, same⟩ := typed.stored_type
  cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact same ▸ typed

theorem Scan.shape {source approved expected mode statements}
    (scan : Scan source approved expected mode statements) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape source mode statements := by
  induction scan with
  | nil => exact .nil
  | breaking rest found form => exact .breaking rest found form
  | continuing rest found form => exact .continuing rest found form
  | returnUnit rest found form => exact .returnUnit rest found form
  | returning rest found form => exact .returnValue rest found form
  | tail found form => exact .tail found form
  | absent found form _ _ _ _ ih => exact .absent found form ih
  | initialized found form _ _ _ _ _ _ _ ih => exact .initialized found form ih
  | discard found form continuing _ _ _ _ ih => exact .discard found form continuing ih
  | block found form _ _ inner remaining => exact .block found form inner remaining
  | conditional found form _ _ _ _ _ _ _ left right remaining => exact .conditional found form left right remaining
  | whileLoop found form _ _ _ _ _ inner remaining => exact .whileLoop found form inner remaining
  | assign found form _ _ profile bare _ _ _ _ ih => exact .assign found form profile bare ih
  | assignProjected found form _ _ profile projected _ _ _ _ _ ih => exact .assignProjected found form profile projected ih
  | bitNotProjected found form _ _ profile projected _ _ ih => exact .bitNotProjected found form profile projected ih
  | bitNot found form _ _ profile bare _ ih => exact .bitNot found form profile bare ih
  | matching found form _ _ _ _ _ _ _ arms fallback remaining =>
      exact .matchWith found form arms fallback remaining
  | forLoop found form _ initial _ _ _ _ after _ inner remaining =>
      exact .forLoop found form initial.shape after.shape inner remaining
  | terminalBlock found form _ _ _ remaining inner => exact .block found form inner remaining
  | terminalConditional found form _ _ _ _ _ _ _ _ remaining left right =>
      exact .conditional found form left right remaining
  | terminalMatch found form _ _ _ _ _ _ _ _ _ _ remaining arms fallback =>
      exact .matchWith found form arms fallback remaining

/-- Changing loop depth is harmless because each recursive body retains the
same actual return type. All writes come from the original assignment typing. -/
theorem Scan.syntax {source approved expected mode statements}
    (scan : Scan source approved expected mode statements) (unique : NodeOccurrencesUnique source)
    {control : ControlContext} (result : control.returnType = expected)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    GenericImperativeMatch.PreparedSyntax source approved context (.statements mode statements) expected := by
  induction scan generalizing control context final facts with
  | nil allowed => exact .body (.nil allowed)
  | breaking rest found form => exact .breaking found form
  | continuing rest found form => exact .continuing found form
  | returnUnit rest found form sourceType expectedUnit =>
      subst expected
      exact .body (.returnUnit rest found form sourceType)
  | returning rest found form sourceType expressionFound valueType value =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | returnValue actual =>
        exact .body (.returnValue rest found form sourceType expressionFound valueType
          (by simpa only [result, valueType] using actual) value)
  | tail found form sourceType expressionFound valueType value =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | expressionValue actual =>
        exact .body (.tail found form sourceType expressionFound valueType (expression_at unique expressionFound actual) value)
  | absent found form declaration monomorphic ordinary _ ih =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letUninitialized _ extended => exact .uninitialized found form declaration monomorphic extended ordinary (ih result tail)
  | initialized found form declaration monomorphic ordinary expressionFound valueType value _ ih =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letInitialized actual _ extended =>
        exact .initialized found form declaration monomorphic extended ordinary expressionFound valueType
          (by simpa only [valueType] using actual) value (ih result tail)
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly monomorphic)
  | discard found form continuing sourceType expressionFound value _ ih =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | expressionValue actual | expressionDiscard actual =>
        exact .discard found form (by rcases continuing with same | same <;> simp_all) sourceType expressionFound (expression_at unique expressionFound actual) value (ih result tail)
  | block found form _ _ inner remaining =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | block actual => exact .scopedBlock found form (inner result actual) (remaining result tail)
  | conditional found form sourceType conditionFound conditionType value _ _ _ left right remaining =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | ifWithoutElse condition actual =>
        exact .ifThen found form sourceType conditionFound conditionType
          (by simpa only [conditionType] using condition) value (left result actual)
          (right result (.nil _ _)) (remaining result tail)
      | ifWithElse condition first second =>
        exact .ifThen found form sourceType conditionFound conditionType
          (by simpa only [conditionType] using condition) value (left result first)
          (right result second) (remaining result tail)
  | whileLoop found form conditionFound conditionType value _ _ inner remaining =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | whileLoop condition actual =>
        exact .whileLoop found form conditionFound conditionType
          (by simpa only [conditionType] using condition) value (inner (control := control.enterLoop) result actual) (remaining result tail)
  | assign found form declaration targetType profile bare rhsFound rhsType value _ ih =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | assignValue assignment =>
        obtain ⟨sourceTyped, writable, rightTyped, numeric⟩ :=
          ScopedSourceForItemsAdmission.assignment_facts declaration targetType bare assignment
        apply GenericImperativeMatch.PreparedSyntax.assign found form sourceTyped writable rightTyped numeric
        · intro child member
          simp only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
          subst child
          exact ⟨value, _, rhsFound, expression_at unique rhsFound rightTyped⟩
        · exact ih result tail

  | assignProjected found form declaration route profile projected keys rhsFound rhsType value _ ih =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | assignValue assignment =>
        obtain ⟨sourceTyped, writable, rightTyped, numeric⟩ :=
          ScopedSourceForItemsAdmission.projected_assignment_facts unique declaration route assignment
        apply GenericImperativeMatch.PreparedSyntax.assign found form sourceTyped writable rightTyped numeric
        · intro child member
          rcases List.mem_cons.mp member with equal | member
          · subst child
            exact ⟨value, _, rhsFound, expression_at unique rhsFound rightTyped⟩
          · obtain ⟨node, found, typed⟩ := route.key_typed unique (sourceTyped _ declaration) member
            exact ⟨keys child member, node, found, typed⟩
        · exact ih result tail

  | bitNotProjected found form declaration route profile projected keys _ ih =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | assignBitNot assignment =>
        obtain ⟨sourceTyped, writable⟩ := ScopedSourceForItemsAdmission.projected_bitNot_facts unique declaration route assignment
        apply GenericImperativeMatch.PreparedSyntax.bitNotProjected found form sourceTyped writable projected (.inl (by rw [profile]; rfl))
        · intro child member
          obtain ⟨node, found, typed⟩ := route.key_typed unique (sourceTyped _ declaration) member
          exact ⟨keys child member, node, found, typed⟩
        · exact ih result tail

  | bitNot found form declaration targetType profile bare _ ih =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | assignBitNot assignment =>
        exact .bitNot found form
          (ScopedSourceForItemsAdmission.bitNot_facts declaration targetType bare assignment)
          bare (.inl (by rw [profile]; rfl)) (ih result tail)

  | matching found form scrutineeFound value hiddenOrdinary armsOrdinary _ _ _ arms fallback remaining =>
      obtain ⟨middle, headFacts, tailFacts, head, tail⟩ := head_tail typed
      obtain ⟨sameContext, caseFacts, scrutineeTyped, casesTyped, defaultTyped⟩ :=
        ScopedSourceMatchAdmission.statement_sites unique found form scrutineeFound head
      subst middle
      have sourceType := ScopedSourceMatchAdmission.statement_type unique found form head
      rw [result] at sourceType
      apply GenericImperativeMatch.PreparedSyntax.matchWith found form sourceType scrutineeFound scrutineeTyped
        value casesTyped defaultTyped hiddenOrdinary armsOrdinary
      · intro request childContext selected
        obtain ⟨last, childFacts, childTyped⟩ :=
          ScopedSourceMatchAdmission.request_typing casesTyped defaultTyped selected
        cases selected with
        | arm member same _ _ =>
          rw [same] at childTyped ⊢
          exact arms _ member result childTyped
        | default same => exact fallback _ same result childTyped
      · exact remaining result tail

  | forLoop found form sourceType initial conditionFound conditionType value _ after _ inner remaining =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | forLoop initTyped condition body postTyped =>
        exact .forLoop found form sourceType
          (ScopedSourceForItemsAdmission.initializers (initial.syntax unique initTyped) initTyped
            (.initializersDone conditionFound conditionType (expression_at unique conditionFound condition) value
              (inner (control := control.enterLoop) result body) (after.syntax unique postTyped)))
          (remaining result tail)


  | terminalBlock found form sourceType _ stops _ inner =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | block body =>
          exact .terminalBlock unique found form sourceType
            (inner result body) (stops.stopped unique body)
  | terminalConditional found form sourceType conditionFound conditionType value _ _ first second _ left right =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | ifWithElse condition firstTyped secondTyped =>
          exact .terminalIf unique found form sourceType conditionFound conditionType
            (by simpa only [conditionType] using condition) value
            (left result firstTyped) (right result secondTyped)
            (first.stopped unique firstTyped) (second.stopped unique secondTyped)
  | terminalMatch found form sourceType scrutineeFound value hiddenOrdinary armsOrdinary _ _ present stoppedArms stoppedDefault _ arms fallback =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      obtain ⟨_, caseFacts, scrutineeTyped, casesTyped, defaultTyped⟩ :=
        ScopedSourceMatchAdmission.statement_sites unique found form scrutineeFound head
      apply GenericImperativeMatch.PreparedSyntax.terminalMatch unique found form (.inr sourceType)
        scrutineeFound scrutineeTyped value casesTyped defaultTyped hiddenOrdinary armsOrdinary
      · intro request childContext selected
        obtain ⟨last, childFacts, childTyped⟩ :=
          ScopedSourceMatchAdmission.request_typing casesTyped defaultTyped selected
        cases selected with
        | arm member same _ _ =>
          rw [same] at childTyped ⊢
          exact arms _ member result childTyped
        | default same => exact fallback _ same result childTyped
      · exact ScopedSourceBodyStopping.ReturnStopped.match_default stoppedArms stoppedDefault
          unique found form present head

/-- The expression checker is a data-only parameter; the finite traversal uses
its proof receipts without evaluating any selected semantic inventory. -/
def scan? (source : TypedSource) {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) (expected : TypeSystem.Ty) :
    (fuel : Nat) → (mode : Bool) → (statements : List StatementId) →
      Option (PLift (Scan source approved expected mode statements))
  | 0, _, _ => none
  | fuel + 1, mode, [] =>
      if allowed : mode = false ∨ expected = .unit then some ⟨.nil allowed⟩ else none
  | fuel + 1, mode, id :: rest =>
    match found : source.lookupStatement? id with
    | none => none
    | some node =>
      match form : node.form with
      | .returnStmt none =>
        if result : expected = .unit then
          if sourceType : node.type = .unit then some ⟨.returnUnit rest found form sourceType result⟩ else none
        else none
      | .returnStmt (some value) =>
        if sourceType : node.type = expected then
          match valueFound : source.lookupExpression? value with
          | none => none
          | some valueNode =>
            if valueType : valueNode.type = expected then do
              let ⟨approved⟩ ← expression value
              pure ⟨.returning rest found form sourceType valueFound valueType approved⟩
            else none
        else none
      | .expression value semicolon =>
        match valueFound : source.lookupExpression? value with
        | none => none
        | some valueNode =>
          if continuing : semicolon = true ∨ mode = false then
            if sourceType : node.type = if semicolon then .unit else valueNode.type then do
              let ⟨approved⟩ ← expression value
              let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
              pure ⟨.discard found form continuing sourceType valueFound approved remaining⟩
            else none
          else
            match semicolonEq : semicolon, modeEq : mode, restEq : rest with
            | false, true, [] =>
              if sourceType : node.type = expected then
                if valueType : valueNode.type = expected then do
                  let ⟨approved⟩ ← expression value
                  pure ⟨.tail found (by simpa only [semicolonEq] using form) sourceType valueFound valueType approved⟩
                else none
              else none
            | _, _, _ => none
      | .letDecl binder initializer =>
        if monomorphic : binder.scheme.quantified = [] then
          if ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false then
            match declaration : SourceCoreDataPlaces.rootBinder source binder.id with
            | .error _ => none
            | .ok actual =>
              if same : actual = binder then
                match initializer with
                | none => do
                  let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
                  pure ⟨.absent found form (by simpa only [same] using declaration) monomorphic ordinary remaining⟩
                | some value =>
                  match valueFound : source.lookupExpression? value with
                  | none => none
                  | some valueNode =>
                    if valueType : valueNode.type = binder.scheme.body then do
                      let ⟨approved⟩ ← expression value
                      let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
                      pure ⟨.initialized found form (by simpa only [same] using declaration)
                        monomorphic ordinary valueFound valueType approved remaining⟩
                    else none
              else none
          else none
        else none
      | .block body => do
        let ⟨inner⟩ ← scan? source expression expected fuel false body
        let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
        pure ⟨.block found form inner remaining⟩
      | .ifThen condition thenBody elseBody =>
        if sourceType : node.type = .unit ∨ node.type = expected then
          match conditionFound : source.lookupExpression? condition with
          | none => none
          | some conditionNode =>
            if conditionType : conditionNode.type = .bool then do
              let ⟨approved⟩ ← expression condition
              let ⟨left⟩ ← scan? source expression expected fuel false thenBody
              let ⟨right⟩ ← scan? source expression expected fuel false (elseBody.getD [])
              let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
              pure ⟨.conditional found form sourceType conditionFound conditionType approved left right remaining⟩
            else none
        else none
      | .whileLoop condition body =>
        match conditionFound : source.lookupExpression? condition with
        | none => none
        | some conditionNode =>
          if conditionType : conditionNode.type = .bool then do
            let ⟨approved⟩ ← expression condition
            let ⟨inner⟩ ← scan? source expression expected fuel false body
            let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
            pure ⟨.whileLoop found form conditionFound conditionType approved inner remaining⟩
          else none
      | .assignValue assignment operator rhs =>
        if profile : operator = .equal ∨ assignment.target.type = .word then
          if bare : assignment.target.projections = [] then
            match declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root with
            | .error _ => none
            | .ok binder =>
              if targetType : binder.scheme.body = assignment.target.type then
                match rhsFound : source.lookupExpression? rhs with
                | none => none
                | some rhsNode =>
                  if rhsType : rhsNode.type = assignment.target.type then do
                    let ⟨approved⟩ ← expression rhs
                    let ⟨remaining⟩ ← scan? source expression expected fuel mode rest
                    pure ⟨.assign found form declaration targetType profile bare rhsFound rhsType approved remaining⟩
                  else none
              else none
          else none
        else none
      | _ => none

end Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyCompletionTyping
/-! Original control summaries identify a body's raw result type. Values at the
end of a nested statement sequence remain discarded by the actual body mode. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
open Frontend SourceInference

private def ResultCompatible (expected actual : TypeSystem.Ty) (mode : Bool)
    (summary : ControlSummary) : Prop :=
  (summary.mayReturn = true → actual = expected) ∧
    (mode = true → ∀ type, summary.fallthrough = some type → type = expected)

private theorem sequence_compatible {expected actual : TypeSystem.Ty} {mode : Bool}
    {head tail : ControlSummary}
    (first : ResultCompatible expected actual false head)
    (remaining : ResultCompatible expected actual mode tail) :
    ResultCompatible expected actual mode (head.sequence tail) := by
  constructor
  · intro returned
    simp only [ControlSummary.sequence, Bool.or_eq_true, Bool.and_eq_true] at returned
    exact returned.elim first.1 (fun h => remaining.1 h.2)
  · intro returning type fallen
    simp only [ControlSummary.sequence] at fallen
    split at fallen
    · exact remaining.2 returning type fallen
    · cases fallen

private theorem head_tail_control {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts ∧
      facts.control = if rest.isEmpty then headFacts.control else headFacts.control.sequence tailFacts.control := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _, rfl⟩
  | cons head tail => exact ⟨_, _, _, head, tail, rfl⟩

private theorem form_control_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementControlFormTyping source control context node.form facts := by
  obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.controlFormTyping typed
  cases Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact formTyped

private theorem nil_expected {source approved expected mode statements}
    (scan : Scan source approved expected mode statements) (returning : mode = true)
    (empty : statements = []) : expected = .unit := by
  subst statements
  cases scan with
  | nil allowed => exact allowed.resolve_left (by simp [returning])

private theorem prefix_compatible {source approved expected mode statements}
    (scan : Scan source approved expected mode statements)
    {actual : TypeSystem.Ty} {head tail : ControlSummary}
    (first : ResultCompatible expected actual false head)
    (unitFallthrough : ∀ type, head.fallthrough = some type → type = .unit)
    (remaining : ResultCompatible expected actual mode tail) :
    ResultCompatible expected actual mode
      (if statements.isEmpty then head else head.sequence tail) := by
  split
  · rename_i empty
    constructor
    · exact first.1
    · intro returning type fallen
      exact (unitFallthrough type fallen).trans (nil_expected scan returning (List.isEmpty_iff.mp empty)).symm
  · exact sequence_compatible first remaining

private theorem terminal_compatible {expected actual : TypeSystem.Ty} {mode : Bool}
    {statements : List StatementId} {head tail : ControlSummary}
    (stopped : head.fallthrough = none)
    (returned : head.mayReturn = true → actual = expected) :
    ResultCompatible expected actual mode
      (if statements.isEmpty then head else head.sequence tail) := by
  have whole : (if statements.isEmpty then head else head.sequence tail) = head := by
    split
    · rfl
    · cases head
      simp_all [ControlSummary.sequence, ControlSummary.canFallthrough]
  rw [whole]
  exact ⟨returned, fun _ _ impossible => by rw [stopped] at impossible; cases impossible⟩

private theorem ordinary_return_compatible {expected actual type : TypeSystem.Ty} :
    ResultCompatible expected actual false (.ordinary type) := by
  simp [ResultCompatible, ControlSummary.ordinary]

private theorem branches_return_compatible {expected actual : TypeSystem.Ty}
    {left right : ControlSummary}
    (first : ResultCompatible expected actual false left)
    (second : ResultCompatible expected actual false right) :
    ResultCompatible expected actual false (left.branches right) := by
  constructor
  · intro returned
    simp only [ControlSummary.branches, Bool.or_eq_true] at returned
    exact returned.elim first.1 second.1
  · simp

private theorem erase_return_compatible {expected actual : TypeSystem.Ty}
    {summary : ControlSummary} (compatible : ResultCompatible expected actual false summary) :
    ResultCompatible expected actual false summary.eraseValue := by
  exact ⟨compatible.1, by simp⟩

private theorem erased_unit {summary : ControlSummary} {type : TypeSystem.Ty}
    (fallen : summary.eraseValue.fallthrough = some type) : type = .unit := by
  cases summary.fallthrough <;> simp_all [ControlSummary.eraseValue]

private theorem branches_unit {left right : ControlSummary} {type : TypeSystem.Ty}
    (fallen : (left.branches right).fallthrough = some type) : type = .unit := by
  simp only [ControlSummary.branches] at fallen
  split at fallen
  · exact (Option.some.inj fallen).symm
  · cases fallen

private theorem returned_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : Option ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt expression)
    (typed : StatementHasType source control context id final facts) : node.type = control.returnType := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

private theorem expression_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression false)
    (typed : StatementHasType source control context id final facts) :
    facts.control = .ordinary node.type := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all

private theorem statement_annotation {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) : node.type = facts.type := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    assumption

theorem stopped_statement_result {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (stopped : ScopedSourceBodyStopping.ReturnStopped source [id])
    (typed : StatementHasType source control context id final facts) : node.type = control.returnType := by
  obtain ⟨_, returned, same⟩ := stopped.facts unique (StatementsHaveType.singleton typed)
  simp only [BodyFacts.singleton] at returned same
  simp only [returned, Bool.true_or, ↓reduceIte] at same
  exact (statement_annotation unique found typed).trans same

private theorem stopped_compatible {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    {expected : TypeSystem.Ty} {mode : Bool} {rest : List StatementId} {tail : ControlSummary}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (sourceType : node.type = expected)
    (stopped : ScopedSourceBodyStopping.ReturnStopped source [id])
    (typed : StatementHasType source control context id final facts) :
    ResultCompatible expected control.returnType mode
      (if rest.isEmpty then facts.control else facts.control.sequence tail) := by
  obtain ⟨stops, returned, same⟩ := stopped.facts unique (StatementsHaveType.singleton typed)
  simp only [BodyFacts.singleton] at returned same
  simp only [returned, Bool.true_or, ↓reduceIte] at same
  have original := statement_annotation unique found typed
  have result : control.returnType = expected := same.symm.trans (original.symm.trans sourceType)
  exact terminal_compatible stops.no_fallthrough (fun _ => result)

private theorem case_controls {source : TypedSource} {control : ControlContext}
    {context : SourceSemantics.Context} {type expected : TypeSystem.Ty}
    {cases : List TypedMatchCase} {facts : List BodyFacts}
    (typed : MatchCasesHaveType source control context type cases facts)
    (arms : ∀ arm ∈ cases, ∀ child final bodyFacts,
      StatementsHaveType source control child arm.body final bodyFacts →
      ResultCompatible expected control.returnType false bodyFacts.control) :
    ∀ bodyFacts ∈ facts, ResultCompatible expected control.returnType false bodyFacts.control := by
  induction cases generalizing facts with
  | nil => cases typed; simp
  | cons first rest ih =>
    cases typed with
    | cons head tail =>
      intro bodyFacts member
      rcases List.mem_cons.mp member with rfl | member
      · cases head with
        | intro _ _ body => exact arms _ (by simp) _ _ _ body
      · exact ih tail (fun arm member => arms arm (List.mem_cons_of_mem _ member)) bodyFacts member

private theorem merged_compatible {expected actual : TypeSystem.Ty}
    {facts : List BodyFacts} {fallback : Option BodyFacts} {summary : ControlSummary}
    (arms : ∀ body ∈ facts, ResultCompatible expected actual false body.control)
    (default : ∀ body, fallback = some body → ResultCompatible expected actual false body.control)
    (merged : mergeBodyControls facts fallback = some summary) :
    ResultCompatible expected actual false summary := by
  induction facts generalizing summary with
  | nil =>
    cases fallback with
    | none => simp [mergeBodyControls] at merged
    | some body =>
      simp only [mergeBodyControls, Option.some.injEq] at merged
      exact merged ▸ default body rfl
  | cons head tail ih =>
    have first := arms head (by simp)
    cases selected : mergeBodyControls tail fallback with
    | none =>
      simp only [mergeBodyControls, selected, Option.some.injEq] at merged
      exact merged ▸ first
    | some next =>
      simp only [mergeBodyControls, selected, Option.some.injEq] at merged
      exact merged ▸ branches_return_compatible first (ih (fun body member => arms body (List.mem_cons_of_mem _ member)) selected)

/-- Scanned statements retain the raw type of every reachable return. Only a
function-mode sequence treats its final ordinary value as a body result. -/
private theorem Scan.control_compatible {source approved expected mode statements}
    (scan : Scan source approved expected mode statements) (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) :
    ResultCompatible expected control.returnType mode facts.control := by
  induction scan generalizing control context final facts with
  | nil allowed =>
    cases typed
    constructor
    · simp [BodyFacts.empty, ControlSummary.ordinary]
    · intro returning type fallen
      have same := allowed.resolve_left (by simp [returning])
      simpa [BodyFacts.empty, ControlSummary.ordinary, same] using fallen.symm
  | breaking rest found form =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact terminal_compatible rfl (by simp [ControlSummary.breaking])
  | continuing rest found form =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact terminal_compatible rfl (by simp [ControlSummary.continuing])
  | returnUnit rest found form sourceType result =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    have resultEq := (returned_annotation unique found form head).symm.trans (sourceType.trans result.symm)
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact terminal_compatible rfl (fun _ => resultEq)
  | returning rest found form sourceType =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    have resultEq := (returned_annotation unique found form head).symm.trans sourceType
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact terminal_compatible rfl (fun _ => resultEq)
  | tail found form sourceType =>
    cases typed with
    | singleton head =>
      have same := expression_annotation unique found form head
      simp only [BodyFacts.singleton]
      rw [same, sourceType]
      exact ⟨by simp [ControlSummary.ordinary], fun _ _ fallen => (Option.some.inj fallen).symm⟩
  | absent found form declaration monomorphic ordinary remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact prefix_compatible remaining ordinary_return_compatible
      (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)
  | initialized found form declaration monomorphic ordinary expressionFound valueType value remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact prefix_compatible remaining ordinary_return_compatible
      (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)
  | discard found form continuing sourceType expressionFound value remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original with
    | expressionValue actual =>
      have modeFalse := continuing.resolve_left (by decide)
      rw [same, modeFalse]
      split
      · exact ordinary_return_compatible
      · exact sequence_compatible ordinary_return_compatible (modeFalse ▸ ih tail)
    | expressionDiscard actual =>
      rw [same]
      exact prefix_compatible remaining ordinary_return_compatible
        (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)
  | block found form body remaining inner tailIH =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original with
    | block bodyTyped =>
      rw [same]
      exact prefix_compatible remaining (erase_return_compatible (inner bodyTyped))
        (fun _ => erased_unit) (tailIH tail)
  | conditional found form sourceType conditionFound conditionType value left right remaining leftIH rightIH tailIH =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original with
    | ifWithoutElse condition thenTyped =>
      rw [same]
      exact prefix_compatible remaining
        (branches_return_compatible (leftIH thenTyped) ordinary_return_compatible)
        (fun _ => branches_unit) (tailIH tail)
    | ifWithElse condition thenTyped elseTyped =>
      rw [same]
      exact prefix_compatible remaining
        (branches_return_compatible (leftIH thenTyped) (rightIH elseTyped))
        (fun _ => branches_unit) (tailIH tail)
  | whileLoop found form conditionFound conditionType value body remaining inner tailIH =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    cases head
    all_goals
      have nodeEq := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
      cases nodeEq
      simp_all only [reduceCtorEq]
    cases form
    apply prefix_compatible remaining _ (fun _ fallen => (Option.some.inj fallen).symm) (tailIH tail)
    exact ⟨(inner (control := control.enterLoop) (by assumption)).1, by simp⟩
  | matching found form scrutineeFound value hiddenOrdinary armsOrdinary arms fallback remaining armsIH fallbackIH tailIH =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original with
    | matchWithoutDefault absent scrutinee casesTyped exhaustive merged =>
      rw [same]
      apply prefix_compatible remaining _ (fun _ => erased_unit) (tailIH tail)
      apply erase_return_compatible
      exact merged_compatible (case_controls casesTyped (fun arm member _ _ _ typed => armsIH arm member typed))
        (fun _ impossible => by cases impossible) merged
    | matchWithDefault present scrutinee casesTyped defaultTyped merged =>
      rw [same]
      apply prefix_compatible remaining _ (fun _ => erased_unit) (tailIH tail)
      apply erase_return_compatible
      exact merged_compatible (case_controls casesTyped (fun arm member _ _ _ typed => armsIH arm member typed))
        (fun _ same => by cases same; exact fallbackIH _ present defaultTyped) merged
  | forLoop found form sourceType initial conditionFound conditionType value body after remaining inner tailIH =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    cases head
    all_goals
      have nodeEq := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
      cases nodeEq
      simp_all only [reduceCtorEq]
    cases form
    apply prefix_compatible remaining _ (fun _ fallen => (Option.some.inj fallen).symm) (tailIH tail)
    exact ⟨(inner (control := control.enterLoop) (by assumption)).1, by simp⟩
  | assign found form declaration targetType profile bare rhsFound rhsType value remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact prefix_compatible remaining ordinary_return_compatible
      (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)
  | assignProjected found form declaration route profile projected keys rhsFound rhsType value remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact prefix_compatible remaining ordinary_return_compatible
      (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)

  | bitNot found form declaration targetType profile bare remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact prefix_compatible remaining ordinary_return_compatible
      (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)

  | bitNotProjected found form declaration route profile projected keys remaining ih =>
    obtain ⟨_, _, _, head, tail, same⟩ := head_tail_control typed
    have original := form_control_at unique found head
    rw [form] at original
    cases original
    rw [same]
    exact prefix_compatible remaining ordinary_return_compatible
      (fun _ fallen => (Option.some.inj fallen).symm) (ih tail)

  | terminalBlock found form sourceType _ stops _ _ =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    rw [same]
    exact stopped_compatible unique found sourceType (.block found form stops) head
  | terminalConditional found form sourceType _ _ _ _ _ first second _ _ _ =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    rw [same]
    exact stopped_compatible unique found sourceType (.conditional found form first second) head
  | terminalMatch found form sourceType _ _ _ _ _ _ present arms fallback _ _ _ =>
    obtain ⟨_, _, _, head, _, same⟩ := head_tail_control typed
    rw [same]
    exact stopped_compatible unique found sourceType (.matching found form present arms fallback) head

/-- Actual source completion determines the raw result, independently of how
nominal types share native representations. -/
theorem Scan.result_eq_of_completes {source approved expected statements}
    (scan : Scan source approved expected true statements) (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts)
    (completed : BodyCompletes control.returnType facts) : control.returnType = expected := by
  have compatible := scan.control_compatible unique typed
  rcases completed.2.2 with ⟨_, returned⟩ | fallen
  · exact compatible.1 returned
  · exact compatible.2 rfl _ fallen

end Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchRequests
/-! The actual compiler certificate retains an arm/default request for every
original body. Static request origins recover typing for all retained children. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchCertificates GenericMatchChildren

theorem scrutinee_found {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {expressions : ExpressionCertificate}
    {requests : List Request} {code : Expr}
    (certificate : Certificate compilation source scope id resolution result reason
      expressions (Occurs requests) code) :
    ∃ node, source.lookupExpression? resolution.scrutinee = some node := by
  cases certificate with
  | matchWith _ _ _ _ _ _ _ found _ _ _ _ _ _ _ => exact ⟨_, found⟩

private theorem arms_request {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {id : StatementId} {scope : Scope} {type : TypeSystem.Ty}
    {requests : List Request} {cases : List TypedMatchCase} {native : List (Pattern × Expr)}
    {arm : TypedMatchCase}
    (certificate : Arms compilation source id scope type (Occurs requests) cases native)
    (member : arm ∈ cases) : ∃ request ∈ requests, request.statements = arm.body := by
  induction certificate with
  | nil => cases member
  | cons pattern typed body tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, body, rfl⟩
    · exact ih member

theorem arm_request {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {expressions : ExpressionCertificate}
    {requests : List Request} {code : Expr} {arm : TypedMatchCase}
    (certificate : Certificate compilation source scope id resolution result reason
      expressions (Occurs requests) code)
    (member : arm ∈ resolution.cases) : ∃ request ∈ requests, request.statements = arm.body := by
  cases certificate with
  | matchWith _ _ _ _ _ _ _ _ _ _ _ arms _ _ _ => exact arms_request arms member

theorem default_request {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {expressions : ExpressionCertificate}
    {requests : List Request} {code : Expr} {statements : List StatementId}
    (certificate : Certificate compilation source scope id resolution result reason
      expressions (Occurs requests) code)
    (present : resolution.defaultBody = some statements) :
    ∃ request ∈ requests, request.statements = statements := by
  cases certificate with
  | matchWith _ _ _ _ _ _ _ _ _ _ _ _ fallback _ _ =>
    rw [present] at fallback
    cases fallback with
    | some body => exact ⟨_, body, rfl⟩

/-- A request may share its statement list with another arm. Its original
membership supplies a genuine context without identifying distinct scopes. -/
theorem original_context {source : TypedSource} {control : ControlContext}
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {cases : List TypedMatchCase} {facts : List BodyFacts}
    {fallback : Option (List StatementId)} {request : Request}
    (typed : MatchCasesHaveType source control context type cases facts)
    (defaultTyped : ∀ statements, fallback = some statements →
      ∃ final bodyFacts, StatementsHaveType source control context statements final bodyFacts)
    (original : (∃ arm ∈ cases, request.statements = arm.body) ∨ fallback = some request.statements) :
    ∃ child final bodyFacts,
      ContextFor source context type cases fallback request child ∧
      StatementsHaveType source control child request.statements final bodyFacts := by
  rcases original with ⟨arm, member, same⟩ | present
  · obtain ⟨binders, arity, child, final, bodyFacts, pattern, extended, body⟩ := case_typing typed member
    exact ⟨child, final, bodyFacts, .arm member same pattern extended, same ▸ body⟩
  · obtain ⟨final, bodyFacts, body⟩ := defaultTyped _ present
    exact ⟨context, final, bodyFacts, .default present, body⟩

/-- The original statement and its actual finite compiler children construct
the scan. Ownership supplies the hidden and pattern input-exclusion facts. -/
theorem matching_scan {compilation : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {id : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {scrutinee : ExpressionNode}
    {result : Ty} {reason : Word} {expressions : ExpressionCertificate}
    {requests : List Request} {code : Expr} {approved : ExpressionId → Prop}
    {expected : TypeSystem.Ty} {mode : Bool} {rest : List StatementId}
    (certificate : Certificate compilation source scope id resolution result reason
      expressions (Occurs requests) code)
    (ownership : LocalIdentityOwnership source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutinee)
    (value : approved resolution.scrutinee)
    (children : ∀ request ∈ requests,
      ScopedSourceBodyAdmission.Scan source approved expected false request.statements)
    (remaining : ScopedSourceBodyAdmission.Scan source approved expected mode rest) :
    ScopedSourceBodyAdmission.Scan source approved expected mode (id :: rest) := by
  obtain ⟨hiddenOrdinary, armsOrdinary⟩ := ordinary_bindings ownership found form
  apply ScopedSourceBodyAdmission.Scan.matching found form scrutineeFound value hiddenOrdinary armsOrdinary
  · intro arm member
    obtain ⟨request, present, same⟩ := arm_request certificate member
    exact same ▸ children request present
  · intro statements present
    obtain ⟨request, member, same⟩ := default_request certificate present
    exact same ▸ children request member
  · exact remaining

end Solcore.SourceSemantics.CoreLowering.ScopedSourceMatchAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceClosure
/-! Actual local-read discovery gives closed replacement ranges for every
prepared candidate. Preparation and callable decoration preserve this fact. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceClosure
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open CallableAncestryProfiles.SourceComposition

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_invariant {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (accepted : forIn items initial step = .ok final) (start : invariant initial)
    (each : ∀ item ∈ items, ∀ state outcome, invariant state →
      step item state = .ok outcome → ∃ updated, outcome = .yield updated ∧ invariant updated) :
    invariant final := by
  induction items generalizing initial with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    exact accepted ▸ start
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    obtain ⟨outcome, ran, accepted⟩ := bind_ok accepted
    obtain ⟨updated, rfl, preserved⟩ := each item List.mem_cons_self initial outcome start ran
    exact ih accepted preserved (fun next member => each next (List.mem_cons_of_mem item member))

private theorem mapM_property {α β ε : Type} {items : List α} {values : List β}
    {action : α → Except ε β} {property : β → Prop}
    (accepted : items.mapM action = .ok values)
    (each : ∀ item ∈ items, ∀ value, action item = .ok value → property value) :
    ∀ value ∈ values, property value := by
  induction items generalizing values with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst values
    simp
  | cons item rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨head, first, accepted⟩ := bind_ok accepted
    obtain ⟨tail, later, accepted⟩ := bind_ok accepted
    cases accepted
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact each item List.mem_cons_self _ first
    · exact ih later (fun next present => each next (List.mem_cons_of_mem item present)) value member

private def unfoldAction (hypothesis : Lean.Name) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let some declaration := (← Lean.getLCtx).findFromUserName? hypothesis
      | throwError "missing accepted action"
    let type ← Lean.instantiateMVars (← Lean.Meta.inferType declaration.toExpr)
    let some (_, left, _) := type.eq? | throwError "expected equality"
    let .const action _ := left.getAppFn | throwError "expected compiler action"
    let goal ← Lean.Elab.Tactic.getMainGoal
    let updated ← Lean.Meta.unfoldLocalDecl goal declaration.fvarId action
    Lean.Elab.Tactic.replaceMainGoal [updated]

theorem read_origin_closed {source : TypedSource}
    {localInstance : SourceSpecializationWorklist.LocalLambdaInstance}
    (origin : SourceSpecializationWorklist.LocalLambdaInstance.ReadOrigin source localInstance) :
    RangesClosed localInstance.substitution := by
  induction origin with
  | root expression present name form matched => exact matchClosed_ranges matched
  | contextual previous expression present name form child matched cumulative ih =>
      rw [cumulative]
      exact RangesClosed.compose ih (matchClosed_ranges matched)

theorem catalog_entries_closed {plan : SourceSpecializationWorklist.Plan}
    {contextFuel : Option Nat} {entries : List SourceCompilationPlan.LocalLambdaCatalogEntry}
    (accepted : SourceCompilationPlan.localLambdaCatalog plan contextFuel = .ok entries) :
    ∀ entry ∈ entries, RangesClosed entry.substitution := by
  unfold SourceCompilationPlan.localLambdaCatalog at accepted
  obtain ⟨done, _, accepted⟩ := bind_ok accepted
  cases done
  obtain ⟨result, assembled, accepted⟩ := bind_ok accepted
  cases accepted
  apply forIn_invariant assembled (by simp)
  intro row _ before outcome previous iteration
  obtain ⟨instances, discovered, iteration⟩ := bind_ok iteration
  obtain ⟨after, appended, iteration⟩ := bind_ok iteration
  cases iteration
  refine ⟨after, rfl, ?_⟩
  apply forIn_invariant appended previous
  intro localInstance present current outcome previous step
  obtain ⟨nodes, _, step⟩ := bind_ok step
  cases step
  refine ⟨_, rfl, ?_⟩
  intro entry occurs
  rcases List.mem_append.mp occurs with old | new
  · exact previous entry old
  · cases List.mem_singleton.mp new
    exact read_origin_closed
      (SourceSpecializationWorklist.localLambdaInstances_read_origin discovered localInstance present)

def CatalogClosed (catalog : Catalog) : Prop :=
  ∀ binding ∈ catalog.bindings, ∀ candidate ∈ binding.instances,
    RangesClosed candidate.origin.substitution

theorem of_preparation {project : Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {plan : SourceSpecializationWorklist.Plan} {contextFuel : Option Nat} {catalog : Catalog}
    (accepted : prepareWithProjection project plan contextFuel = .ok catalog) :
    CatalogClosed catalog := by
  unfold prepareWithProjection at accepted
  obtain ⟨entries, discovered, accepted⟩ := bind_ok accepted
  have closedEntries : ∀ entry ∈ entries, RangesClosed entry.substitution := by
    apply catalog_entries_closed
    cases actual : SourceCompilationPlan.localLambdaCatalog plan contextFuel with
    | error error => simp [actual, Except.mapError] at discovered
    | ok values =>
        have same : values = entries := by simpa only [actual, Except.mapError, Except.ok.injEq] using discovered
        exact congrArg Except.ok same
  obtain ⟨instances, instantiated, accepted⟩ := bind_ok accepted
  have valid : ∀ candidate ∈ instances, RangesClosed candidate.origin.substitution := by
    refine mapM_property (property := fun candidate => RangesClosed candidate.origin.substitution) instantiated ?_
    intro entry member candidate actual
    run_tac unfoldAction `actual
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at actual
    iterate 8 split at actual <;> try contradiction
    obtain ⟨parameterType, _, actual⟩ := bind_ok actual
    obtain ⟨resultType, _, actual⟩ := bind_ok actual
    cases actual
    exact closedEntries entry member
  obtain ⟨bindings, assembled, accepted⟩ := bind_ok accepted
  cases accepted
  change ∀ binding ∈ bindings, ∀ candidate ∈ binding.instances, RangesClosed candidate.origin.substitution
  apply forIn_invariant assembled (by simp)
  intro specialized _ before outcome previous iteration
  try dsimp only at iteration
  split at iteration
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at iteration
  · obtain ⟨after, nodes, iteration⟩ := bind_ok iteration
    cases iteration
    refine ⟨after, rfl, ?_⟩
    apply forIn_invariant nodes previous
    intro node _ current outcome previous step
    try dsimp only at step
    split at step
    · split at step
      · cases step
        exact ⟨current, rfl, previous⟩
      · split at step
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at step
        · split at step
          · cases step
            refine ⟨_, rfl, ?_⟩
            intro binding member candidate memberCandidate
            rcases List.mem_append.mp member with old | new
            · exact previous binding old candidate memberCandidate
            · cases List.mem_singleton.mp new
              exact valid candidate (List.mem_filter.mp memberCandidate).1
          · cases step
            exact ⟨current, rfl, previous⟩
    · cases step
      exact ⟨current, rfl, previous⟩

theorem with_contracts {catalog assigned : Catalog}
    {idAt : Key → ExpressionId → Substitution → Option Core.Word}
    (valid : CatalogClosed catalog)
    (accepted : catalog.withCallableContracts idAt = .ok assigned) :
    CatalogClosed assigned := by
  unfold Catalog.withCallableContracts at accepted
  obtain ⟨bindings, prepared, accepted⟩ := bind_ok accepted
  cases accepted
  refine mapM_property (property := fun binding => ∀ candidate ∈ binding.instances,
    RangesClosed candidate.origin.substitution) prepared ?_
  intro binding member updated actual
  obtain ⟨instances, preparedInstances, actual⟩ := bind_ok actual
  cases actual
  refine mapM_property (property := fun candidate => RangesClosed candidate.origin.substitution) preparedInstances ?_
  intro candidate present decorated actual
  try dsimp only at actual
  split at actual <;> try contradiction
  cases actual
  exact valid binding member candidate present

theorem at_context {catalog : Catalog} {caller : Key} {binder : Resolved.LocalId}
    {binding : Binding} {active : Substitution} {candidate : Instance}
    (closed : CatalogClosed catalog)
    (located : catalog.binding caller binder = .ok binding)
    (member : candidate ∈ binding.atContext active) : RangesClosed candidate.origin.substitution := by
  have instanceMember := (List.mem_filter.mp member).1
  unfold Catalog.binding at located
  generalize filtered : catalog.bindings.filter
    (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) = entries at located
  cases entries with
  | nil => cases located
  | cons entry rest =>
    cases rest with
    | cons next tail => cases located
    | nil =>
      cases located
      have selected := List.mem_filter.mp (show binding ∈ catalog.bindings.filter
        (fun entry => decide (entry.caller = caller ∧ entry.binder.id = binder)) from by
          rw [filtered]
          simp)
      exact closed binding selected.1 candidate instanceMember

end Solcore.SourceSemantics.CoreLowering.PreparedLocalInstanceClosure
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyFormation
/-! Genuine unrestricted ordinary support forms a closure at its actual
nested Header packet. Source attribution and the full carried seed stay original.
Forward inclusion transfers only the new closure, with one function model for
all actual input/output heaps and the unchanged reached packet. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open PreparedLambdaBodySupport CallableIndexedOwnedSourceAdmission

section Seed
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

/-- The actual chosen contextual seed carries its prepared body before any
capture value exists. No execution law or old body package is a field. -/
structure Formation (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  produced : Produced (compiled := compiled) caller.named parameters result statements context evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  issued : CallableIndexedOwnedContextualLambdaSourceDiagnostics.IssuedSource compiled produced.site.code.compilation.owner
    (CallableIndexedNamedGeneration.source caller.named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  body : PreparedLambdaBodySupport.Body produced.compilation produced.site.code
    (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
    issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault
  bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code
  bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named
  declarations : CompatibleExpressionReads.ScopeDeclarations
    (CallableIndexedNamedGeneration.source caller.named) scope context
  sourceType : produced.site.code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
  ordinary : Dynamic.OrdinaryRequirementLayout produced.site.code.sourceNode.requirements produced.site.code.sourceNode.coercions []
  coercions : produced.site.code.sourceNode.coercions = []
  callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller context evidence

variable {caller context evidence}

def Formation.function {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure caller.named head.parameters head.result head.statements context evidence environment

def Formation.code {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Code compiled.indexed (head.function environment) scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) :=
  RecursiveNamedLambdaFormationHeads.recaptureCode (values := .initial compiled.compatible.checked)
    head.produced.site.code environment

def Formation.support {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Support (head.code environment) :=
  (Support.of_site caller head.produced.compilation head.produced.site head.expressionSyntax head.certificates
    head.issued head.diagnosticPolicy head.body).recapture environment

theorem Formation.prepared {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : PreparedAt (head.code environment) (head.support environment) :=
  .recaptured caller head.produced.compilation head.produced.site head.expressionSyntax head.certificates
    head.issued head.diagnosticPolicy head.body head.produced.binderPolicy head.produced.compilerPolicy head.produced.issuedRecipe head.bodyView head.bodyReasons head.declarations environment
end Seed

end Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedBranchingLambdaIssuance
/-! The actual selected compilation authenticates the prepared body issuer.
Root-table replacement leaves both original assignment and place inventories intact. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingLambdaIssuance
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralPlaceDiagnosticShells
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))

theorem of_compilation
    {lowered : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed caller.named lowered namedCode)
    (issuedAt : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed lowered)
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named)) :
    ∃ issued : IssuedSource compiled caller.named.signature.key (source caller.named),
      issued.assignments = compilation.own.assignments ∧
      PlaceReasonsEq issued.diagnostics.program lowered := by
  obtain ⟨diagnostics, found, sameBase, samePlaces⟩ := issuedAt
  obtain ⟨root, extra, prepared, collected⟩ :=
    CallableIndexedOwnedPublicPlaceMissingDiagnostics.inventory_at_header caller found
  have basePrepared := CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base prepared
  have selected := compilation.diagnostic
  rw [sameBase] at selected
  obtain ⟨first, assignmentsPrepared⟩ := SourceCoreProgramFaultSites.prepare_assignments_at
    basePrepared (CallableIndexedActualNamedSourceReceipts.header_record compiled caller) selected
  change SourceCoreAssignmentFaultSites.prepare (source caller.named) first =
    .ok compilation.own.assignments at assignmentsPrepared
  rw [caller.agreement.source] at collected
  let issued : IssuedSource compiled caller.named.signature.key (source caller.named) := {
    first := first
    assignments := compilation.own.assignments
    assignmentsPrepared := assignmentsPrepared
    typing := typing
    plan := compiled.indexed.base.plan
    root := root
    extra := extra
    diagnostics := diagnostics
    prepared := prepared
    collected := collected }
  exact ⟨issued, rfl, placeReasons_of_places samePlaces.symm⟩

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingLambdaIssuance
end

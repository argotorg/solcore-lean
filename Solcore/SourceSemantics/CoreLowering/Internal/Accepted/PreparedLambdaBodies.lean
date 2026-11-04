import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.CompilerProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalLambdaCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndexDiagnostics

/-!
# Prepared lambda bodies

Formation of prepared lambda bodies: physical formation, collectors, static facts and the producer.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyResultTyping
/-! Original return annotations identify a scoped body's result independently
of its native representation. Approval transport preserves every source node. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
open Core Frontend SourceInference
open AcceptedCompilerBodyProfile (HasReturn returns)

theorem Scan.map {source : TypedSource} {approved other : ExpressionId → Prop}
    {expected : TypeSystem.Ty} {mode : Bool} {statements : List StatementId}
    (scan : Scan source approved expected mode statements)
    (mapped : ∀ id, approved id → other id) : Scan source other expected mode statements := by
  induction scan with
  | nil allowed => exact .nil allowed
  | breaking rest found form => exact .breaking rest found form
  | continuing rest found form => exact .continuing rest found form
  | returnUnit rest found form sourceType result => exact .returnUnit rest found form sourceType result
  | returning rest found form sourceType expressionFound valueType value =>
    exact .returning rest found form sourceType expressionFound valueType (mapped _ value)
  | tail found form sourceType expressionFound valueType value =>
    exact .tail found form sourceType expressionFound valueType (mapped _ value)
  | absent found form declaration monomorphic ordinary _ ih => exact .absent found form declaration monomorphic ordinary ih
  | initialized found form declaration monomorphic ordinary expressionFound valueType value _ ih =>
    exact .initialized found form declaration monomorphic ordinary expressionFound valueType (mapped _ value) ih
  | discard found form continuing sourceType expressionFound value _ ih =>
    exact .discard found form continuing sourceType expressionFound (mapped _ value) ih
  | block found form _ _ inner remaining => exact .block found form inner remaining
  | conditional found form sourceType conditionFound conditionType value _ _ _ left right remaining =>
    exact .conditional found form sourceType conditionFound conditionType (mapped _ value) left right remaining
  | whileLoop found form conditionFound conditionType value _ _ inner remaining =>
    exact .whileLoop found form conditionFound conditionType (mapped _ value) inner remaining
  | matching found form scrutineeFound value hiddenOrdinary armsOrdinary _ _ _ arms fallback remaining =>
    exact .matching found form scrutineeFound (mapped _ value) hiddenOrdinary armsOrdinary arms fallback remaining
  | forLoop found form sourceType initial conditionFound conditionType value _ after _ inner remaining =>
    exact .forLoop found form sourceType (initial.map mapped) conditionFound conditionType (mapped _ value)
      inner (after.map mapped) remaining
  | assign found form declaration targetType profile bare rhsFound rhsType value _ ih =>
    exact .assign found form declaration targetType profile bare rhsFound rhsType (mapped _ value) ih

  | assignProjected found form declaration route profile projected keys rhsFound rhsType value _ ih =>
    exact .assignProjected found form declaration route profile projected (fun key member => mapped key (keys key member)) rhsFound rhsType (mapped _ value) ih
  | bitNotProjected found form declaration route profile projected keys _ ih =>
    exact .bitNotProjected found form declaration route profile projected (fun key member => mapped key (keys key member)) ih
  | bitNot found form declaration targetType profile bare _ ih =>
    exact .bitNot found form declaration targetType profile bare ih
  | terminalBlock found form sourceType _ stops remaining inner =>
    exact .terminalBlock found form sourceType inner stops remaining
  | terminalConditional found form sourceType conditionFound conditionType value _ _ first second remaining left right =>
    exact .terminalConditional found form sourceType conditionFound conditionType (mapped _ value)
      left right first second remaining
  | terminalMatch found form sourceType scrutineeFound value hiddenOrdinary armsOrdinary _ _ present stoppedArms stoppedDefault remaining arms fallback =>
    exact .terminalMatch found form sourceType scrutineeFound (mapped _ value) hiddenOrdinary armsOrdinary
      arms fallback present stoppedArms stoppedDefault remaining

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

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

private theorem return_in_tail {source : TypedSource} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} (found : source.lookupStatement? id = some node)
    (ordinary : returns node.form = false) (present : HasReturn source (id :: rest)) :
    HasReturn source rest := by
  obtain ⟨actual, member, value, selected, returned⟩ := present
  rcases List.mem_cons.mp member with same | member
  · subst actual
    cases Option.some.inj (found.symm.trans selected)
    simp [ordinary] at returned
  · exact ⟨actual, member, value, selected, returned⟩

private theorem no_control_at_zero {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .breakStmt ∨ node.form = .continueStmt)
    (typed : StatementHasType source control context id final facts) (noLoop : control.loopDepth = 0) : False := by
  cases typed
  all_goals
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans found)
    cases same
    simp_all [ControlContext.loopAllowed]

/-- A real return in the original statement list fixes the raw result type.
Nested blocks and loops retain the same return context; no native equality is used. -/
theorem Scan.result_eq_of_return {source : TypedSource} {approved : ExpressionId → Prop}
    {expected : TypeSystem.Ty} {mode : Bool} {statements : List StatementId}
    (scan : Scan source approved expected mode statements) (unique : NodeOccurrencesUnique source)
    (present : HasReturn source statements)
    {control : ControlContext} {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts) (noLoop : control.loopDepth = 0) :
    control.returnType = expected := by
  induction scan generalizing control context final facts with
  | nil => obtain ⟨_, member, _⟩ := present; cases member
  | breaking rest found form =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    exact False.elim (no_control_at_zero unique found (.inl form) head noLoop)
  | continuing rest found form =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    exact False.elim (no_control_at_zero unique found (.inr form) head noLoop)
  | returnUnit rest found form sourceType result =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    exact (returned_annotation unique found form head).symm.trans (sourceType.trans result.symm)
  | returning rest found form sourceType =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    exact (returned_annotation unique found form head).symm.trans sourceType
  | tail found form =>
    have absent := return_in_tail found (by simp [form, returns]) present
    obtain ⟨_, member, _⟩ := absent
    cases member
  | absent found form _ _ _ _ ih =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact ih (return_in_tail found (by simp [form, returns]) present) tail noLoop
  | initialized found form _ _ _ _ _ _ _ ih =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact ih (return_in_tail found (by simp [form, returns]) present) tail noLoop
  | discard found form _ _ _ _ _ ih =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact ih (return_in_tail found (by simp [form, returns]) present) tail noLoop
  | block found form _ _ _ remaining =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact remaining (return_in_tail found (by simp [form, returns]) present) tail noLoop
  | conditional found form _ _ _ _ _ _ _ _ _ remaining =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact remaining (return_in_tail found (by simp [form, returns]) present) tail noLoop
  | whileLoop found form _ _ _ _ _ _ remaining =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact remaining (return_in_tail found (by simp [form, returns]) present) tail noLoop
  | matching found form _ _ _ _ _ _ _ _ _ remaining =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact remaining (return_in_tail found (by simp [form, returns]) present) tail noLoop
  | forLoop found form _ _ _ _ _ _ _ _ _ remaining =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact remaining (return_in_tail found (by simp [form, returns]) present) tail noLoop
  | assign found form _ _ _ _ _ _ _ _ ih =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact ih (return_in_tail found (by simp [form, returns]) present) tail noLoop
  | assignProjected found form _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact ih (return_in_tail found (by simp [form, returns]) present) tail noLoop

  | bitNotProjected found form _ _ _ _ _ _ ih =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact ih (return_in_tail found (by simp [form, returns]) present) tail noLoop

  | bitNot found form _ _ _ _ _ ih =>
    obtain ⟨_, _, _, _, tail⟩ := head_tail typed
    exact ih (return_in_tail found (by simp [form, returns]) present) tail noLoop

  | terminalBlock found form sourceType _ stops _ _ =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    exact (stopped_statement_result unique found (.block found form stops) head).symm.trans sourceType
  | terminalConditional found form sourceType _ _ _ _ _ first second _ _ _ =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    exact (stopped_statement_result unique found (.conditional found form first second) head).symm.trans sourceType
  | terminalMatch found form sourceType _ _ _ _ _ _ defaultEq arms fallback _ _ _ =>
    obtain ⟨_, _, _, head, _⟩ := head_tail typed
    exact (stopped_statement_result unique found (.matching found form defaultEq arms fallback) head).symm.trans sourceType

end Solcore.SourceSemantics.CoreLowering.ScopedSourceBodyAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyPhysicalFormation
/-! Actual formation attaches the full captured slot receipt to the same Code,
history and original Source origin. The capture proof is supplied by the real
input environment before the freshly formed value enters the positive model.
The formation copies the captured cells, and the copies keep every global slot. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyPhysicalFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open PreparedLambdaBodySupport (Support SourceOrigin PreparedAt)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}

/-- The prepared seed of a code is the seed of the same code over other
captures. -/
theorem prepared_recapture {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code} (prepared : PreparedAt code support) (environment : Dynamic.Environment) :
    PreparedAt (code.recapture environment) (support.recapture environment) := by
  cases prepared with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView bodyReasons declarations _ =>
    exact .recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView bodyReasons declarations environment

/-- A prepared code is the lambda of a Site, which copies its captures. -/
theorem prepared_snapshots {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code} (prepared : PreparedAt code support) :
    code.policy.snapshotLambda code.id = true := by
  cases prepared with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView bodyReasons declarations environment =>
    exact site.snapshots

section Formation
variable {scope : SourceCoreLocalCell.Scope} {actual canonical : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code) (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : PreparedAt code support)
  (allSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1 scope captured.canonical)
  (callerReceipt : Nonempty (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt
    support.caller function.context function.evidence))

/-- The history is read from the actual entered owning row. -/
def history_at : History code where
  native := (initial.rows owner.position).authority.current
  ghost := (initial.rows owner.position).authority.ghost
  metadata := CallableIndexedNamedGeneration.state support.caller.named
  carried := packet.carried
  source := support.source.symm
  owner := by rw [support.compilation]; rfl
  active := support.active.symm

theorem source_origin : SourceOrigin support (history_at captured code support owner initial packet) := ⟨rfl⟩

include support in
theorem reference_index : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  rw [CallableIndexedLambdaValues.Code.referenceIndex, support.compilation]
  rfl

include profile prefixContext observed provenance allSlots callerReceipt in
/-- One original contextual formation retains its complete traces and
represented value, plus the same static member for later initialized reads.
The factory is used once, without an escaped-token hypothesis. The member is
the formed closure over the copies of its captured cells. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      CallableIndexedOwnedPreparedPhysicalClosureAssociation.StaticMember headers keys registry faults formed.finalMap
        formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  let history := history_at captured code support owner initial packet
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [reference_index captured code support]
    exact observed.reference
  have read : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native) := by
    have actualRead := (initial.rows owner.position).authority.frame.read
    rw [(initial.rows owner.position).frame_eq] at actualRead
    exact actualRead
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured code history (prepared_snapshots provenance)
    (reference_index captured code support) heaps reference read
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formed.represents heaps.runtime_hasTypes)
  exact ⟨formed, formed.source _ ordinary coercions, formed.evaluated,
    (fun _ _ completed => Core.evaluation_deterministic completed formed.evaluated),
    ⟨.preparedBranching (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨(source_origin captured code support owner initial packet).metadata⟩
      prefixContext (observed.of_slots formed.slots) (reference_index captured code support) typed
      (prepared_recapture provenance formed.captured) (allSlots.of_slots formed.slots) callerReceipt⟩⟩

end Formation

end Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyPhysicalFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedBranchingLambdaFormation
/-! The actual branching lambda Site constructs its prepared body before capture.
Original Source typing and the accepted native compiler supply every static
child; projected diagnostics remain attached to the original issuer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedBranchingLambdaBodySupport (Syntax Child)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (original : CallableIndexedOwnedContextualLambdaProducerReceipts.Produced (compiled := compiled)
    caller.named parameters result statements sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)

/-- The selected physical formation also retains the actual complete named
caller dictionary, which later expression certificates use after recapture. -/
structure Formation (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    extends CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation caller context evidence scope id lowered where
  callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller context evidence

 theorem of_produced
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named))
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) original.site.code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
      (closure caller.named parameters result statements sourceContext evidence []))
    (sameLedger : sourceContext.solvedRequirements = original.site.code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (canonical : original.site.code.view = source caller.named)
    (signatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (hidden : GenericImperativeMatch.MatchHiddenFresh (source caller.named))
    (entryDeclarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named)
      (original.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) inputs.context)
    (syntaxTree : GenericImperativeMatch.Syntax (source caller.named) (Syntax (source caller.named))
      inputs.context (.statements true statements) result)
    (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons original.site.code caller.named)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext)
    (sourceType : original.site.code.sourceNode.type = FunctionValues.sourceType
      (closure caller.named parameters result statements sourceContext evidence []))
    (ordinary : Dynamic.OrdinaryRequirementLayout original.site.code.sourceNode.requirements
      original.site.code.sourceNode.coercions [])
    (coercions : original.site.code.sourceNode.coercions = [])
    (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller sourceContext evidence) :
    Nonempty (Formation caller sourceContext evidence scope id lowered) := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, issuedAt, recipe, compilerPolicy, sameCompilation⟩ := original.issuedRecipe
  let produced : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Produced (compiled := compiled)
      caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered :=
    ⟨diagnostics, namedCode, compilation, original.site, original.identifier, original.emitted,
      original.binderPolicy, recipe, original.compilerPolicy, original.issuedRecipe⟩
  obtain ⟨issuer, sameAssignments, samePlaces⟩ :=
    PreparedBranchingLambdaIssuance.of_compilation caller compilation issuedAt typing
  have owner : produced.site.code.compilation.owner = caller.named.signature.key := by
    rw [produced.site.compilation]
    rfl
  let issued : CallableIndexedOwnedContextualLambdaSourceDiagnostics.IssuedSource compiled
      produced.site.code.compilation.owner (source caller.named) := {
    first := issuer.first
    assignments := issuer.assignments
    assignmentsPrepared := issuer.assignmentsPrepared
    typing := issuer.typing
    plan := issuer.plan
    root := issuer.root
    extra := issuer.extra
    diagnostics := issuer.diagnostics
    prepared := issuer.prepared
    collected := by simpa only [owner] using issuer.collected }
  have assignments : issued.assignments = produced.compilation.own.assignments := sameAssignments
  have places : CallableIndexedOwnedLiteralPlaceDiagnosticShells.PlaceReasonsEq
      issued.diagnostics.program produced.diagnostics := samePlaces
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
  have projection := (CallableIndexedOwnedContextualLambdaPackReceipts.Code.source_projections original.site.code profile).2
  have allocation : (bodyPolicy produced.compilation produced.site.code).sourceCells =
      some (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
        compiled.indexed.base.globals.length (compiled.indexed.layouts.allocatorAt
          produced.site.code.compilation.owner produced.site.code.active produced.site.code.allocationError)) := by
    rw [produced.site.compilation, produced.site.active, produced.site.allocationError]
    rfl
  let static : CallableIndexedOwnedPreparedNativeJointBodyCollectors.NativeExtractionInputs
      (layouts := compiled.indexed.layouts) (owner := produced.site.code.compilation.owner)
      (active := produced.site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
      (globals := compiled.indexed.base.globals.length) (onError := produced.site.code.allocationError)
      (values := .initial compiled.compatible.checked) (source := produced.site.code.view)
      (expressionSyntax := Syntax produced.site.code.view) (certificates := Child 0 produced.site.code.view)
      (reasonAt := produced.site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions)
      (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      (invalidOperand := issued.invalidOperand) (invalidUnary := issued.invalidUnary)
      (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
      true (bodyPolicy produced.compilation produced.site.code) inputs.context
      (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) := {
    matchCompilation := CallableIndexedOwnedLiteralReturnSiteShells.ambientMatch produced
    matchPolicy := CallableIndexedOwnedLiteralReturnSiteShells.match_policy produced
    matchValues := rfl
    matchDefinitions := rfl
    matchAllocator := allocation
    matchChildStatic := GenericImperativeMatch.MatchChildStatic.of_hidden (canonical.symm ▸ hidden)
    readPolicy := rfl
    binderPolicy := fun current binder mono => CallableIndexedOwnedLiteralReturnSiteShells.binder_policy produced binder current mono
    allocationPolicy := allocation
    expressions := by
      intro context closed residual sourceSignatures current fuel candidate node child declaration approved found typed accepted nativeType native
      exact ⟨node, found, typed, True.intro⟩
    assignments := CallableIndexedOwnedLiteralPlaceDiagnosticShells.assignment_policy produced issued assignments places
    unaries := CallableIndexedOwnedLiteralPlaceDiagnosticShells.unary_policy produced issued assignments places
    closed := runtime.variables_closed
    residual := runtime.residual_variables_open
    sourceSignatures := signatures
    declarations := by simpa only [produced, canonical] using entryDeclarations
    ledger := (Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended).solvedRequirements.trans
      (sameLedger.trans (by rw [original.site.compilation]; rfl)) }
  have edited : CallableLambdaViewEdits.LocalView (source caller.named) produced.site.code.view [] := by
    rw [canonical]
    exact .refl _
  obtain ⟨body, _entry, _readFuel⟩ := CallableIndexedOwnedPreparedNativeJointBodyCollectors.at_site
    produced.compilation produced.site produced.recipe (Program.ofChecked compiled.sourceProgram) inputs frame
    Syntax Child 0 .reachable issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault
    edited (by intro candidate member; cases member) frame.code.graph.nodeOccurrencesUnique sameLedger
    (by intro candidate reached allowed; exact True.intro)
    (by intro context current candidate child reached given; simpa only [produced, canonical] using given)
    syntaxTree (canonical.symm ▸ syntaxTree) projection static
    (CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native original.site.code)
  exact ⟨{
    parameters := parameters
    result := result
    statements := statements
    produced := produced
    expressionSyntax := Syntax
    certificates := Child
    issued := issued
    diagnosticPolicy := .reachable
    body := body
    bodyView := by intro candidate reached; change (source caller.named).lookupExpression? candidate = original.site.code.view.lookupExpression? candidate; rw [canonical]
    bodyReasons := bodyReasons
    declarations := declarations
    sourceType := sourceType
    ordinary := ordinary
    coercions := coercions
    callerReceipt := callerReceipt }⟩

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyNativeCollectors
/-! The original accepted lambda body supplies one exact prepared tree. Its
finite diagnostic interpretation is chosen only after the tree is retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyNativeCollectors
open Core Frontend SourceInference
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedNativeJointBodyCollectors (NativeExtractionInputs)
open CallableIndexedOwnedPreparedBranchingLambdaBodySupport (Syntax Child)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : CallableIndexedNamedGeneration.Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode)

theorem at_site {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {captured : Dynamic.Environment}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (site : Site compiled.indexed named parameters result statements sourceContext evidence captured scope administrative)
    (recipe : BodyRecipe namedCompilation site.code)
    (program : Program) (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) site.code)
    (frame : Dynamic.ClosureFrame program (CallableIndexedLambdaGeneration.closure named parameters result statements sourceContext evidence captured))
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (sameLedger : sourceContext.solvedRequirements = site.code.compilation.solvedRequirements)
    (view : site.code.view = CallableIndexedNamedGeneration.source named)
    (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source named))
    (hidden : GenericImperativeMatch.MatchHiddenFresh (CallableIndexedNamedGeneration.source named))
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape (CallableIndexedNamedGeneration.source named) true statements)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax (CallableIndexedNamedGeneration.source named)
      (Syntax (CallableIndexedNamedGeneration.source named)) inputs.context (.statements true statements) result)
    (projection : compiled.compatible.checked.catalog.project result = .ok site.code.receipt.resultCore)
    (static : NativeExtractionInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
      (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
      (onError := site.code.allocationError) (values := .initial compiled.compatible.checked) (source := site.code.view)
      (expressionSyntax := Syntax site.code.view) (certificates := Child 0 site.code.view)
      (reasonAt := site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
      (invalidOperand := invalidOperand) (invalidUnary := invalidUnary) (invalidProjection := invalidProjection)
      (missingDefault := missingDefault) true (bodyPolicy namedCompilation site.code) inputs.context
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope))
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative)
      site.code.receipt.body (LanguageResult.resultType site.code.receipt.resultCore) compiled.indexed.layouts.definitions) :
    ∃ body : PreparedLambdaBodySupport.Body namedCompilation site.code program Syntax Child
        invalidOperand invalidUnary invalidProjection missingDefault,
      body.toContext = inputs := by
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted (values := .initial compiled.compatible.checked)
    site.code (bodyPolicy namedCompilation site.code) (callback_of_recipe namedCompilation recipe)
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, accepted⟩ := CompatibleEncoding.bind_ok accepted
  have emitted : site.code.receipt.body = CompatibleStatements.finish site.code.receipt.resultCore flow
      site.code.compilation.internalReason site.code.compilation.internalReason := Except.ok.inj accepted.symm
  obtain ⟨nativeFlowType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow (emitted ▸ nativeTyped)
  have edited : LocalView (CallableIndexedNamedGeneration.source named) site.code.view [] := by
    rw [view]
    exact .refl _
  have binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      (bodyPolicy namedCompilation site.code).lowerBinder site.code.view scope binder =
        SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked site.code.view scope binder :=
    static.binderPolicy
  let collect (faults : FunctionCalls.FaultRep)
      (operands : PreparedLambdaBodyStaticReceipts.OperandLaw (CallableIndexedNamedGeneration.source named) invalidOperand faults)
      (unary : PreparedLambdaBodyStaticReceipts.UnaryLaw (CallableIndexedNamedGeneration.source named) invalidUnary faults) :=
    CallableIndexedOwnedPreparedNativeBranchingCollectors.collected
      (initial := inputs.context) (roots := statements.map NodeId.statement)
      edited (by intro id member; cases member) unique static.readPolicy binderPolicy static.allocationPolicy
      static.assignments static.unaries operands unary
      static.matchPolicy static.matchValues static.matchDefinitions static.matchAllocator hidden catalog static.ledger
      (certificates := fun _ _ _ _ => True)
      (by intros; exact True.intro)
      syntaxTree rfl shape (Dynamic.RuntimeContextFields.refl _)
      static.closed static.residual static.sourceSignatures
      (by simpa only [view] using static.declarations)
      (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩)) projection generated flowTyped
  let chosen := collect (fun _ _ => True)
    (by
      unfold PreparedLambdaBodyStaticReceipts.OperandLaw
      intro site assignment operator rhs origin profile previous right invalid
      exact True.intro)
    (by
      unfold PreparedLambdaBodyStaticReceipts.UnaryLaw
      intro site assignment origin profile
      exact True.intro)
  let extraction : PreparedLambdaBodyStaticReceipts.PreparedExtraction compiled.indexed.layouts
      site.code.compilation.owner site.code.active compiled.indexed.ancestry.layout.frame
      compiled.indexed.base.globals.length site.code.allocationError (.initial compiled.compatible.checked)
      (CallableIndexedNamedGeneration.source named) invalidOperand invalidUnary invalidProjection missingDefault
      (Syntax (CallableIndexedNamedGeneration.source named)) (Child 0 (CallableIndexedNamedGeneration.source named))
      compiled.indexed.layouts.definitions administrative inputs.context
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true statements) result site.code.receipt.resultCore flow := {
    tree := chosen.tree
    sites := by
      intro registry faults operands unary
      exact (collect faults operands unary).sites registry }
  exact ⟨{
    toContext := inputs, frame := frame, readFuel := 0, flow := flow,
    projection := projection, emitted := emitted,
    valid := CallableIndexedLambdaStaticBodySupport.context_valid
      (values := .initial compiled.compatible.checked) site.code inputs frame sameLedger,
    unique := unique, syntaxTree := syntaxTree, shape := shape, view := view,
    recipe := recipe, generated := generated, extraction := extraction }, rfl⟩

end Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyNativeCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyFormationProducer
/-! The actual branching lambda Site constructs its prepared body before capture.
Original Source typing and the accepted native compiler supply every static
child; projected diagnostics remain attached to the original issuer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedBranchingLambdaBodySupport (Syntax Child)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (original : CallableIndexedOwnedContextualLambdaProducerReceipts.Produced (compiled := compiled)
    caller.named parameters result statements sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)

 theorem of_produced
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named))
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) original.site.code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
      (closure caller.named parameters result statements sourceContext evidence []))
    (sameLedger : sourceContext.solvedRequirements = original.site.code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (canonical : original.site.code.view = source caller.named)
    (signatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (hidden : GenericImperativeMatch.MatchHiddenFresh (source caller.named))
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape (source caller.named) true statements)
    (entryDeclarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named)
      (original.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) inputs.context)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax (source caller.named) (Syntax (source caller.named))
      inputs.context (.statements true statements) result)
    (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons original.site.code caller.named)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext)
    (sourceType : original.site.code.sourceNode.type = FunctionValues.sourceType
      (closure caller.named parameters result statements sourceContext evidence []))
    (ordinary : Dynamic.OrdinaryRequirementLayout original.site.code.sourceNode.requirements
      original.site.code.sourceNode.coercions [])
    (coercions : original.site.code.sourceNode.coercions = [])
    (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller sourceContext evidence) :
    Nonempty (Formation caller sourceContext evidence scope id lowered) := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, issuedAt, recipe, compilerPolicy, sameCompilation⟩ := original.issuedRecipe
  let produced : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Produced (compiled := compiled)
      caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered :=
    ⟨diagnostics, namedCode, compilation, original.site, original.identifier, original.emitted,
      original.binderPolicy, recipe, original.compilerPolicy, original.issuedRecipe⟩
  obtain ⟨issuer, sameAssignments, samePlaces⟩ :=
    PreparedBranchingLambdaIssuance.of_compilation caller compilation issuedAt typing
  have owner : produced.site.code.compilation.owner = caller.named.signature.key := by
    rw [produced.site.compilation]
    rfl
  let issued : CallableIndexedOwnedContextualLambdaSourceDiagnostics.IssuedSource compiled
      produced.site.code.compilation.owner (source caller.named) := {
    first := issuer.first
    assignments := issuer.assignments
    assignmentsPrepared := issuer.assignmentsPrepared
    typing := issuer.typing
    plan := issuer.plan
    root := issuer.root
    extra := issuer.extra
    diagnostics := issuer.diagnostics
    prepared := issuer.prepared
    collected := by simpa only [owner] using issuer.collected }
  have assignments : issued.assignments = produced.compilation.own.assignments := sameAssignments
  have places : CallableIndexedOwnedLiteralPlaceDiagnosticShells.PlaceReasonsEq
      issued.diagnostics.program produced.diagnostics := samePlaces
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
  have projection := (CallableIndexedOwnedContextualLambdaPackReceipts.Code.source_projections original.site.code profile).2
  have allocation : (bodyPolicy produced.compilation produced.site.code).sourceCells =
      some (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
        compiled.indexed.base.globals.length (compiled.indexed.layouts.allocatorAt
          produced.site.code.compilation.owner produced.site.code.active produced.site.code.allocationError)) := by
    rw [produced.site.compilation, produced.site.active, produced.site.allocationError]
    rfl
  let static : CallableIndexedOwnedPreparedNativeJointBodyCollectors.NativeExtractionInputs
      (layouts := compiled.indexed.layouts) (owner := produced.site.code.compilation.owner)
      (active := produced.site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
      (globals := compiled.indexed.base.globals.length) (onError := produced.site.code.allocationError)
      (values := .initial compiled.compatible.checked) (source := produced.site.code.view)
      (expressionSyntax := Syntax produced.site.code.view) (certificates := Child 0 produced.site.code.view)
      (reasonAt := produced.site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions)
      (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      (invalidOperand := issued.invalidOperand) (invalidUnary := issued.invalidUnary)
      (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
      true (bodyPolicy produced.compilation produced.site.code) inputs.context
      (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) := {
    matchCompilation := CallableIndexedOwnedLiteralReturnSiteShells.ambientMatch produced
    matchPolicy := CallableIndexedOwnedLiteralReturnSiteShells.match_policy produced
    matchValues := rfl
    matchDefinitions := rfl
    matchAllocator := allocation
    matchChildStatic := GenericImperativeMatch.MatchChildStatic.of_hidden (canonical.symm ▸ hidden)
    readPolicy := rfl
    binderPolicy := fun current binder mono => CallableIndexedOwnedLiteralReturnSiteShells.binder_policy produced binder current mono
    allocationPolicy := allocation
    expressions := by
      intro context closed residual sourceSignatures current fuel candidate node child declaration approved found typed accepted nativeType native
      exact ⟨node, found, typed, True.intro⟩
    assignments := CallableIndexedOwnedLiteralPlaceDiagnosticShells.assignment_policy produced issued assignments places
    unaries := CallableIndexedOwnedLiteralPlaceDiagnosticShells.unary_policy produced issued assignments places
    closed := runtime.variables_closed
    residual := runtime.residual_variables_open
    sourceSignatures := signatures
    declarations := by simpa only [produced, canonical] using entryDeclarations
    ledger := (Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended).solvedRequirements.trans
      (sameLedger.trans (by rw [original.site.compilation]; rfl)) }
  obtain ⟨body, _entry⟩ := PreparedLambdaBodyNativeCollectors.at_site
    produced.compilation produced.site produced.recipe (Program.ofChecked compiled.sourceProgram) inputs frame
    issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault
    sameLedger canonical frame.code.graph.nodeOccurrencesUnique hidden catalog shape syntaxTree projection static
    (CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native original.site.code)
  exact ⟨{
    parameters := parameters
    result := result
    statements := statements
    produced := produced
    expressionSyntax := Syntax
    certificates := Child
    issued := issued
    diagnosticPolicy := .reachable
    body := body
    bodyView := by intro candidate reached; change (source caller.named).lookupExpression? candidate = original.site.code.view.lookupExpression? candidate; rw [canonical]
    bodyReasons := bodyReasons
    declarations := declarations
    sourceType := sourceType
    ordinary := ordinary
    coercions := coercions
    callerReceipt := callerReceipt }⟩

end Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyStaticFacts
/-! The original prepared Site retains compiler provenance, Source declarations,
and authentic read and index issuers without a uniform-error body package. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering
namespace PreparedLambdaBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaProvenance
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative} {support : Support code}

theorem PreparedAt.policy_recipe (receipt : PreparedAt code support) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained support.caller.named code := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact compilerPolicy

theorem PreparedAt.issued_recipe (receipt : PreparedAt code support) :
    CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained support.caller.named code := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact issuedRecipe

theorem PreparedAt.body_view (receipt : PreparedAt code support) :
    BodyView code := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact bodyView

theorem PreparedAt.body_reasons (receipt : PreparedAt code support) :
    BodyReasons code support.caller.named := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact bodyReasons

theorem PreparedAt.scope_declarations (receipt : PreparedAt code support) :
    CompatibleExpressionReads.ScopeDeclarations function.source scope function.context := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact declarations

end PreparedLambdaBodySupport

namespace CallableIndexedOwnedContextualLambdaReadDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaProvenance
open CallableIndexedOwnedPublicFaultReceiverTables
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}
theorem prepared_branching_uninitialized
    (support : PreparedLambdaBodySupport.Support code)
    (reasons : BodyReasons code support.caller.named)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {fuel : Nat} {context : SourceSemantics.Context} {readScope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression id))
    (receipt : CompatibleExpressionReads.LoweredRead fuel
      (.initial compiled.compatible.checked) function.source context code.reasonAt readScope id lowered)
    (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (code.reasonAt id) := by
  obtain ⟨certificate, _type, _binding⟩ := receipt
  obtain ⟨issued, present, token⟩ := reasons id reached
  obtain ⟨actual, namedCode, actualPresent, _cached, compiledCode⟩ :=
    NamedCalls.compiled_at compiled.indexed support.caller.selected
  have sameIssuer : actual = issued := Option.some.inj (actualPresent.symm.trans present)
  subst actual
  obtain ⟨compilation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed compiledCode
  have ownFound : issued.program.base.find? support.caller.named.signature.key = some compilation.own := by
    have selected := compilation.diagnostic
    have sameBase : (match compiled.indexed.base.callableContext with
        | none => issued.program
        | some native => { issued.program with rootTable := native.diagnostics.rootTable }).base =
        issued.program.base := by cases compiled.indexed.base.callableContext <;> rfl
    exact (congrArg (fun base => base.find? support.caller.named.signature.key) sameBase).symm.trans selected
  have original : function.source = support.caller.named.specialized.function.typedBody := support.source
  have unique : NodeOccurrencesUnique support.caller.named.specialized.function.typedBody := original ▸ support.unique
  have contains : ContainsExpression support.caller.named.specialized.function.typedBody id certificate.node :=
    original ▸ lookupExpression?_sound certificate.metadata.found
  obtain ⟨read, _expression, _binder, _span, readToken, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver present
      (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)
      unique contains certificate.form ownFound
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  apply CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
    (by simpa only [← readToken, ← token] using decoded)
  exact .readUninitialized location certificate.binder

end CallableIndexedOwnedContextualLambdaReadDiagnostics

namespace CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaProvenance
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {source : TypedSource} {id base : ExpressionId} {node baseNode : ExpressionNode}
  {layout : Core.OrderedMapping.Layout}
  {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
  {first second : SourceCoreBasic.LoweredExpr}
theorem of_prepared_branching {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    (support : PreparedLambdaBodySupport.Support code)
    (reasons : BodyReasons code support.caller.named)
    (sameSource : source = function.source)
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression id))
    (indexed : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
      source id base node baseNode layout comparison first second) :
    Nonempty (Port compiled indexed (code.reasonAt id)) := by
  obtain ⟨issued, present, token⟩ := reasons id reached
  exact ⟨{
    owner := support.caller.named.signature.key
    row := support.caller.named.specialized
    record := CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller
    sourceEq := sameSource.trans support.source
    unique := sameSource ▸ support.unique
    issuer := issued
    present := present
    token := token }⟩

/-- Actual certificate paths restrict the retained body issuer to used indices. -/
theorem prepared_branching_ready {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    (support : PreparedLambdaBodySupport.Support code)
    (reasons : BodyReasons code support.caller.named)
    (sameSource : source = function.source)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression rootId))
    (root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
      source context code.reasonAt rootScope rootId lowered) : IndexReady root := by
  intro _ _ _ _ _ _ _ _ _ _ _ indexed _ _ _ path
  have actualReached := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.indexes_reached
    path (sameSource ▸ reached)
  exact of_prepared_branching support reasons sameSource (sameSource ▸ actualReached) indexed

end CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
end Solcore.SourceSemantics.CoreLowering
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PreparedOrdinaryLambdaStaticFacts
/-! The original prepared Site retains compiler provenance, Source declarations,
and authentic read and index issuers without a uniform-error body package. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering
namespace CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaProvenance
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative} {support : Support code}

theorem PreparedAt.policy_recipe (receipt : PreparedAt code support) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained support.caller.named code := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact compilerPolicy

theorem PreparedAt.issued_recipe (receipt : PreparedAt code support) :
    CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained support.caller.named code := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact issuedRecipe

theorem PreparedAt.body_view (receipt : PreparedAt code support) :
    BodyView code := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact bodyView

theorem PreparedAt.body_reasons (receipt : PreparedAt code support) :
    BodyReasons code support.caller.named := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact bodyReasons

theorem PreparedAt.scope_declarations (receipt : PreparedAt code support) :
    CompatibleExpressionReads.ScopeDeclarations function.source scope function.context := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment => exact declarations

end CallableIndexedOwnedPreparedOrdinaryLambdaSupport

namespace CallableIndexedOwnedContextualLambdaReadDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaProvenance
open CallableIndexedOwnedPublicFaultReceiverTables
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}
theorem prepared_uninitialized
    (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
    (reasons : BodyReasons code support.caller.named)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {fuel : Nat} {context : SourceSemantics.Context} {readScope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression id))
    (receipt : CompatibleExpressionReads.LoweredRead fuel
      (.initial compiled.compatible.checked) function.source context code.reasonAt readScope id lowered)
    (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (code.reasonAt id) := by
  obtain ⟨certificate, _type, _binding⟩ := receipt
  obtain ⟨issued, present, token⟩ := reasons id reached
  obtain ⟨actual, namedCode, actualPresent, _cached, compiledCode⟩ :=
    NamedCalls.compiled_at compiled.indexed support.caller.selected
  have sameIssuer : actual = issued := Option.some.inj (actualPresent.symm.trans present)
  subst actual
  obtain ⟨compilation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed compiledCode
  have ownFound : issued.program.base.find? support.caller.named.signature.key = some compilation.own := by
    have selected := compilation.diagnostic
    have sameBase : (match compiled.indexed.base.callableContext with
        | none => issued.program
        | some native => { issued.program with rootTable := native.diagnostics.rootTable }).base =
        issued.program.base := by cases compiled.indexed.base.callableContext <;> rfl
    exact (congrArg (fun base => base.find? support.caller.named.signature.key) sameBase).symm.trans selected
  have original : function.source = support.caller.named.specialized.function.typedBody := support.source
  have unique : NodeOccurrencesUnique support.caller.named.specialized.function.typedBody := original ▸ support.unique
  have contains : ContainsExpression support.caller.named.specialized.function.typedBody id certificate.node :=
    original ▸ lookupExpression?_sound certificate.metadata.found
  obtain ⟨read, _expression, _binder, _span, readToken, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver present
      (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)
      unique contains certificate.form ownFound
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  apply CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
    (by simpa only [← readToken, ← token] using decoded)
  exact .readUninitialized location certificate.binder

end CallableIndexedOwnedContextualLambdaReadDiagnostics

namespace CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaProvenance
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {source : TypedSource} {id base : ExpressionId} {node baseNode : ExpressionNode}
  {layout : Core.OrderedMapping.Layout}
  {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
  {first second : SourceCoreBasic.LoweredExpr}
theorem of_prepared_ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
    (reasons : BodyReasons code support.caller.named)
    (sameSource : source = function.source)
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression id))
    (indexed : CompatibleExpressionIndices.Header (.initial compiled.compatible.checked)
      source id base node baseNode layout comparison first second) :
    Nonempty (Port compiled indexed (code.reasonAt id)) := by
  obtain ⟨issued, present, token⟩ := reasons id reached
  exact ⟨{
    owner := support.caller.named.signature.key
    row := support.caller.named.specialized
    record := CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller
    sourceEq := sameSource.trans support.source
    unique := sameSource ▸ support.unique
    issuer := issued
    present := present
    token := token }⟩

/-- Actual certificate paths restrict the retained body issuer to used indices. -/
theorem prepared_ordinary_ready {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
    (reasons : BodyReasons code support.caller.named)
    (sameSource : source = function.source)
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (reached : CallableLambdaBodyReachability.Reaches function.source
      (function.body.map NodeId.statement) (.expression rootId))
    (root : Certificate policy body compilation readFuel (.initial compiled.compatible.checked)
      source context code.reasonAt rootScope rootId lowered) : IndexReady root := by
  intro _ _ _ _ _ _ _ _ _ _ _ indexed _ _ _ path
  have actualReached := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.indexes_reached
    path (sameSource ▸ reached)
  exact of_prepared_ordinary support reasons sameSource (sameSource ▸ actualReached) indexed

end CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
end Solcore.SourceSemantics.CoreLowering
end

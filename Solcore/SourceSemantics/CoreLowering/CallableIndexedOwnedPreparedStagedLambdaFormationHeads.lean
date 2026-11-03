import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionExclusion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaFormationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds

/-! Ordinary lambda formation uses the actual named packet and keeps the
positive closure member of the formed closure, over the copies of its captured
cells, in the public receiving model. The retained Site and body are static
compiler receipts; captures come from this input. The reached packet is the
input packet transported to the formed state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open RecursiveNamedLambdaFormationHeads
open CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads (Formation)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry receiving : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (context : SourceSemantics.Context) {stages : Staging.Recursive.Registry}
  (invocation : Staging.Recursive.Scope)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (sameSource : invocation.source = CallableIndexedNamedGeneration.source caller.named)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "bridge" => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller

abbrev Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
    caller context invocation.evidence scope id lowered)

private theorem no_stage
    {program : Program} {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {size : Nat}
    {parameters result body failedScope call reason}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body)
    (coercions : node.coercions = [])
    (trace : Staging.Recursive.Size.Expression program registry size scope context environment
      before id (.fault (.stage failedScope call reason)) after) : False := by
  have actual : ∀ {shape requirements}, Staging.Recursive.Occurrence scope id shape requirements →
      shape = .lambda parameters result body := by
    intro shape requirements occurrence
    obtain ⟨actualNode, contains, sameForm, _requirements, _coercions⟩ := occurrence
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    exact sameForm.symm.trans form
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found coercions contains))
  | generalizedLocal contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | group occurrence _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _ | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _
  | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
      cases actual occurrence

include complete globals slots prefixZero in
/-- One actual formation copies the captured cells into the receiving heap and
forms the closure over the copies, with its positive static member; the input
packet is transported to the formed state. -/
private theorem forms {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
      caller context invocation.evidence scope id lowered)
    {mapping world administrative environment canonical actual actualContext before store ξ}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (nativeTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨scope, mapping, world, before, store, canonical⟩) :
    ∃ payload copies after finalStore finalMap finalWorld,
      Dynamic.EnvironmentCopies (receipt.toFormation.function environment).source environment before copies after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word payload) finalStore ∧
      ValueRep compiled.compatible.checked receiving functions finalMap finalWorld
        receipt.site.code.sourceNode.type (.closure { receipt.toFormation.function environment with captured := copies })
        payload lowered.type ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld
        after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
          ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        (CallableIndexedOwnedNestedCanonicalState.protocol owner caller).Relates initial reached := by
  let head := receipt.toFormation
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
    initial.property.observed initial.property.carried initial.property.bundle globals
  let captured := captures_for complete globals entry environments agrees nativeTyped
  have observed := capture_globals_for complete globals slots entry environments agrees nativeTyped
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical
      (initial.val.rows owner.position).authority.frameLocation at observed
    rw [(initial.val.rows owner.position).frame_eq] at observed
    exact observed
  let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
  let support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults := head.support environment
  let actualHistory : History code :=
    @CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at compiled headers keys bodyRegistry
      semanticFaults (head.function environment) scope mapping world before store actual canonical
      captured code support owner initial.val initial.property
  have origin := CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.source_origin
    (function := head.function environment) captured code support owner initial.val initial.property
  have referenceIndex := CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reference_index
    (function := head.function environment) captured code support
  obtain ⟨formed, _sourceTrace, native, related, _determined⟩ :=
    CallableIndexedOwnedGeneralLambdaValues.ordinary_lambda_of_formation (function := head.function environment)
      initial.val owner captured code actualHistory support origin rfl observed referenceIndex
      rfl profile heaps head.site.snapshots receipt.ordinary receipt.coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry semanticFaults profile).runtime_hasType
    (registry := bodyRegistry) related
  have member : CallableIndexedOwnedContextualTypedClosureReceipts.StaticMember headers keys bodyRegistry semanticFaults
      formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding actualHistory.native formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore :=
    ⟨.ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨origin.metadata⟩ rfl (observed.of_slots formed.slots) referenceIndex typed
      (CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.provenance_recapture
        (receipt.at environment globals) formed.captured)⟩
  have payload := CallableIndexedOwnedContextualCellOrigins.payload_static_member (registry := receiving) profile member
  obtain ⟨reached, transported⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
    initial formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  refine ⟨value code formed.embedding actualHistory.native formed.closureActual, formed.captured, formed.finalHeap,
    formed.finalStore, formed.finalMap, formed.finalWorld, formed.copy, ?_, ?_, formed.heaps, formed.maps,
    formed.worlds, formed.frame, reached, transported⟩
  · simpa only [code, Formation.code, recaptureCode, head, receipt.emitted, captured, captures_for, actualHistory] using native
  have sourceType : receipt.site.code.sourceNode.type = FunctionValues.sourceType (head.function environment) := receipt.sourceType
  have nativeType := CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type
    (compiled := compiled) (function := head.function environment) captured code
  rw [sourceType]
  have emittedType : lowered.type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
    simpa only [code, Formation.code, recaptureCode, head, receipt.emitted] using nativeType
  rw [emittedType]
  exact payload

variable (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (faults : RecursiveStageMeaning.FaultRep)

include complete globals slots prefixZero sameSource unique wellFormed runtime covers in
theorem preserves (size : Nat) :
    PreservesAt bridge context model stages invocation
      (Certificate (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) caller context invocation) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  obtain ⟨receipt⟩ := certified
  let head := receipt.toFormation
  let code := head.code environment
  have sourceFound : invocation.source.lookupExpression? id = some receipt.site.code.sourceNode := by
    simpa only [sameSource, receipt.identifier, CallableIndexedLambdaGeneration.closure] using receipt.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  have changed : ∃ copies, outcome = .value (.closure { head.function environment with captured := copies }) ∧
      Dynamic.EnvironmentCopies (head.function environment).source environment before copies after := by
    cases outcome with
    | value value =>
      have evaluated : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
          (head.function environment).context (head.function environment).evidence
          (head.function environment).source environment before code.id value after := by
        simpa only [sameSource, code, head, Formation.code, Formation.function,
          CallableIndexedLambdaGeneration.closure, recaptureCode, receipt.identifier] using trace.sound.value_plain
      obtain ⟨copies, rfl, copy⟩ := source_value_of_code (values := .initial compiled.compatible.checked) code
        (by simpa only [head, Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using unique)
        receipt.coercions evaluated
      exact ⟨copies, rfl, copy⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        apply False.elim
        apply excludes_fault_of_code (values := .initial compiled.compatible.checked) code
          (by simpa only [head, Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using unique)
          receipt.coercions
        simpa only [sameSource, code, head, Formation.code, Formation.function,
          CallableIndexedLambdaGeneration.closure, recaptureCode, receipt.identifier] using trace.sound.semanticFault_plain
      | stage failedScope call reason =>
        exact False.elim (no_stage unique sourceFound receipt.site.code.sourceForm receipt.coercions trace)
  obtain ⟨copies, rfl, copy⟩ := changed
  obtain ⟨payload, formedCopies, formedHeap, finalStore, finalMap, finalWorld, formedCopy, native, represented,
      finalHeaps, maps, worlds, frame, reached, related⟩ :=
    forms caller owner context invocation profile complete globals slots prefixZero receipt environments heaps agrees
      nativeTyped initial
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formedCopy
  refine ⟨.inRight .word payload, finalStore, finalMap, finalWorld, native, .value represented,
    finalHeaps, maps, worlds, frame, copy.metadata_extends, reached, related, ?_⟩
  exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame

include complete globals slots prefixZero sameSource wellFormed runtime covers in
theorem reflects (size : Nat) :
    ReflectsAt bridge context model stages invocation
      (Certificate (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) caller context invocation) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  obtain ⟨receipt⟩ := certified
  have sourceFound : invocation.source.lookupExpression? id = some receipt.site.code.sourceNode := by
    simpa only [sameSource, receipt.identifier, CallableIndexedLambdaGeneration.closure] using receipt.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨payload, copies, after, formedStore, finalMap, finalWorld, copy, native, represented,
      finalHeaps, maps, worlds, frame, reached, related⟩ :=
    forms caller owner context invocation profile complete globals slots prefixZero receipt environments heaps agrees
      nativeTyped initial
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic native completed.sound
  have snapshot : Dynamic.EnvironmentCopies invocation.source environment before copies after := by
    rw [sameSource]
    exact copy
  have sourceTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize []) invocation context environment before id
      (.value (.closure { receipt.toFormation.function environment with captured := copies })) after := by
    apply Staging.Recursive.Size.Expression.atomicValue (lookupExpression?_sound sourceFound)
      (receipt.site.code.sourceForm ▸ Staging.Recursive.AtomicForm.lambda _ _ _) receipt.coercions
    rw [receipt.site.code.sourceForm]
    simpa only [Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource, receipt.coercions] using
      (Dynamic.ExpressionFormEvaluates.lambda (program := Program.ofChecked compiled.sourceProgram)
        (context := context) (evidence := invocation.evidence) (source := invocation.source)
        (environment := environment) (before := before) (after := after) (captured := copies)
        (parameters := receipt.parameters) (returnType := receipt.result) (body := receipt.statements)
        receipt.ordinary snapshot)
  refine ⟨Staging.Recursive.Size.stepSize [], _, after, finalMap, finalWorld, sourceTrace, .value represented,
    finalHeaps, maps, worlds, frame, copy.metadata_extends, reached, related, ?_⟩
  exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed sourceTrace frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaFormationHeads

import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPrincipalLambdaFormation

/-! Genuine ordinary and principal formation heads create a positive closure
leaf directly from the retained static receipt. Each direction invokes the
original factory once over the incoming positive cells, with its General
representation. Formation copies the captured cells, so the positive cells and
the caller's packet are transported to the formed state; the actual Source
trace establishes admission in that transported packet. No escaped diagnostic,
selected caller code, reverse General inclusion or body meaning is required by
formation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedContextualTypedClosureReceipts (StaticMember)
open CallableIndexedOwnedContextualCellOrigins (PayloadOrigins CellOrigins PostWithOrigins post_at_same_state)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)

namespace Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry faults)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)

open CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation (history_at source_origin reference_index)

/-- The full head result retains the original effects and the same packet
witness, transported to the formed state that holds the copies of the captured
cells, with the positive heap there. The static member of the formed closure is
inside that returned existential beside the actual positive post. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
      PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        function.context profile code.sourceNode.type code.lowered.type outcome result reached ∧
      ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
          (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
        StaticMember headers keys bodyRegistry faults finalMap finalWorld formed.closure
          (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
          code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

/-- The legacy full-head projection has one registry. Its explicit equality
is needed only by this compatibility port; formation keeps the body and
receiving registries independent with the same result and reached caller. -/
theorem ResultAt.forget {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {result : Core.Value} {finalStore : Store}
    (sameRegistry : registry = bodyRegistry)
    (returned : ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore) :
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.ResultAt (registry := bodyRegistry) captured code support owner initial packet
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile) outcome after result finalStore := by
  cases sameRegistry
  obtain ⟨nativeTrace, finalMap, finalWorld, represented, finalCells, maps, worlds, frame, metadata,
    reached, related, post, _member⟩ := returned
  exact ⟨nativeTrace, finalMap, finalWorld, represented, finalCells, maps, worlds, frame, metadata,
    reached, related, post.admission⟩

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (copied : code.policy.snapshotLambda code.id = true)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include prefixContext observed provenance cells copied ordinary coercions in
/-- The original ordinary factory runs once over the incoming positive cells.
Its General representation supplies the static member of the formed closure
over the copies of its captured cells; no escaped-control row is used. -/
private theorem formation_member :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedGeneralLambdaValues.ordinary_lambda_of_formation initial owner captured code
      (history_at captured code support owner initial packet) support
      (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) rfl profile cells copied ordinary coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
    (registry := bodyRegistry) represented
  exact ⟨formed, sourceTrace, nativeTrace, determined,
    ⟨.ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨(source_origin captured code support owner initial packet).metadata⟩
      prefixContext (observed.of_slots formed.slots) (reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.provenance_recapture provenance formed.captured)⟩⟩

include sourceType admitted wellFormed runtime covers locals typed in
/-- Pure attachment uses the trace and member already returned by one factory.
The caller is the same packet used by formation, transported to the formed
state; its actual Source trace supplies admission there, beside the formed
positive cells. -/
private theorem result_at_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
      (history_at captured code support owner initial packet) heap store owner.key.frameLocation)
    (sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      function.context function.evidence function.source function.captured heap code.id (.closure formed.closure)
      formed.finalHeap)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
        formed.closureActual)) formed.finalStore)
    (member : StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore) :
    ResultAt (registry := registry) captured code owner profile support initial packet (.value (.closure formed.closure))
      formed.finalHeap
      (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
        formed.closureActual)) formed.finalStore := by
  have payload : PayloadOrigins headers keys bodyRegistry registry faults profile formed.finalMap formed.finalWorld
      code.sourceNode.type (.closure formed.closure)
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.lowered.type := by
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedContextualCellOrigins.payload_static_member (registry := registry) profile member
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding
        (history_at captured code support owner initial packet).native formed.closureActual)) := .value payload
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner support.caller)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨nativeTrace, formed.finalMap, formed.finalWorld, represented, formed.heaps, formed.maps, formed.worlds,
    formed.frame, formed.copy.metadata_extends, reached, related,
    post_at_same_state (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      profile reached post formed.heaps represented, formed, member⟩

include prefixContext observed provenance cells sourceType copied ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Invert the actual Source head and form its closure over the copies of its
captured cells once. The genuine metadata, syntax, capture history and positive
cells all describe this original head; no accepted-call selection or body
continuation is assumed. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨formed, sourceTrace, nativeTrace, _determined, member⟩ :=
      formation_member captured code owner profile cells support initial packet prefixContext observed provenance
        copied ordinary coercions
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
    exact ⟨_, formed.finalStore, result_at_formation captured code owner profile support initial packet
      wellFormed runtime covers locals typed sourceType admitted formed sourceTrace nativeTrace member⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include prefixContext observed provenance cells sourceType copied ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Compare the supplied native completion with one genuine formation. Its
independent Source grade and positive post use that same factory trace directly;
reflection does not invoke preservation and form the closure a second time. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, nativeTrace, determined, member⟩ :=
    formation_member captured code owner profile cells support initial packet prefixContext observed provenance
      copied ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, sized,
    result_at_formation captured code owner profile support initial packet
      wellFormed runtime covers locals typed sourceType admitted formed sourceTrace nativeTrace member⟩

end Ordinary

namespace Principal
variable
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code bodyRegistry faults)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code support)

open CallableIndexedOwnedMethodLambdaFormationReceipts (history_at source_origin leading reference_index)

/-- The full head result retains the original effects and the same packet
witness, transported to the formed state that holds the copies of the captured
cells, with the positive heap there. The static member of the formed closure is
inside that returned existential beside the actual positive post. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
        ⟨scope, finalMap, finalWorld, after, finalStore, captured.canonical⟩,
      (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
      PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
        function.context profile code.sourceNode.type code.lowered.type outcome result reached ∧
      ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
          (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
        StaticMember headers keys bodyRegistry faults finalMap finalWorld formed.closure
          (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
          code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore

/-- The legacy full-head projection has one registry. Its explicit equality
is needed only by this compatibility port; formation keeps the body and
receiving registries independent with the same result and reached caller. -/
theorem ResultAt.forget {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {result : Core.Value} {finalStore : Store}
    (sameRegistry : registry = bodyRegistry)
    (returned : ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore) :
    CallableIndexedOwnedAdmittedPrincipalLambdaFormation.ResultAt (registry := bodyRegistry) captured code support owner initial packet
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile) outcome after result finalStore := by
  cases sameRegistry
  obtain ⟨nativeTrace, finalMap, finalWorld, represented, finalCells, maps, worlds, frame, metadata,
    reached, related, post, _member⟩ := returned
  exact ⟨nativeTrace, finalMap, finalWorld, represented, finalCells, maps, worlds, frame, metadata,
    reached, related, post.admission⟩

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (copied : code.policy.snapshotLambda code.id = true)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include packet provenance cells copied ordinary coercions in
/-- The original principal factory runs once over the incoming positive cells.
Its General representation, actual leading bundle and history supply the static
member of the formed closure over the copies of its captured cells; no
escaped-control row is used. -/
private theorem formation_member :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedAdmittedPrincipalLambdaFormation.principal_representation captured code support owner
      initial packet profile cells copied ordinary coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
    (registry := bodyRegistry) represented
  have leadingFormed : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    leading captured code support owner initial packet
  exact ⟨formed, sourceTrace, nativeTrace, determined,
    ⟨.principal (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support formed.captured)
      (CallableIndexedOwnedMethodLambdaValues.recaptureOrigin (source_origin captured code support owner initial packet)
        formed.captured)
      (packet.observed.of_slots formed.slots) leadingFormed (reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation.provenance_recapture provenance formed.captured)⟩⟩

include sourceType admitted wellFormed runtime covers locals typed in
/-- Pure attachment uses the trace and member already returned by one factory.
The caller is the same packet used by formation, transported to the formed
state; its actual Source trace supplies admission there, beside the formed
positive cells. -/
private theorem result_at_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
      (history_at captured code support owner initial packet) heap store owner.key.frameLocation)
    (sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      function.context function.evidence function.source function.captured heap code.id (.closure formed.closure)
      formed.finalHeap)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
        formed.closureActual)) formed.finalStore)
    (member : StaticMember headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore) :
    ResultAt (registry := registry) captured code owner profile support initial packet (.value (.closure formed.closure))
      formed.finalHeap
      (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
        formed.closureActual)) formed.finalStore := by
  have payload : PayloadOrigins headers keys bodyRegistry registry faults profile formed.finalMap formed.finalWorld
      code.sourceNode.type (.closure formed.closure)
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.lowered.type := by
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedContextualCellOrigins.payload_static_member (registry := registry) profile member
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding
        (history_at captured code support owner initial packet).native formed.closureActual)) := .value payload
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
    (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨nativeTrace, formed.finalMap, formed.finalWorld, represented, formed.heaps, formed.maps, formed.worlds,
    formed.frame, formed.copy.metadata_extends, reached, related,
    post_at_same_state (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      profile reached post formed.heaps represented, formed, member⟩

include packet provenance cells sourceType copied ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Invert the actual Source head and form its closure over the copies of its
captured cells once. The genuine metadata, syntax, capture history and positive
cells all describe this original head; no accepted-call selection or body
continuation is assumed. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨formed, sourceTrace, nativeTrace, _determined, member⟩ :=
      formation_member captured code owner profile cells support initial packet provenance
        copied ordinary coercions
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
    exact ⟨_, formed.finalStore, result_at_formation captured code owner profile support initial packet
      wellFormed runtime covers locals typed sourceType admitted formed sourceTrace nativeTrace member⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include packet provenance cells sourceType copied ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Compare the supplied native completion with one genuine formation. Its
independent Source grade and positive post use that same factory trace directly;
reflection does not invoke preservation and form the closure a second time. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, nativeTrace, determined, member⟩ :=
    formation_member captured code owner profile cells support initial packet provenance
      copied ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure formed.closure), formed.finalHeap, sized,
    result_at_formation captured code owner profile support initial packet
      wellFormed runtime covers locals typed sourceType admitted formed sourceTrace nativeTrace member⟩

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureFormationReceipts

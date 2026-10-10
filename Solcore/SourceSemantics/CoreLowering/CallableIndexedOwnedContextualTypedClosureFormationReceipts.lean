import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedPrincipalLambdaFormation

/-! Genuine ordinary and principal formation heads create a positive closure
leaf directly from the retained static receipt. Each direction invokes the
original factory once under General with identity inclusion. Incoming positive
cells stay at the unchanged heap and store; the actual Source trace establishes
admission in the same returned packet. No escaped diagnostic, selected caller
code, reverse General inclusion or body meaning is required by formation. -/
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

/-- The full head result retains the original effects, unchanged positive
heap and same packet witness. Its static member is inside that returned
existential beside the actual positive post. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  GenericExpressionMeaning.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
    mapping world code.sourceNode.type code.lowered.type faults outcome result ∧
  CellOrigins headers keys bodyRegistry registry faults profile mapping world after finalStore ∧
  LocationMap.Extends mapping mapping ∧ WorldExtends world world ∧
  AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
  ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
      ⟨scope, mapping, world, after, finalStore, canonical⟩,
    (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
    PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      function.context profile code.sourceNode.type code.lowered.type outcome result reached ∧
    StaticMember headers keys bodyRegistry faults mapping world function
      (value code captured.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native actual)
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
  obtain ⟨nativeTrace, represented, finalCells, maps, worlds, frame, metadata,
    reached, related, post, _member⟩ := returned
  exact ⟨nativeTrace, represented, finalCells, maps, worlds, frame, metadata,
    reached, related, post.admission⟩

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include cells sourceType admitted wellFormed runtime covers locals typed in
/-- Pure attachment uses the trace and member already returned by one factory.
The unchanged caller is the same packet used by formation; its actual Source
trace supplies admission and its incoming positive cells remain valid. -/
private theorem result_at_formation
    (sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      function.context function.evidence function.source function.captured heap code.id (.closure function) heap)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native actual)) store)
    (member : StaticMember headers keys bodyRegistry faults mapping world function
      (value code captured.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore) :
    ResultAt (registry := registry) captured code owner profile support initial packet (.value (.closure function)) heap
      (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native actual)) store := by
  have payload : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      code.sourceNode.type (.closure function)
      (value code captured.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native actual) code.lowered.type := by
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedContextualCellOrigins.payload_static_member (registry := registry) profile member
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      mapping world code.sourceNode.type code.lowered.type faults
      (.value (.closure function)) (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at captured code support owner initial packet).native actual)) := .value payload
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ ⟨initial, packet⟩ admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) (AdministrativePreserved.refl mapping store)
  exact ⟨nativeTrace, represented, cells, .refl _, .refl _, .refl _ _, .refl _,
    ⟨initial, packet⟩, Relates.refl initial,
    post_at_same_state (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      profile ⟨initial, packet⟩ post cells represented, member⟩

include prefixContext observed provenance cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Invert the actual Source head and form its same closure once. The genuine
metadata, syntax, capture history and positive cells all describe this original
head; no accepted-call selection or body continuation is assumed. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨rfl, rfl⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨sourceTrace, nativeTrace, _general, _determined, member⟩ :=
      CallableIndexedOwnedContextualTypedClosureReceipts.formation_member
        (captured := captured) (code := code) (support := support) (owner := owner)
        (initial := initial) (packet := packet) (profile := profile)
        (prefixContext := prefixContext) (observed := observed) (provenance := provenance)
        (functions := CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
        (inclusion := fun represented => represented) cells.runtime_hasTypes ordinary coercions
    exact ⟨_, store, result_at_formation captured code owner profile cells support initial packet
      wellFormed runtime covers locals typed sourceType admitted sourceTrace nativeTrace member⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include prefixContext observed provenance cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Compare the supplied native completion with one genuine formation. Its
independent Source grade and positive post use that same factory trace directly;
reflection does not invoke preservation and form the closure a second time. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore := by
  obtain ⟨sourceTrace, nativeTrace, _general, determined, member⟩ :=
    CallableIndexedOwnedContextualTypedClosureReceipts.formation_member
      (captured := captured) (code := code) (support := support) (owner := owner)
      (initial := initial) (packet := packet) (profile := profile)
      (prefixContext := prefixContext) (observed := observed) (provenance := provenance)
      (functions := CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
      (inclusion := fun represented => represented) cells.runtime_hasTypes ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure function), heap, sized,
    result_at_formation captured code owner profile cells support initial packet
      wellFormed runtime covers locals typed sourceType admitted sourceTrace nativeTrace member⟩

end Ordinary

namespace Principal
variable
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code bodyRegistry faults)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code support)

/-- The full head result retains the original effects, unchanged positive
heap and same packet witness. Its static member is inside that returned
existential beside the actual positive post. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Core.Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  GenericExpressionMeaning.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
    mapping world code.sourceNode.type code.lowered.type faults outcome result ∧
  CellOrigins headers keys bodyRegistry registry faults profile mapping world after finalStore ∧
  LocationMap.Extends mapping mapping ∧ WorldExtends world world ∧
  AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
  ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
      ⟨scope, mapping, world, after, finalStore, captured.canonical⟩,
    (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
    PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      function.context profile code.sourceNode.type code.lowered.type outcome result reached ∧
    StaticMember headers keys bodyRegistry faults mapping world function
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)
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
  obtain ⟨nativeTrace, represented, finalCells, maps, worlds, frame, metadata,
    reached, related, post, _member⟩ := returned
  exact ⟨nativeTrace, represented, finalCells, maps, worlds, frame, metadata,
    reached, related, post.admission⟩

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include cells sourceType admitted wellFormed runtime covers locals typed in
/-- Pure attachment uses the trace and member already returned by one factory.
The unchanged caller is the same packet used by formation; its actual Source
trace supplies admission and its incoming positive cells remain valid. -/
private theorem result_at_formation
    (sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      function.context function.evidence function.source function.captured heap code.id (.closure function) heap)
    (nativeTrace : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)) store)
    (member : StaticMember headers keys bodyRegistry faults mapping world function
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore) :
    ResultAt (registry := registry) captured code owner profile support initial packet (.value (.closure function)) heap
      (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)) store := by
  have payload : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      code.sourceNode.type (.closure function)
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual) code.lowered.type := by
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedContextualCellOrigins.payload_static_member (registry := registry) profile member
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      mapping world code.sourceNode.type code.lowered.type faults
      (.value (.closure function)) (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at captured code support owner initial packet).native actual)) := .value payload
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ ⟨initial, packet⟩ admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) (AdministrativePreserved.refl mapping store)
  exact ⟨nativeTrace, represented, cells, .refl _, .refl _, .refl _ _, .refl _,
    ⟨initial, packet⟩, Relates.refl initial,
    post_at_same_state (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      profile ⟨initial, packet⟩ post cells represented, member⟩

include packet provenance cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Invert the actual Source head and form its same closure once. The genuine
metadata, syntax, capture history and positive cells all describe this original
head; no accepted-call selection or body continuation is assumed. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨rfl, rfl⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨sourceTrace, nativeTrace, _general, _determined, member⟩ :=
      CallableIndexedOwnedContextualTypedClosureReceipts.principal_formation_member
        (captured := captured) (code := code) (support := support) (owner := owner)
        (initial := initial) (packet := packet) (profile := profile)
        (provenance := provenance)
        (functions := CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
        (inclusion := fun represented => represented) cells.runtime_hasTypes ordinary coercions
    exact ⟨_, store, result_at_formation captured code owner profile cells support initial packet
      wellFormed runtime covers locals typed sourceType admitted sourceTrace nativeTrace member⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include packet provenance cells sourceType ordinary coercions admitted wellFormed runtime covers locals typed in
/-- Compare the supplied native completion with one genuine formation. Its
independent Source grade and positive post use that same factory trace directly;
reflection does not invoke preservation and form the closure a second time. -/
theorem reflects_at {size : Nat} {result : Core.Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) captured code owner profile support initial packet outcome after result finalStore := by
  obtain ⟨sourceTrace, nativeTrace, _general, determined, member⟩ :=
    CallableIndexedOwnedContextualTypedClosureReceipts.principal_formation_member
      (captured := captured) (code := code) (support := support) (owner := owner)
      (initial := initial) (packet := packet) (profile := profile)
      (provenance := provenance)
      (functions := CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
      (inclusion := fun represented => represented) cells.runtime_hasTypes ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, .value (.closure function), heap, sized,
    result_at_formation captured code owner profile cells support initial packet
      wellFormed runtime covers locals typed sourceType admitted sourceTrace nativeTrace member⟩

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureFormationReceipts

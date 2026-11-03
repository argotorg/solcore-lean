import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeDirectCellOrigins

/-! Authentic ordinary and selected Principal packets supply the actual frame
read for one original Code formation. The formation copies the captured cells;
the new leaf keeps that same prepared body, recaptured at the copies, and the
static qualification of the recaptured Code without manufacturing universal
diagnostic laws. The real trace supplies admission at the original pool
transported to the formed heap and store. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (StaticMember CellOrigins Post functions)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (owner : OwnedKey keys)
  (qualification : Facet compiled)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

namespace Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (qualified : ∀ environment, qualification.ordinary (code.recapture environment) (support.recapture environment))
  (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

/-- This exact owned row and original Header seed construct lexical history. -/
def history_at : History code where
  native := (initial.rows owner.position).authority.current
  ghost := (initial.rows owner.position).authority.ghost
  metadata := CallableIndexedNamedGeneration.state support.caller.named
  carried := packet.carried
  source := support.source.symm
  owner := by rw [support.compilation]; rfl
  active := support.active.symm

include support in
theorem reference_index : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  rw [CallableIndexedLambdaValues.Code.referenceIndex, support.compilation]
  rfl

local notation "history" => history_at captured code owner support initial packet
local notation "carrier " formed:max => value code (Formed.embedding formed)
  (CallableIndexedLambdaValues.History.native history) (Formed.closureActual formed)

include packet prepared qualified profile prefixContext observed in
/-- One elementary actual formation copies the captured cells and supplies
Source/native traces and runtime typing; the direct positive constructor
retains the prepared packet, recaptured at the copies, for the formed closure. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (carrier formed)) formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (carrier formed) code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (carrier formed) ∧ finalStore = formed.finalStore) := by
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [reference_index captured code support]
    exact observed.reference
  have read : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
        (CallableIndexedLambdaValues.History.native history)) := by
    have actualRead := (initial.rows owner.position).authority.frame.read
    rw [(initial.rows owner.position).frame_eq] at actualRead
    exact actualRead
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured code history
    (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.prepared_snapshots prepared)
    (reference_index captured code support) heaps reference read
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := bodyRegistry) (formed.represents heaps.runtime_hasTypes)
  exact ⟨formed, formed.source _ ordinary coercions, formed.evaluated,
    ⟨.ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨rfl⟩
      (CallableIndexedOwnedPreparedOrdinaryLambdaFormation.prepared_recapture prepared formed.captured)
      (qualified formed.captured) prefixContext (observed.of_slots formed.slots)
      (reference_index captured code support) typed⟩,
    fun _ _ completed => Core.evaluation_deterministic completed formed.evaluated⟩

variable
  (cells : CellOrigins qualification headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile qualified prefixContext observed in
/-- The caller packet, transported to the formed state, keeps incoming direct
cells over the copies and the newly formed direct result. Admission comes from
the actual Source trace. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
        captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (carrier formed)) formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (carrier formed) code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, canonical⟩,
        (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
        Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
          function.context qualification profile code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure)) (.inRight .word (carrier formed)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (carrier formed) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code owner qualification profile support qualified prepared initial packet prefixContext observed
    cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (carrier formed)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedPreparedNativeDirectCellOrigins.payload_static_member (registry := registry) profile member
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner support.caller)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := after_expression
    (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, post, formed.heaps, represented⟩, determined⟩

end Ordinary

namespace Principal

section Prepared
open CallableIndexedOwnedPreparedPrincipalLambdaSupport (Support PreparedAt)

/-- The prepared principal seed of a code is the seed of the same code over
other captures. -/
theorem prepared_recapture {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code} (prepared : PreparedAt code support) (environment : Dynamic.Environment) :
    PreparedAt (code.recapture environment) (support.recapture environment) := by
  cases prepared with
  | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView _ =>
    exact .recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView environment

/-- A prepared principal code is the lambda of a selected method Site, which
copies its captures. -/
theorem prepared_snapshots {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code} (prepared : PreparedAt code support) :
    code.policy.snapshotLambda code.id = true := by
  cases prepared with
  | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView environment =>
    exact site.snapshots

end Prepared

variable
  (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (qualified : ∀ environment, qualification.principal (code.recapture environment) (support.recapture environment))
  (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

/-- Selected method authority supplies its original dictionary-bearing seed. -/
def history_at : History code where
  native := (initial.rows owner.position).authority.current
  ghost := (initial.rows owner.position).authority.ghost
  metadata := CallableIndexedNamedGeneration.state support.principal.named
  carried := packet.carried
  source := support.source.symm
  owner := by rw [support.compilation]; rfl
  active := support.active.symm

include packet in
theorem leading : captured.administrative[0]? = some support.principal.named.signature.parameterType := by
  have bundle := packet.bundle
  rw [captured.represented.runtime_hasTypes.type_tags] at bundle
  simpa [SourceCoreLocalCell.coreContext, List.getElem?_append] using bundle

include support in
theorem reference_index : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  rw [CallableIndexedLambdaValues.Code.referenceIndex, support.compilation]
  rfl

local notation "history" => history_at captured code owner support initial packet
local notation "carrier " formed:max => value code (Formed.embedding formed)
  (CallableIndexedLambdaValues.History.native history) (Formed.closureActual formed)

include packet prepared qualified profile in
/-- The real Principal frame read and the same Code's elementary formation,
which copies the captured cells, construct one direct selected-method member
for the formed closure without an ordinary Header. -/
theorem formation_member
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (carrier formed)) formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (carrier formed) code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (carrier formed) ∧ finalStore = formed.finalStore) := by
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [reference_index captured code support]
    exact packet.observed.reference
  have read : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
        (CallableIndexedLambdaValues.History.native history)) := by
    have actualRead := (initial.rows owner.position).authority.frame.read
    rw [(initial.rows owner.position).frame_eq] at actualRead
    exact actualRead
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured code history (prepared_snapshots prepared)
    (reference_index captured code support) heaps reference read
  have typed := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := bodyRegistry) (formed.represents heaps.runtime_hasTypes)
  have leadingFormed : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    leading captured code owner support initial packet
  exact ⟨formed, formed.source _ ordinary coercions, formed.evaluated,
    ⟨.principal (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨rfl⟩ (prepared_recapture prepared formed.captured)
      (qualified formed.captured) (packet.observed.of_slots formed.slots) leadingFormed
      (reference_index captured code support) typed⟩,
    fun _ _ completed => Core.evaluation_deterministic completed formed.evaluated⟩

variable
  (cells : CellOrigins qualification headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile qualified in
/-- Selected Principal formation keeps the actual packet, transported to the
formed state, with direct cells over the copies and the represented result,
with its independently indexed receiving registry. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
        captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (carrier formed)) formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (carrier formed) code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner
          support.principal.named).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩,
        (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates
          ⟨initial, packet⟩ reached ∧
        Post (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
          (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
          function.context qualification profile code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure)) (.inRight .word (carrier formed)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (carrier formed) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code owner qualification profile support qualified prepared initial packet cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functions qualification headers keys bodyRegistry faults profile))
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (carrier formed)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedPreparedNativeDirectCellOrigins.payload_static_member (registry := registry) profile member
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named)
    (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := after_expression
    (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, post, formed.heaps, represented⟩, determined⟩

end Principal
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectFormationReceipts

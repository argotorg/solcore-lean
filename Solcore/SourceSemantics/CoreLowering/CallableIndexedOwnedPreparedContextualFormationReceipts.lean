import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalFormationReceipts

/-! Actual ordinary and selected-method formation directly construct the stronger
prepared closure leaf. Each factory runs once at its authentic input packet.
Incoming prepared cells remain at that unchanged heap and store; the actual
Source trace establishes admission there. The receiving registry is explicit
and independent of body preparation. No legacy ResultAt projection, old-leaf
upgrade or semantic body callback is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualCellOrigins (StaticMember CellOrigins PostWithOrigins)
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
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

namespace Ordinary
variable {canonical : Environment}
  (support : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Support code)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

local notation "plain" => CallableIndexedOwnedPreparedOrdinaryBodyProjection.plain support actualSites sites
local notation "history" => CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
  captured code plain owner initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

include actualSites sites packet prepared profile prefixContext observed in
/-- The ordinary factory's actual trace and runtime typing justify the one new
leaf. Preparation comes directly from the retained support at that same Code. -/
theorem formation_member
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word carrier) store ∧
    StaticMember headers keys bodyRegistry faults mapping world function carrier
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word carrier ∧ finalStore = store) := by
  obtain ⟨sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.formation
      captured code plain owner initial packet profile prefixContext observed
      (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile)
      (fun related => related) stored ordinary coercions
  have typed : RuntimeValueHasType world carrier
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions :=
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
      (registry := bodyRegistry) represented
  exact ⟨sourceTrace, nativeTrace,
    StaticMember.ordinary (.ordinary owner captured code history support actualSites sites ⟨rfl⟩ prepared
      prefixContext observed
      (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reference_index captured code plain) typed),
    determined⟩

variable
  (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include actualSites sites cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile prefixContext observed in
/-- Strong cells and the newly prepared value accompany the original formation
at its unchanged actual packet. Only the real trace establishes Source admission. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word carrier) store ∧
    StaticMember headers keys bodyRegistry faults mapping world function carrier
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
    PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      function.context profile code.sourceNode.type code.lowered.type
      (.value (.closure function)) (.inRight .word carrier) ⟨initial, packet⟩ ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word carrier ∧ finalStore = store) := by
  obtain ⟨sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code owner profile support actualSites sites prepared initial packet prefixContext observed
    cells.runtime_hasTypes ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      mapping world code.sourceNode.type code.lowered.type faults
      (.value (.closure function)) (.inRight .word carrier) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedPreparedContextualCellOrigins.payload_static_member (registry := registry) profile member
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ ⟨initial, packet⟩ admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) (AdministrativePreserved.refl mapping store)
  exact ⟨sourceTrace, nativeTrace, member,
    CallableIndexedOwnedPreparedContextualCellOrigins.post_at_same_state
      (bodyRegistry := bodyRegistry) (registry := registry)
      (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      profile ⟨initial, packet⟩ post cells represented,
    determined⟩

end Ordinary

namespace Principal
variable
  (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

local notation "plain" => support.plain actualSites sites
local notation "history" => CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
  captured code plain owner initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

include actualSites sites packet prepared profile in
/-- The existing prepared method producer runs once with actual selected
dictionary authority; its retained Receipt enters the stronger leaf directly. -/
theorem formation_member
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word carrier) store ∧
    StaticMember headers keys bodyRegistry faults mapping world function carrier
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word carrier ∧ finalStore = store) := by
  obtain ⟨sourceTrace, nativeTrace, preparedMember, determined⟩ :=
    CallableIndexedOwnedPreparedPrincipalFormationReceipts.formation_member
      captured code support actualSites sites prepared owner initial packet profile stored ordinary coercions
  obtain ⟨receipt⟩ := preparedMember
  exact ⟨sourceTrace, nativeTrace, StaticMember.principal receipt, determined⟩

variable
  (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include actualSites sites cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile in
/-- The actual formed carrier and unchanged principal packet receive strong
prepared cells/result without projecting to a one-registry legacy contract. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word carrier) store ∧
    StaticMember headers keys bodyRegistry faults mapping world function carrier
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
    PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      function.context profile code.sourceNode.type code.lowered.type
      (.value (.closure function)) (.inRight .word carrier) ⟨initial, packet⟩ ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word carrier ∧ finalStore = store) := by
  obtain ⟨sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code owner profile support actualSites sites prepared initial packet
    cells.runtime_hasTypes ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedPreparedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      mapping world code.sourceNode.type code.lowered.type faults
      (.value (.closure function)) (.inRight .word carrier) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact CallableIndexedOwnedPreparedContextualCellOrigins.payload_static_member (registry := registry) profile member
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ ⟨initial, packet⟩ admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) (AdministrativePreserved.refl mapping store)
  exact ⟨sourceTrace, nativeTrace, member,
    CallableIndexedOwnedPreparedContextualCellOrigins.post_at_same_state
      (bodyRegistry := bodyRegistry) (registry := registry)
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      profile ⟨initial, packet⟩ post cells represented,
    determined⟩

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualFormationReceipts

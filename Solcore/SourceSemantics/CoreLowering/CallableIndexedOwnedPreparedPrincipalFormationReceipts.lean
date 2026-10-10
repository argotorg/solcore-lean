import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins

/-! One original principal formation produces the genuine Source/native trace.
The retained prepared principal support constructs its prospective positive
receipt at that exact carrier. The same trace adds Source admission and the
existing positive post at the unchanged reached packet. No old StaticMember
is inverted and no body callback is supplied. The current payload model still
stores the forward plain leaf; migration to prepared leaves remains separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedPrincipalLambdaSupport (Support PreparedAt Receipt)
open CallableIndexedOwnedContextualCellOrigins (CellOrigins PostWithOrigins)
open CallableIndexedOwnedSourceAdmission

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {scope : SourceCoreLocalCell.Scope} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree support.body).CatalogSites
    .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
  (prepared : PreparedAt code support)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "plain" => support.plain actualSites sites
local notation "history" => CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
  captured code plain owner initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

include actualSites sites packet prepared profile in
/-- The authentic method factory runs once. Preparation is retained from its
own support, and runtime typing comes from that actual formed value. -/
theorem formation_member
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word carrier) store ∧
    Nonempty (Receipt headers keys bodyRegistry faults mapping world function carrier
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word carrier ∧ finalStore = store) := by
  obtain ⟨sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedMethodLambdaFormationReceipts.formation
      captured code plain owner initial packet profile stored ordinary coercions
  have typed : RuntimeValueHasType world carrier
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions :=
    (CallableIndexedOwnedMethodLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
      (registry := bodyRegistry) represented
  exact ⟨sourceTrace, nativeTrace,
    ⟨.principal owner captured code history support actualSites sites ⟨rfl⟩ prepared packet.observed
      (CallableIndexedOwnedMethodLambdaFormationReceipts.leading captured code plain owner initial packet)
      (CallableIndexedOwnedMethodLambdaFormationReceipts.reference_index captured code plain) typed⟩,
    determined⟩

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
/-- The prepared receipt and current positive post accompany the same actual
Source/native formation and unchanged reached packet. The factory is invoked
once; only the new value erases forward into the current plain positive model. -/
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word carrier) store ∧
    Nonempty (Receipt headers keys bodyRegistry faults mapping world function carrier
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore) ∧
    PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      function.context profile code.sourceNode.type code.lowered.type
      (.value (.closure function)) (.inRight .word carrier) ⟨initial, packet⟩ ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word carrier ∧ finalStore = store) := by
  obtain ⟨sourceTrace, nativeTrace, member, determined⟩ := formation_member
    captured code support actualSites sites prepared owner initial packet profile
    cells.runtime_hasTypes ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      mapping world code.sourceNode.type code.lowered.type faults
      (.value (.closure function)) (.inRight .word carrier) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    obtain ⟨receipt⟩ := member
    exact CallableIndexedOwnedContextualCellOrigins.payload_static_member (registry := registry) profile ⟨receipt.forget⟩
  have post := CallableIndexedOwnedSourceAdmission.after_expression
    (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ ⟨initial, packet⟩ admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) (AdministrativePreserved.refl mapping store)
  exact ⟨sourceTrace, nativeTrace, member,
    CallableIndexedOwnedContextualCellOrigins.post_at_same_state
      (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
      profile ⟨initial, packet⟩ post cells represented,
    determined⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalFormationReceipts

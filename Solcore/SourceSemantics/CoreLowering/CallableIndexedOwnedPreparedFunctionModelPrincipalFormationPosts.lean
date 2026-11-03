import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelFormationBounds

/-! The exact principal formation post is exposed for caller restoration.
The original prepared formation runs once, copying the captured cells, and the
incoming pool is transported to the formed heap, mapping, world and store under
the receiving function model. The proof is the existing principal formation
proof with a public port. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelPrincipalFormationPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (StaticMember)
open CallableIndexedOwnedSourceAdmission

open CallableIndexedOwnedPreparedFunctionModelFormationBounds (Post)

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
  (models : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (lift : ∀ {mapping world function native bindings parameter result},
    StaticMember qualification headers keys bodyRegistry faults mapping world function native bindings parameter result →
    models.Represents registry mapping world (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameter result))

variable
  (support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code)
  (qualified : ∀ environment, qualification.principal (code.recapture environment) (support.recapture environment))
  (prepared : CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)

local notation "history" => CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.history_at
  captured code owner support initial packet
local notation "carrier" => value code captured.embedding (CallableIndexedLambdaValues.History.native history) actual

variable
  (cells : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry models mapping world heap store)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (admitted : Admission (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    function.context ⟨initial, packet⟩)

include lift cells wellFormed runtime covers locals typed sourceType admitted prepared packet profile qualified in
theorem formation_post
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models) captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual))
        formed.finalStore ∧
      StaticMember qualification headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      (∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named).State
          ⟨scope, formed.finalMap, formed.finalWorld, formed.finalHeap, formed.finalStore, captured.canonical⟩,
        (CallableIndexedOwnedOriginCanonicalState.protocol owner support.principal.named).Relates ⟨initial, packet⟩ reached ∧
        Post (models := models) (registry := registry) (faults := faults)
          (CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named) function.context code.sourceNode.type code.lowered.type
          (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) reached) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual) ∧ finalStore = formed.finalStore) := by
  obtain ⟨formed, sourceTrace, nativeTrace, member, determined⟩ :=
    CallableIndexedOwnedPreparedDirectFormationReceipts.Principal.formation_member
      captured code owner qualification profile support qualified prepared initial packet
      cells ordinary coercions
  have represented : GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry models)
      formed.finalMap formed.finalWorld code.sourceNode.type code.lowered.type faults
      (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding (CallableIndexedLambdaValues.History.native history) formed.closureActual)) := by
    apply FunctionCalls.ResultRepresents.value
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact .function (lift member)
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner support.principal.named) (CallableIndexedOwnedOriginCanonicalState.administrativeTransport (headers := headers) owner support.principal.named)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := after_expression (bridge := CallableIndexedOwnedMethodLambdaEntries.bridge (headers := headers) owner support.principal.named)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨formed, sourceTrace, nativeTrace, member, ⟨reached, related, ⟨post, formed.heaps, represented⟩⟩, determined⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFunctionModelPrincipalFormationPosts

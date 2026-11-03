import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualInitializedClosureReceipts

/-! One actual contextual formation returns its original source/native traces,
receiving-model value and positive Member. Formation copies the captured cells
over the incoming CellOrigins receipt, so that receipt holds again at the formed
state, where the Member is the formed closure over the copies. Forward
attachment of the Member supplies the strong payload at that actual native
value. Ordinary and principal packets retain their original authority and
history. The original Selection supplies its same-code escaped-control row; no
general-model inverse, allocation replay or body meaning is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginFormationReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualStoredClosureAssociationReceipts (Member)
open CallableIndexedOwnedContextualCellOrigins (PayloadOrigins CellOrigins)

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
  (receiving : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).Includes receiving)
  (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {parentScope : SourceCoreLocalCell.Scope}
  {parentId callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  {certificate : GenericExpressionMeaning.Certificate}
  (compiler : CallableIndirectCallCertificates.Receipt policy lowerBody fuel compilation source parentScope
    parentId callee ids metadata reasonAt lowered)
  {nativeContext : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler nativeContext)
  (selected : CallableIndexedOwnedSelectedIndirectHeads.Selection (faults := faults)
    (certificate := certificate) compiler prepared code)

section Ordinary
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

include inclusion cells selected prefixContext observed provenance in
/-- The original ordinary formation factory runs once over the incoming
positive cells, under its actual receiving model. The strong result, Member
and heap describe the same formed closure over the copies of its captured
cells and its original packet-derived history. -/
theorem ordinary_formation
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      receiving.Represents bodyRegistry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      Member headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      PayloadOrigins headers keys bodyRegistry registry faults profile formed.finalMap formed.finalWorld
        (FunctionValues.sourceType function) (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      CellOrigins headers keys bodyRegistry registry faults profile formed.finalMap formed.finalWorld
        formed.finalHeap formed.finalStore ∧
      FunctionCalls.ResultRepresents
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
        formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) faults
        (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding
          (history_at captured code support owner initial packet).native formed.closureActual)) := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedGeneralLambdaValues.ordinary_lambda_of_formation initial owner captured code
      (history_at captured code support owner initial packet) support
      (source_origin captured code support owner initial packet) prefixContext observed
      (reference_index captured code support) rfl profile cells copied ordinary coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
    (registry := bodyRegistry) represented
  have member : Member headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore :=
    .ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨(source_origin captured code support owner initial packet).metadata⟩
      prefixContext (observed.of_slots formed.slots) (reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.provenance_recapture provenance formed.captured)
      selected.escaped
  have payload := CallableIndexedOwnedContextualCellOrigins.payload_member (registry := registry) profile member
  exact ⟨formed, sourceTrace, nativeTrace, inclusion member.represents, determined, member, payload, formed.heaps,
    .value payload⟩

end Ordinary

section Principal
variable
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code bodyRegistry faults)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code support)

open CallableIndexedOwnedMethodLambdaFormationReceipts (history_at source_origin leading reference_index)

include inclusion cells selected packet provenance in
/-- The original principal formation factory runs once over the incoming
positive cells. Its actual leading bundle, Source origin and history stay in
the same Member, now at the formed closure over the copies of its captured
cells; a forward strong payload receipt is added at the formed heap and store. -/
theorem principal_formation
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      receiving.Represents bodyRegistry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) ∧
      Member headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
      PayloadOrigins headers keys bodyRegistry registry faults profile formed.finalMap formed.finalWorld
        (FunctionValues.sourceType function) (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      CellOrigins headers keys bodyRegistry registry faults profile formed.finalMap formed.finalWorld
        formed.finalHeap formed.finalStore ∧
      FunctionCalls.ResultRepresents
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
        formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) faults
        (.value (.closure formed.closure)) (.inRight .word (value code formed.embedding
          (history_at captured code support owner initial packet).native formed.closureActual)) := by
  obtain ⟨formed, sourceTrace, nativeTrace, represented, determined⟩ :=
    CallableIndexedOwnedAdmittedPrincipalLambdaFormation.principal_representation captured code support owner
      initial packet profile cells copied ordinary coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).runtime_hasType
    (registry := bodyRegistry) represented
  have leadingFormed : formed.captures.administrative[0]? = some support.principal.named.signature.parameterType :=
    leading captured code support owner initial packet
  have member : Member headers keys bodyRegistry faults formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore :=
    .principal (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (CallableIndexedOwnedMethodLambdaValues.recaptureSupport support formed.captured)
      (CallableIndexedOwnedMethodLambdaValues.recaptureOrigin (source_origin captured code support owner initial packet)
        formed.captured)
      (packet.observed.of_slots formed.slots) leadingFormed (reference_index captured code support) typed
      (CallableIndexedOwnedAdmittedContextualPrincipalLambdaFormation.provenance_recapture provenance formed.captured)
      selected.escaped
  have payload := CallableIndexedOwnedContextualCellOrigins.payload_member (registry := registry) profile member
  exact ⟨formed, sourceTrace, nativeTrace, inclusion member.represents, determined, member, payload, formed.heaps,
    .value payload⟩

end Principal
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginFormationReceipts

import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualInitializedClosureReceipts

/-! One actual contextual formation returns its original source/native traces,
receiving-model value and positive Member. Pure formation keeps the input heap
and store, so the same CellOrigins receipt remains valid. Forward attachment of
the Member supplies the strong payload at that actual native value. Ordinary
and principal packets retain their original authority and history. The original
Selection supplies its same-code escaped-control row; no general-model inverse,
allocation replay or body meaning is used. -/
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

include inclusion cells selected prefixContext observed provenance in
/-- The original ordinary formation factory runs once under its actual
receiving model. The strong result and heap describe the same pure tuple and
its original packet-derived history. -/
theorem ordinary_formation
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
          captured code support owner initial packet).native actual)) store ∧
    receiving.Represents bodyRegistry mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
          captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
          captured code support owner initial packet).native actual) ∧ finalStore = store) ∧
    Member headers keys bodyRegistry faults mapping world function
      (value code captured.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
          captured code support owner initial packet).native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
    PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
          captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store ∧
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      mapping world (FunctionValues.sourceType function)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) faults
      (.value (.closure function)) (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
          captured code support owner initial packet).native actual)) := by
  obtain ⟨sourceTrace, nativeTrace, represented, determined, member⟩ :=
    CallableIndexedOwnedContextualStoredClosureAssociationReceipts.formation_member
      (captured := captured) (code := code) (support := support) (owner := owner)
      (initial := initial) (packet := packet) (profile := profile) (prefixContext := prefixContext)
      (observed := observed) (provenance := provenance) (functions := receiving)
      (inclusion := inclusion) (escaped := selected.escaped) cells.runtime_hasTypes ordinary coercions
  have payload := CallableIndexedOwnedContextualCellOrigins.payload_member (registry := registry) profile member
  exact ⟨sourceTrace, nativeTrace, represented, determined, member, payload, cells, .value payload⟩

end Ordinary

section Principal
variable
  (support : CallableIndexedOwnedMethodLambdaSupport.Support code bodyRegistry faults)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner support.principal.named _ initial)
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code support)

include inclusion cells selected packet provenance in
/-- The original principal formation factory runs once. Its actual leading
bundle, Source origin and history stay in the same Member; only a forward
strong payload receipt is added to the unchanged input heap and store. -/
theorem principal_formation
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
          captured code support owner initial packet).native actual)) store ∧
    receiving.Represents bodyRegistry mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
          captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
          captured code support owner initial packet).native actual) ∧ finalStore = store) ∧
    Member headers keys bodyRegistry faults mapping world function
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
          captured code support owner initial packet).native actual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore ∧
    PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
          captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store ∧
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      mapping world (FunctionValues.sourceType function)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) faults
      (.value (.closure function)) (.inRight .word (value code captured.embedding
        (CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
          captured code support owner initial packet).native actual)) := by
  obtain ⟨sourceTrace, nativeTrace, represented, determined, member⟩ :=
    CallableIndexedOwnedContextualStoredClosureAssociationReceipts.principal_formation_member
      (captured := captured) (code := code) (support := support) (owner := owner)
      (initial := initial) (packet := packet) (profile := profile) (provenance := provenance)
      (functions := receiving) (inclusion := inclusion) (escaped := selected.escaped)
      cells.runtime_hasTypes ordinary coercions
  have payload := CallableIndexedOwnedContextualCellOrigins.payload_member (registry := registry) profile member
  exact ⟨sourceTrace, nativeTrace, represented, determined, member, payload, cells, .value payload⟩

end Principal
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginFormationReceipts

import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts

/-! One actual public bootstrap and parameter construction retain both strong
body contracts at the same receipt, including the genuine lexical exit and
returned admission. These proof ports perform no public execution action. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicBodyExitReceipts
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedNamedGeneration
open SourceCoreChosenOrdinaryAcceptedFixture SourceCoreChosenOrdinaryAcceptedHeader
open SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence
open SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt

variable (fixture : AcceptedFixture) {caller : ActualHeader fixture}
  {compilation : Compilation fixture.packet.compiled.indexed caller.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.Root fixture caller compilation)
  (inventory : SourceCoreChosenOrdinaryAcceptedStaticInventory.Inventory fixture)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {world : StoreTyping} {store : Store}

variable
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
    (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions fixture root inventory registry faults) registry world store)
  (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions fixture root inventory registry faults) (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) initial.state caller [])

/-- The original parameter agreement and both strong body contracts name the
same actual receipt. Source and native grades are independently quantified. -/
structure BodyAtReceiptWithExit : Prop where
  agreement : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.ParameterAgreement fixture initial receipt
  source : ∀ size,
    CallableIndexedOwnedPreparedNamedParameterReceipts.PreservesAt receipt (faults := faults) size
  native : ∀ size,
    CallableIndexedOwnedPreparedNamedParameterReceipts.ReflectsAt receipt (faults := faults) size

/-- The public recipe constructs the original parameter receipt once. Its
body ports retain the actual exit and returned state without low erasure. -/
theorem at_completed (prepared : PublicRecipeReceipt fixture)
    {fuel : Nat} (completed : CompletedBootstrap prepared fuel)
    (bootstrap : BootstrapEvidence fixture caller)
    (shape : SourceCoreChosenOrdinaryAcceptedTyping.Shape fixture)
    (typing : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
    (checked : SourceCoreChosenOrdinaryAcceptedHeader.Metadata fixture.packet)
    (chosen : SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts.ChosenParentReceipt fixture root)
    (outer : SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts.Receipt fixture)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial fixture.packet.compiled.compatible.checked).registry registry) :
    ∃ world,
    ∃ initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
        (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions fixture root inventory registry faults) registry world completed.store,
    ∃ receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
        (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions fixture root inventory registry faults) (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) initial.state caller [],
      BodyAtReceiptWithExit fixture root inventory initial receipt := by
  obtain ⟨world, initial, receipt, agreement⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.parameter_entry fixture prepared completed bootstrap
      (SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence.functions fixture root inventory registry faults) registry
  have complete := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete fixture prepared bootstrap.toHeaderAt
  have prefixZero : (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).key.capturePrefix = 0 := rfl
  refine ⟨world, initial, receipt, agreement, ?_, ?_⟩
  · intro size
    exact SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts.source_preserves_at_receipt
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) complete prefixZero receipt extension size
  · intro size
    exact SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts.native_reflects_at_receipt
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) complete prefixZero receipt extension size

end Tests.SourceCoreChosenOrdinaryAcceptedPublicBodyExitReceipts

import Solcore.Test.SourceCoreChosenOrdinaryAcceptedPublicParameterEntry
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence

/-! The genuine public bootstrap and parameter prefix produce one actual body
receipt. Both body meanings hold at that same receipt, retaining its returned
pool and Source admission as well as the original continuation agreement. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
namespace Tests.SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence
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

/-- The receiving chosen model uses the one actual root and singleton public
catalog in both the constructed initial state and the body result. -/
def functions (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed) :=
  CallableIndexedOwnedChosenOrdinaryLambdaValues.model root.root
    (SourceCoreChosenOrdinaryAcceptedLiteralFactory.literalSyntax fixture)
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.headers fixture caller)
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.keys fixture) registry faults inventory.contracts

variable {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {world : StoreTyping} {store : Store}
  (initial : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.InitialAt fixture caller
    (functions fixture root inventory registry faults) registry world store)
  (receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
    (functions fixture root inventory registry faults)
    (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) initial.state caller [])

/-- Every port is a conclusion at the same produced receipt. The strong body
result keeps its actual returned pool and successful Source post admission. -/
structure BodyAtReceipt : Prop where
  agreement : SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.ParameterAgreement fixture initial receipt
  preserves : ∀ (budget : Nat) {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
      size caller.function caller.context receipt.body.environment receipt.body.heap outcome after →
    size ≤ budget →
    ∃ value finalStore finalMap finalWorld,
      Evaluates receipt.body.actualBody receipt.body.store (caller.body.rename receipt.body.embedding) value finalStore ∧
      SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.ResultAt
        (fixture := fixture) (root := root) (inventory := inventory)
        (owner := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
        (receipt := receipt) outcome after value finalStore finalMap finalWorld
  reflects : ∀ (budget : Nat) {size : Nat} {value : Value} {finalStore : Store},
    EvaluationSize size receipt.body.actualBody receipt.body.store
      (caller.body.rename receipt.body.embedding) value finalStore →
    size ≤ budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked fixture.packet.compiled.sourceProgram)
        sourceSize caller.function caller.context receipt.body.environment receipt.body.heap outcome after ∧
      SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.ResultAt
        (fixture := fixture) (root := root) (inventory := inventory)
        (owner := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture)
        (receipt := receipt) outcome after value finalStore finalMap finalWorld
  source_body_at : ∀ size,
    CallableIndexedOwnedInvocationBounds.SourceBodyAt (faults := faults) receipt.body receipt.reached size
  native_body_at : ∀ size,
    CallableIndexedOwnedInvocationBounds.NativeBodyAt (faults := faults) receipt.body receipt.reached size

/-- One actual public parameter construction closes both body meanings.
Complete comes from that same public recipe; the capture prefix is literally
zero. Static Source/compiler receipts and the receiving registry stay genuine. -/
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
        (functions fixture root inventory registry faults) registry world completed.store,
    ∃ receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry)
        (functions fixture root inventory registry faults)
        (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) initial.state caller [],
      BodyAtReceipt fixture root inventory initial receipt := by
  obtain ⟨world, initial, receipt, agreement⟩ :=
    SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.parameter_entry fixture prepared completed bootstrap
      (functions fixture root inventory registry faults) registry
  have complete := SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.catalog_complete fixture prepared bootstrap.toHeaderAt
  have prefixZero : (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture).key.capturePrefix = 0 := rfl
  refine ⟨world, initial, receipt, agreement, ?_, ?_, ?_, ?_⟩
  · intro budget size outcome after trace within
    exact SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.preserves_at_receipt
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) complete prefixZero receipt extension budget trace within
  · intro budget size value finalStore nativeCompleted within
    exact SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.reflects_at_receipt
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) complete prefixZero receipt extension budget nativeCompleted within
  · intro size
    exact SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.source_body_at
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) complete prefixZero receipt extension size
  · intro size
    exact SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence.native_body_at
      fixture bootstrap.toRuntimeEvidence shape typing checked inventory root chosen outer
      (SourceCoreChosenOrdinaryAcceptedPublicParameterEntry.owner fixture) complete prefixZero receipt extension size

end Tests.SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence

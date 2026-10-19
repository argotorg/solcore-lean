import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicPhysicalHistory
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicHistoryArgumentsReceiving
import Solcore.SourceSemantics.CoreLowering.CellAwarePhysicalFunctionOrigins

/-! Public history is instantiated directly with positive physical closure
origins. Original export and reimport receipts preserve those origins through
containers, repeated handles, and actual returned sessions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicClosureHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key)
open RecursiveNamedPublicFunctionHistory (Caller Entry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry receiving : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}

local notation "rootFunctions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry faults profile

abbrev History {artifact : Artifact} (session : Session artifact)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (caller : Caller headers keys mapping world heap store) (entries : List Entry) : Prop :=
  CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := cells) (receiving := receiving) (anchor := anchor)
    session mapping world heap store caller entries

/-- The original history supplies positive captured members, the current heap,
and the exact physical cache. The actual input encoder chooses each retained
handle at its original argument position. -/
theorem History.current_arguments
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
    {caller : Caller headers keys mapping world before store}
    (history : History (cells := cells) (bodyRegistry := bodyRegistry) (faults := faults) (profile := profile)
      (receiving := receiving) (anchor := anchor) session mapping world before store caller entries)
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {root : Root compiled} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
    {publicArguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    {payloads : Environment} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint recipe
      ((Recipe.prepare_compiled prepared).symm ▸ root) world store payloads encodedValues)
    {arguments : List Dynamic.Value}
    (inputReceipts : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries header.function.context
      (header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
      GenericHeap.CellHeapRepresents cells mapping world before store ∧
      Dynamic.HeapWellTyped header.function.context before ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving rootFunctions)
        mapping world header.bindings arguments payloads ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨_nativeAt, heaps, stable, heapTyped, retained⟩ := history.semantic.current
  have contexts := SelectedCompilationPublicReturnedValues.header_context_supports anchor header bodyTyping
  obtain ⟨represented, argumentsTyped⟩ :=
    SelectedCompilationPublicHistoryArgumentsReceiving.StartAt.history_arguments_receiving
      started _ selected entries (fun entry member => (retained entry member).1)
      (fun entry member => (retained entry member).2.1)
      (fun entry member => (retained entry member).2.2.transportContext contexts.1)
      inputReceipts metadata (SelectedCompilationHeaderCertificates.certified bodyTyping header)
  exact ⟨stable, heaps, heapTyped.transportContext contexts.1, represented, argumentsTyped⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicClosureHistory

import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOrdinaryRootLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedRootLifting

/-! The ordinary Source trace determines the induction grade. Each real body
uses strictly smaller ordinary traces; independently measured staged prefixes
supply the reached physical state through the closed preservation family. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageActualLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open SelectedCompilationPhysicalProgramSupport (Support functions stages)
open SelectedCompilationStageLiftBounds (LiftsRootsAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys initial)
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)

include issued extension in
/-- Every original selected expression either preserves its ordinary outcome
and heap or reaches a genuine earlier stage rejection at its exact heap. -/
theorem lifts_roots (size : Nat) :
    LiftsRootsAt (headers := headers) (keys := keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support))
      (stages compiled) (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics) size := by
  induction size using Nat.strongRecOn with
  | ind budget children =>
    intro context invocation scope expression lowered root owner keyPhysical
    cases root.support with
    | ordinary actual =>
      exact SelectedCompilationStageOrdinaryRootLifting.lifts
        support issued extension actual owner keyPhysical budget children
    | coercedDirect actual =>
      exact SelectedCompilationStageCoercedRootLifting.lifts
        support issued extension actual owner keyPhysical budget children

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageActualLifting

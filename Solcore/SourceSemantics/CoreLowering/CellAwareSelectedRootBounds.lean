import Solcore.SourceSemantics.CoreLowering.CellAwareStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerSlotForgetting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures

/-! The numeric family quantifies over roots with actual complete cache state.
Every invocation produces this same carrier through its parameter allocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSelectedRootBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationMixedRootSupport (RootAt)
open CellAwareStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (cells : GenericHeap.CellModel definitions)
  (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
  (faults : RecursiveStageMeaning.FaultRep)

def PreservesRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : RootAt compiled headers stages context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    PreservesAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      context model cells stages invocation (Point scope expression lowered) faults size

def ReflectsRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : RootAt compiled headers stages context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    ReflectsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      context model cells stages invocation (Point scope expression lowered) faults size

theorem preservesRootsAt_ordinary_iff (size : Nat) :
    PreservesRootsAt (headers := headers) (keys := keys) model (GenericHeap.CellModel.ordinary model)
      stages semanticFaults faults size ↔
    SelectedCompilationMixedRootBounds.PreservesRootsAt (headers := headers) (keys := keys) model
      stages semanticFaults faults size := by
  simp only [PreservesRootsAt, SelectedCompilationMixedRootBounds.PreservesRootsAt, CellAwareStagedExpressionBounds.preservesAt_ordinary_iff]

theorem reflectsRootsAt_ordinary_iff (size : Nat) :
    ReflectsRootsAt (headers := headers) (keys := keys) model (GenericHeap.CellModel.ordinary model)
      stages semanticFaults faults size ↔
    SelectedCompilationMixedRootBounds.ReflectsRootsAt (headers := headers) (keys := keys) model
      stages semanticFaults faults size := by
  simp only [ReflectsRootsAt, SelectedCompilationMixedRootBounds.ReflectsRootsAt, CellAwareStagedExpressionBounds.reflectsAt_ordinary_iff]

end Solcore.SourceSemantics.CoreLowering.CellAwareSelectedRootBounds

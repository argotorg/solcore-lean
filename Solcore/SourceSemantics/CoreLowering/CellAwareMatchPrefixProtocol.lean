import Solcore.SourceSemantics.CoreLowering.CellAwareScopeAuthority
import Solcore.SourceSemantics.CoreLowering.ProtectedStateCellAllocation
import Solcore.SourceSemantics.CoreLowering.ProtectedStateScopeReturn

/-! Match prefixes allocate ordinary cells while retaining generalized cells.
The existing prefix proofs carry this concrete effect in their protocol relation;
the underlying protected state and its observation are unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMatchPrefixProtocol
open Core Frontend SourceInference GeneralHeap CallableIndexedHistory
open ProtectedStateTransition
universe u v

variable {Records : Type v} {definitions : DataEnvironment}
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions)
    (protocol : Protocol.{u, v} Records)

/-- Every relation edge retains the actual mapped descriptor rows. -/
def withEffects : Protocol.{u, v} Records where
  State := protocol.State
  records := protocol.records
  Relates := fun {initial reached} first last =>
    protocol.Relates first last ∧ CellAwareScopeAuthority.Effect instances
      initial.mapping initial.world initial.heap initial.store
      reached.mapping reached.world reached.heap reached.store
  refl := fun {_index} state => ⟨protocol.refl state, .refl _ _ _ _⟩
  trans := fun first second => ⟨protocol.trans first.1 second.1, first.2.trans second.2⟩

def bindings (original : Bindings protocol) : Bindings (withEffects instances protocol) where
  prepend := original.prepend
  prepend_related := fun state id type value =>
    ⟨original.prepend_related state id type value, .refl _ _ _ _⟩
  prepend_records := original.prepend_records
  restore := original.restore
  restore_related := fun state => ⟨original.restore_related state, .refl _ _ _ _⟩
  restore_records := original.restore_records

/-- The real allocator appends its snapshot, marker and payload. This proves
descriptor retention from the actual operation, without a separate effect law. -/
def producer {catalog : SourceCoreDataCatalog.Catalog}
    {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {cells : GenericHeap.CellModel definitions}
    (original : CellAllocation.Producer (catalog := catalog) protocol layouts frame cells) :
    CellAllocation.Producer (catalog := catalog) (withEffects instances protocol) layouts frame cells where
  Ready := original.Ready
  complete := by
    intro owner active request globals allocate allocation annotation same nativeDefinitions registered
      mapping world administrative environment canonical actual before after store contextLocation native
      sourceCell payload sourceLocation environments agrees heaps reference read payloadAt cell allocated initial ready
    obtain ⟨captured, captures, captureTyped, evaluated, finalHeaps, finalReference, preserved, final, related⟩ :=
      original.complete allocation annotation same nativeDefinitions registered environments agrees heaps
        reference read payloadAt cell allocated initial ready
    refine ⟨captured, captures, captureTyped, evaluated, finalHeaps, finalReference, preserved,
      final, related, ?_⟩
    exact CellAwareScopeAuthority.Effect.append _ _ allocated.metadata ⟨_, rfl⟩ ⟨_, rfl⟩

/-- Forget the additional relation component only after the caller has retained
its concrete effect and the same reached protected state. -/
def forgetReturn {scope canonical reachedScope reachedCanonical}
    (receipt : ReturnTo (withEffects instances protocol) scope canonical reachedScope reachedCanonical) :
    ReturnTo protocol scope canonical reachedScope reachedCanonical where
  restore := receipt.restore
  related := fun state => (receipt.related state).1
  records_eq := receipt.records_eq

end Solcore.SourceSemantics.CoreLowering.CellAwareMatchPrefixProtocol

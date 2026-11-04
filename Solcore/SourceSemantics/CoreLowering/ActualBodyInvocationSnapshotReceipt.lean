import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationAllocationReceipt
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.OrdinaryBodies

/-! A generalized declaration of an actual body policy snapshots its scope. Its
marked descriptor allocation has the same receipt as an ordinary initialized
let; the scope copies around the bundle initializer and that allocation are
returned with the literal continuation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference
open CellAwareGeneralizedSnapshotCode (snapshotInner snapshotSequence)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}

/-- A successful snapshot declaration exposes its actual marked callback, the
scope copies it emits around the bundle and its allocation, and its literal
continuation. -/
theorem Index.let_initialized_snapshot_receipt (index : Index compiled bodyRelation)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder}
    {output payload : Ty} {initializer body code : Expr}
    (accepted : SourceCoreSourceCells.letInitializedSnapshot index.policy.sourceCells source scope binder
      (LocalLoop.controlType output) payload initializer body = .ok code) :
    ∃ allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts
        index.owner index.active (TypedLexicalWhile.initializedRequest source scope binder payload),
      ∃ annotation : SourceCoreCallableIndexedAllocationFrames.Annotated
          compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
          (compiled.indexed.layouts.allocatorAt index.owner index.active
            (fun error => .sourceAllocation (reprStr error)))
          (TypedLexicalWhile.initializedRequest source scope binder payload),
        annotation.original = allocation.expression ∧
        ∃ captured, SourceCoreSourceCells.copyScope (some index.allocationCallback) source scope
            (fun index => index) (snapshotInner payload initializer annotation.expression) = .ok captured ∧
          code = snapshotSequence output captured body := by
  rw [index.sourceCells] at accepted
  simp only [SourceCoreSourceCells.letInitializedSnapshot] at accepted
  obtain ⟨allocationCode, generated, accepted⟩ := CompatibleEncoding.bind_ok accepted
  obtain ⟨captured, copied, accepted⟩ := CompatibleEncoding.bind_ok accepted
  cases accepted
  obtain ⟨allocation, annotation, same, codeEq⟩ :=
    index.allocation_receipt (request := TypedLexicalWhile.initializedRequest source scope binder payload) generated
  subst codeEq
  exact ⟨allocation, annotation, same, captured, copied, rfl⟩

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation

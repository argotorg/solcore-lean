import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationReachedReads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocation
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileTree

/-! Actual body policies retain their marked allocator. Receipts are indexed
by the compiler's concrete request source, independently of runtime Source.
Only the genuine body owner and input identifiers are related here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}

def Index.allocationCallback (index : Index compiled bodyRelation) : SourceCoreSourceCells.Allocator :=
  SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
    compiled.indexed.base.globals.length
    (compiled.indexed.layouts.allocatorAt index.owner index.active
      (fun error => .sourceAllocation (reprStr error)))

theorem Index.sourceCells (index : Index compiled bodyRelation) :
    index.policy.sourceCells = some index.allocationCallback := by
  cases index with
  | named receipt selected => rfl
  | contextual material view =>
    change (material.inputs.representation.atContext material.inputs.current.owner
      material.packet.original.emission.prepared.substitution).expressions.sourceCells = _
    rw [material.indexed.represented]
    change some (SourceCoreCallableIndexedAllocationFrames.allocator _ _
      (compiled.indexed.layouts.allocatorAt material.inputs.current.owner
        material.packet.original.emission.prepared.substitution
        (fun error => .sourceAllocation (reprStr error)))) = _
    simp only [Index.allocationCallback, Index.owner, Index.active, material.compilation,
      material.active, GeneralizedLocalLambdaCompilation.context]

theorem Index.compiler_owner (index : Index compiled ReachedView) :
    index.compilerSource.owner = index.source.owner := index.reached_view.owner.symm

theorem Index.compiler_inputs (index : Index compiled ReachedView) :
    index.compilerSource.inputs.map (·.id) = index.source.inputs.map (·.id) :=
  index.reached_view.inputs.symm

theorem Index.compiler_noninput (index : Index compiled ReachedView)
    {binder : Resolved.LocalId}
    (ordinary : index.source.inputs.any (fun input => decide (input.id = binder)) = false) :
    index.compilerSource.inputs.any (fun input => decide (input.id = binder)) = false := by
  have same := congrArg (fun inputs : List Resolved.LocalId => inputs.any (fun input => decide (input = binder))) index.compiler_inputs
  simp only [List.any_map, Function.comp_def] at same
  exact same.trans ordinary

/-- The annotation and marked allocation are returned by their original
factories at exactly the request passed by the accepted body policy. -/
theorem Index.allocation_receipt (index : Index compiled bodyRelation)
    {request : SourceCoreSourceCells.Request} {code : Expr}
    (accepted : index.allocationCallback request = .ok code) :
    ∃ allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts
        index.owner index.active request,
      ∃ annotation : SourceCoreCallableIndexedAllocationFrames.Annotated
          compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
          (compiled.indexed.layouts.allocatorAt index.owner index.active
            (fun error => .sourceAllocation (reprStr error))) request,
        annotation.original = allocation.expression ∧ annotation.expression = code := by
  unfold Index.allocationCallback at accepted
  obtain ⟨annotation, created, exact⟩ := CallableIndexedAllocation.allocator_receipt _ _ _ _ accepted
  have allocated := annotation.allocated
  unfold SourceCoreAllocationLayouts.Prepared.allocatorAt at allocated
  cases actual : SourceCoreAllocationLayouts.allocate compiled.indexed.layouts index.owner index.active request with
  | error error => simp only [actual, Except.mapError, reduceCtorEq] at allocated
  | ok output =>
    have same : output = annotation.original := by simpa only [actual, Except.mapError, Except.ok.injEq] using allocated
    obtain ⟨allocation, result⟩ := SourceCoreAllocationLayouts.allocate_receipt actual
    exact ⟨allocation, annotation, same.symm.trans result.symm, annotation.exact.trans exact.symm⟩

/-- A successful initialized let exposes its actual marked callback and its
literal continuation; no metadata equality of the two source tables is used. -/
theorem Index.let_initialized_receipt (index : Index compiled bodyRelation)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder}
    {output payload : Ty} {initializer body code : Expr}
    (accepted : SourceCoreSourceCells.letInitialized index.policy.sourceCells source scope Renaming.id
      binder (LocalLoop.controlType output) payload initializer body = .ok code) :
    ∃ allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts
        index.owner index.active (TypedLexicalWhile.initializedRequest source scope binder payload),
      ∃ annotation : SourceCoreCallableIndexedAllocationFrames.Annotated
          compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
          (compiled.indexed.layouts.allocatorAt index.owner index.active
            (fun error => .sourceAllocation (reprStr error)))
          (TypedLexicalWhile.initializedRequest source scope binder payload),
        annotation.original = allocation.expression ∧
        code = TypedLexicalWhile.sequence output initializer annotation.expression body := by
  rw [index.sourceCells] at accepted
  unfold SourceCoreSourceCells.letInitialized at accepted
  cases allocated : index.allocationCallback (TypedLexicalWhile.initializedRequest source scope binder payload) with
  | error error =>
    simp only [TypedLexicalWhile.initializedRequest, CompatibleStatementInitialized.request] at allocated
    simp only [allocated, bind, Except.bind, reduceCtorEq] at accepted
  | ok allocationCode =>
    have emitted : code = TypedLexicalWhile.sequence output initializer allocationCode body := by
      simp only [TypedLexicalWhile.initializedRequest, CompatibleStatementInitialized.request] at allocated
      simpa only [allocated, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        TypedLexicalWhile.sequence, CompatibleStatementInitialized.sequence] using accepted.symm
    obtain ⟨allocation, annotation, same, codeEq⟩ := index.allocation_receipt allocated
    exact ⟨allocation, annotation, same, emitted.trans (by rw [codeEq])⟩

/-- The absent payload branch uses the same concrete indexed allocator. -/
theorem Index.let_uninitialized_receipt (index : Index compiled bodyRelation)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder}
    {payload : Ty} {body code : Expr}
    (accepted : SourceCoreSourceCells.letUninitialized index.policy.sourceCells source scope Renaming.id
      binder payload body = .ok code) :
    ∃ allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts
        index.owner index.active (TypedLexicalWhile.absentRequest source scope binder payload),
      ∃ annotation : SourceCoreCallableIndexedAllocationFrames.Annotated
          compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
          (compiled.indexed.layouts.allocatorAt index.owner index.active
            (fun error => .sourceAllocation (reprStr error)))
          (TypedLexicalWhile.absentRequest source scope binder payload),
        annotation.original = allocation.expression ∧ code = .letE annotation.expression body := by
  rw [index.sourceCells] at accepted
  unfold SourceCoreSourceCells.letUninitialized at accepted
  cases allocated : index.allocationCallback (TypedLexicalWhile.absentRequest source scope binder payload) with
  | error error =>
    simp only [TypedLexicalWhile.absentRequest] at allocated
    simp only [allocated, bind, Except.bind, reduceCtorEq] at accepted
  | ok allocationCode =>
    have emitted : code = .letE allocationCode body := by
      simp only [TypedLexicalWhile.absentRequest] at allocated
      simpa only [allocated, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using accepted.symm
    obtain ⟨allocation, annotation, same, codeEq⟩ := index.allocation_receipt allocated
    exact ⟨allocation, annotation, same, emitted.trans (by rw [codeEq])⟩

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation

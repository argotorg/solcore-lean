import Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationRenaming
import Solcore.SourceSemantics.CoreLowering.FunctionArguments

/-! Static receipts for the actual common parameter fold. The tree records
only emitted allocation sites, their real layout receipts and binder insertion.
It contains neither source nor Core execution premises. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterCertificates
open Core Frontend SourceInference
open CallableIndexedAllocationCompletion
abbrev Binding := TypedBinder × Ty
abbrev Scope := SourceCoreSourceCells.Scope

def request (source : TypedSource) (scope : Scope) (index : Nat) (binding : Binding) : SourceCoreSourceCells.Request :=
  ⟨source, scope, Renaming.comp (Renaming.insertion 0) (Renaming.insertion index),
    binding.1, binding.2, some (.var 0)⟩

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (source : TypedSource) (total : Nat) (output : Ty) (body : Expr) :
    Scope → Nat → List Binding → Expr → Prop where
  | nil {scope index} : Tree layouts owner active layout globals onError source total output body scope index [] body
  | cons {scope index binder payload bindings code}
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope index (binder, payload)))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals
        (layouts.allocatorAt owner active onError) (request source scope index (binder, payload)))
      (same : annotation.original = allocation.expression)
      (tail : Tree layouts owner active layout globals onError source total output body
        ((binder.id, payload) :: scope) (index + 1) bindings code) :
      Tree layouts owner active layout globals onError source total output body scope index ((binder, payload) :: bindings)
        (LanguageResult.bind output
          (LanguageResult.success (SourceCoreFunctions.argumentProjection index total (.var index)))
          (.letE annotation.expression (code.weakenAt 1)))

private def step (allocate : SourceCoreSourceCells.Allocator) (source : TypedSource) (scope : Scope)
    (all : List Binding) (output : Ty) (item : Binding × Nat) (body : Expr) : Except SourceCoreBasic.Error Expr :=
  SourceCoreSourceCells.letInitialized (some allocate) source
    ((all.take item.2).reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (Renaming.insertion item.2) item.1.1 output item.1.2
    (LanguageResult.success (SourceCoreFunctions.argumentProjection item.2 all.length (.var item.2))) body

private theorem of_fold {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (source : TypedSource) (scope : Scope) (all done bindings : List Binding)
    (split : all = done ++ bindings) (output : Ty) (body : Expr) {code : Expr}
    (accepted : (bindings.zipIdx done.length).foldrM
      (step (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)) source scope all output) body = .ok code) :
    Tree layouts owner active layout globals onError source all.length output body
      (done.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) done.length bindings code := by
  induction bindings generalizing done code with
  | nil =>
    simp only [List.zipIdx_nil, List.foldrM_nil] at accepted
    cases accepted
    exact .nil
  | cons binding rest ih =>
    simp only [List.zipIdx_cons, List.foldrM_cons] at accepted
    cases tail : (rest.zipIdx (done.length + 1)).foldrM
        (step (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)) source scope all output) body with
    | error error => simp [tail, bind, Except.bind] at accepted
    | ok next =>
      simp only [tail, bind, Except.bind] at accepted
      have nextTree := ih (done := done ++ [binding]) (by simpa [List.append_assoc] using split)
        (by simpa using tail)
      have prior : all.take done.length = done := by rw [split]; simp
      simp only [step, prior, SourceCoreSourceCells.letInitialized, bind, Except.bind] at accepted
      change (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)
          (request source (done.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) done.length binding) >>= fun v =>
          pure (LanguageResult.bind output
            (LanguageResult.success (SourceCoreFunctions.argumentProjection done.length all.length (.var done.length)))
            (.letE v (next.weakenAt 1)))) = .ok code at accepted
      cases allocationAccepted : SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)
          (request source (done.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) done.length binding) with
      | error error => simp only [allocationAccepted, bind, Except.bind, reduceCtorEq] at accepted
      | ok allocationCode =>
        have accepted' : LanguageResult.bind output
            (LanguageResult.success (SourceCoreFunctions.argumentProjection done.length all.length (.var done.length)))
            (.letE allocationCode (next.weakenAt 1)) = code := by
          simpa only [allocationAccepted, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using accepted
        obtain ⟨allocation, annotation, same, emitted⟩ := accepted_receipts onError allocationAccepted
        rw [← accepted', emitted]
        apply Tree.cons allocation annotation same
        simpa using nextTree

/-- Successful production compilation extracts every parameter allocation
receipt and the exact nested temporary-binder structure. -/
theorem of_accepted {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {scope : Scope} {bindings : List Binding} {output : Ty} {body code : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      source scope bindings output SourceCoreFunctions.argumentProjection body = .ok code) :
    Tree layouts owner active layout globals onError source bindings.length output body scope 0 bindings code := by
  exact of_fold onError source scope bindings [] bindings rfl output body accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterCertificates

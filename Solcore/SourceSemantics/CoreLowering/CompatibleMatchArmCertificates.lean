import Solcore.SourceSemantics.CoreLowering.CallableIndexedAllocationRenaming
import Solcore.Frontend.SourceCoreCompatibleDataMatches

/-! Static receipts for the actual compatible match arm allocator. The
packed binding values and loaded scrutinee are lexical temporaries; captures
skip both and retain the real hidden source reference. No evaluation premise
is stored in the tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmCertificates
open Core Frontend SourceInference
open CallableIndexedAllocationCompletion
abbrev Binding := TypedBinder × Ty
abbrev Scope := SourceCoreSourceCells.Scope

def request (source : TypedSource) (scope : Scope) (index : Nat) (binding : Binding) : SourceCoreSourceCells.Request :=
  ⟨source, scope, Renaming.comp (Renaming.insertion 0)
    (Renaming.comp (Renaming.insertion (index + 1)) (Renaming.insertion index)),
    binding.1, binding.2, some (.var 0)⟩

inductive Tree (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (source : TypedSource) (types : List Ty) (output : Ty) (body : Expr) :
    Scope → Nat → List Binding → Expr → Prop where
  | nil {scope index} : Tree layouts owner active layout globals onError source types output body scope index [] body
  | cons {scope index binder payload bindings code}
      (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (request source scope index (binder, payload)))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals
        (layouts.allocatorAt owner active onError) (request source scope index (binder, payload)))
      (same : annotation.original = allocation.expression)
      (tail : Tree layouts owner active layout globals onError source types output body
        ((binder.id, payload) :: scope) (index + 1) bindings code) :
      Tree layouts owner active layout globals onError source types output body scope index ((binder, payload) :: bindings)
        (LanguageResult.bind output
          (LanguageResult.success (SourceCoreDataExpressions.projectPacked index types (.var index)))
          (.letE annotation.expression (code.weakenAt 1)))

private def step (allocate : SourceCoreSourceCells.Allocator) (source : TypedSource) (scope : Scope)
    (all : List Binding) (output : Ty) (item : Binding × Nat) (body : Expr) : Except SourceCoreBasic.Error Expr :=
  SourceCoreSourceCells.letInitialized (some allocate) source
    ((all.take item.2).reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (Renaming.comp (Renaming.insertion (item.2 + 1)) (Renaming.insertion item.2)) item.1.1 output item.1.2
    (LanguageResult.success (SourceCoreDataExpressions.projectPacked item.2 (all.map Prod.snd) (.var item.2))) body

private theorem of_fold {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (source : TypedSource) (scope : Scope) (all done bindings : List Binding)
    (split : all = done ++ bindings) (output : Ty) (body : Expr) {code : Expr}
    (accepted : (bindings.zipIdx done.length).foldrM
      (step (SourceCoreCallableIndexedAllocationFrames.allocator layout globals
        (layouts.allocatorAt owner active onError)) source scope all output) body = .ok code) :
    Tree layouts owner active layout globals onError source (all.map Prod.snd) output body
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
            (LanguageResult.success (SourceCoreDataExpressions.projectPacked done.length (all.map Prod.snd) (.var done.length)))
            (.letE v (next.weakenAt 1)))) = .ok code at accepted
      cases allocationAccepted : SourceCoreCallableIndexedAllocationFrames.allocator layout globals
          (layouts.allocatorAt owner active onError)
          (request source (done.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) done.length binding) with
      | error error => simp only [allocationAccepted, bind, Except.bind, reduceCtorEq] at accepted
      | ok allocationCode =>
        have accepted' : LanguageResult.bind output
            (LanguageResult.success (SourceCoreDataExpressions.projectPacked done.length (all.map Prod.snd) (.var done.length)))
            (.letE allocationCode (next.weakenAt 1)) = code := by
          simpa only [allocationAccepted, bind, Except.bind, pure, Except.pure, Except.ok.injEq] using accepted
        obtain ⟨allocation, annotation, same, emitted⟩ := accepted_receipts onError allocationAccepted
        rw [← accepted', emitted]
        apply Tree.cons allocation annotation same
        simpa using nextTree

/-- The real compiler fold supplies each marked allocation receipt and its
exact lexical insertions. The body is still an arbitrary continuation. -/
theorem of_accepted {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {context : SourceCoreCompatibleDataMatches.Context}
    {source : TypedSource} {scope : Scope} {bindings : List Binding} {output : Ty} {body code : Expr}
    (allocator : context.sourceCells = some
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError)))
    (accepted : SourceCoreCompatibleDataMatches.bindArmWithAllocator context source scope bindings output body = .ok code) :
    Tree layouts owner active layout globals onError source (bindings.map Prod.snd) output
      (body.weakenAt bindings.length) scope 0 bindings code := by
  unfold SourceCoreCompatibleDataMatches.bindArmWithAllocator at accepted
  simp only [allocator] at accepted
  exact of_fold onError source scope bindings [] bindings rfl output (body.weakenAt bindings.length) accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmCertificates

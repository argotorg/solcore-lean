import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchCertificates
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates
import Solcore.SourceSemantics.CoreLowering.CoreClosedRenaming

/-! Native child typing follows the actual marked compatible arm prefix.
Only syntactic unused slots are removed. No source type, closure identity or
runtime authority is inferred from these native typing statements. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeArms
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchArmCertificates hiding Scope
open TypedLexicalWhile.Native

def referenceContext (bindings : List Binding) (context : Core.Context) : Core.Context :=
  bindings.foldl (fun context binding => OptionalCell.referenceType binding.2 :: context) context

def referencePrefix (bindings : List Binding) : Core.Context :=
  bindings.reverse.map (fun binding => OptionalCell.referenceType binding.2)

private theorem referenceContext_prefix (bindings : List Binding) (context : Core.Context) :
    referenceContext bindings context = referencePrefix bindings ++ context := by
  induction bindings generalizing context with
  | nil => rfl
  | cons head tail ih => simp [referenceContext, referencePrefix, List.reverse_cons, List.append_assoc]

private theorem referenceContext_scope (bindings : List Binding) (scope : Scope) (administrative : Core.Context) :
    referenceContext bindings (SourceCoreLocalCell.coreContext scope ++ administrative) =
      SourceCoreLocalCell.coreContext (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) ++ administrative := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons head tail ih =>
    simpa only [referenceContext, List.foldl_cons, SourceCoreLocalCell.coreContext, List.map_cons, List.cons_append, OptionalCell.referenceType] using
      ih ((head.1.id, head.2) :: scope)

private theorem remove_at {definitions : DataEnvironment} (leading suffix : Core.Context) (inserted : Ty)
    {expression : Expr} {type : Ty}
    (typed : HasType (leading ++ inserted :: suffix) (expression.weakenAt leading.length) type definitions) :
    HasType (leading ++ suffix) expression type definitions := by
  rw [← Expr.rename_insertion] at typed
  apply typing expression ?_ typed
  clear typed
  induction leading with
  | nil => intro index type found; simpa [Renaming.insertion] using found
  | cons head leading ih =>
    simpa only [List.length_cons, List.cons_append, ← Renaming.lift_insertion] using ih.lift head

theorem Tree.body_typing {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {source : TypedSource} {types : List Ty} {output : Ty} {body : Expr}
    {scope : Scope} {index : Nat} {bindings : List Binding} {code : Expr}
    (tree : CompatibleMatchArmCertificates.Tree layouts owner active frame globals onError source types output body scope index bindings code)
    {context : Core.Context} {definitions : DataEnvironment} {type : Ty}
    (typed : HasType context code type definitions) :
    HasType (referenceContext bindings context) body type definitions := by
  induction tree generalizing context with
  | nil => exact typed
  | cons allocation annotation same tail ih =>
    cases typed with
    | caseE initial failure next =>
      exact ih (remove_second (absent_child allocation annotation same next))

/-- The two actual lexical temporaries are removed from the weakened body.
The resulting context is exactly the compiler arm scope plus its ambient tail. -/
theorem bindArm_body_typing {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {compilation : SourceCoreCompatibleDataMatches.Context}
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {source : TypedSource} {scope : Scope} {bindings : List Binding} {output : Ty} {body code : Expr}
    (accepted : bindArmWithAllocator compilation source scope bindings output (body.weakenAt bindings.length) = .ok code)
    {bundle scrutinee type : Ty} {administrative : Core.Context} {definitions : DataEnvironment}
    (typed : HasType (bundle :: scrutinee :: (SourceCoreLocalCell.coreContext scope ++ administrative)) code type definitions) :
    HasType (SourceCoreLocalCell.coreContext (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) ++ administrative)
      body type definitions := by
  have initial := Tree.body_typing (CompatibleMatchArmCertificates.of_accepted onError allocator accepted) typed
  rw [referenceContext_prefix] at initial
  have length : (referencePrefix bindings).length = bindings.length := by simp [referencePrefix]
  rw [← length] at initial
  have once := remove_at (referencePrefix bindings) (scrutinee :: (SourceCoreLocalCell.coreContext scope ++ administrative)) bundle initial
  have twice := remove_at (referencePrefix bindings) (SourceCoreLocalCell.coreContext scope ++ administrative) scrutinee once
  rw [← referenceContext_prefix, referenceContext_scope] at twice
  exact twice

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeArms

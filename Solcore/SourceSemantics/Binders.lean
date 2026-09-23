import Solcore.SourceSemantics.Types
import Solcore.Frontend.SourceInference.TypedIR

/-!
Declarative lexical-binder formation and context extension.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend.SourceInference

/-- A stable local identity is not already defined in the lexical context. -/
def LocalFresh (context : Context) (id : Resolved.LocalId) : Prop :=
  id ∉ context.locals.map Prod.fst

/-- A retained binder is owned by the surrounding declaration and carries a
well-formed rank-1 scheme. -/
structure BinderWellFormed (context : Context)
    (owner : Resolved.DeclarationId) (binder : TypedBinder) : Prop where
  owned : binder.id.owner = owner
  scheme : SchemeWellFormed context binder.scheme

/-- Extend a context by one fresh, well-formed retained binder. -/
inductive BinderExtends (owner : Resolved.DeclarationId) :
    Context → TypedBinder → Context → Prop where
  | intro
      {context : Context} {binder : TypedBinder}
      (wellFormed : BinderWellFormed context owner binder)
      (fresh : LocalFresh context binder.id) :
      BinderExtends owner context binder
        (context.withLocal binder.id binder.scheme)

/-- Source-ordered extension by a list of binders. -/
inductive BindersExtend (owner : Resolved.DeclarationId) :
    Context → List TypedBinder → Context → Prop where
  | nil (context : Context) : BindersExtend owner context [] context
  | cons
      {context middle final : Context}
      {binder : TypedBinder} {binders : List TypedBinder}
      (head : BinderExtends owner context binder middle)
      (tail : BindersExtend owner middle binders final) :
      BindersExtend owner context (binder :: binders) final

/-- Lambda and function parameters are monomorphic and expose their types in
source order while extending the lexical context. -/
inductive MonoBindersExtend (owner : Resolved.DeclarationId) :
    Context → List TypedBinder → List TypeSystem.Ty → Context → Prop where
  | nil (context : Context) : MonoBindersExtend owner context [] [] context
  | cons
      {context middle final : Context}
      {binder : TypedBinder} {binders : List TypedBinder}
      {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
      (scheme_eq : binder.scheme = .mono type)
      (head : BinderExtends owner context binder middle)
      (tail : MonoBindersExtend owner middle binders types final) :
      MonoBindersExtend owner context (binder :: binders) (type :: types) final

namespace BinderExtends

theorem local_self
    {owner : Resolved.DeclarationId} {context final : Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner context binder final) :
    final.LocalLookup binder.id binder.scheme := by
  cases extension
  exact .head

theorem context_fields
    {owner : Resolved.DeclarationId} {context final : Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner context binder final) :
    final.signatures = context.signatures ∧
      final.currentDeclaration = context.currentDeclaration ∧
      final.typeParameters = context.typeParameters ∧
      final.assumptions = context.assumptions ∧
      final.solvedRequirements = context.solvedRequirements := by
  cases extension
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem typeVariables_eq
    {owner : Resolved.DeclarationId} {context final : Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner context binder final) :
    final.typeVariables = context.typeVariables := by
  cases extension
  rfl

theorem residualTypeVariables_eq
    {owner : Resolved.DeclarationId} {context final : Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner context binder final) :
    final.residualTypeVariables = context.residualTypeVariables := by
  cases extension
  rfl

end BinderExtends

namespace MonoBindersExtend

/-- Extending one fixed context by one fixed monomorphic binder/type sequence
determines the final lexical context. -/
theorem functional
    {owner : Resolved.DeclarationId} {context left right : Context}
    {binders : List TypedBinder} {types : List TypeSystem.Ty}
    (leftExtension : MonoBindersExtend owner context binders types left)
    (rightExtension : MonoBindersExtend owner context binders types right) :
    left = right := by
  induction leftExtension generalizing right with
  | nil =>
      cases rightExtension
      rfl
  | cons leftScheme leftHead leftTail induction =>
      cases rightExtension with
      | cons rightScheme rightHead rightTail =>
          cases leftHead
          cases rightHead
          exact induction rightTail

theorem length_eq
    {owner : Resolved.DeclarationId} {context final : Context}
    {binders : List TypedBinder} {types : List TypeSystem.Ty}
    (extension : MonoBindersExtend owner context binders types final) :
    binders.length = types.length := by
  induction extension with
  | nil => rfl
  | cons _ _ _ tail_ih =>
      simp only [List.length_cons, Nat.succ.injEq]
      exact tail_ih

theorem schemes_eq
    {owner : Resolved.DeclarationId} {context final : Context}
    {binders : List TypedBinder} {types : List TypeSystem.Ty}
    (extension : MonoBindersExtend owner context binders types final) :
    binders.map (fun binder => binder.scheme) = types.map TypeSystem.Scheme.mono := by
  induction extension with
  | nil => rfl
  | cons scheme_eq _ _ tail_ih => simp [scheme_eq, tail_ih]

end MonoBindersExtend

end Solcore.SourceSemantics

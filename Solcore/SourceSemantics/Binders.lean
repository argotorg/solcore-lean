import Solcore.SourceSemantics.Types
import Solcore.Frontend.SourceInference.TypedIR

/-!
Declarative lexical-binder formation and context extension.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend.SourceInference

/-- A stable local identity is absent from both paired lexical scopes.

Keeping the value and qualified-requirement scopes fresh together prevents a
new binder from shadowing stale scheme metadata in an otherwise malformed
context. -/
def LocalFresh (context : Context) (id : Resolved.LocalId) : Prop :=
  id ∉ context.locals.map Prod.fst ∧
    id ∉ context.localSchemeRequirements.map Prod.fst

/-- Stable identities of the proof obligations abstracted by one local
scheme, in predicate order. -/
def localSchemeTemplateIds (binder : TypedBinder) : List RequirementId :=
  binder.schemeRequirements.map fun requirement =>
    requirement.templateRequirement

/-- Instantiate every predicate abstracted by one local scheme with the same
flexible substitution, preserving source order.  Actual requirement IDs are
checked against this list positionally at each reference occurrence. -/
def instantiateLocalSchemePredicates (substitution : TypeSystem.Substitution)
    (binder : TypedBinder) : List Frontend.ProgramPredicate :=
  binder.schemeRequirements.map fun requirement =>
    Frontend.TypedTraitResolution.applySubstitution substitution
      requirement.predicate

/-- Static context of a generalized initializer.  Its quantified variables
are lexical inference variables, while its qualified predicates are available
only as hypotheses of the initializer being abstracted. -/
def localSchemeInitializerContext (context : Context)
    (binder : TypedBinder) : Context :=
  (context.withTypeVariables binder.scheme.quantified).withAssumptions
    (context.assumptions ++
      binder.schemeRequirements.map fun requirement => requirement.predicate)

@[simp] theorem localSchemeTemplateIds_eq_nil
    (binder : TypedBinder) (requirements_empty : binder.schemeRequirements = []) :
    localSchemeTemplateIds binder = [] := by
  simp [localSchemeTemplateIds, requirements_empty]

@[simp] theorem localSchemeInitializerContext_eq_withTypeVariables
    (context : Context) (binder : TypedBinder)
    (requirements_empty : binder.schemeRequirements = []) :
    localSchemeInitializerContext context binder =
      context.withTypeVariables binder.scheme.quantified := by
  cases context
  simp [localSchemeInitializerContext, Context.withTypeVariables,
    Context.withAssumptions, requirements_empty]

/-- One qualified local-scheme predicate is meaningful in the initializer,
depends on at least one variable actually quantified by the scheme, and names
an exact retained assumption row in the source requirement ledger. -/
structure LocalSchemeRequirementWellFormed (context : Context)
    (binder : TypedBinder) (requirement : LocalSchemeRequirement) : Prop where
  predicate : PredicateAdmissible
    (localSchemeInitializerContext context binder) requirement.predicate
  depends_on_quantified : ∃ metavariable,
    metavariable ∈ binder.scheme.quantified ∧
      metavariable ∈
        Frontend.TypedTraitResolution.predicateVariables requirement.predicate
  template : ∃ solved,
    context.solvedRequirements.filter (fun candidate =>
        candidate.id == requirement.templateRequirement) = [solved] ∧
      solved.id = requirement.templateRequirement ∧
      solved.predicate = requirement.predicate ∧
      solved.evidence = .assumption requirement.predicate

/-- Source-ordered qualified predicates have distinct template identities and
each template satisfies the formation judgment above. -/
structure LocalSchemeRequirementsWellFormed (context : Context)
    (binder : TypedBinder) : Prop where
  ids_unique : (localSchemeTemplateIds binder).Nodup
  entries : ∀ requirement, requirement ∈ binder.schemeRequirements →
    LocalSchemeRequirementWellFormed context binder requirement

namespace LocalSchemeRequirementsWellFormed

theorem empty (context : Context) (binder : TypedBinder)
    (requirements_empty : binder.schemeRequirements = []) :
    LocalSchemeRequirementsWellFormed context binder := by
  constructor
  · simp [localSchemeTemplateIds, requirements_empty]
  · intro requirement member
    simp [requirements_empty] at member

end LocalSchemeRequirementsWellFormed

/-- Scheme-bound flexible variables are fresh for both the ambient inference
scope and every scheme already retained in the lexical context.  The latter
condition is stated over the complete local table, rather than only visible
first-match lookups, so malformed duplicate tables cannot hide a capture. -/
def SchemeQuantifiersFresh (context : Context) (scheme : TypeSystem.Scheme) :
    Prop :=
  ∀ metavariable, metavariable ∈ scheme.quantified →
    metavariable ∉ context.typeVariables ∧
      ∀ entry, entry ∈ context.locals →
        metavariable ∉ entry.2.quantified

/-- A retained binder is owned by the surrounding declaration and carries a
well-formed rank-1 scheme. -/
structure BinderWellFormed (context : Context)
    (owner : Resolved.DeclarationId) (binder : TypedBinder) : Prop where
  owned : binder.id.owner = owner
  scheme : SchemeWellFormed context binder.scheme
  quantified_fresh : SchemeQuantifiersFresh context binder.scheme
  /-- Qualified requirements belong only to genuinely generalized local
  schemes.  Keeping this condition on the common binder judgment excludes
  inert or misleading metadata from parameters, patterns, and monomorphic
  lets without duplicating the restriction at every introduction site. -/
  monomorphic_requirements_empty :
    binder.scheme.quantified = [] → binder.schemeRequirements = []

/-- Extend a context by one fresh, well-formed retained binder. -/
inductive BinderExtends (owner : Resolved.DeclarationId) :
    Context → TypedBinder → Context → Prop where
  | intro
      {context : Context} {binder : TypedBinder}
      (wellFormed : BinderWellFormed context owner binder)
      (fresh : LocalFresh context binder.id) :
      BinderExtends owner context binder
        (context.withLocal binder.id binder.scheme binder.schemeRequirements)

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

theorem fresh
    {owner : Resolved.DeclarationId} {context final : Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner context binder final) :
    LocalFresh context binder.id := by
  cases extension
  assumption

theorem local_fresh
    {owner : Resolved.DeclarationId} {context final : Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner context binder final) :
    binder.id ∉ context.locals.map Prod.fst :=
  extension.fresh.1

theorem local_scheme_requirements_fresh
    {owner : Resolved.DeclarationId} {context final : Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner context binder final) :
    binder.id ∉ context.localSchemeRequirements.map Prod.fst :=
  extension.fresh.2

theorem local_self
    {owner : Resolved.DeclarationId} {context final : Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner context binder final) :
    final.LocalLookup binder.id binder.scheme := by
  cases extension
  exact .head

theorem local_scheme_requirements_self
    {owner : Resolved.DeclarationId} {context final : Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner context binder final) :
    final.LocalSchemeRequirementsLookup binder.id binder.schemeRequirements := by
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

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

/-- The context-independent shape of a source-ordered monomorphic binder
sequence.  Lexical freshness and type formation are supplied separately when
the sequence is installed into a particular context. -/
inductive MonomorphicBinders (owner : Resolved.DeclarationId) :
    List TypedBinder → List TypeSystem.Ty → Prop where
  | nil : MonomorphicBinders owner [] []
  | cons
      {binder : TypedBinder} {binders : List TypedBinder}
      {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
      (owned : binder.id.owner = owner)
      (scheme_eq : binder.scheme = .mono type)
      (requirements_eq : binder.schemeRequirements = [])
      (tail : MonomorphicBinders owner binders types) :
      MonomorphicBinders owner (binder :: binders) (type :: types)

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

/-- A source-ordered list of fresh monomorphic binders can always be installed
in the lexical context.  This is the algorithm-independent constructor used
for both named-function inputs and lambda parameters: the caller supplies only
the retained binder shape, stable-identity freshness, and closed formation of
the corresponding types. -/
theorem exists_of_monomorphic
    {owner : Resolved.DeclarationId} {context : Context}
    {binders : List TypedBinder} {types : List TypeSystem.Ty}
    (aligned : MonomorphicBinders owner binders types)
    (ids_unique : (binders.map fun binder => binder.id).Nodup)
    (initially_fresh : ∀ binder, binder ∈ binders →
      LocalFresh context binder.id)
    (types_well_formed : ∀ type, type ∈ types →
      TypeWellFormed context type) :
    ∃ final, MonoBindersExtend owner context binders types final := by
  induction aligned generalizing context with
  | nil =>
      exact ⟨context, .nil context⟩
  | @cons binder binders type types owned scheme_eq requirements_eq _ induction =>
      simp only [List.map_cons] at ids_unique
      rw [List.nodup_cons] at ids_unique
      have binder_fresh : LocalFresh context binder.id :=
        initially_fresh binder (by simp)
      have type_well_formed : TypeWellFormed context type :=
        types_well_formed type (by simp)
      have binder_well_formed : BinderWellFormed context owner binder := by
        refine {
          owned := owned
          scheme := ?_
          quantified_fresh := ?_
          monomorphic_requirements_empty := ?_
        }
        · rw [scheme_eq]
          exact SchemeWellFormed.mono type_well_formed
        · rw [scheme_eq]
          simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
        · intro _
          exact requirements_eq
      let middle := context.withLocal binder.id binder.scheme
        binder.schemeRequirements
      have head : BinderExtends owner context binder middle := by
        exact .intro binder_well_formed binder_fresh
      have tail_fresh : ∀ candidate, candidate ∈ binders →
          LocalFresh middle candidate.id := by
        intro candidate member
        have fresh := initially_fresh candidate (by simp [member])
        have different : candidate.id ≠ binder.id := by
          intro same
          exact ids_unique.1 (List.mem_map.mpr ⟨candidate, member, same⟩)
        constructor
        · simpa [middle, Context.withLocal, different] using fresh.1
        · simpa [middle, Context.withLocal, different] using fresh.2
      have tail_well_formed : ∀ candidate, candidate ∈ types →
          TypeWellFormed middle candidate := by
        intro candidate member
        have wellFormed := types_well_formed candidate (by simp [member])
        exact wellFormed.withLocal binder.id binder.scheme
          binder.schemeRequirements
      rcases induction ids_unique.2 tail_fresh tail_well_formed with
        ⟨final, tail⟩
      exact ⟨final, .cons scheme_eq head tail⟩

private theorem localIds_nodup_of_indices_nodup
    (ids : List Resolved.LocalId)
    (indices : (ids.map fun id => id.binderIndex).Nodup) : ids.Nodup := by
  induction ids with
  | nil => exact .nil
  | cons head tail induction =>
      simp only [List.map_cons] at indices
      rw [List.nodup_cons] at indices ⊢
      refine ⟨?_, induction indices.2⟩
      intro member
      exact indices.1 (List.mem_map.mpr ⟨_, member, rfl⟩)

private theorem initial_input_ids_nodup
    (owner : Resolved.DeclarationId) (locals : TypeSystem.Environment)
    (comptime : List Bool) :
    (((Frontend.SourceInference.State.initial owner locals comptime).inputs.map
      fun binder => binder.id).Nodup) := by
  apply localIds_nodup_of_indices_nodup
  rw [Frontend.SourceInference.State.initial_inputs_definition,
    List.mapIdx_eq_zipIdx_map, List.map_map]
  simpa [Function.comp_def] using
    (List.nodup_range' (s := 0) (n := locals.length))

private theorem initial_input_alignment_mapIdx
    (owner : Resolved.DeclarationId) (names : List String)
    (types : List TypeSystem.Ty) (comptime : Nat → Bool)
    (binderIndex : Nat → Nat)
    (length_eq : names.length = types.length) :
    MonomorphicBinders owner
      (((names.zip types).map fun parameter =>
          (parameter.1, TypeSystem.Scheme.mono parameter.2)).mapIdx
        fun index entry => {
          id := { owner, binderIndex := binderIndex index }
          name := entry.1
          scheme := entry.2
          comptime := comptime index
        })
      types := by
  induction names generalizing types comptime binderIndex with
  | nil =>
      cases types with
      | nil => exact .nil
      | cons type types => simp at length_eq
  | cons name names induction =>
      cases types with
      | nil => simp at length_eq
      | cons type types =>
          simp only [List.length_cons, Nat.succ.injEq] at length_eq
          simp only [List.zip_cons_cons, List.map_cons, List.mapIdx_cons]
          exact .cons (by simp) (by simp [TypeSystem.Scheme.mono]) (by simp)
            (induction types (fun index => comptime (index + 1))
              (fun index => binderIndex (index + 1))
              length_eq)

private theorem initial_input_alignment
    (owner : Resolved.DeclarationId) (names : List String)
    (types : List TypeSystem.Ty) (comptime : List Bool)
    (length_eq : names.length = types.length) :
    MonomorphicBinders owner
      (Frontend.SourceInference.State.initial owner
        ((names.zip types).map fun parameter =>
          (parameter.1, TypeSystem.Scheme.mono parameter.2)) comptime).inputs
      types := by
  rw [Frontend.SourceInference.State.initial_inputs_definition]
  exact initial_input_alignment_mapIdx owner names types
    (fun index => comptime.getD index false) id length_eq

/-- The input binders allocated by `State.initial` extend an empty lexical
scope with exactly the closed signature parameter types, in source order.
The staging list is intentionally unrestricted: it affects retained metadata
but not monomorphic binder formation. -/
theorem initialInputs
    (owner : Resolved.DeclarationId) (context : Context)
    (names : List String) (types : List TypeSystem.Ty)
    (comptime : List Bool)
    (length_eq : names.length = types.length)
    (locals_empty : context.locals = [])
    (requirements_empty : context.localSchemeRequirements = [])
    (types_well_formed : ∀ type, type ∈ types →
      TypeWellFormed context type) :
    ∃ lexicalContext,
      MonoBindersExtend owner context
        (Frontend.SourceInference.State.initial owner
          ((names.zip types).map fun parameter =>
            (parameter.1, TypeSystem.Scheme.mono parameter.2))
          comptime).inputs
        types lexicalContext := by
  apply exists_of_monomorphic
  · exact initial_input_alignment owner names types comptime length_eq
  · exact initial_input_ids_nodup owner _ comptime
  · intro binder member
    simp [LocalFresh, locals_empty, requirements_empty]
  · exact types_well_formed

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

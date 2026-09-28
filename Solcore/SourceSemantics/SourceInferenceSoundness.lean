import Solcore.Frontend.SourceInference.ProgramProperties
import Solcore.Frontend.SourceInference.RequirementProperties
import Solcore.SourceSemantics.ProgramCheckingSoundness
import Solcore.SourceSemantics.TraitSubstitutionProperties
import Solcore.SourceSemantics.TraitResolutionSoundness

/-! Conditional bridge from executable finalization to declarative typing. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend SourceInference

private theorem trait?_eq_some_facts
    {signatures : ProgramSignatures} {id : Resolved.DeclarationId}
    {signature : ProgramTraitSignature}
    (found : signatures.trait? id = some signature) :
    signature ∈ signatures.traits ∧ signature.id = id := by
  have rawFound : signatures.traits.find?
      (fun candidate => decide (candidate.id = id)) = some signature := by
    simpa [ProgramSignatures.trait?] using found
  have accepted : decide (signature.id = id) = true :=
    List.find?_some
      (p := fun candidate : ProgramTraitSignature =>
        decide (candidate.id = id)) rawFound
  exact ⟨List.mem_of_find?_eq_some rawFound,
    of_decide_eq_true accepted⟩

private theorem list_eq_pair_of_length_eq_two
    {value : Type} {values : List value}
    (length_eq : values.length = 2) :
    ∃ first second, values = [first, second] := by
  cases values with
  | nil => simp at length_eq
  | cons first rest =>
      cases rest with
      | nil => simp at length_eq
      | cons second tail =>
          cases tail with
          | nil => exact ⟨first, second, rfl⟩
          | cons third tail => simp at length_eq

private theorem list_eq_singleton_of_length_eq_one
    {value : Type} {values : List value}
    (length_eq : values.length = 1) :
    ∃ item, values = [item] := by
  cases values with
  | nil => simp at length_eq
  | cons item rest =>
      cases rest with
      | nil => exact ⟨item, rfl⟩
      | cons second tail => simp at length_eq

private theorem list_perm_reverse {value : Type} (values : List value) :
    values.Perm values.reverse := by
  induction values with
  | nil => exact .nil
  | cons head tail induction =>
      rw [List.reverse_cons]
      exact (List.Perm.cons head induction).trans (by
        simpa only [List.singleton_append] using
          (List.perm_append_comm :
            ([head] ++ tail.reverse).Perm (tail.reverse ++ [head])))

/-- Finalized semantic schemes projected from the stable executable binder
stack.  The list order remains the executable lookup order; alignment with a
semantic context is therefore stated by permutation rather than equality. -/
def closedBinderLocals (substitution : TypeSystem.Substitution)
    (binders : List TypedBinder) :
    Resolved.LocalScope TypeSystem.Scheme :=
  binders.map fun binder =>
    (binder.id, (binder.applySubstitution substitution).scheme)

/-- Finalized qualified-requirement metadata paired with the same stable
binder identities as `closedBinderLocals`. -/
def closedBinderRequirements (substitution : TypeSystem.Substitution)
    (binders : List TypedBinder) :
    Resolved.LocalScope (List LocalSchemeRequirement) :=
  binders.map fun binder =>
    (binder.id, (binder.applySubstitution substitution).schemeRequirements)

/-- Stable executable binders and the two paired semantic local scopes carry
the same entries.  Initial parameters may be installed into the semantic
context in reverse order, so permutation plus unique identities is the exact
order-insensitive invariant. -/
structure LocalEnvironmentAligned
    (state : Frontend.SourceInference.State)
    (substitution : TypeSystem.Substitution)
    (context : SourceSemantics.Context) : Prop where
  ids_nodup : (state.localBinders.map fun binder => binder.id).Nodup
  locals_perm :
    (closedBinderLocals substitution state.localBinders).Perm context.locals
  requirements_perm :
    (closedBinderRequirements substitution state.localBinders).Perm
      context.localSchemeRequirements

namespace LocalEnvironmentAligned

/-- A monomorphic semantic binder extension over an empty lexical base
constructs the order-insensitive alignment for the corresponding closed
executable binders. -/
theorem ofMonoBindersExtend
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context final : SourceSemantics.Context}
    {owner : Resolved.DeclarationId} {types : List TypeSystem.Ty}
    (ids_nodup : (state.localBinders.map fun binder => binder.id).Nodup)
    (locals_empty : context.locals = [])
    (requirements_empty : context.localSchemeRequirements = [])
    (extension : MonoBindersExtend owner context
      (state.localBinders.map
        (TypedBinder.applySubstitution substitution)) types final) :
    LocalEnvironmentAligned state substitution final := by
  constructor
  · exact ids_nodup
  · rw [MonoBindersExtend.locals_eq extension, locals_empty,
      List.append_nil]
    simpa [closedBinderLocals, List.map_reverse, List.map_map,
      Function.comp_def, TypedBinder.applySubstitution] using
      list_perm_reverse (closedBinderLocals substitution state.localBinders)
  · rw [MonoBindersExtend.localSchemeRequirements_eq extension,
      requirements_empty, List.append_nil]
    simpa [closedBinderRequirements, List.map_reverse, List.map_map,
      Function.comp_def, TypedBinder.applySubstitution] using
      list_perm_reverse
        (closedBinderRequirements substitution state.localBinders)

/-- The stable input identities produced by `State.initial` discharge the
uniqueness premise of `ofMonoBindersExtend`. -/
theorem ofInitialMonoBindersExtend
    (owner : Resolved.DeclarationId) (locals : TypeSystem.Environment)
    (comptime : List Bool) (substitution : TypeSystem.Substitution)
    {context final : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (locals_empty : context.locals = [])
    (requirements_empty : context.localSchemeRequirements = [])
    (extension : MonoBindersExtend owner context
      ((Frontend.SourceInference.State.initial owner locals comptime
          ).localBinders.map
        (TypedBinder.applySubstitution substitution)) types final) :
    LocalEnvironmentAligned
      (Frontend.SourceInference.State.initial owner locals comptime)
      substitution final := by
  apply ofMonoBindersExtend
    (locals_empty := locals_empty)
    (requirements_empty := requirements_empty)
    (extension := extension)
  simpa only [← Frontend.SourceInference.State.initial_inputs_eq_localBinders]
    using MonoBindersExtend.initialInputIds_nodup owner locals comptime

/-- Replacing the legacy name-keyed local cache cannot affect the stable
binder alignment used by source semantics. -/
theorem withLocals
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned state substitution context)
    (locals : TypeSystem.Environment) :
    LocalEnvironmentAligned (state.withLocals locals) substitution context := by
  constructor
  · exact aligned.ids_nodup
  · exact aligned.locals_perm
  · exact aligned.requirements_perm

/-- Allocating a fresh stable binder extends both executable and semantic
local scopes in lockstep.  The semantic entry is the closed view of the
newly allocated executable binder. -/
theorem allocateBinder
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned state substitution context)
    (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false)
    (schemeRequirements : List LocalSchemeRequirement := [])
    {binder : TypedBinder} {final : Frontend.SourceInference.State}
    (allocated : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, final))
    (fresh : binder.id ∉ state.localBinders.map fun retained => retained.id) :
    LocalEnvironmentAligned final substitution
      (context.withLocal binder.id
        (binder.applySubstitution substitution).scheme
        (binder.applySubstitution substitution).schemeRequirements) := by
  have binder_eq :
      (state.allocateBinder name scheme span comptime
        schemeRequirements).1 = binder :=
    congrArg Prod.fst allocated
  have final_eq :
      (state.allocateBinder name scheme span comptime
        schemeRequirements).2 = final :=
    congrArg Prod.snd allocated
  subst binder
  subst final
  constructor
  · simpa [Frontend.SourceInference.State.allocateBinder] using
      (List.nodup_cons.mpr ⟨fresh, aligned.ids_nodup⟩)
  · simpa [closedBinderLocals,
      Frontend.SourceInference.State.allocateBinder,
      SourceSemantics.Context.withLocal] using
      aligned.locals_perm.cons
        ((state.allocateBinder name scheme span comptime
          schemeRequirements).1.id,
          ((state.allocateBinder name scheme span comptime
            schemeRequirements).1.applySubstitution substitution).scheme)
  · simpa [closedBinderRequirements,
      Frontend.SourceInference.State.allocateBinder,
      SourceSemantics.Context.withLocal] using
      aligned.requirements_perm.cons
        ((state.allocateBinder name scheme span comptime
          schemeRequirements).1.id,
          ((state.allocateBinder name scheme span comptime
            schemeRequirements).1.applySubstitution
              substitution).schemeRequirements)

/-- The source-inference allocator invariant discharges the explicit stable-ID
freshness premise of `allocateBinder`. -/
theorem allocateBinder_of_localBindersBelowNextLocal
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned state substitution context)
    (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false)
    (schemeRequirements : List LocalSchemeRequirement := [])
    {binder : TypedBinder} {final : Frontend.SourceInference.State}
    (allocated : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, final))
    (below : state.LocalBindersBelowNextLocal) :
    LocalEnvironmentAligned final substitution
      (context.withLocal binder.id
        (binder.applySubstitution substitution).scheme
        (binder.applySubstitution substitution).schemeRequirements) := by
  exact aligned.allocateBinder name scheme span comptime schemeRequirements
    allocated
    (Frontend.SourceInference.State.allocateBinder_success_id_fresh
      below allocated)

/-- Executable first-match name lookup identifies a stable binder whose
closed scheme and qualified metadata are both available in the aligned
semantic context. -/
theorem lookup_of_lookupBinder?
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    {name : String} {binder : TypedBinder}
    (aligned : LocalEnvironmentAligned state substitution context)
    (found : state.lookupBinder? name = some binder) :
    context.LocalLookup binder.id
        (binder.applySubstitution substitution).scheme ∧
      context.LocalSchemeRequirementsLookup binder.id
        (binder.applySubstitution substitution).schemeRequirements := by
  have rawFound : state.localBinders.find?
      (fun candidate => candidate.name == name) = some binder := by
    exact Frontend.SourceInference.State.lookupBinder?_eq_some_raw found
  have binderMember : binder ∈ state.localBinders :=
    List.mem_of_find?_eq_some rawFound
  have localMember :
      (binder.id, (binder.applySubstitution substitution).scheme) ∈
        closedBinderLocals substitution state.localBinders :=
    List.mem_map.mpr ⟨binder, binderMember, rfl⟩
  have requirementMember :
      (binder.id,
        (binder.applySubstitution substitution).schemeRequirements) ∈
        closedBinderRequirements substitution state.localBinders :=
    List.mem_map.mpr ⟨binder, binderMember, rfl⟩
  have closedLocalIdsNodup :
      ((closedBinderLocals substitution state.localBinders).map
        Prod.fst).Nodup := by
    simpa [closedBinderLocals, List.map_map, Function.comp_def,
      TypedBinder.applySubstitution] using aligned.ids_nodup
  have contextLocalIdsNodup :
      (context.locals.map Prod.fst).Nodup :=
    (aligned.locals_perm.map Prod.fst).nodup_iff.mp closedLocalIdsNodup
  have closedRequirementIdsNodup :
      ((closedBinderRequirements substitution state.localBinders).map
        Prod.fst).Nodup := by
    simpa [closedBinderRequirements, List.map_map, Function.comp_def,
      TypedBinder.applySubstitution] using aligned.ids_nodup
  have contextRequirementIdsNodup :
      (context.localSchemeRequirements.map Prod.fst).Nodup :=
    (aligned.requirements_perm.map Prod.fst).nodup_iff.mp
      closedRequirementIdsNodup
  constructor
  · exact Resolved.LocalScope.Lookup.of_mem_of_ids_nodup
      contextLocalIdsNodup (aligned.locals_perm.mem_iff.mp localMember)
  · exact Resolved.LocalScope.Lookup.of_mem_of_ids_nodup
      contextRequirementIdsNodup
        (aligned.requirements_perm.mem_iff.mp requirementMember)

/-- Forgetting executable names and semantic stable identities leaves the
same closed scheme collection on both sides of the alignment. -/
theorem localSchemes_perm
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned state substitution context) :
    ((state.binderEnvironment.apply substitution).map Prod.snd).Perm
      (context.locals.map Prod.snd) := by
  have projected := aligned.locals_perm.map Prod.snd
  simpa [closedBinderLocals,
    Frontend.SourceInference.State.binderEnvironment,
    TypeSystem.Environment.apply, List.map_map, Function.comp_def,
    FlexibleSubstitution.applyTypedBinder_scheme] using projected

/-- Freshness in the stable executable binder stack transfers to both paired
declarative local scopes. -/
theorem localFresh_of_not_mem_localBinders
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    {id : Resolved.LocalId}
    (aligned : LocalEnvironmentAligned state substitution context)
    (fresh : id ∉ state.localBinders.map fun binder => binder.id) :
    LocalFresh context id := by
  constructor
  · intro member
    have sourceMember :=
      (aligned.locals_perm.map Prod.fst).mem_iff.mpr member
    apply fresh
    simpa [closedBinderLocals, List.map_map, Function.comp_def,
      TypedBinder.applySubstitution] using sourceMember
  · intro member
    have sourceMember :=
      (aligned.requirements_perm.map Prod.fst).mem_iff.mpr member
    apply fresh
    simpa [closedBinderRequirements, List.map_map, Function.comp_def,
      TypedBinder.applySubstitution] using sourceMember

/-- Closing any allocated binder produces its declarative context extension
once scheme formation, quantifier freshness, and the monomorphic-requirement
restriction have been established.  Alignment transfers the allocator's
freshness fact to both semantic local tables. -/
theorem binderExtends_of_allocateBinder
    {state final : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    {name : String} {scheme : TypeSystem.Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement}
    {binder : TypedBinder}
    (aligned : LocalEnvironmentAligned state substitution context)
    (below : state.LocalBindersBelowNextLocal)
    (allocated : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, final))
    (schemeWellFormed : SchemeWellFormed context
      (binder.applySubstitution substitution).scheme)
    (quantifiedFresh : SchemeQuantifiersFresh context
      (binder.applySubstitution substitution).scheme)
    (monomorphicRequirementsEmpty :
      (binder.applySubstitution substitution).scheme.quantified = [] →
        (binder.applySubstitution substitution).schemeRequirements = []) :
    BinderExtends state.owner context
      (binder.applySubstitution substitution)
      (context.withLocal binder.id
        (binder.applySubstitution substitution).scheme
        (binder.applySubstitution substitution).schemeRequirements) := by
  have binderEq :
      (state.allocateBinder name scheme span comptime
        schemeRequirements).1 = binder :=
    congrArg Prod.fst allocated
  have rawOwned : binder.id.owner = state.owner := by
    rw [← binderEq]
    rfl
  have rawFresh :
      binder.id ∉ state.localBinders.map fun retained => retained.id :=
    Frontend.SourceInference.State.allocateBinder_success_id_fresh below
      allocated
  apply BinderExtends.intro
  · exact {
      owned := by
        simpa [TypedBinder.applySubstitution] using rawOwned
      scheme := schemeWellFormed
      quantified_fresh := quantifiedFresh
      monomorphic_requirements_empty := monomorphicRequirementsEmpty
    }
  · apply aligned.localFresh_of_not_mem_localBinders
    simpa [TypedBinder.applySubstitution] using rawFresh

/-- The general allocated-binder extension specializes directly to the
monomorphic `let` case. -/
theorem monomorphicBinderExtends_of_allocateBinder
    {state final : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    {name : String} {scheme : TypeSystem.Scheme}
    {span : Option Syntax.SourceSpan} {comptime : Bool}
    {schemeRequirements : List LocalSchemeRequirement}
    {binder : TypedBinder} {type : TypeSystem.Ty}
    (aligned : LocalEnvironmentAligned state substitution context)
    (below : state.LocalBindersBelowNextLocal)
    (allocated : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, final))
    (scheme_eq : (binder.applySubstitution substitution).scheme = .mono type)
    (requirements_eq :
      (binder.applySubstitution substitution).schemeRequirements = [])
    (typeWellFormed : TypeWellFormed context type) :
    BinderExtends state.owner context
      (binder.applySubstitution substitution)
      (context.withLocal binder.id
        (binder.applySubstitution substitution).scheme
        (binder.applySubstitution substitution).schemeRequirements) := by
  apply aligned.binderExtends_of_allocateBinder below allocated
  · rw [scheme_eq]
    exact SchemeWellFormed.mono typeWellFormed
  · rw [scheme_eq]
    intro metavariable member
    simp [TypeSystem.Scheme.mono] at member
  · intro _
    exact requirements_eq

/-- The executable environment and aligned semantic local scope block
exactly the same flexible variables during local-value generalization. -/
theorem mem_local_freeVariables_iff
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned state substitution context)
    (metavariable : TypeSystem.TypeVarId) :
    metavariable ∈
        (state.binderEnvironment.apply substitution).freeVariables ↔
      metavariable ∈ context.locals.flatMap
        (fun entry => entry.2.freeVariables) := by
  have schemesPerm := aligned.localSchemes_perm
  constructor
  · rw [TypeSystem.Environment.mem_freeVariables_iff]
    rintro ⟨entry, entryMember, variableMember⟩
    have sourceMember : entry.2 ∈
        (state.binderEnvironment.apply substitution).map Prod.snd :=
      List.mem_map.mpr ⟨entry, entryMember, rfl⟩
    have targetMember : entry.2 ∈ context.locals.map Prod.snd :=
      schemesPerm.mem_iff.mp sourceMember
    rcases List.mem_map.mp targetMember with
      ⟨targetEntry, targetEntryMember, schemeEq⟩
    rw [List.mem_flatMap]
    exact ⟨targetEntry, targetEntryMember, by
      simpa [schemeEq] using variableMember⟩
  · rw [List.mem_flatMap]
    rintro ⟨entry, entryMember, variableMember⟩
    rw [TypeSystem.Environment.mem_freeVariables_iff]
    have targetMember : entry.2 ∈ context.locals.map Prod.snd :=
      List.mem_map.mpr ⟨entry, entryMember, rfl⟩
    have sourceMember : entry.2 ∈
        (state.binderEnvironment.apply substitution).map Prod.snd :=
      schemesPerm.mem_iff.mpr targetMember
    rcases List.mem_map.mp sourceMember with
      ⟨sourceEntry, sourceEntryMember, schemeEq⟩
    exact ⟨sourceEntry, sourceEntryMember, by
      simpa [schemeEq] using variableMember⟩

/-- Local-environment alignment depends on an inference state only through
its stable binder stack.  This packages preservation for state updates which
affect inference, evidence, or occurrences but not the active lexical scope. -/
theorem congr_localBinders
    {state final : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned state substitution context)
    (localBinders_eq : final.localBinders = state.localBinders) :
    LocalEnvironmentAligned final substitution context := by
  constructor
  · simpa [localBinders_eq] using aligned.ids_nodup
  · simpa [closedBinderLocals, localBinders_eq] using aligned.locals_perm
  · simpa [closedBinderRequirements, localBinders_eq] using
      aligned.requirements_perm

/-- Restoring an outer executable lexical snapshot also restores its exact
alignment with the unchanged declarative context. -/
theorem restoreLexicalScope
    {outer inner : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned outer substitution context) :
    LocalEnvironmentAligned
      (inner.restoreLexicalScope outer.lexicalScope) substitution context := by
  apply aligned.congr_localBinders
  rfl

/-- Recording the enclosing statement after restoring an outer lexical
snapshot preserves the outer environment alignment. -/
theorem restoreLexicalScope_recordNode
    {outer inner : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned outer substitution context)
    (node : Node) :
    LocalEnvironmentAligned
      ((inner.restoreLexicalScope outer.lexicalScope).recordNode node)
      substitution context := by
  apply (aligned.restoreLexicalScope (inner := inner)).congr_localBinders
  rfl

end LocalEnvironmentAligned

/-- Every stable binder in the currently active executable lexical scope has
both a well-formed closed scheme and well-formed qualified-requirement
metadata in the matching declarative context.  This invariant is deliberately
independent of local-environment alignment: formation and lookup alignment
evolve for different reasons during inference. -/
structure ActiveLocalFormation
    (state : Frontend.SourceInference.State)
    (substitution : TypeSystem.Substitution)
    (context : SourceSemantics.Context) : Prop where
  schemes : ∀ binder, binder ∈ state.localBinders →
    SchemeWellFormed context
      (binder.applySubstitution substitution).scheme
  requirements : ∀ binder, binder ∈ state.localBinders →
    LocalSchemeRequirementsWellFormed context
      (binder.applySubstitution substitution)

namespace ActiveLocalFormation

/-- Direct membership in the active binder stack exposes both formation
judgments for the corresponding closed binder. -/
theorem facts_of_mem
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context} {binder : TypedBinder}
    (formation : ActiveLocalFormation state substitution context)
    (member : binder ∈ state.localBinders) :
    SchemeWellFormed context
        (binder.applySubstitution substitution).scheme ∧
      LocalSchemeRequirementsWellFormed context
        (binder.applySubstitution substitution) :=
  ⟨formation.schemes binder member, formation.requirements binder member⟩

/-- Scheme formation projected from active-binder membership. -/
theorem schemeWellFormed_of_mem
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context} {binder : TypedBinder}
    (formation : ActiveLocalFormation state substitution context)
    (member : binder ∈ state.localBinders) :
    SchemeWellFormed context
      (binder.applySubstitution substitution).scheme :=
  formation.schemes binder member

/-- Qualified-requirement formation projected from active-binder
membership. -/
theorem localSchemeRequirementsWellFormed_of_mem
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context} {binder : TypedBinder}
    (formation : ActiveLocalFormation state substitution context)
    (member : binder ∈ state.localBinders) :
    LocalSchemeRequirementsWellFormed context
      (binder.applySubstitution substitution) :=
  formation.requirements binder member

/-- A successful guarded source-name lookup selects an active binder, so it
inherits both formation judgments. -/
theorem facts_of_lookupBinder?
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    {name : String} {binder : TypedBinder}
    (formation : ActiveLocalFormation state substitution context)
    (found : state.lookupBinder? name = some binder) :
    SchemeWellFormed context
        (binder.applySubstitution substitution).scheme ∧
      LocalSchemeRequirementsWellFormed context
        (binder.applySubstitution substitution) := by
  exact formation.facts_of_mem
    (Frontend.SourceInference.State.lookupBinder?_eq_some_facts found).1

/-- Active formation depends on an inference state only through its stable
binder stack. -/
theorem congr_localBinders
    {state final : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (formation : ActiveLocalFormation state substitution context)
    (localBinders_eq : final.localBinders = state.localBinders) :
    ActiveLocalFormation final substitution context := by
  constructor
  · intro binder member
    rw [localBinders_eq] at member
    exact formation.schemes binder member
  · intro binder member
    rw [localBinders_eq] at member
    exact formation.requirements binder member

/-- Replacing the legacy name-keyed local cache leaves active stable-binder
formation unchanged. -/
theorem withLocals
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (formation : ActiveLocalFormation state substitution context)
    (locals : TypeSystem.Environment) :
    ActiveLocalFormation (state.withLocals locals) substitution context := by
  apply formation.congr_localBinders
  rfl

/-- Restoring an outer lexical snapshot recovers exactly the outer state's
active-binder formation, independently of facts accumulated in the inner
state. -/
theorem restoreLexicalScope
    {outer inner : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (formation : ActiveLocalFormation outer substitution context) :
    ActiveLocalFormation
      (inner.restoreLexicalScope outer.lexicalScope) substitution context := by
  apply formation.congr_localBinders
  rfl

/-- Recording the enclosing statement after restoring an outer lexical
snapshot preserves the outer active-binder formation. -/
theorem restoreLexicalScope_recordNode
    {outer inner : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (formation : ActiveLocalFormation outer substitution context)
    (node : Node) :
    ActiveLocalFormation
      ((inner.restoreLexicalScope outer.lexicalScope).recordNode node)
      substitution context := by
  apply (formation.restoreLexicalScope (inner := inner)).congr_localBinders
  rfl

/-- Adding one semantic local changes none of the context fields observed by
scheme or qualified-requirement formation. -/
theorem withLocal
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (formation : ActiveLocalFormation state substitution context)
    (id : Resolved.LocalId) (scheme : TypeSystem.Scheme)
    (requirements : List LocalSchemeRequirement := []) :
    ActiveLocalFormation state substitution
      (context.withLocal id scheme requirements) := by
  constructor
  · intro binder member
    exact StructuralSubstitution.SchemeWellFormed.transportContext
      (source := context)
      (target := context.withLocal id scheme requirements)
      rfl rfl rfl rfl rfl (formation.schemes binder member)
  · intro binder member
    exact
      StructuralSubstitution.LocalSchemeRequirementsWellFormed.transportContext
        (source := context)
        (target := context.withLocal id scheme requirements)
        rfl rfl rfl rfl rfl rfl
        (formation.requirements binder member)

private structure FormationContextFields
    (source target : SourceSemantics.Context) : Prop where
  signatures_eq : target.signatures = source.signatures
  parameters_eq : target.typeParameters = source.typeParameters
  declaration_eq : target.currentDeclaration = source.currentDeclaration
  variables_eq : target.typeVariables = source.typeVariables
  residualVariables_eq :
    target.residualTypeVariables = source.residualTypeVariables
  solvedRequirements_eq :
    target.solvedRequirements = source.solvedRequirements

private theorem FormationContextFields.ofBinderExtends
    {owner : Resolved.DeclarationId} {source target : SourceSemantics.Context}
    {binder : TypedBinder}
    (extension : BinderExtends owner source binder target) :
    FormationContextFields source target := by
  have fields := extension.context_fields
  exact {
    signatures_eq := fields.1
    parameters_eq := fields.2.2.1
    declaration_eq := fields.2.1
    variables_eq := extension.typeVariables_eq
    residualVariables_eq := extension.residualTypeVariables_eq
    solvedRequirements_eq := fields.2.2.2.2
  }

private theorem FormationContextFields.trans
    {source middle target : SourceSemantics.Context}
    (first : FormationContextFields source middle)
    (second : FormationContextFields middle target) :
    FormationContextFields source target := {
  signatures_eq := second.signatures_eq.trans first.signatures_eq
  parameters_eq := second.parameters_eq.trans first.parameters_eq
  declaration_eq := second.declaration_eq.trans first.declaration_eq
  variables_eq := second.variables_eq.trans first.variables_eq
  residualVariables_eq :=
    second.residualVariables_eq.trans first.residualVariables_eq
  solvedRequirements_eq :=
    second.solvedRequirements_eq.trans first.solvedRequirements_eq
}

private theorem formationContextFields_of_monoBindersExtend
    {owner : Resolved.DeclarationId}
    {context final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List TypeSystem.Ty}
    (extension : MonoBindersExtend owner context binders types final) :
    FormationContextFields context final := by
  induction extension with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons _ head _ induction =>
      exact (FormationContextFields.ofBinderExtends head).trans induction

private theorem monoBindersExtend_member_formation
    {owner : Resolved.DeclarationId}
    {context final : SourceSemantics.Context}
    {binders : List TypedBinder} {types : List TypeSystem.Ty}
    (extension : MonoBindersExtend owner context binders types final) :
    ∀ binder, binder ∈ binders →
      SchemeWellFormed final binder.scheme ∧
        LocalSchemeRequirementsWellFormed final binder := by
  induction extension with
  | nil =>
      intro binder member
      simp at member
  | cons scheme_eq head tail induction =>
      intro binder member
      rcases List.mem_cons.mp member with rfl | member
      · have fields := formationContextFields_of_monoBindersExtend
          (MonoBindersExtend.cons scheme_eq head tail)
        cases head with
        | intro binderWellFormed _ =>
            constructor
            · exact StructuralSubstitution.SchemeWellFormed.transportContext
                fields.signatures_eq fields.parameters_eq
                fields.declaration_eq fields.variables_eq
                fields.residualVariables_eq binderWellFormed.scheme
            · apply LocalSchemeRequirementsWellFormed.empty
              apply binderWellFormed.monomorphic_requirements_empty
              simp [scheme_eq, TypeSystem.Scheme.mono]
      · exact induction binder member

/-- Installing the substituted active binder stack as monomorphic semantic
parameters establishes active formation in the final lexical context. -/
theorem ofMonoBindersExtend
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context final : SourceSemantics.Context}
    {owner : Resolved.DeclarationId} {types : List TypeSystem.Ty}
    (extension : MonoBindersExtend owner context
      (state.localBinders.map
        (TypedBinder.applySubstitution substitution)) types final) :
    ActiveLocalFormation state substitution final := by
  constructor
  · intro binder member
    exact (monoBindersExtend_member_formation extension
      (binder.applySubstitution substitution)
      (List.mem_map.mpr ⟨binder, member, rfl⟩)).1
  · intro binder member
    exact (monoBindersExtend_member_formation extension
      (binder.applySubstitution substitution)
      (List.mem_map.mpr ⟨binder, member, rfl⟩)).2

/-- Visible allocation preserves all old active formation and adds the newly
closed binder in lockstep with the matching semantic local extension. -/
theorem allocateBinder
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (formation : ActiveLocalFormation state substitution context)
    (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false)
    (schemeRequirements : List LocalSchemeRequirement := [])
    {binder : TypedBinder} {final : Frontend.SourceInference.State}
    (allocated : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, final))
    (schemeWellFormed : SchemeWellFormed context
      (binder.applySubstitution substitution).scheme)
    (requirementsWellFormed : LocalSchemeRequirementsWellFormed context
      (binder.applySubstitution substitution)) :
    ActiveLocalFormation final substitution
      (context.withLocal binder.id
        (binder.applySubstitution substitution).scheme
        (binder.applySubstitution substitution).schemeRequirements) := by
  have binder_eq :
      (state.allocateBinder name scheme span comptime
        schemeRequirements).1 = binder :=
    congrArg Prod.fst allocated
  have final_eq :
      (state.allocateBinder name scheme span comptime
        schemeRequirements).2 = final :=
    congrArg Prod.snd allocated
  subst binder
  subst final
  have retained := formation.withLocal
    (state.allocateBinder name scheme span comptime schemeRequirements).1.id
    ((state.allocateBinder name scheme span comptime
      schemeRequirements).1.applySubstitution substitution).scheme
    ((state.allocateBinder name scheme span comptime
      schemeRequirements).1.applySubstitution substitution).schemeRequirements
  constructor
  · intro candidate member
    change candidate ∈
      (state.allocateBinder name scheme span comptime
        schemeRequirements).1 :: state.localBinders at member
    rcases List.mem_cons.mp member with rfl | member
    · exact StructuralSubstitution.SchemeWellFormed.transportContext
        (source := context)
        (target := context.withLocal
          (state.allocateBinder name scheme span comptime
            schemeRequirements).1.id
          ((state.allocateBinder name scheme span comptime
            schemeRequirements).1.applySubstitution substitution).scheme
          ((state.allocateBinder name scheme span comptime
            schemeRequirements).1.applySubstitution
              substitution).schemeRequirements)
        rfl rfl rfl rfl rfl schemeWellFormed
    · exact retained.schemes candidate member
  · intro candidate member
    change candidate ∈
      (state.allocateBinder name scheme span comptime
        schemeRequirements).1 :: state.localBinders at member
    rcases List.mem_cons.mp member with rfl | member
    · exact
        StructuralSubstitution.LocalSchemeRequirementsWellFormed.transportContext
          (source := context)
          (target := context.withLocal
            (state.allocateBinder name scheme span comptime
              schemeRequirements).1.id
            ((state.allocateBinder name scheme span comptime
              schemeRequirements).1.applySubstitution substitution).scheme
            ((state.allocateBinder name scheme span comptime
              schemeRequirements).1.applySubstitution
                substitution).schemeRequirements)
          rfl rfl rfl rfl rfl rfl requirementsWellFormed
    · exact retained.requirements candidate member

end ActiveLocalFormation

/-- The complete lexical invariant threaded by recursive statement typing:
stable executable binders are aligned with the declarative local context, and
every active closed scheme and qualified-requirement template is formed in
that same context. -/
structure ActiveLocalContextInvariant
    (state : Frontend.SourceInference.State)
    (substitution : TypeSystem.Substitution)
    (context : SourceSemantics.Context) : Prop where
  aligned : LocalEnvironmentAligned state substitution context
  formation : ActiveLocalFormation state substitution context

namespace ActiveLocalContextInvariant

/-- Any update which preserves the active binder stack preserves the combined
lexical invariant. -/
theorem congr_localBinders
    {state final : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (localBinders_eq : final.localBinders = state.localBinders) :
    ActiveLocalContextInvariant final substitution context :=
  ⟨invariant.aligned.congr_localBinders localBinders_eq,
    invariant.formation.congr_localBinders localBinders_eq⟩

/-- Expression inference may allocate transient lambda or match binders, but
restores the caller's active lexical scope before returning.  Consequently the
combined executable/declarative local-context invariant is unchanged. -/
theorem inferExprFuel
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option TypeSystem.Ty}
    {state final : Frontend.SourceInference.State}
    {inferred : InferredExpression}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (success : Detail.inferExprFuel fuel inferenceContext expression expected
      state = .ok (inferred, final)) :
    ActiveLocalContextInvariant final substitution context := by
  apply invariant.congr_localBinders
  have scopeEq := Detail.inferExprFuel_success_lexicalScope_eq success
  simpa [Frontend.SourceInference.State.lexicalScope] using
    congrArg (fun scope : LexicalScope => scope.binders) scopeEq

/-- Source-ordered expression-list inference restores the caller's active
lexical scope, so it preserves the combined executable/declarative invariant. -/
theorem inferExprsFuel
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {expressions : List Syntax.Expr}
    {state final : Frontend.SourceInference.State}
    {inferred : List InferredExpression}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (success : Detail.inferExprsFuel fuel inferenceContext expressions state =
      .ok (inferred, final)) :
    ActiveLocalContextInvariant final substitution context := by
  apply invariant.congr_localBinders
  have scopeEq := Detail.inferExprsFuel_success_lexicalScope_eq success
  simpa [Frontend.SourceInference.State.lexicalScope] using
    congrArg (fun scope : LexicalScope => scope.binders) scopeEq

/-- Place inference traverses index expressions and member projections but
restores the caller's active lexical scope before returning. -/
theorem inferPlaceFuel
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression : Syntax.Expr}
    {state final : Frontend.SourceInference.State}
    {place : PlaceResolution}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (success : Detail.inferPlaceFuel fuel inferenceContext targetExpression
      state = .ok (place, final)) :
    ActiveLocalContextInvariant final substitution context := by
  apply invariant.congr_localBinders
  have scopeEq := Detail.inferPlaceFuel_success_lexicalScope_eq success
  simpa [Frontend.SourceInference.State.lexicalScope] using
    congrArg (fun scope : LexicalScope => scope.binders) scopeEq

/-- Assignment-value inference preserves the caller's active lexical scope
across both place traversal and right-hand-side expression inference. -/
theorem inferAssignedValueFuel
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression value : Syntax.Expr} {operator : Syntax.ValueAssignOp}
    {state final : Frontend.SourceInference.State}
    {assignment : AssignmentResolution} {inferredValue : InferredExpression}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (success : Detail.inferAssignedValueFuel fuel inferenceContext
      targetExpression operator value state =
        .ok (assignment, inferredValue, final)) :
    ActiveLocalContextInvariant final substitution context := by
  apply invariant.congr_localBinders
  have scopeEq :=
    Detail.inferAssignedValueFuel_success_lexicalScope_eq success
  simpa [Frontend.SourceInference.State.lexicalScope] using
    congrArg (fun scope : LexicalScope => scope.binders) scopeEq

/-- A guarded lookup of a monomorphic active binder yields a writable source
local at its type resolved by any semantic extension of the current inference
substitution. -/
theorem writableLocal_of_lookupBinder?
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    {name : String} {binder : TypedBinder}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (found : state.lookupBinder? name = some binder)
    (monomorphic : binder.scheme.quantified = [])
    (extension : substitution.SemanticallyExtends
      state.inference.substitution) :
    WritableLocal context binder.id
      (substitution.apply (state.resolve binder.scheme.body)) := by
  have lookup := (invariant.aligned.lookup_of_lookupBinder? found).1
  have formed := (invariant.formation.facts_of_lookupBinder? found).1
  refine .intro lookup formed (by simpa using monomorphic) ?_
  have resolvedEq :
      substitution.apply (state.resolve binder.scheme.body) =
        substitution.apply binder.scheme.body := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using extension binder.scheme.body
  simpa [TypeSystem.Scheme.apply, TypeSystem.Substitution.without,
    monomorphic] using resolvedEq.symm

/-- Replacing the compatibility-only name environment does not affect the
stable lexical invariant. -/
theorem withLocals
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (locals : TypeSystem.Environment) :
    ActiveLocalContextInvariant (state.withLocals locals) substitution
      context :=
  ⟨invariant.aligned.withLocals locals,
    invariant.formation.withLocals locals⟩

/-- Reserving a statement occurrence changes no stable local binder, so it
preserves the complete active-local invariant. -/
theorem allocateStatementId
    {state final : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context} {id : StatementId}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (allocated : state.allocateStatementId = (id, final)) :
    ActiveLocalContextInvariant final substitution context := by
  apply invariant.congr_localBinders
  have finalEq : (state.allocateStatementId).2 = final :=
    congrArg Prod.snd allocated
  rw [← finalEq]
  rfl

/-- Reserving the hidden local used by match lowering advances only the shared
local allocator; it does not enter a source-visible binder. -/
theorem allocateHiddenLocal
    {state final : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context} {id : Resolved.LocalId}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (allocated : state.allocateHiddenLocal = (id, final)) :
    ActiveLocalContextInvariant final substitution context := by
  apply invariant.congr_localBinders
  have finalEq : state.allocateHiddenLocal.2 = final :=
    congrArg Prod.snd allocated
  rw [← finalEq]
  rfl

/-- Recording an already allocated occurrence changes only the node table and
therefore preserves the complete active-local invariant. -/
theorem recordNode
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (node : Node) :
    ActiveLocalContextInvariant (state.recordNode node) substitution
      context := by
  apply invariant.congr_localBinders
  rfl

/-- Unification updates only the inference substitution, so it preserves the
complete active-local invariant. -/
theorem unify
    {state final : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context} {left right : TypeSystem.Ty}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (success : Detail.unify state left right = .ok final) :
    ActiveLocalContextInvariant final substitution context := by
  apply invariant.congr_localBinders
  unfold Detail.unify at success
  cases inferenceResult : Detail.liftUnification
      (state.inference.unify left right) with
  | error error =>
      simp [inferenceResult, bind, Except.bind] at success
  | ok inference =>
      simp only [inferenceResult, bind, Except.bind] at success
      change Except.ok { state with inference } = Except.ok final at success
      injection success with finalEq
      subst final
      rfl

/-- Restoring an enclosing lexical snapshot restores both halves of the
combined invariant. -/
theorem restoreLexicalScope
    {outer inner : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant outer substitution context) :
    ActiveLocalContextInvariant
      (inner.restoreLexicalScope outer.lexicalScope) substitution context :=
  ⟨invariant.aligned.restoreLexicalScope,
    invariant.formation.restoreLexicalScope⟩

/-- Recording the enclosing statement after lexical restoration preserves
the complete outer invariant. -/
theorem restoreLexicalScope_recordNode
    {outer inner : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant outer substitution context)
    (node : Node) :
    ActiveLocalContextInvariant
      ((inner.restoreLexicalScope outer.lexicalScope).recordNode node)
      substitution context :=
  ⟨invariant.aligned.restoreLexicalScope_recordNode node,
    invariant.formation.restoreLexicalScope_recordNode node⟩

/-- One fresh visible binder extends executable and declarative local scopes
in lockstep while preserving lookup alignment and active formation. -/
theorem allocateBinder_of_localBindersBelowNextLocal
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false)
    (schemeRequirements : List LocalSchemeRequirement := [])
    {binder : TypedBinder} {final : Frontend.SourceInference.State}
    (allocated : state.allocateBinder name scheme span comptime
      schemeRequirements = (binder, final))
    (below : state.LocalBindersBelowNextLocal)
    (schemeWellFormed : SchemeWellFormed context
      (binder.applySubstitution substitution).scheme)
    (requirementsWellFormed : LocalSchemeRequirementsWellFormed context
      (binder.applySubstitution substitution)) :
    ActiveLocalContextInvariant final substitution
      (context.withLocal binder.id
        (binder.applySubstitution substitution).scheme
        (binder.applySubstitution substitution).schemeRequirements) :=
  ⟨invariant.aligned.allocateBinder_of_localBindersBelowNextLocal
      name scheme span comptime schemeRequirements allocated below,
    invariant.formation.allocateBinder name scheme span comptime
      schemeRequirements allocated schemeWellFormed requirementsWellFormed⟩

end ActiveLocalContextInvariant

/-- A successful local-identifier place exposes the selected monomorphic
binder and the exact unprojected place returned by executable inference. -/
theorem inferPlaceFuel_success_identifier_facts
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {target : Syntax.Expr} {name : Syntax.Identifier}
    {state : Frontend.SourceInference.State}
    {result : PlaceResolution × Frontend.SourceInference.State}
    (targetEq : target.value = .identifier name)
    (success : Detail.inferPlaceFuel (fuel + 1) inferenceContext target state =
      .ok result) :
    ∃ binder,
      state.lookupBinder? name.value = some binder ∧
      binder.scheme.quantified = [] ∧
      result = ({
        root := binder.id
        projections := []
        type := state.resolve binder.scheme.body
      }, state) := by
  unfold Detail.inferPlaceFuel at success
  simp only [targetEq] at success
  cases lookupEq : state.lookupBinder? name.value with
  | none =>
      simp [lookupEq] at success
  | some binder =>
      simp only [lookupEq] at success
      cases emptyEq : binder.scheme.quantified.isEmpty with
      | false =>
          simp [emptyEq] at success
      | true =>
          simp only [emptyEq, if_true, pure, Pure.pure, Except.pure] at success
          injection success with resultEq
          rw [← resultEq]
          exact ⟨binder, rfl, List.isEmpty_iff.mp emptyEq, rfl⟩

/-- A successful identifier place is a declaratively typed writable local in
any fixed typed source once the closing substitution extends the returned
inference state. -/
theorem inferPlaceFuel_success_identifier_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression : Syntax.Expr} {name : Syntax.Identifier}
    {initial final : Frontend.SourceInference.State}
    {place : PlaceResolution} {source : TypedSource}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (targetEq : targetExpression.value = .identifier name)
    (success : Detail.inferPlaceFuel (fuel + 1) inferenceContext
      targetExpression initial = .ok (place, final))
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      final.inference.substitution) :
    SourcePlaceHasType (source.applySubstitution outer) target
      (place.applySubstitution outer) (outer.apply place.type) := by
  obtain ⟨binder, lookupEq, monomorphic, resultEq⟩ :=
    inferPlaceFuel_success_identifier_facts targetEq success
  injection resultEq with placeEq finalEq
  subst place
  subst final
  have writable := invariant.writableLocal_of_lookupBinder? lookupEq
    monomorphic outerExtension
  exact .intro writable (.nil _) rfl

/-- Every successful executable place traversal reconstructs a declaratively
typed source place in one fixed finalized source.  Expression typing remains
an explicit recursive callback for mapping keys; local roots, grouping, fresh
metavariables, unification, and projection composition are discharged here. -/
theorem inferPlaceFuel_success_sound
    {source : TypedSource} {outer : TypeSystem.Substitution}
    {target : SourceSemantics.Context}
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression : Syntax.Expr}
    {initial final : Frontend.SourceInference.State}
    {place : PlaceResolution}
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical :
      ∀ signature ∈ inferenceContext.signatures.functions,
        signature.scheme.body = .function
          (TypeSystem.Ty.productMany signature.parameterTypes)
          (TypeSystem.Ty.productMany signature.returnTypes))
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      final.inference.substitution)
    (expressionSound :
      ∀ {expressionFuel : Nat} {expression : Syntax.Expr}
        {expected : Option TypeSystem.Ty}
        {expressionInitial expressionFinal : Frontend.SourceInference.State}
        {inferred : InferredExpression},
        Detail.inferExprFuel expressionFuel inferenceContext expression
            expected expressionInitial = .ok (inferred, expressionFinal) →
          ExpressionHasType (source.applySubstitution outer) target
            inferred.id (outer.apply inferred.type))
    (success : Detail.inferPlaceFuel fuel inferenceContext targetExpression
      initial = .ok (place, final)) :
    SourcePlaceHasType (source.applySubstitution outer) target
      (place.applySubstitution outer) (outer.apply place.type) := by
  induction fuel generalizing targetExpression initial final place with
  | zero =>
      simp [Detail.inferPlaceFuel] at success
  | succ fuel induction =>
      cases targetEq : targetExpression.value with
      | identifier name =>
          exact inferPlaceFuel_success_identifier_sound targetEq success
            invariant outerExtension
      | group inner =>
          apply induction ready invariant outerExtension
          simpa only [Detail.inferPlaceFuel, targetEq] using success
      | index base brackets key =>
          unfold Detail.inferPlaceFuel at success
          simp only [targetEq, bind, Except.bind] at success
          cases baseResult : Detail.inferPlaceFuel fuel inferenceContext base
              initial with
          | error error =>
              simp [baseResult] at success
          | ok basePair =>
              rcases basePair with ⟨basePlace, baseState⟩
              simp only [baseResult] at success
              let keyAllocation := baseState.fresh
              let valueAllocation := keyAllocation.2.fresh
              cases unifyResult : Detail.unify valueAllocation.2 basePlace.type
                  (.mapping keyAllocation.1 valueAllocation.1) with
              | error error =>
                  simp [keyAllocation, valueAllocation, unifyResult] at success
              | ok unifiedState =>
                  simp only [keyAllocation, valueAllocation, unifyResult]
                    at success
                  cases keyResult : Detail.inferExprFuel fuel inferenceContext
                      key (some (unifiedState.resolve keyAllocation.1))
                      unifiedState with
                  | error error =>
                      simp [keyAllocation, keyResult] at success
                  | ok keyPair =>
                      rcases keyPair with ⟨inferredKey, keyState⟩
                      simp only [keyAllocation, keyResult, pure, Pure.pure,
                        Except.pure] at success
                      injection success with resultEq
                      injection resultEq with placeEq finalEq
                      subst place
                      subst final
                      have baseProperties :=
                        Detail.inferPlaceFuel_inferenceProperties ready
                          signatureFormation functionsCanonical baseResult
                      have keyProperties :=
                        Detail.fresh_eq_inferenceProperties
                          baseProperties.2.1
                          (initial := baseState) (type := keyAllocation.1)
                          (next := keyAllocation.2) rfl
                      have valueProperties :=
                        Detail.fresh_eq_inferenceProperties
                          keyProperties.2.1
                          (initial := keyAllocation.2)
                          (type := valueAllocation.1)
                          (next := valueAllocation.2) rfl
                      have baseAtValue : basePlace.type.VariablesBelow
                          valueAllocation.2.inference.next :=
                        baseProperties.2.2.weaken
                          (keyProperties.1.trans valueProperties.1).next_le
                      have keyAtValue : keyAllocation.1.VariablesBelow
                          valueAllocation.2.inference.next :=
                        keyProperties.2.2.weaken valueProperties.1.next_le
                      have mappingBelow :
                          (TypeSystem.Ty.mapping keyAllocation.1
                            valueAllocation.1).VariablesBelow
                              valueAllocation.2.inference.next :=
                        (TypeSystem.Ty.variablesBelow_mapping_iff _ _ _).2
                          ⟨keyAtValue, valueProperties.2.2⟩
                      have unifyProgress := Detail.unify_inferenceProgress
                        valueProperties.2.1.solved baseAtValue mappingBelow
                        unifyResult
                      have unifiedReady :=
                        Detail.unify_preserves_inferenceReady
                          valueProperties.2.1 baseAtValue mappingBelow
                          unifyResult
                      have keyAtUnified : keyAllocation.1.VariablesBelow
                          unifiedState.inference.next :=
                        keyAtValue.weaken unifyProgress.next_le
                      have resolvedKeyBelow :
                          (unifiedState.resolve keyAllocation.1).VariablesBelow
                            unifiedState.inference.next :=
                        unifiedReady.solved.variablesBelow_apply keyAtUnified
                      have keyExpressionProperties :=
                        Detail.inferExprFuel_inferenceProperties unifiedReady
                          signatureFormation functionsCanonical (by
                            intro expectedType member
                            simp only [Option.mem_def] at member
                            injection member with typeEq
                            subst expectedType
                            exact resolvedKeyBelow) keyResult
                      have tailProgress : baseState.InferenceProgress keyState :=
                        keyProperties.1.trans
                          (valueProperties.1.trans
                            (unifyProgress.trans keyExpressionProperties.1))
                      have outerBase : outer.SemanticallyExtends
                          baseState.inference.substitution :=
                        TypeSystem.Substitution.SemanticallyExtends.trans
                          outerExtension tailProgress.substitution_extends
                      have baseType := induction ready invariant outerBase
                        baseResult
                      have outerUnified : outer.SemanticallyExtends
                          unifiedState.inference.substitution :=
                        TypeSystem.Substitution.SemanticallyExtends.trans
                          outerExtension
                          keyExpressionProperties.1.substitution_extends
                      have mappingEq : outer.apply basePlace.type =
                          .mapping (outer.apply keyAllocation.1)
                            (outer.apply valueAllocation.1) := by
                        calc
                          outer.apply basePlace.type =
                              outer.apply (unifiedState.resolve
                                basePlace.type) := by
                            simpa [Frontend.SourceInference.State.resolve,
                              TypeSystem.InferState.resolve] using
                                (outerUnified basePlace.type).symm
                          _ = outer.apply (unifiedState.resolve
                                (.mapping keyAllocation.1
                                  valueAllocation.1)) :=
                            congrArg outer.apply
                              (Detail.unify_resolve_eq unifyResult)
                          _ = outer.apply (.mapping keyAllocation.1
                                valueAllocation.1) := by
                            simpa [Frontend.SourceInference.State.resolve,
                              TypeSystem.InferState.resolve] using
                                outerUnified (.mapping keyAllocation.1
                                  valueAllocation.1)
                          _ = .mapping (outer.apply keyAllocation.1)
                                (outer.apply valueAllocation.1) := rfl
                      have baseMapping : SourcePlaceHasType
                          (source.applySubstitution outer) target
                          (basePlace.applySubstitution outer)
                          (.mapping (outer.apply keyAllocation.1)
                            (outer.apply valueAllocation.1)) := by
                        rw [← mappingEq]
                        exact baseType
                      have keyExpectedEq : outer.apply inferredKey.type =
                          outer.apply keyAllocation.1 := by
                        calc
                          outer.apply inferredKey.type =
                              outer.apply (unifiedState.resolve
                                keyAllocation.1) :=
                            Detail.inferExprFuel_expected_type_apply_eq
                              keyResult outerExtension
                          _ = outer.apply keyAllocation.1 := by
                            simpa [Frontend.SourceInference.State.resolve,
                              TypeSystem.InferState.resolve] using
                                outerUnified keyAllocation.1
                      have keyType : ExpressionHasType
                          (source.applySubstitution outer) target inferredKey.id
                          (outer.apply keyAllocation.1) := by
                        rw [← keyExpectedEq]
                        exact expressionSound keyResult
                      have indexed := SourcePlaceHasType.snocIndex baseMapping
                        keyType
                      have resolvedValueEq :
                          outer.apply (keyState.resolve valueAllocation.1) =
                            outer.apply valueAllocation.1 := by
                        simpa [Frontend.SourceInference.State.resolve,
                          TypeSystem.InferState.resolve] using
                            outerExtension valueAllocation.1
                      simpa [keyAllocation, valueAllocation,
                        PlaceResolution.applySubstitution,
                        resolvedValueEq] using indexed
      | literal literal =>
          simp [Detail.inferPlaceFuel, targetEq] at success
      | dotConstructor dot name arguments =>
          simp [Detail.inferPlaceFuel, targetEq] at success
      | proxy marker type =>
          simp [Detail.inferPlaceFuel, targetEq] at success
      | lambda keyword parameters returnType body =>
          simp [Detail.inferPlaceFuel, targetEq] at success
      | unary operator operand =>
          simp [Detail.inferPlaceFuel, targetEq] at success
      | binary left operator right =>
          simp [Detail.inferPlaceFuel, targetEq] at success
      | call callee arguments =>
          simp [Detail.inferPlaceFuel, targetEq] at success
      | field base dot name =>
          simp [Detail.inferPlaceFuel, targetEq] at success
      | conditional condition question thenBranch colon elseBranch =>
          simp [Detail.inferPlaceFuel, targetEq] at success
      | tuple elements =>
          simp [Detail.inferPlaceFuel, targetEq] at success
      | array elements =>
          simp [Detail.inferPlaceFuel, targetEq] at success
      | error =>
          simp [Detail.inferPlaceFuel, targetEq] at success

/-- Successful value-assignment inference reconstructs the complete
declarative assignment judgment.  Plain assignment retains the inferred place
type; every compound operator is checked at `Word`. -/
theorem inferAssignedValueFuel_success_sound
    {source : TypedSource} {outer : TypeSystem.Substitution}
    {target : SourceSemantics.Context}
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp}
    {initial final : Frontend.SourceInference.State}
    {assignment : AssignmentResolution}
    {inferredValue : InferredExpression}
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical :
      ∀ signature ∈ inferenceContext.signatures.functions,
        signature.scheme.body = .function
          (TypeSystem.Ty.productMany signature.parameterTypes)
          (TypeSystem.Ty.productMany signature.returnTypes))
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      final.inference.substitution)
    (expressionSound :
      ∀ {expressionFuel : Nat} {expression : Syntax.Expr}
        {expected : Option TypeSystem.Ty}
        {expressionInitial expressionFinal : Frontend.SourceInference.State}
        {inferred : InferredExpression},
        Detail.inferExprFuel expressionFuel inferenceContext expression
            expected expressionInitial = .ok (inferred, expressionFinal) →
          ExpressionHasType (source.applySubstitution outer) target
            inferred.id (outer.apply inferred.type))
    (success : Detail.inferAssignedValueFuel fuel inferenceContext
      targetExpression operator value initial =
        .ok (assignment, inferredValue, final)) :
    SourceAssignmentHasType (source.applySubstitution outer) target
      (assignment.applySubstitution outer) operator inferredValue.id := by
  unfold Detail.inferAssignedValueFuel at success
  cases placeResult : Detail.inferPlaceFuel fuel inferenceContext
      targetExpression initial with
  | error error =>
      simp [placeResult, bind, Except.bind] at success
  | ok placePair =>
      rcases placePair with ⟨place, placeState⟩
      simp only [placeResult, bind, Except.bind, Prod.eta] at success
      have placeProperties := Detail.inferPlaceFuel_inferenceProperties ready
        signatureFormation functionsCanonical placeResult
      have finishNonEqual
          (operatorKind : WordCompoundAssignmentOperator operator)
          (tailSuccess :
            (do
              let fittedState ← Detail.unify placeState place.type .word
              let (inferredValue, finalState) ←
                Detail.inferExprFuel fuel inferenceContext value (some .word)
                  fittedState
              pure (({ target := { place with
                type := finalState.resolve place.type } } :
                  AssignmentResolution), inferredValue, finalState)) =
                .ok (assignment, inferredValue, final)) :
          SourceAssignmentHasType (source.applySubstitution outer) target
            (assignment.applySubstitution outer) operator inferredValue.id := by
        cases unifyResult : Detail.unify placeState place.type .word with
        | error error =>
            simp [unifyResult, bind, Except.bind] at tailSuccess
        | ok fittedState =>
            simp only [unifyResult, bind, Except.bind] at tailSuccess
            have fitProgress := Detail.unify_inferenceProgress
              placeProperties.2.1.solved placeProperties.2.2
              (TypeSystem.Ty.variablesBelow_constructor _ _) unifyResult
            have fittedReady := Detail.unify_preserves_inferenceReady
              placeProperties.2.1 placeProperties.2.2
              (TypeSystem.Ty.variablesBelow_constructor _ _) unifyResult
            cases valueResult : Detail.inferExprFuel fuel inferenceContext
                value (some .word) fittedState with
            | error error =>
                simp [valueResult] at tailSuccess
            | ok valuePair =>
                rcases valuePair with ⟨inferred, finalState⟩
                simp only [valueResult, pure, Pure.pure, Except.pure]
                  at tailSuccess
                injection tailSuccess with resultEq
                injection resultEq with assignmentEq valueStateEq
                injection valueStateEq with inferredEq finalEq
                subst assignment
                subst inferredValue
                subst final
                have valueProperties :=
                  Detail.inferExprFuel_inferenceProperties fittedReady
                    signatureFormation functionsCanonical (by
                      intro expectedType member
                      simp only [Option.mem_def] at member
                      injection member with typeEq
                      subst expectedType
                      exact TypeSystem.Ty.variablesBelow_constructor _ _)
                    valueResult
                have outerFitted : outer.SemanticallyExtends
                    fittedState.inference.substitution :=
                  TypeSystem.Substitution.SemanticallyExtends.trans
                    outerExtension valueProperties.1.substitution_extends
                have outerPlace : outer.SemanticallyExtends
                    placeState.inference.substitution :=
                  TypeSystem.Substitution.SemanticallyExtends.trans
                    outerFitted fitProgress.substitution_extends
                have placeType := inferPlaceFuel_success_sound ready
                  signatureFormation functionsCanonical invariant outerPlace
                  expressionSound placeResult
                have resolvedWord : fittedState.resolve place.type = .word :=
                  (Detail.unify_resolve_eq unifyResult).trans (by rfl)
                have placeWordEq : outer.apply place.type = .word := by
                  calc
                    outer.apply place.type =
                        outer.apply (fittedState.resolve place.type) := by
                      simpa [Frontend.SourceInference.State.resolve,
                        TypeSystem.InferState.resolve] using
                          (outerFitted place.type).symm
                    _ = outer.apply .word := congrArg outer.apply resolvedWord
                    _ = .word := rfl
                have placeWord : SourcePlaceHasType
                    (source.applySubstitution outer) target
                    (place.applySubstitution outer) .word := by
                  rw [← placeWordEq]
                  exact placeType
                have valueExpectedEq : outer.apply inferred.type = .word := by
                  simpa using
                    (Detail.inferExprFuel_expected_type_apply_eq valueResult
                      outerExtension)
                have valueWord : ExpressionHasType
                    (source.applySubstitution outer) target inferred.id
                    .word := by
                  rw [← valueExpectedEq]
                  exact expressionSound valueResult
                have resolvedFinal :
                    outer.apply (finalState.resolve place.type) =
                      outer.apply place.type := by
                  simpa [Frontend.SourceInference.State.resolve,
                    TypeSystem.InferState.resolve] using
                      outerExtension place.type
                have storedPlaceEq :
                    ({ place with type := finalState.resolve place.type } :
                      PlaceResolution).applySubstitution outer =
                        place.applySubstitution outer := by
                  cases place
                  simp [PlaceResolution.applySubstitution, resolvedFinal]
                have storedPlaceWord : SourcePlaceHasType
                    (source.applySubstitution outer) target
                    (({ place with type := finalState.resolve place.type } :
                      PlaceResolution).applySubstitution outer) .word := by
                  rw [storedPlaceEq]
                  exact placeWord
                exact .wordCompound operatorKind storedPlaceWord valueWord rfl
      cases operator with
      | equal =>
          simp only [pure, Pure.pure, Except.pure] at success
          cases valueResult : Detail.inferExprFuel fuel inferenceContext value
              (some (placeState.resolve place.type)) placeState with
          | error error =>
              simp [valueResult] at success
          | ok valuePair =>
              rcases valuePair with ⟨inferred, finalState⟩
              simp only [valueResult] at success
              injection success with resultEq
              injection resultEq with assignmentEq valueStateEq
              injection valueStateEq with inferredEq finalEq
              subst assignment
              subst inferredValue
              subst final
              have expectedBelow :
                  (placeState.resolve place.type).VariablesBelow
                    placeState.inference.next :=
                placeProperties.2.1.solved.variablesBelow_apply
                  placeProperties.2.2
              have valueProperties :=
                Detail.inferExprFuel_inferenceProperties
                  placeProperties.2.1 signatureFormation functionsCanonical
                  (by
                    intro expectedType member
                    simp only [Option.mem_def] at member
                    injection member with typeEq
                    subst expectedType
                    exact expectedBelow) valueResult
              have outerPlace : outer.SemanticallyExtends
                  placeState.inference.substitution :=
                TypeSystem.Substitution.SemanticallyExtends.trans
                  outerExtension valueProperties.1.substitution_extends
              have placeType := inferPlaceFuel_success_sound ready
                signatureFormation functionsCanonical invariant outerPlace
                expressionSound placeResult
              have valueExpectedEq : outer.apply inferred.type =
                  outer.apply place.type := by
                calc
                  outer.apply inferred.type =
                      outer.apply (placeState.resolve place.type) :=
                    Detail.inferExprFuel_expected_type_apply_eq valueResult
                      outerExtension
                  _ = outer.apply place.type := by
                    simpa [Frontend.SourceInference.State.resolve,
                      TypeSystem.InferState.resolve] using outerPlace place.type
              have valueType : ExpressionHasType
                  (source.applySubstitution outer) target inferred.id
                  (outer.apply place.type) := by
                rw [← valueExpectedEq]
                exact expressionSound valueResult
              have resolvedFinal :
                  outer.apply (finalState.resolve place.type) =
                    outer.apply place.type := by
                simpa [Frontend.SourceInference.State.resolve,
                  TypeSystem.InferState.resolve] using
                    outerExtension place.type
              have storedPlaceEq :
                  ({ place with type := finalState.resolve place.type } :
                    PlaceResolution).applySubstitution outer =
                      place.applySubstitution outer := by
                cases place
                simp [PlaceResolution.applySubstitution, resolvedFinal]
              have storedPlaceType : SourcePlaceHasType
                  (source.applySubstitution outer) target
                  (({ place with type := finalState.resolve place.type } :
                    PlaceResolution).applySubstitution outer)
                  (outer.apply place.type) := by
                rw [storedPlaceEq]
                exact placeType
              exact .equal storedPlaceType valueType rfl
      | add => exact finishNonEqual .add success
      | subtract => exact finishNonEqual .subtract success
      | multiply => exact finishNonEqual .multiply success
      | divide => exact finishNonEqual .divide success
      | modulo => exact finishNonEqual .modulo success
      | bitAnd => exact finishNonEqual .bitAnd success
      | bitXor => exact finishNonEqual .bitXor success
      | bitOr => exact finishNonEqual .bitOr success

/-- Alignment supplies the two semantic lookups for a guarded local name,
while active formation supplies the corresponding closed scheme judgments. -/
theorem localReferenceEnvironmentFacts_of_lookupBinder?
    {state : Frontend.SourceInference.State}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    {name : String} {binder : TypedBinder}
    (aligned : LocalEnvironmentAligned state substitution context)
    (formation : ActiveLocalFormation state substitution context)
    (found : state.lookupBinder? name = some binder) :
    context.LocalLookup binder.id
        (binder.applySubstitution substitution).scheme ∧
      context.LocalSchemeRequirementsLookup binder.id
        (binder.applySubstitution substitution).schemeRequirements ∧
      SchemeWellFormed context
        (binder.applySubstitution substitution).scheme ∧
      LocalSchemeRequirementsWellFormed context
        (binder.applySubstitution substitution) := by
  have lookups := aligned.lookup_of_lookupBinder? found
  have formed := formation.facts_of_lookupBinder? found
  exact ⟨lookups.1, lookups.2, formed.1, formed.2⟩

/-- A successful body check installs the finalized input binders into one
declarative lexical context and simultaneously aligns that context with the
checker's initial stable-binder state under the final inference substitution.
This is the common starting point for deep body-typing reconstruction. -/
theorem checkFunctionBody_success_initialLocalEnvironmentAligned
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (parameterTypes : TypesWellFormed
      (checkedBodyContext signatures signature checked)
      signature.parameterTypes)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    ∃ lexicalContext,
      MonoBindersExtend signature.id
          (checkedBodyContext signatures signature checked)
          checked.typedBody.inputs signature.parameterTypes lexicalContext ∧
        LocalEnvironmentAligned
          (Frontend.SourceInference.State.initial signature.id
            ((signature.parameterNames.zip signature.parameterTypes).map
              fun parameter =>
                (parameter.1, TypeSystem.Scheme.mono parameter.2))
            signature.parameterComptime)
          checked.substitution lexicalContext := by
  obtain ⟨lexicalContext, extension⟩ :=
    checkFunctionBody_success_inputs_extend
      (context := checkedBodyContext signatures signature checked)
      rfl rfl parameterTypes success
  refine ⟨lexicalContext, extension, ?_⟩
  apply LocalEnvironmentAligned.ofInitialMonoBindersExtend
    signature.id
    ((signature.parameterNames.zip signature.parameterTypes).map
      fun parameter =>
        (parameter.1, TypeSystem.Scheme.mono parameter.2))
    signature.parameterComptime checked.substitution
    (context := checkedBodyContext signatures signature checked)
    (final := lexicalContext) (types := signature.parameterTypes)
    rfl rfl
  have inputsEq :=
    Frontend.SourceInference.checkFunctionBody_success_typedBody_inputs success
  rw [inputsEq] at extension
  simpa only [Frontend.SourceInference.State.initial_inputs_eq_localBinders]
    using extension

/-- The initial semantic lexical context simultaneously carries exact lookup
alignment and formation for every finalized input binder.  This is the
complete lexical starting invariant for recursive body-typing reconstruction. -/
theorem checkFunctionBody_success_initialLocalEnvironmentFacts
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (parameterTypes : TypesWellFormed
      (checkedBodyContext signatures signature checked)
      signature.parameterTypes)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    ∃ lexicalContext,
      MonoBindersExtend signature.id
          (checkedBodyContext signatures signature checked)
          checked.typedBody.inputs signature.parameterTypes lexicalContext ∧
        LocalEnvironmentAligned
          (Frontend.SourceInference.State.initial signature.id
            ((signature.parameterNames.zip signature.parameterTypes).map
              fun parameter =>
                (parameter.1, TypeSystem.Scheme.mono parameter.2))
            signature.parameterComptime)
          checked.substitution lexicalContext ∧
        ActiveLocalFormation
          (Frontend.SourceInference.State.initial signature.id
            ((signature.parameterNames.zip signature.parameterTypes).map
              fun parameter =>
                (parameter.1, TypeSystem.Scheme.mono parameter.2))
            signature.parameterComptime)
          checked.substitution lexicalContext := by
  obtain ⟨lexicalContext, extension, aligned⟩ :=
    checkFunctionBody_success_initialLocalEnvironmentAligned parameterTypes
      success
  refine ⟨lexicalContext, extension, aligned, ?_⟩
  apply ActiveLocalFormation.ofMonoBindersExtend
  have initialExtension := extension
  have inputsEq :=
    Frontend.SourceInference.checkFunctionBody_success_typedBody_inputs success
  rw [inputsEq] at initialExtension
  simpa only [Frontend.SourceInference.State.initial_inputs_eq_localBinders]
    using initialExtension

/-- Package the initial lookup alignment and active formation supplied by a
successful body check into the invariant consumed by recursive statement
typing. -/
theorem checkFunctionBody_success_initialActiveLocalContextInvariant
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (parameterTypes : TypesWellFormed
      (checkedBodyContext signatures signature checked)
      signature.parameterTypes)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    ∃ lexicalContext,
      MonoBindersExtend signature.id
          (checkedBodyContext signatures signature checked)
          checked.typedBody.inputs signature.parameterTypes lexicalContext ∧
        ActiveLocalContextInvariant
          (Frontend.SourceInference.State.initial signature.id
            ((signature.parameterNames.zip signature.parameterTypes).map
              fun parameter =>
                (parameter.1, TypeSystem.Scheme.mono parameter.2))
            signature.parameterComptime)
          checked.substitution lexicalContext := by
  obtain ⟨lexicalContext, extension, aligned, formation⟩ :=
    checkFunctionBody_success_initialLocalEnvironmentFacts parameterTypes
      success
  exact ⟨lexicalContext, extension, ⟨aligned, formation⟩⟩

/-- The frontend no-capture certificate already has exactly the
predicate-wide shape required by the semantic substitution bridge. -/
theorem localBinderInstantiationNoCapture_predicateRangeAvoids
    {outer : TypeSystem.Substitution} {binder : TypedBinder}
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder) :
    ∀ requirement, requirement ∈ binder.schemeRequirements →
      FlexibleSubstitution.PredicateRangeAvoidsVariablesOn outer
        binder.scheme.quantified requirement.predicate := by
  intro requirement member
  exact noCapture.requirement_ranges requirement member

/-- Reconstruct a declaratively valid local-scheme use from the frontend's
canonical fresh instantiation and its final no-capture certificate.  In a
residually open target context, admissibility of the final inference
substitution automatically supplies admissibility of the composed canonical
instantiation range. -/
theorem canonicalLocalSchemeInstantiationValid_afterSubstitution
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    {binder : TypedBinder} {actualRequirements : List RequirementId}
    (binders : TypeParameterBindersWellFormed target)
    (residual : target.residualTypeVariables = true)
    (outerRange : SubstitutionRangeAdmissible target outer)
    (formation : LocalSchemeRequirementsWellFormed target
      (binder.applySubstitution outer))
    (schemeWellFormed : SchemeWellFormed target
      (binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder)
    (next : Nat)
    (actualUnique : actualRequirements.Nodup)
    (actualDisjoint : ∀ id, id ∈ actualRequirements →
      id ∉ localSchemeTemplateIds (binder.applySubstitution outer))
    (requirements : RequirementSequenceProves target actualRequirements
      ((instantiateLocalSchemePredicates
          (binder.scheme.instantiateWithSubstitution next).substitution
          binder).map
        (TypedTraitResolution.applySubstitution outer))) :
    LocalSchemeInstantiationValid target
      (binder.applySubstitution outer)
      (outer.apply (binder.scheme.instantiateWithSubstitution next).body)
      actualRequirements := by
  apply
    FlexibleSubstitution.LocalSchemeInstantiationValid.of_instantiateWithSubstitution_afterSubstitution_atTarget
      formation schemeWellFormed noCapture.quantified_fresh
      noCapture.body_range
      (localBinderInstantiationNoCapture_predicateRangeAvoids noCapture)
      next
      (FlexibleSubstitution.SubstitutionRangeAdmissible.mapRange_instantiateWithSubstitution
        binder.scheme next binders residual outerRange)
      actualUnique actualDisjoint requirements

/-- Adding the two semantic local-environment lookups turns the canonical
frontend instantiation certificate into a complete valid local reference
use. -/
theorem canonicalLocalReferenceUseValid_afterSubstitution
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    {binder : TypedBinder} {actualRequirements : List RequirementId}
    (schemeLookup : target.LocalLookup binder.id
      (binder.applySubstitution outer).scheme)
    (requirementsLookup : target.LocalSchemeRequirementsLookup binder.id
      (binder.applySubstitution outer).schemeRequirements)
    (binders : TypeParameterBindersWellFormed target)
    (residual : target.residualTypeVariables = true)
    (outerRange : SubstitutionRangeAdmissible target outer)
    (formation : LocalSchemeRequirementsWellFormed target
      (binder.applySubstitution outer))
    (schemeWellFormed : SchemeWellFormed target
      (binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder)
    (next : Nat)
    (actualUnique : actualRequirements.Nodup)
    (actualDisjoint : ∀ id, id ∈ actualRequirements →
      id ∉ localSchemeTemplateIds (binder.applySubstitution outer))
    (requirements : RequirementSequenceProves target actualRequirements
      ((instantiateLocalSchemePredicates
          (binder.scheme.instantiateWithSubstitution next).substitution
          binder).map
        (TypedTraitResolution.applySubstitution outer))) :
    ReferenceUseValid target (.local binder.id)
      (outer.apply (binder.scheme.instantiateWithSubstitution next).body)
      actualRequirements := by
  simpa only [FlexibleSubstitution.applyTypedBinder_id] using
    (ReferenceUseValid.local
      (binder := binder.applySubstitution outer)
      schemeLookup requirementsLookup
      (canonicalLocalSchemeInstantiationValid_afterSubstitution binders
        residual outerRange formation schemeWellFormed noCapture next
        actualUnique actualDisjoint requirements))

/-- Every complete reference-use certificate validates all requirement
identities owned by that reference shape. -/
theorem referenceUseValid_requirementIdsValid
    {context : SourceSemantics.Context} {resolution : ReferenceResolution}
    {type : TypeSystem.Ty} {requirements : List RequirementId}
    (valid : ReferenceUseValid context resolution type requirements) :
    RequirementIdsValid context requirements := by
  cases valid with
  | «local» _ _ instantiation =>
      exact instantiation.actual_requirements_valid
  | declaration _ proves => exact proves.ids_valid
  | builtinFunction _ =>
      intro requirement member
      simp at member
  | builtinBoolean _ =>
      intro requirement member
      simp at member

/-- A semantically valid local reference and its ordinary requirement/coercion
layout assemble directly into the common expression-typing envelope. -/
theorem localReferenceExpressionHasType_of_referenceUseValid
    {source : TypedSource} {target : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {name : String}
    {binder : TypedBinder} {rawType : TypeSystem.Ty}
    {actualRequirements : List RequirementId}
    (contains : ContainsExpression source id node)
    (formEq : node.form = .reference name (.local binder.id))
    (referenceValid : ReferenceUseValid target (.local binder.id) rawType
      actualRequirements)
    (rawAdmissible : TypeAdmissible target rawType)
    (finalAdmissible : TypeAdmissible target node.type)
    (path : CoercionPathValid target rawType node.type node.coercions)
    (layout : node.requirements =
      actualRequirements ++ coercionRequirementIds node.coercions) :
    ExpressionHasType source target id node.type := by
  apply ExpressionHasType.ofOrdinary contains
    (rawType := rawType) (owned := actualRequirements)
  · rw [formEq]
    exact .reference referenceValid
  · exact rawAdmissible
  · exact finalAdmissible
  · exact referenceUseValid_requirementIdsValid referenceValid
  · exact path
  · exact layout

/-- The complete canonical frontend-local certificate therefore types a
retained local-reference expression once its ordinary output path is known. -/
theorem canonicalLocalReferenceExpressionHasType_afterSubstitution
    {source : TypedSource}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {name : String}
    {binder : TypedBinder} {actualRequirements : List RequirementId}
    (contains : ContainsExpression source id node)
    (formEq : node.form = .reference name (.local binder.id))
    (schemeLookup : target.LocalLookup binder.id
      (binder.applySubstitution outer).scheme)
    (requirementsLookup : target.LocalSchemeRequirementsLookup binder.id
      (binder.applySubstitution outer).schemeRequirements)
    (binders : TypeParameterBindersWellFormed target)
    (residual : target.residualTypeVariables = true)
    (outerRange : SubstitutionRangeAdmissible target outer)
    (formation : LocalSchemeRequirementsWellFormed target
      (binder.applySubstitution outer))
    (schemeWellFormed : SchemeWellFormed target
      (binder.applySubstitution outer).scheme)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer binder)
    (next : Nat)
    (actualUnique : actualRequirements.Nodup)
    (actualDisjoint : ∀ requirement,
      requirement ∈ actualRequirements →
        requirement ∉ localSchemeTemplateIds
          (binder.applySubstitution outer))
    (requirements : RequirementSequenceProves target actualRequirements
      ((instantiateLocalSchemePredicates
          (binder.scheme.instantiateWithSubstitution next).substitution
          binder).map
        (TypedTraitResolution.applySubstitution outer)))
    (rawAdmissible : TypeAdmissible target
      (outer.apply (binder.scheme.instantiateWithSubstitution next).body))
    (finalAdmissible : TypeAdmissible target node.type)
    (path : CoercionPathValid target
      (outer.apply (binder.scheme.instantiateWithSubstitution next).body)
      node.type node.coercions)
    (layout : node.requirements =
      actualRequirements ++ coercionRequirementIds node.coercions) :
    ExpressionHasType source target id node.type := by
  apply localReferenceExpressionHasType_of_referenceUseValid contains formEq
    (canonicalLocalReferenceUseValid_afterSubstitution schemeLookup
      requirementsLookup binders residual outerRange formation schemeWellFormed
      noCapture next actualUnique actualDisjoint requirements)
    rawAdmissible finalAdmissible path layout

/-- Generalizing a type with no flexible variables is observationally the
monomorphic scheme for that type.  Since every retained qualified requirement
must mention a quantified variable, the accompanying requirement row is empty;
the resulting scheme therefore satisfies exact generalization in every
semantic context. -/
theorem generalizeValue_closed_facts
    (state : Frontend.SourceInference.State)
    (locals : TypeSystem.Environment) (requirementStart : Nat)
    (type : TypeSystem.Ty) (context : SourceSemantics.Context)
    (closed : type.freeVariables = []) :
    (Detail.generalizeValue state locals requirementStart type).scheme =
        .mono type ∧
      (Detail.generalizeValue state locals requirementStart type).requirements =
        [] ∧
      SchemeGeneralizes context
        (Detail.generalizeValue state locals requirementStart type).scheme := by
  have quantifiedEmpty :
      (Detail.generalizeValue state locals requirementStart type).scheme.quantified =
        [] := by
    rw [Detail.generalizeValue_scheme_quantified, closed]
    rfl
  have schemeEq :
      (Detail.generalizeValue state locals requirementStart type).scheme =
        .mono type := by
    generalize schemeDef :
      (Detail.generalizeValue state locals requirementStart type).scheme =
        scheme at quantifiedEmpty ⊢
    cases scheme with
    | mk quantified body =>
        change quantified = [] at quantifiedEmpty
        have bodyEq : body = type := by
          have bodyValue :=
            Detail.generalizeValue_scheme_body state locals requirementStart type
          rw [schemeDef] at bodyValue
          exact bodyValue
        cases quantifiedEmpty
        cases bodyEq
        rfl
  refine ⟨schemeEq,
    Detail.generalizeValue_requirements_empty_of_quantified_eq_nil
      state locals requirementStart type quantifiedEmpty, ?_⟩
  rw [schemeEq]
  unfold SchemeGeneralizes SchemeGeneralizesExcept
  simp [TypeSystem.Scheme.mono, closed]

/-- Agreement of the executable and declarative generalization barriers on
the inferred type's candidate variables is enough to recover exact qualified
rank-one generalization.  Variables outside `type.freeVariables` are
irrelevant because neither side of `SchemeGeneralizesExcept` can select them. -/
theorem generalizeValue_schemeGeneralizesExcept_of_barrier
    (state : Frontend.SourceInference.State)
    (locals : TypeSystem.Environment) (requirementStart : Nat)
    (type : TypeSystem.Ty) (context : SourceSemantics.Context)
    (barrier : ∀ metavariable, metavariable ∈ type.freeVariables →
      (metavariable ∈
          Detail.generalizeValueBlockedVariables state locals requirementStart ↔
        metavariable ∈ GeneralizationBlockedVariablesExcept context
          ((Detail.generalizeValue state locals requirementStart type).requirements.map
            fun requirement => requirement.templateRequirement))) :
    SchemeGeneralizesExcept context
      ((Detail.generalizeValue state locals requirementStart type).requirements.map
        fun requirement => requirement.templateRequirement)
      (Detail.generalizeValue state locals requirementStart type).scheme := by
  unfold SchemeGeneralizesExcept
  rw [Detail.generalizeValue_scheme_quantified,
    Detail.generalizeValue_scheme_body]
  apply List.filter_congr
  intro metavariable member
  have barrierAt := barrier metavariable member
  by_cases executableBlocked : metavariable ∈
      Detail.generalizeValueBlockedVariables state locals requirementStart
  · have semanticBlocked := barrierAt.mp executableBlocked
    simp [executableBlocked, semanticBlocked]
  · have semanticUnblocked : metavariable ∉
        GeneralizationBlockedVariablesExcept context
          ((Detail.generalizeValue state locals requirementStart type).requirements.map
            fun requirement => requirement.templateRequirement) := by
      intro semanticBlocked
      exact executableBlocked (barrierAt.mpr semanticBlocked)
    simp [executableBlocked, semanticUnblocked]

/-- A raw binder allocated from `generalizeValue` acquires both formation
judgments after final substitution.  Scheme-body formation comes from the
already typed final initializer; qualified-template identity and evidence
come from the final scoped ledger, while raw predicate and dependency facts
are transported through the closing substitution. -/
theorem generalizeValue_binderFormation_afterSubstitution
    (state : Frontend.SourceInference.State)
    (locals : TypeSystem.Environment) (requirementStart : Nat)
    (type : TypeSystem.Ty)
    {substitution : TypeSystem.Substitution}
    {closedVariables : List TypeSystem.TypeVarId}
    {sourceContext targetContext : SourceSemantics.Context}
    {rawSource : TypedSource} {binder : TypedBinder} {initializer : NodeId}
    (scheme_eq : binder.scheme =
      (Detail.generalizeValue state locals requirementStart type).scheme)
    (requirements_eq : binder.schemeRequirements =
      (Detail.generalizeValue state locals requirementStart type).requirements)
    (closes : FlexibleSubstitution.ContextCloses substitution closedVariables
      sourceContext targetContext)
    (fresh : ∀ metavariable,
      metavariable ∈ binder.scheme.quantified →
        metavariable ∉ substitution.domain)
    (ledger : ScopedRequirementLedgerWellFormed targetContext
      (rawSource.applySubstitution substitution))
    (contains : ∀ requirement,
      requirement ∈ binder.schemeRequirements →
        ContainsLocalSchemeTemplate rawSource {
          binder := binder
          initializer := initializer
          requirement := requirement
        })
    (predicates : ∀ requirement,
      requirement ∈ binder.schemeRequirements →
        PredicateAdmissible
          (localSchemeInitializerContext sourceContext binder)
          requirement.predicate)
    (bodyAdmissible : TypeAdmissible
      (localSchemeInitializerContext targetContext
        (binder.applySubstitution substitution))
      (binder.applySubstitution substitution).scheme.body) :
    SchemeWellFormed targetContext
        (binder.applySubstitution substitution).scheme ∧
      LocalSchemeRequirementsWellFormed targetContext
        (binder.applySubstitution substitution) := by
  have rawQuantifiedNodup : binder.scheme.quantified.Nodup := by
    rw [scheme_eq]
    exact Detail.generalizeValue_scheme_quantified_nodup state locals
      requirementStart type
  have finalQuantifiedNodup :
      (binder.applySubstitution substitution).scheme.quantified.Nodup := by
    simpa using rawQuantifiedNodup
  constructor
  · exact
      StructuralSubstitution.SchemeWellFormed.ofLocalSchemeInitializerAdmissible
        bodyAdmissible finalQuantifiedNodup
  · apply
      FlexibleSubstitution.ScopedRequirementLedgerWellFormed.localSchemeRequirementsWellFormed_afterSubstitution
        (binder := binder) (initializer := initializer)
        closes fresh ledger contains predicates
    intro requirement member
    rw [requirements_eq] at member
    rcases Detail.generalizeValue_requirement_depends_on_quantified state
        locals requirementStart type requirement member with
      ⟨metavariable, quantified, occurs⟩
    refine ⟨metavariable, ?_, occurs⟩
    rw [scheme_eq]
    exact quantified

/-- Any expression node retained by an inference state is declaratively
contained in every typed-source view of that state. -/
theorem toTypedSource_containsExpression_of_mem
    {state : Frontend.SourceInference.State} {node : ExpressionNode}
    (member : Node.expression node ∈ state.nodes)
    (roots : List NodeId := []) :
    ContainsExpression (state.toTypedSource roots) node.id node := by
  exact ⟨(by simpa [Frontend.SourceInference.State.toTypedSource] using member),
    rfl⟩

/-- Any statement node retained by an inference state is declaratively
contained in every typed-source view of that state. -/
theorem toTypedSource_containsStatement_of_mem
    {state : Frontend.SourceInference.State} {node : StatementNode}
    (member : Node.statement node ∈ state.nodes)
    (roots : List NodeId := []) :
    ContainsStatement (state.toTypedSource roots) node.id node := by
  exact ⟨(by simpa [Frontend.SourceInference.State.toTypedSource] using member),
    rfl⟩

/-- Recording an expression node immediately materializes declarative
expression containment. -/
theorem recordNode_containsExpression
    (state : Frontend.SourceInference.State) (node : ExpressionNode)
    (roots : List NodeId := []) :
    ContainsExpression
      ((state.recordNode (.expression node)).toTypedSource roots)
      node.id node := by
  apply toTypedSource_containsExpression_of_mem
  simp [Frontend.SourceInference.State.recordNode]

/-- Recording a statement node immediately materializes declarative
statement containment. -/
theorem recordNode_containsStatement
    (state : Frontend.SourceInference.State) (node : StatementNode)
    (roots : List NodeId := []) :
    ContainsStatement
      ((state.recordNode (.statement node)).toTypedSource roots)
      node.id node := by
  apply toTypedSource_containsStatement_of_mem
  simp [Frontend.SourceInference.State.recordNode]

/-- The expression-recording helper materializes its exact payload as a
declaratively contained expression node. -/
theorem recordExpression_containsExpression
    (source : Syntax.Expr) (expression : InferredExpression)
    (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep)
    (state : Frontend.SourceInference.State) (roots : List NodeId := [])
    (localSchemeInstantiationStart : Option Nat := none) :
    ContainsExpression
      ((Detail.recordExpression source expression form requirements coercions
        state localSchemeInstantiationStart).2.toTypedSource roots)
      expression.id {
        id := expression.id
        span := source.span
        type := expression.type
        form
        requirements
        coercions
        localSchemeInstantiationStart
      } := by
  unfold Detail.recordExpression
  exact recordNode_containsExpression state _ roots

/-- Successful expected-type recording materializes the exact expression node
returned by the frontend, leaving only its fitted coercion path existential. -/
theorem recordExpressionWithExpected_success_containsExpression
    {context : Frontend.SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId}
    {type : TypeSystem.Ty} {form : ExpressionForm}
    {requirements : List RequirementId}
    {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {localSchemeInstantiationStart : Option Nat}
    {result : InferredExpression × Frontend.SourceInference.State}
    (success : Detail.recordExpressionWithExpected context source id type form
      requirements expected state localSchemeInstantiationStart = .ok result)
    (roots : List NodeId := []) :
    ∃ coercions,
      ContainsExpression (result.2.toTypedSource roots) result.1.id {
        id := result.1.id
        span := source.span
        type := result.1.type
        form
        requirements := requirements ++
          Detail.coercionRequirements coercions
        coercions
        localSchemeInstantiationStart
      } := by
  obtain ⟨fitted, _, resultExpression, resultState⟩ :=
    Detail.recordExpressionWithExpected_success_record success
  refine ⟨fitted.coercions, ?_⟩
  rw [resultState, resultExpression]
  exact recordNode_containsExpression fitted.state _ roots

/-- Successful expression inference against a concrete expectation remains
equal to that expectation in every later inference state.  This is the
frontend-wide coherence fact used by returns, conditions, annotated locals,
and other expected-typed expression consumers. -/
theorem inferExprFuel_success_expected_type_afterProgress
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {expected : TypeSystem.Ty}
    {initial finalState : Frontend.SourceInference.State}
    {result : InferredExpression × Frontend.SourceInference.State}
    (success : Detail.inferExprFuel fuel context expression (some expected)
      initial = .ok result)
    (progress : result.2.InferenceProgress finalState) :
    finalState.resolve result.1.type = finalState.resolve expected := by
  simpa [Frontend.SourceInference.State.resolve,
    TypeSystem.InferState.resolve] using
      (Detail.inferExprFuel_expected_type_apply_eq success
        progress.substitution_extends)

/-- A successful grouped-expression branch exposes both recursive inference
and the exact parent recording operation.  The retained parent points to the
child occurrence returned by that recursive call and owns only requirements
introduced by its fitted output-coercion path. -/
theorem inferExprFuel_success_group_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression inner : Syntax.Expr} {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : expression.value = .group inner)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (success : Detail.inferExprFuel (fuel + 1) context expression expected
      initial = .ok result)
    (roots : List NodeId := []) :
    ∃ innerResult innerState coercions,
      Detail.inferExprFuel fuel context inner expected allocated =
        .ok (innerResult, innerState) ∧
      Detail.recordExpressionWithExpected context expression id
        innerResult.type (.group innerResult.id) [] expected innerState =
          .ok result ∧
      ContainsExpression (result.2.toTypedSource roots) result.1.id {
        id := result.1.id
        span := expression.span
        type := result.1.type
        form := .group innerResult.id
        requirements := Detail.coercionRequirements coercions
        coercions
      } := by
  unfold Detail.inferExprFuel at success
  simp only [allocationEq, expressionEq, bind, Except.bind] at success
  cases innerSuccess :
      Detail.inferExprFuel fuel context inner expected allocated with
  | error error =>
      simp [innerSuccess] at success
  | ok innerPair =>
      rcases innerPair with ⟨innerResult, innerState⟩
      simp only [innerSuccess] at success
      obtain ⟨coercions, contains⟩ :=
        recordExpressionWithExpected_success_containsExpression success roots
      exact ⟨innerResult, innerState, coercions, rfl, success,
        by simpa using contains⟩

/-- A grouped expression inherits its raw type from its already typed child.
After final substitution, validating the parent's fitted output path is enough
to type the retained group occurrence. -/
theorem groupBranchExpressionHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    {expression : Syntax.Expr} {result innerResult : InferredExpression}
    {coercions : List CoercionStep}
    (contains : ContainsExpression source result.id {
      id := result.id
      span := expression.span
      type := result.type
      form := .group innerResult.id
      requirements := Detail.coercionRequirements coercions
      coercions
    })
    (innerType : ExpressionHasType (source.applySubstitution outer) target
      innerResult.id (outer.apply innerResult.type))
    (finalAdmissible : TypeAdmissible target (outer.apply result.type))
    (path : CoercionPathValid target (outer.apply innerResult.type)
      (outer.apply result.type)
      (coercions.map (CoercionStep.applySubstitution outer))) :
    ExpressionHasType (source.applySubstitution outer) target result.id
      (outer.apply result.type) := by
  apply ExpressionHasType.ofOrdinary
    (rawType := outer.apply innerResult.type) (owned := [])
    (FlexibleSubstitution.ContainsExpression.applySubstitution outer contains)
  · exact .group innerType
  · exact innerType.type_admissible
  · exact finalAdmissible
  · intro requirement member
    simp at member
  · exact path
  · change Detail.coercionRequirements coercions =
      coercionRequirementIds
        (coercions.map (CoercionStep.applySubstitution outer))
    rw [FlexibleSubstitution.coercionRequirementIds_applySubstitution]
    rfl

/-- A successful annotated declaration without an initializer exposes the
exact source-type resolution and binder-allocation pipeline.  Its
generalization barrier is the requirement position immediately after
statement-ID allocation. -/
theorem inferStatementFuel_success_letAnnotatedUninitialized_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name (some sourceType) none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ resolvedType locals valueType generalized binding,
      Detail.resolveSourceType context sourceType = .ok resolvedType ∧
      locals = allocated.binderEnvironment.apply
        allocated.inference.substitution ∧
      valueType = allocated.resolve resolvedType ∧
      generalized = Detail.generalizeValue allocated locals
        allocated.nextRequirement valueType ∧
      (allocated.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements = binding ∧
      result = {
        id
        type := .unit
        hasValue := false
        sawReturn := false
        state := binding.2.recordNode (.statement {
          id
          span := statement.span
          type := .unit
          form := .letDecl binding.1 none
        })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .letDecl binding.1 none
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases resolution : Detail.resolveSourceType context sourceType with
  | error error =>
      simp [resolution] at success
  | ok resolvedType =>
      simp only [resolution, pure, Pure.pure, Except.pure] at success
      let locals := allocated.binderEnvironment.apply
        allocated.inference.substitution
      let valueType := allocated.resolve resolvedType
      let generalized := Detail.generalizeValue allocated locals
        allocated.nextRequirement valueType
      let binding := (allocated.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false generalized.requirements
      injection success with resultEq
      rw [← resultEq]
      exact ⟨resolvedType, locals, valueType, generalized, binding,
        rfl, rfl, rfl, rfl, rfl, rfl,
        recordNode_containsStatement binding.2 _ roots⟩

/-- Closing a binder generalized from a resolved source annotation yields a
well-formed monomorphic scheme, no qualified local requirements, and the exact
declarative generalization judgment.  The generalization barrier position is
explicit so the certificate serves both initialized and uninitialized lets. -/
theorem resolvedAnnotationBinderFacts_afterSubstitution
    {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    {inferenceContext : Frontend.SourceInference.Context}
    {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr}
    {state final : Frontend.SourceInference.State}
    {requirementStart : Nat}
    {resolvedType valueType : TypeSystem.Ty}
    {locals : TypeSystem.Environment}
    {generalized : Detail.GeneralizedValue} {binder : TypedBinder}
    (resolution : Detail.resolveSourceType inferenceContext sourceType =
      .ok resolvedType)
    (valueType_eq : valueType = state.resolve resolvedType)
    (generalized_eq : generalized = Detail.generalizeValue state locals
      requirementStart valueType)
    (allocated : (state.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false generalized.requirements =
        (binder, final))
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (parameters_eq : target.typeParameters = inferenceContext.typeParameters)
    (declaration_eq : target.currentDeclaration =
      some inferenceContext.scope.genericOwner) :
    TypeWellFormed target resolvedType ∧
      (binder.applySubstitution outer).scheme = .mono resolvedType ∧
      (binder.applySubstitution outer).schemeRequirements = [] ∧
      SchemeGeneralizes target
        (binder.applySubstitution outer).scheme := by
  have typeWellFormed : TypeWellFormed target resolvedType :=
    resolveSourceType_success_typeWellFormed canonical signatures_eq
      parameters_eq declaration_eq resolution
  have resolvedClosed : resolvedType.freeVariables = [] :=
    StructuralSubstitution.TypeWellFormed.freeVariables_eq_nil typeWellFormed
  have resolvedByState : state.resolve resolvedType = resolvedType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
      (Detail.resolveSourceType_success_apply_eq_self
        state.inference.substitution resolution)
  have valueClosed : valueType.freeVariables = [] := by
    rw [valueType_eq, resolvedByState]
    exact resolvedClosed
  have generalizedFacts := generalizeValue_closed_facts state locals
    requirementStart valueType target valueClosed
  have generalizedSchemeEq : generalized.scheme = .mono resolvedType := by
    calc
      generalized.scheme =
          (Detail.generalizeValue state locals requirementStart
            valueType).scheme :=
        congrArg Detail.GeneralizedValue.scheme generalized_eq
      _ = .mono valueType := generalizedFacts.1
      _ = .mono resolvedType := by rw [valueType_eq, resolvedByState]
  have generalizedRequirementsEq : generalized.requirements = [] := by
    calc
      generalized.requirements =
          (Detail.generalizeValue state locals requirementStart
            valueType).requirements :=
        congrArg Detail.GeneralizedValue.requirements generalized_eq
      _ = [] := generalizedFacts.2.1
  have binderEq :
      ((state.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements).1 = binder :=
    congrArg Prod.fst allocated
  have binderSchemeEq : binder.scheme = generalized.scheme := by
    rw [← binderEq]
    rfl
  have binderRequirementsEq : binder.schemeRequirements = [] := by
    rw [← binderEq]
    exact generalizedRequirementsEq
  have resolvedByOuter : outer.apply resolvedType = resolvedType :=
    Detail.resolveSourceType_success_apply_eq_self outer resolution
  have closedSchemeEq :
      (binder.applySubstitution outer).scheme = .mono resolvedType := by
    simp [binderSchemeEq, generalizedSchemeEq, TypeSystem.Scheme.apply,
      TypeSystem.Scheme.mono, TypeSystem.Substitution.without,
      resolvedByOuter]
  have closedRequirementsEq :
      (binder.applySubstitution outer).schemeRequirements = [] := by
    simp [binderRequirementsEq]
  refine ⟨typeWellFormed, closedSchemeEq, closedRequirementsEq, ?_⟩
  rw [closedSchemeEq]
  unfold SchemeGeneralizes SchemeGeneralizesExcept
  simp [TypeSystem.Scheme.mono, resolvedClosed]

/-- The executable pipeline for an annotated declaration without an
initializer reconstructs the declarative monomorphic `let` judgment after
final substitution.  Closed source annotations make both local
generalization and the closing substitution inert; stable-local alignment
then supplies the exact semantic context extension. -/
theorem letAnnotatedUninitializedStatementHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {id : StatementId}
    {state final : Frontend.SourceInference.State}
    {resolvedType valueType : TypeSystem.Ty}
    {locals : TypeSystem.Environment}
    {generalized : Detail.GeneralizedValue} {binder : TypedBinder}
    (resolution : Detail.resolveSourceType inferenceContext sourceType =
      .ok resolvedType)
    (valueType_eq : valueType = state.resolve resolvedType)
    (generalized_eq : generalized = Detail.generalizeValue state locals
      state.nextRequirement valueType)
    (allocated : (state.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false generalized.requirements =
        (binder, final))
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := .unit
      form := .letDecl binder none
    })
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (parameters_eq : target.typeParameters = inferenceContext.typeParameters)
    (declaration_eq : target.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (aligned : LocalEnvironmentAligned state outer target)
    (below : state.LocalBindersBelowNextLocal)
    (owner_eq : source.owner = state.owner) :
    StatementHasType (source.applySubstitution outer) control target id
      (target.withLocal binder.id
        (binder.applySubstitution outer).scheme
        (binder.applySubstitution outer).schemeRequirements) {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } := by
  obtain ⟨typeWellFormed, closedSchemeEq, closedRequirementsEq,
      generalizes⟩ :=
    resolvedAnnotationBinderFacts_afterSubstitution resolution
      valueType_eq generalized_eq allocated canonical signatures_eq
      parameters_eq declaration_eq
  have extended : BinderExtends (state.withLocals locals).owner target
      (binder.applySubstitution outer)
      (target.withLocal binder.id
        (binder.applySubstitution outer).scheme
        (binder.applySubstitution outer).schemeRequirements) := by
    apply
      (aligned.withLocals locals).monomorphicBinderExtends_of_allocateBinder
        (Frontend.SourceInference.State.withLocals_preserves_localBindersBelowNextLocal
          state locals below)
        allocated closedSchemeEq closedRequirementsEq typeWellFormed
  exact .letUninitialized
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl
    (by rw [closedSchemeEq]; rfl)
    generalizes
    (by
      simpa [Frontend.SourceInference.State.withLocals, owner_eq] using
        extended)
    (by simp [StatementNode.applySubstitution])

/-- A retained initialized `let` with a monomorphic closed binder is typed by
the finalized initializer, exact generalization, and the matching lexical
context extension. -/
theorem letInitializedMonomorphicStatementHasType_afterSubstitution
    {source : TypedSource} {target final : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {statement : Syntax.Statement} {id : StatementId}
    {binder : TypedBinder} {initializer : ExpressionId}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := .unit
      form := .letDecl binder (some initializer)
    })
    (initializerType : ExpressionHasType
      (source.applySubstitution outer) target initializer
      (binder.applySubstitution outer).scheme.body)
    (monomorphic :
      (binder.applySubstitution outer).scheme.quantified = [])
    (generalizes : SchemeGeneralizes target
      (binder.applySubstitution outer).scheme)
    (extension : BinderExtends source.owner target
      (binder.applySubstitution outer) final) :
    StatementHasType (source.applySubstitution outer) control target id final {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .ordinary .unit
    } := by
  exact .letInitialized
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl initializerType monomorphic generalizes
    (by simpa using extension)
    (by simp [StatementNode.applySubstitution])

/-- The generalized initialized `let` constructor has the same substitution
boundary, with qualified requirement formation and initializer typing in the
scheme's scoped initializer context supplied explicitly. -/
theorem letInitializedGeneralizedStatementHasType_afterSubstitution
    {source : TypedSource} {target final : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {statement : Syntax.Statement} {id : StatementId}
    {binder : TypedBinder} {initializer : ExpressionId}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := .unit
      form := .letDecl binder (some initializer)
    })
    (polymorphic :
      (binder.applySubstitution outer).scheme.quantified ≠ [])
    (requirementsWellFormed : LocalSchemeRequirementsWellFormed target
      (binder.applySubstitution outer))
    (generalizes : SchemeGeneralizesExcept target
      (localSchemeTemplateIds (binder.applySubstitution outer))
      (binder.applySubstitution outer).scheme)
    (initializerType : ExpressionHasType (source.applySubstitution outer)
      (localSchemeInitializerContext target
        (binder.applySubstitution outer))
      initializer (binder.applySubstitution outer).scheme.body)
    (extension : BinderExtends source.owner target
      (binder.applySubstitution outer) final) :
    StatementHasType (source.applySubstitution outer) control target id final {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .ordinary .unit
    } := by
  exact .letInitializedGeneralized
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl polymorphic requirementsWellFormed generalizes initializerType
    (by simpa using extension)
    (by simp [StatementNode.applySubstitution])

/-- Expected-type coherence makes an initialized declaration with a source
annotation monomorphic before generalization.  Given recursive initializer
typing and a final substitution extending its inference state, the complete
executable binder pipeline therefore reconstructs the ordinary initialized
`let` judgment. -/
theorem letAnnotatedInitializedStatementHasType_afterSubstitution
    {fuel : Nat} {source : TypedSource}
    {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {id : StatementId}
    {expressionState initializerState final :
      Frontend.SourceInference.State}
    {resolvedType valueType : TypeSystem.Ty}
    {inferred : InferredExpression} {requirementStart : Nat}
    {locals : TypeSystem.Environment}
    {generalized : Detail.GeneralizedValue} {binder : TypedBinder}
    (resolution : Detail.resolveSourceType inferenceContext sourceType =
      .ok resolvedType)
    (initializerSuccess : Detail.inferExprFuel fuel inferenceContext
      initializer (some resolvedType) expressionState =
        .ok (inferred, initializerState))
    (valueType_eq : valueType = initializerState.resolve inferred.type)
    (generalized_eq : generalized = Detail.generalizeValue initializerState
      locals requirementStart valueType)
    (allocated : (initializerState.withLocals locals).allocateBinder
      name.value generalized.scheme (some name.span) false
      generalized.requirements = (binder, final))
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := .unit
      form := .letDecl binder (some inferred.id)
    })
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (parameters_eq : target.typeParameters = inferenceContext.typeParameters)
    (declaration_eq : target.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (aligned : LocalEnvironmentAligned initializerState outer target)
    (below : initializerState.LocalBindersBelowNextLocal)
    (owner_eq : source.owner = initializerState.owner)
    (initializerSolved : initializerState.inference.Solved)
    (outerExtension : outer.SemanticallyExtends
      initializerState.inference.substitution)
    (initializerType : ExpressionHasType
      (source.applySubstitution outer) target inferred.id
      (outer.apply inferred.type)) :
    StatementHasType (source.applySubstitution outer) control target id
      (target.withLocal binder.id
        (binder.applySubstitution outer).scheme
        (binder.applySubstitution outer).schemeRequirements) {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } := by
  have rawExpected :
      initializerState.resolve inferred.type =
        initializerState.resolve resolvedType :=
    inferExprFuel_success_expected_type_afterProgress initializerSuccess
      (Frontend.SourceInference.State.InferenceProgress.refl
        initializerSolved)
  have resolvedValueTypeEq :
      valueType = initializerState.resolve resolvedType :=
    valueType_eq.trans rawExpected
  obtain ⟨typeWellFormed, closedSchemeEq, closedRequirementsEq,
      generalizes⟩ :=
    resolvedAnnotationBinderFacts_afterSubstitution resolution
      resolvedValueTypeEq generalized_eq allocated canonical signatures_eq
      parameters_eq declaration_eq
  have outerExpected :
      outer.apply inferred.type = outer.apply resolvedType :=
    Detail.inferExprFuel_expected_type_apply_eq initializerSuccess
      outerExtension
  have resolvedByOuter : outer.apply resolvedType = resolvedType :=
    Detail.resolveSourceType_success_apply_eq_self outer resolution
  have initializerFinalEq : outer.apply inferred.type = resolvedType :=
    outerExpected.trans resolvedByOuter
  have binderBodyEq :
      (binder.applySubstitution outer).scheme.body = resolvedType := by
    rw [closedSchemeEq]
    rfl
  have closedInitializerType : ExpressionHasType
      (source.applySubstitution outer) target inferred.id
      (binder.applySubstitution outer).scheme.body := by
    rw [binderBodyEq, ← initializerFinalEq]
    exact initializerType
  have extended : BinderExtends
      (initializerState.withLocals locals).owner target
      (binder.applySubstitution outer)
      (target.withLocal binder.id
        (binder.applySubstitution outer).scheme
        (binder.applySubstitution outer).schemeRequirements) := by
    apply
      (aligned.withLocals locals).monomorphicBinderExtends_of_allocateBinder
        (Frontend.SourceInference.State.withLocals_preserves_localBindersBelowNextLocal
          initializerState locals below)
        allocated closedSchemeEq closedRequirementsEq typeWellFormed
  apply letInitializedMonomorphicStatementHasType_afterSubstitution
    contains closedInitializerType
  · rw [closedSchemeEq]
    rfl
  · exact generalizes
  · simpa [Frontend.SourceInference.State.withLocals, owner_eq] using
      extended

/-- The resolved-annotation binder certificate advances the complete
active-local invariant.  This is the compositional lexical result required to
continue typing statements after either annotated declaration form. -/
theorem resolvedAnnotationBinderPreservesActiveLocalContextInvariant_afterSubstitution
    {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    {inferenceContext : Frontend.SourceInference.Context}
    {name : Syntax.Identifier} {sourceType : Syntax.TypeExpr}
    {state final : Frontend.SourceInference.State}
    {requirementStart : Nat}
    {resolvedType valueType : TypeSystem.Ty}
    {locals : TypeSystem.Environment}
    {generalized : Detail.GeneralizedValue} {binder : TypedBinder}
    (resolution : Detail.resolveSourceType inferenceContext sourceType =
      .ok resolvedType)
    (valueType_eq : valueType = state.resolve resolvedType)
    (generalized_eq : generalized = Detail.generalizeValue state locals
      requirementStart valueType)
    (allocated : (state.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false generalized.requirements =
        (binder, final))
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (parameters_eq : target.typeParameters = inferenceContext.typeParameters)
    (declaration_eq : target.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (invariant : ActiveLocalContextInvariant state outer target)
    (below : state.LocalBindersBelowNextLocal) :
    ActiveLocalContextInvariant final outer
      (target.withLocal binder.id
        (binder.applySubstitution outer).scheme
        (binder.applySubstitution outer).schemeRequirements) := by
  obtain ⟨typeWellFormed, closedSchemeEq, closedRequirementsEq, _⟩ :=
    resolvedAnnotationBinderFacts_afterSubstitution resolution
      valueType_eq generalized_eq allocated canonical signatures_eq
      parameters_eq declaration_eq
  apply
    (invariant.withLocals locals).allocateBinder_of_localBindersBelowNextLocal
      name.value generalized.scheme (some name.span) false
      generalized.requirements allocated
      (Frontend.SourceInference.State.withLocals_preserves_localBindersBelowNextLocal
        state locals below)
  · rw [closedSchemeEq]
    exact SchemeWellFormed.mono typeWellFormed
  · exact LocalSchemeRequirementsWellFormed.empty target _
      closedRequirementsEq

/-- The proof-facing facts of one finalized statement agree with the three
fields retained by executable statement inference.  Control is deliberately
absent: it is determined by `StatementHasType`, whereas `StatementResult`
stores only the observable type/value/return projections. -/
structure StatementResultMatchesFactsAfterSubstitution
    (substitution : TypeSystem.Substitution)
    (result : Detail.StatementResult) (facts : StatementFacts) : Prop where
  type_eq : facts.type = substitution.apply result.type
  hasValue_eq : facts.hasValue = result.hasValue
  sawReturn_eq : facts.sawReturn = result.sawReturn

/-- The complete annotated-uninitialized branch is compositional: successful
inference yields a declaratively typed statement, advances the active lexical
invariant to the recorded output state, and agrees exactly with the
executable statement summary. -/
theorem inferStatementFuel_success_letAnnotatedUninitialized_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .letDecl name (some sourceType) none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (parameters_eq : target.typeParameters = inferenceContext.typeParameters)
    (declaration_eq : target.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (below : initial.LocalBindersBelowNextLocal)
    (roots : List NodeId := []) :
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved :=
      Frontend.SourceInference.State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [finalEq] at preserved
    exact preserved
  obtain ⟨resolvedType, locals, valueType, generalized, binding,
      resolution, _, valueTypeEq, generalizedEq, bindingEq, resultEq,
      contains⟩ :=
    inferStatementFuel_success_letAnnotatedUninitialized_facts statementEq
      allocationEq success roots
  subst result
  let finalContext := target.withLocal binding.1.id
    (binding.1.applySubstitution outer).scheme
    (binding.1.applySubstitution outer).schemeRequirements
  have bindingInvariant : ActiveLocalContextInvariant binding.2 outer
      finalContext := by
    exact
      resolvedAnnotationBinderPreservesActiveLocalContextInvariant_afterSubstitution
        resolution valueTypeEq generalizedEq bindingEq canonical
        signatures_eq parameters_eq declaration_eq allocatedInvariant
        allocatedBelow
  have recordedInvariant : ActiveLocalContextInvariant
      (binding.2.recordNode (.statement {
        id
        span := statement.span
        type := .unit
        form := .letDecl binding.1 none
      })) outer finalContext :=
    bindingInvariant.recordNode _
  have bindingStateEq :
      ((allocated.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements).2 = binding.2 :=
    congrArg Prod.snd bindingEq
  have sourceOwner :
      ((binding.2.recordNode (.statement {
        id
        span := statement.span
        type := .unit
        form := .letDecl binding.1 none
      })).toTypedSource roots).owner = allocated.owner := by
    change binding.2.owner = allocated.owner
    rw [← bindingStateEq]
    rfl
  have typing : StatementHasType
      (((binding.2.recordNode (.statement {
        id
        span := statement.span
        type := .unit
        form := .letDecl binding.1 none
      })).toTypedSource roots).applySubstitution outer)
      control target id finalContext {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      } := by
    exact letAnnotatedUninitializedStatementHasType_afterSubstitution
      resolution valueTypeEq generalizedEq bindingEq contains canonical
      signatures_eq parameters_eq declaration_eq allocatedInvariant.aligned
      allocatedBelow sourceOwner
  refine ⟨finalContext, {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .ordinary .unit
    }, recordedInvariant, typing, ?_⟩
  constructor <;> rfl

/-- A successful unannotated initialized declaration exposes the initializer
inference and the exact generalized binder subsequently entered into scope.
The requirement barrier remains the pre-initializer position retained in the
allocated statement state. -/
theorem inferStatementFuel_success_letUnannotatedInitialized_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name none (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ inferred initializerState locals valueType generalized binding,
      Detail.inferExprFuel fuel context initializer none allocated =
        .ok (inferred, initializerState) ∧
      locals = initializerState.binderEnvironment.apply
        initializerState.inference.substitution ∧
      valueType = initializerState.resolve inferred.type ∧
      generalized = Detail.generalizeValue initializerState locals
        allocated.nextRequirement valueType ∧
      (initializerState.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements = binding ∧
      result = {
        id
        type := .unit
        hasValue := false
        sawReturn := false
        state := binding.2.recordNode (.statement {
          id
          span := statement.span
          type := .unit
          form := .letDecl binding.1 (some inferred.id)
        })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .letDecl binding.1 (some inferred.id)
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases initializerSuccess :
      Detail.inferExprFuel fuel context initializer none allocated with
  | error error =>
      simp [initializerSuccess] at success
  | ok initializerPair =>
      rcases initializerPair with ⟨inferred, initializerState⟩
      simp only [initializerSuccess, pure, Pure.pure, Except.pure] at success
      let locals := initializerState.binderEnvironment.apply
        initializerState.inference.substitution
      let valueType := initializerState.resolve inferred.type
      let generalized := Detail.generalizeValue initializerState locals
        allocated.nextRequirement valueType
      let binding :=
        (initializerState.withLocals locals).allocateBinder name.value
          generalized.scheme (some name.span) false generalized.requirements
      injection success with resultEq
      rw [← resultEq]
      exact ⟨inferred, initializerState, locals, valueType, generalized,
        binding, rfl, rfl, rfl, rfl, rfl, rfl,
        recordNode_containsStatement binding.2 _ roots⟩

/-- The semantic obligations deliberately left at the unannotated
initialized-`let` boundary.  A producer supplies typing in the generalized
initializer context, qualified-requirement formation, exact generalization,
and quantifier freshness; the compositional wrapper below handles the
executable branch inversion and lexical-state bookkeeping. -/
structure UnannotatedInitializedLetCertificate
    (source : TypedSource) (target : SourceSemantics.Context)
    (outer : TypeSystem.Substitution) (binder : TypedBinder)
    (initializer : ExpressionId) : Prop where
  initializer_type : ExpressionHasType (source.applySubstitution outer)
    (localSchemeInitializerContext target
      (binder.applySubstitution outer))
    initializer (binder.applySubstitution outer).scheme.body
  requirements_well_formed : LocalSchemeRequirementsWellFormed target
    (binder.applySubstitution outer)
  generalizes : SchemeGeneralizesExcept target
    (localSchemeTemplateIds (binder.applySubstitution outer))
    (binder.applySubstitution outer).scheme
  quantified_fresh : SchemeQuantifiersFresh target
    (binder.applySubstitution outer).scheme

/-- Successful unannotated initialized declaration inference is sound once
the genuinely semantic generalization obligations are supplied by an
`UnannotatedInitializedLetCertificate`.  The wrapper derives scheme
formation and the monomorphic qualified-requirement restriction from the
exact executable generalization, installs the allocated binder, and returns
the active context needed by following statements. -/
theorem inferStatementFuel_success_letUnannotatedInitialized_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {initializer : Syntax.Expr} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .letDecl name none (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (below : initial.LocalBindersBelowNextLocal)
    (roots : List NodeId := [])
    (certificate :
      ∀ {inferred initializerState locals valueType generalized binding},
        Detail.inferExprFuel fuel inferenceContext initializer none allocated =
          .ok (inferred, initializerState) →
        locals = initializerState.binderEnvironment.apply
          initializerState.inference.substitution →
        valueType = initializerState.resolve inferred.type →
        generalized = Detail.generalizeValue initializerState locals
          allocated.nextRequirement valueType →
        (initializerState.withLocals locals).allocateBinder name.value
          generalized.scheme (some name.span) false
          generalized.requirements = binding →
        UnannotatedInitializedLetCertificate
          (result.state.toTypedSource roots) target outer binding.1
          inferred.id) :
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved :=
      Frontend.SourceInference.State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [finalEq] at preserved
    exact preserved
  obtain ⟨inferred, initializerState, locals, valueType, generalized,
      binding, initializerSuccess, localsEq, valueTypeEq, generalizedEq,
      bindingEq, resultEq, contains⟩ :=
    inferStatementFuel_success_letUnannotatedInitialized_facts statementEq
      allocationEq success roots
  have initializerInvariant :
      ActiveLocalContextInvariant initializerState outer target :=
    allocatedInvariant.inferExprFuel initializerSuccess
  have initializerBelow : initializerState.LocalBindersBelowNextLocal :=
    Detail.inferExprFuel_preserves_localBindersBelowNextLocal allocatedBelow
      initializerSuccess
  have semanticCertificate := certificate initializerSuccess localsEq
    valueTypeEq generalizedEq bindingEq
  subst result
  have binderEq :
      ((initializerState.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements).1 = binding.1 :=
    congrArg Prod.fst bindingEq
  have bindingStateEq :
      ((initializerState.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements).2 = binding.2 :=
    congrArg Prod.snd bindingEq
  have rawSchemeEq : binding.1.scheme = generalized.scheme := by
    rw [← binderEq]
    rfl
  have rawRequirementsEq :
      binding.1.schemeRequirements = generalized.requirements := by
    rw [← binderEq]
    rfl
  have rawQuantifiedNodup : binding.1.scheme.quantified.Nodup := by
    rw [rawSchemeEq, generalizedEq]
    exact Detail.generalizeValue_scheme_quantified_nodup initializerState
      locals allocated.nextRequirement valueType
  have closedQuantifiedNodup :
      (binding.1.applySubstitution outer).scheme.quantified.Nodup := by
    simpa using rawQuantifiedNodup
  have schemeWellFormed : SchemeWellFormed target
      (binding.1.applySubstitution outer).scheme :=
    StructuralSubstitution.SchemeWellFormed.ofLocalSchemeInitializerAdmissible
      semanticCertificate.initializer_type.type_admissible
      closedQuantifiedNodup
  have monomorphicRequirementsEmpty :
      (binding.1.applySubstitution outer).scheme.quantified = [] →
        (binding.1.applySubstitution outer).schemeRequirements = [] := by
    intro closedQuantifiedEmpty
    have rawQuantifiedEmpty : binding.1.scheme.quantified = [] := by
      simpa using closedQuantifiedEmpty
    have generalizedQuantifiedEmpty : generalized.scheme.quantified = [] := by
      rw [← rawSchemeEq]
      exact rawQuantifiedEmpty
    have canonicalQuantifiedEmpty :
        (Detail.generalizeValue initializerState locals
          allocated.nextRequirement valueType).scheme.quantified = [] := by
      rw [← generalizedEq]
      exact generalizedQuantifiedEmpty
    have canonicalRequirementsEmpty :=
      Detail.generalizeValue_requirements_empty_of_quantified_eq_nil
        initializerState locals allocated.nextRequirement valueType
        canonicalQuantifiedEmpty
    have generalizedRequirementsEmpty : generalized.requirements = [] := by
      rw [generalizedEq]
      exact canonicalRequirementsEmpty
    have rawRequirementsEmpty : binding.1.schemeRequirements = [] := by
      rw [rawRequirementsEq, generalizedRequirementsEmpty]
    simp [rawRequirementsEmpty]
  let finalContext := target.withLocal binding.1.id
    (binding.1.applySubstitution outer).scheme
    (binding.1.applySubstitution outer).schemeRequirements
  have bindingInvariant : ActiveLocalContextInvariant binding.2 outer
      finalContext := by
    exact (initializerInvariant.withLocals locals)
      |>.allocateBinder_of_localBindersBelowNextLocal name.value
        generalized.scheme (some name.span) false generalized.requirements
        bindingEq
        (Frontend.SourceInference.State.withLocals_preserves_localBindersBelowNextLocal
          initializerState locals initializerBelow)
        schemeWellFormed semanticCertificate.requirements_well_formed
  have extended : BinderExtends
      (initializerState.withLocals locals).owner target
      (binding.1.applySubstitution outer) finalContext := by
    exact (initializerInvariant.aligned.withLocals locals)
      |>.binderExtends_of_allocateBinder
        (Frontend.SourceInference.State.withLocals_preserves_localBindersBelowNextLocal
          initializerState locals initializerBelow)
        bindingEq schemeWellFormed semanticCertificate.quantified_fresh
        monomorphicRequirementsEmpty
  have recordedInvariant : ActiveLocalContextInvariant
      (binding.2.recordNode (.statement {
        id
        span := statement.span
        type := .unit
        form := .letDecl binding.1 (some inferred.id)
      })) outer finalContext :=
    bindingInvariant.recordNode _
  have sourceOwner :
      ((binding.2.recordNode (.statement {
        id
        span := statement.span
        type := .unit
        form := .letDecl binding.1 (some inferred.id)
      })).toTypedSource roots).owner = initializerState.owner := by
    change binding.2.owner = initializerState.owner
    rw [← bindingStateEq]
    rfl
  have semanticExtension : BinderExtends
      ((binding.2.recordNode (.statement {
        id
        span := statement.span
        type := .unit
        form := .letDecl binding.1 (some inferred.id)
      })).toTypedSource roots).owner target
      (binding.1.applySubstitution outer) finalContext := by
    rw [sourceOwner]
    simpa [Frontend.SourceInference.State.withLocals] using extended
  have typing : StatementHasType
      (((binding.2.recordNode (.statement {
        id
        span := statement.span
        type := .unit
        form := .letDecl binding.1 (some inferred.id)
      })).toTypedSource roots).applySubstitution outer)
      control target id finalContext {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      } := by
    by_cases monomorphic :
        (binding.1.applySubstitution outer).scheme.quantified = []
    · have requirementsEmpty := monomorphicRequirementsEmpty monomorphic
      have initializerContextEq :
          localSchemeInitializerContext target
              (binding.1.applySubstitution outer) = target := by
        rw [localSchemeInitializerContext_eq_withTypeVariables target _
          requirementsEmpty, monomorphic]
        exact SourceSemantics.Context.withTypeVariables_nil target
      have ordinaryInitializerType : ExpressionHasType
          (((binding.2.recordNode (.statement {
            id
            span := statement.span
            type := .unit
            form := .letDecl binding.1 (some inferred.id)
          })).toTypedSource roots).applySubstitution outer)
          target inferred.id
          (binding.1.applySubstitution outer).scheme.body := by
        simpa only [initializerContextEq] using
          semanticCertificate.initializer_type
      have ordinaryGeneralizes : SchemeGeneralizes target
          (binding.1.applySubstitution outer).scheme := by
        have exactGeneralizes := semanticCertificate.generalizes
        have templateIdsEmpty : localSchemeTemplateIds
            (binding.1.applySubstitution outer) = [] :=
          localSchemeTemplateIds_eq_nil _ requirementsEmpty
        rw [templateIdsEmpty] at exactGeneralizes
        exact (SchemeGeneralizesExcept_nil target _).mp exactGeneralizes
      exact letInitializedMonomorphicStatementHasType_afterSubstitution
        contains ordinaryInitializerType monomorphic ordinaryGeneralizes
        semanticExtension
    · exact letInitializedGeneralizedStatementHasType_afterSubstitution
        contains monomorphic semanticCertificate.requirements_well_formed
        semanticCertificate.generalizes semanticCertificate.initializer_type
        semanticExtension
  refine ⟨finalContext, {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .ordinary .unit
    }, recordedInvariant, typing, ?_⟩
  constructor <;> rfl

/-- A successful annotated initialized declaration exposes both source-type
resolution and expected-type initializer inference before the same exact
generalization and binder-allocation pipeline.  Generalization still starts
at the requirement position captured before initializer inference. -/
theorem inferStatementFuel_success_letAnnotatedInitialized_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .letDecl name (some sourceType) (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ resolvedType inferred initializerState locals valueType generalized
        binding,
      Detail.resolveSourceType context sourceType = .ok resolvedType ∧
      Detail.inferExprFuel fuel context initializer (some resolvedType)
        allocated = .ok (inferred, initializerState) ∧
      locals = initializerState.binderEnvironment.apply
        initializerState.inference.substitution ∧
      valueType = initializerState.resolve inferred.type ∧
      generalized = Detail.generalizeValue initializerState locals
        allocated.nextRequirement valueType ∧
      (initializerState.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements = binding ∧
      result = {
        id
        type := .unit
        hasValue := false
        sawReturn := false
        state := binding.2.recordNode (.statement {
          id
          span := statement.span
          type := .unit
          form := .letDecl binding.1 (some inferred.id)
        })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .letDecl binding.1 (some inferred.id)
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases resolution : Detail.resolveSourceType context sourceType with
  | error error =>
      simp [resolution] at success
  | ok resolvedType =>
      simp only [resolution] at success
      cases initializerSuccess : Detail.inferExprFuel fuel context initializer
          (some resolvedType) allocated with
      | error error =>
          simp [initializerSuccess] at success
      | ok initializerPair =>
          rcases initializerPair with ⟨inferred, initializerState⟩
          simp only [initializerSuccess, pure, Pure.pure, Except.pure]
            at success
          let locals := initializerState.binderEnvironment.apply
            initializerState.inference.substitution
          let valueType := initializerState.resolve inferred.type
          let generalized := Detail.generalizeValue initializerState locals
            allocated.nextRequirement valueType
          let binding :=
            (initializerState.withLocals locals).allocateBinder name.value
              generalized.scheme (some name.span) false
              generalized.requirements
          injection success with resultEq
          rw [← resultEq]
          exact ⟨resolvedType, inferred, initializerState, locals, valueType,
            generalized, binding, rfl, initializerSuccess, rfl, rfl, rfl, rfl,
            rfl,
            recordNode_containsStatement binding.2 _ roots⟩

/-- The complete annotated-initialized branch is compositional modulo the
recursive typing theorem for its initializer.  All remaining obligations are
discharged from inference readiness, expected-type coherence, closed source
annotation formation, stable-local preservation, and the exact executable
branch inversion. -/
theorem inferStatementFuel_success_letAnnotatedInitialized_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier}
    {sourceType : Syntax.TypeExpr} {initializer : Syntax.Expr}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .letDecl name (some sourceType) (some initializer))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      Frontend.ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (parameters_eq : target.typeParameters = inferenceContext.typeParameters)
    (declaration_eq : target.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (ready : initial.InferenceReady)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (below : initial.LocalBindersBelowNextLocal)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (initializerSound :
      ∀ {expected : TypeSystem.Ty} {inferred : InferredExpression}
        {initializerState : Frontend.SourceInference.State},
        Detail.resolveSourceType inferenceContext sourceType = .ok expected →
        Detail.inferExprFuel fuel inferenceContext initializer (some expected)
            allocated = .ok (inferred, initializerState) →
        ExpressionHasType
          ((result.state.toTypedSource roots).applySubstitution outer)
          target inferred.id (outer.apply inferred.type)) :
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
    have preserved :=
      Frontend.SourceInference.State.allocateStatementId_preserves_localBindersBelowNextLocal
        initial below
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [finalEq] at preserved
    exact preserved
  have allocatedReady : allocated.InferenceReady := by
    have preserved :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [finalEq] at preserved
    exact preserved
  obtain ⟨resolvedType, inferred, initializerState, locals, valueType,
      generalized, binding, resolution, initializerSuccess, _, valueTypeEq,
      generalizedEq, bindingEq, resultEq, contains⟩ :=
    inferStatementFuel_success_letAnnotatedInitialized_facts statementEq
      allocationEq success roots
  have initializerProperties :=
    Detail.inferExprFuel_inferenceProperties allocatedReady
      signatureFormation functionsCanonical (by
        intro expectedType member
        simp only [Option.mem_def] at member
        injection member with typeEq
        subst expectedType
        exact Detail.resolveSourceType_success_variablesBelow resolution _)
      initializerSuccess
  have initializerInvariant :
      ActiveLocalContextInvariant initializerState outer target :=
    allocatedInvariant.inferExprFuel initializerSuccess
  have initializerBelow : initializerState.LocalBindersBelowNextLocal :=
    Detail.inferExprFuel_preserves_localBindersBelowNextLocal allocatedBelow
      initializerSuccess
  have initializerTyping := initializerSound resolution initializerSuccess
  subst result
  have bindingStateEq :
      ((initializerState.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements).2 = binding.2 :=
    congrArg Prod.snd bindingEq
  have bindingInferenceEq :
      binding.2.inference = initializerState.inference := by
    rw [← bindingStateEq]
    rfl
  have initializerExtension : outer.SemanticallyExtends
      initializerState.inference.substitution := by
    change outer.SemanticallyExtends
      binding.2.inference.substitution at outerExtension
    rw [bindingInferenceEq] at outerExtension
    exact outerExtension
  have rawExpected :
      initializerState.resolve inferred.type =
        initializerState.resolve resolvedType :=
    inferExprFuel_success_expected_type_afterProgress initializerSuccess
      (Frontend.SourceInference.State.InferenceProgress.refl
        initializerProperties.2.1.solved)
  have resolvedValueTypeEq :
      valueType = initializerState.resolve resolvedType :=
    valueTypeEq.trans rawExpected
  let finalContext := target.withLocal binding.1.id
    (binding.1.applySubstitution outer).scheme
    (binding.1.applySubstitution outer).schemeRequirements
  have bindingInvariant : ActiveLocalContextInvariant binding.2 outer
      finalContext := by
    exact
      resolvedAnnotationBinderPreservesActiveLocalContextInvariant_afterSubstitution
        resolution resolvedValueTypeEq generalizedEq bindingEq canonical
        signatures_eq parameters_eq declaration_eq initializerInvariant
        initializerBelow
  have recordedInvariant : ActiveLocalContextInvariant
      (binding.2.recordNode (.statement {
        id
        span := statement.span
        type := .unit
        form := .letDecl binding.1 (some inferred.id)
      })) outer finalContext :=
    bindingInvariant.recordNode _
  have sourceOwner :
      ((binding.2.recordNode (.statement {
        id
        span := statement.span
        type := .unit
        form := .letDecl binding.1 (some inferred.id)
      })).toTypedSource roots).owner = initializerState.owner := by
    change binding.2.owner = initializerState.owner
    rw [← bindingStateEq]
    rfl
  have typing : StatementHasType
      (((binding.2.recordNode (.statement {
        id
        span := statement.span
        type := .unit
        form := .letDecl binding.1 (some inferred.id)
      })).toTypedSource roots).applySubstitution outer)
      control target id finalContext {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      } := by
    exact letAnnotatedInitializedStatementHasType_afterSubstitution
      resolution initializerSuccess valueTypeEq generalizedEq bindingEq
      contains canonical signatures_eq parameters_eq declaration_eq
      initializerInvariant.aligned initializerBelow sourceOwner
      initializerProperties.2.1.solved initializerExtension initializerTyping
  refine ⟨finalContext, {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .ordinary .unit
    }, recordedInvariant, typing, ?_⟩
  constructor <;> rfl

/-- A successful expression-statement branch exposes the exact child
inference and the complete `StatementResult` recorded by the executable
frontend.  Consequently the retained statement node has exactly the type and
semicolon flag used to choose between value production and discard. -/
theorem inferStatementFuel_success_expression_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expression : Syntax.Expr}
    {trailingSemicolon : Bool} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .expression expression trailingSemicolon)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ inferred expressionState,
      Detail.inferExprFuel fuel context expression none allocated =
        .ok (inferred, expressionState) ∧
      result = {
        id
        type := if trailingSemicolon then .unit else inferred.type
        hasValue := !trailingSemicolon
        sawReturn := false
        state := expressionState.recordNode (.statement {
          id
          span := statement.span
          type := if trailingSemicolon then .unit else inferred.type
          form := .expression inferred.id trailingSemicolon
        })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .expression inferred.id trailingSemicolon
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases expressionSuccess :
      Detail.inferExprFuel fuel context expression none allocated with
  | error error =>
      simp [expressionSuccess] at success
  | ok expressionPair =>
      rcases expressionPair with ⟨inferred, expressionState⟩
      simp only [expressionSuccess, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      rw [← resultEq]
      exact ⟨inferred, expressionState, rfl, rfl,
        recordNode_containsStatement expressionState _ roots⟩

/-- A successful value-assignment statement exposes the complete delegated
assignment inference result and the exact ordinary-unit node recorded by the
statement layer. -/
theorem inferStatementFuel_success_assignValue_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .assignValue targetExpression operator value)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ assignment inferredValue assignmentState,
      Detail.inferAssignedValueFuel fuel context targetExpression
        operator.value value allocated =
          .ok (assignment, inferredValue, assignmentState) ∧
      result = {
        id
        type := .unit
        hasValue := false
        sawReturn := false
        state := assignmentState.recordNode (.statement {
          id
          span := statement.span
          type := .unit
          form := .assignValue assignment operator.value inferredValue.id
        })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .assignValue assignment operator.value inferredValue.id
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases assignmentSuccess : Detail.inferAssignedValueFuel fuel context
      targetExpression operator.value value allocated with
  | error error =>
      simp [assignmentSuccess] at success
  | ok assignmentResult =>
      rcases assignmentResult with
        ⟨assignment, inferredValue, assignmentState⟩
      simp only [assignmentSuccess, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      rw [← resultEq]
      exact ⟨assignment, inferredValue, assignmentState, rfl, rfl,
        recordNode_containsStatement assignmentState _ roots⟩

/-- A successful bit-not assignment exposes place inference, the exact
unification forcing the place to `Word`, and the finalized assignment target
stored in the recorded statement node. -/
theorem inferStatementFuel_success_assignBitNot_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .assignBitNot targetExpression operatorSpan)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ place placeState unified,
      Detail.inferPlaceFuel fuel context targetExpression allocated =
        .ok (place, placeState) ∧
      Detail.unify placeState place.type .word = .ok unified ∧
      unified.resolve place.type = .word ∧
      result = {
        id
        type := .unit
        hasValue := false
        sawReturn := false
        state := unified.recordNode (.statement {
          id
          span := statement.span
          type := .unit
          form := .assignBitNot {
            target := { place with type := unified.resolve place.type }
          }
        })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .assignBitNot {
          target := { place with type := unified.resolve place.type }
        }
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases placeSuccess : Detail.inferPlaceFuel fuel context targetExpression
      allocated with
  | error error =>
      simp [placeSuccess] at success
  | ok placeResult =>
      rcases placeResult with ⟨place, placeState⟩
      simp only [placeSuccess] at success
      cases unifySuccess : Detail.unify placeState place.type .word with
      | error error =>
          simp [unifySuccess] at success
      | ok unified =>
          simp only [unifySuccess, pure, Pure.pure, Except.pure] at success
          injection success with resultEq
          have resolvedEq : unified.resolve place.type = .word :=
            (Detail.unify_resolve_eq unifySuccess).trans (by rfl)
          rw [← resultEq]
          exact ⟨place, placeState, unified, rfl, unifySuccess, resolvedEq, rfl,
            recordNode_containsStatement unified _ roots⟩

/-- A successful `if` without an `else` exposes condition inference, checking of
the then-body, restoration of the condition state's lexical scope, and the
canonical unit statement recorded after that restoration. -/
theorem inferStatementFuel_success_ifWithoutElse_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .ifThen condition thenBody none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ inferredCondition conditionState thenResult,
      Detail.inferExprFuel fuel context condition (some .bool) allocated =
        .ok (inferredCondition, conditionState) ∧
      Detail.inferStatementsFuel fuel context thenBody.value expectedReturn
        conditionState = .ok thenResult ∧
      result = {
        id
        type := .unit
        hasValue := false
        sawReturn := false
        state :=
          (thenResult.state.restoreLexicalScope
            conditionState.lexicalScope).recordNode (.statement {
              id
              span := statement.span
              type := .unit
              form := .ifThen inferredCondition.id thenResult.statements none
            })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .ifThen inferredCondition.id thenResult.statements none
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases conditionSuccess : Detail.inferExprFuel fuel context condition
      (some .bool) allocated with
  | error error =>
      simp [conditionSuccess] at success
  | ok conditionPair =>
      rcases conditionPair with ⟨inferredCondition, conditionState⟩
      simp only [conditionSuccess] at success
      cases thenSuccess : Detail.inferStatementsFuel fuel context thenBody.value
          expectedReturn conditionState with
      | error error =>
          simp [thenSuccess] at success
      | ok thenResult =>
          simp only [thenSuccess, pure, Pure.pure, Except.pure] at success
          injection success with resultEq
          rw [← resultEq]
          exact ⟨inferredCondition, conditionState, thenResult,
            rfl, thenSuccess, rfl,
            recordNode_containsStatement
              (thenResult.state.restoreLexicalScope conditionState.lexicalScope)
              _ roots⟩

/-- A successful `if` with an `else` exposes both branch traversals in their
exact executable order.  The else branch starts from the restored then-state,
and the retained statement is recorded only after the else scope is restored. -/
theorem inferStatementFuel_success_ifWithElse_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .ifThen condition thenBody (some elseBody))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ inferredCondition conditionState thenResult elseResult,
      Detail.inferExprFuel fuel context condition (some .bool) allocated =
        .ok (inferredCondition, conditionState) ∧
      Detail.inferStatementsFuel fuel context thenBody.value expectedReturn
        conditionState = .ok thenResult ∧
      Detail.inferStatementsFuel fuel context elseBody.value expectedReturn
        (thenResult.state.restoreLexicalScope conditionState.lexicalScope) =
          .ok elseResult ∧
      result = {
        id
        type := if thenResult.sawReturn && elseResult.sawReturn then
          elseResult.state.resolve expectedReturn
        else
          .unit
        hasValue := thenResult.sawReturn && elseResult.sawReturn
        sawReturn := thenResult.sawReturn && elseResult.sawReturn
        state :=
          (elseResult.state.restoreLexicalScope
            conditionState.lexicalScope).recordNode (.statement {
              id
              span := statement.span
              type := if thenResult.sawReturn && elseResult.sawReturn then
                elseResult.state.resolve expectedReturn
              else
                .unit
              form := .ifThen inferredCondition.id thenResult.statements
                (some elseResult.statements)
            })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .ifThen inferredCondition.id thenResult.statements
          (some elseResult.statements)
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases conditionSuccess : Detail.inferExprFuel fuel context condition
      (some .bool) allocated with
  | error error =>
      simp [conditionSuccess] at success
  | ok conditionPair =>
      rcases conditionPair with ⟨inferredCondition, conditionState⟩
      simp only [conditionSuccess] at success
      cases thenSuccess : Detail.inferStatementsFuel fuel context thenBody.value
          expectedReturn conditionState with
      | error error =>
          simp [thenSuccess] at success
      | ok thenResult =>
          simp only [thenSuccess] at success
          cases elseSuccess : Detail.inferStatementsFuel fuel context
              elseBody.value expectedReturn
              (thenResult.state.restoreLexicalScope
                conditionState.lexicalScope) with
          | error error =>
              simp [elseSuccess] at success
          | ok elseResult =>
              simp only [elseSuccess, pure, Pure.pure, Except.pure] at success
              injection success with resultEq
              rw [← resultEq]
              exact ⟨inferredCondition, conditionState, thenResult, elseResult,
                rfl, thenSuccess, elseSuccess, rfl,
                recordNode_containsStatement
                  (elseResult.state.restoreLexicalScope
                    conditionState.lexicalScope) _ roots⟩

/-- A successful bare-return branch exposes the exact unification which makes
the declared return type unit, together with the statement node recorded after
that unification. -/
theorem inferStatementFuel_success_returnUnit_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .returnStmt none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ unified,
      Detail.unify allocated .unit expectedReturn = .ok unified ∧
      unified.resolve expectedReturn = .unit ∧
      result = {
        id
        type := unified.resolve expectedReturn
        hasValue := true
        sawReturn := true
        state := unified.recordNode (.statement {
          id
          span := statement.span
          type := unified.resolve expectedReturn
          form := .returnStmt none
        })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .returnStmt none
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases unifySuccess : Detail.unify allocated .unit expectedReturn with
  | error error =>
      simp [unifySuccess] at success
  | ok unified =>
      simp only [unifySuccess, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      have resolvedEq : unified.resolve expectedReturn = .unit := by
        exact (Detail.unify_resolve_eq unifySuccess).symm.trans (by rfl)
      rw [← resultEq]
      exact ⟨unified, rfl, resolvedEq, rfl,
        recordNode_containsStatement unified _ roots⟩

/-- A successful value-return branch exposes the recursively inferred value
and the exact return node recorded by the frontend.  Expected-type coherence
of the child is intentionally kept separate because it is a property of the
whole expression traversal, not of statement recording. -/
theorem inferStatementFuel_success_returnValue_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {value : Syntax.Expr}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .returnStmt (some value))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ inferred valueState,
      Detail.inferExprFuel fuel context value (some expectedReturn) allocated =
        .ok (inferred, valueState) ∧
      result = {
        id
        type := valueState.resolve expectedReturn
        hasValue := true
        sawReturn := true
        state := valueState.recordNode (.statement {
          id
          span := statement.span
          type := valueState.resolve expectedReturn
          form := .returnStmt (some inferred.id)
        })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .returnStmt (some inferred.id)
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases valueSuccess :
      Detail.inferExprFuel fuel context value (some expectedReturn) allocated with
  | error error =>
      simp [valueSuccess] at success
  | ok valuePair =>
      rcases valuePair with ⟨inferred, valueState⟩
      simp only [valueSuccess, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      rw [← resultEq]
      exact ⟨inferred, valueState, rfl, rfl,
        recordNode_containsStatement valueState _ roots⟩

/-- Successful `break` inference records the canonical unit statement and
simultaneously exposes the nonzero loop depth which justifies it. -/
theorem inferStatementFuel_success_break_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .breakStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    context.loopDepth ≠ 0 ∧
      result = {
        id
        type := .unit
        hasValue := false
        sawReturn := false
        state := allocated.recordNode (.statement {
          id
          span := statement.span
          type := .unit
          form := .breakStmt
        })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .breakStmt
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq] at success
  split at success
  · simp_all
  · rename_i loopNonzero
    injection success with resultEq
    rw [← resultEq]
    exact ⟨loopNonzero, rfl,
      recordNode_containsStatement allocated _ roots⟩

/-- Successful `continue` inference has the same allocation shape as `break`
and exposes the same loop-availability fact. -/
theorem inferStatementFuel_success_continue_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .continueStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    context.loopDepth ≠ 0 ∧
      result = {
        id
        type := .unit
        hasValue := false
        sawReturn := false
        state := allocated.recordNode (.statement {
          id
          span := statement.span
          type := .unit
          form := .continueStmt
        })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .continueStmt
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq] at success
  split at success
  · simp_all
  · rename_i loopNonzero
    injection success with resultEq
    rw [← resultEq]
    exact ⟨loopNonzero, rfl,
      recordNode_containsStatement allocated _ roots⟩

/-- A successful block branch exposes the recursively inferred statement
sequence, the restoration of the enclosing lexical scope, and the exact block
node recorded after that restoration. -/
theorem inferStatementFuel_success_block_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {body : List Syntax.Statement}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .block body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ bodyResult,
      Detail.inferStatementsFuel fuel context body expectedReturn allocated =
        .ok bodyResult ∧
      result = {
        id
        type := bodyResult.type
        hasValue := bodyResult.sawReturn
        sawReturn := bodyResult.sawReturn
        state :=
          (bodyResult.state.restoreLexicalScope allocated.lexicalScope
            ).recordNode (.statement {
              id
              span := statement.span
              type := bodyResult.type
              form := .block bodyResult.statements
            })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .block bodyResult.statements
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases bodySuccess :
      Detail.inferStatementsFuel fuel context body expectedReturn allocated with
  | error error =>
      simp [bodySuccess] at success
  | ok bodyResult =>
      simp only [bodySuccess, pure, Pure.pure, Except.pure] at success
      injection success with resultEq
      rw [← resultEq]
      exact ⟨bodyResult, rfl, rfl,
        recordNode_containsStatement
          (bodyResult.state.restoreLexicalScope allocated.lexicalScope)
          _ roots⟩

/-- Execute the common scrutinee step used by source `match` statements.
A singleton is inferred directly; every other source list is inferred in order
and retained through one synthetic tuple occurrence. -/
def inferMatchScrutineesFuel
    (fuel : Nat) (context : Frontend.SourceInference.Context)
    (span : Syntax.SourceSpan) (sources : List Syntax.Expr)
    (state : Frontend.SourceInference.State) :
    Except Frontend.SourceInference.Error
      (InferredExpression × Frontend.SourceInference.State) :=
  match sources with
  | [source] => Detail.inferExprFuel fuel context source none state
  | sources => do
      let (elements, state) ← Detail.inferExprsFuel fuel context sources state
      let (tupleId, state) := state.allocateExpressionId
      let type := TypeSystem.Ty.productMany (elements.map (·.type))
      let state := state.recordNode (.expression {
        id := tupleId
        span
        type
        form := .tuple (elements.map (·.id))
      })
      pure ({ id := tupleId, type }, state)

/-- Pointwise deep soundness for expression inference lifts through the
source-ordered expression-list traversal.  The semantic source is fixed by
the caller, so it may be the enclosing expression or statement's final common
source rather than the intermediate state returned by the list traversal. -/
theorem inferExprsFuel_success_expressionsHaveTypes
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {expressions : List Syntax.Expr}
    {state final : Frontend.SourceInference.State}
    {inferred : List InferredExpression}
    (expressionSound :
      ∀ {childFuel : Nat} {expression : Syntax.Expr}
        {childInitial childFinal : Frontend.SourceInference.State}
        {child : InferredExpression},
        Detail.inferExprFuel childFuel inferenceContext expression none
            childInitial = .ok (child, childFinal) →
          ExpressionHasType source target child.id
            (outer.apply child.type))
    (success : Detail.inferExprsFuel fuel inferenceContext expressions state =
      .ok (inferred, final)) :
    ExpressionsHaveTypes source target (inferred.map (·.id))
      (inferred.map fun expression => outer.apply expression.type) := by
  induction fuel generalizing expressions state inferred final with
  | zero =>
      simp [Detail.inferExprsFuel] at success
  | succ fuel induction =>
      cases expressions with
      | nil =>
          simp only [Detail.inferExprsFuel, Except.ok.injEq,
            Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil target
      | cons expression rest =>
          unfold Detail.inferExprsFuel at success
          cases headSuccess : Detail.inferExprFuel fuel inferenceContext
              expression none state with
          | error error =>
              simp [headSuccess, bind, Except.bind] at success
          | ok headPair =>
              rcases headPair with ⟨head, headState⟩
              simp only [headSuccess, bind, Except.bind] at success
              cases tailSuccess : Detail.inferExprsFuel fuel inferenceContext
                  rest headState with
              | error error =>
                  simp [tailSuccess] at success
              | ok tailPair =>
                  rcases tailPair with ⟨tail, tailState⟩
                  simp only [tailSuccess, pure, Pure.pure, Except.pure]
                    at success
                  injection success with resultEq
                  cases resultEq
                  exact .cons (expressionSound headSuccess)
                    (induction tailSuccess)

/-- A retained synthetic tuple is typed by the pointwise typings of its
children.  The tuple owns no requirements or output coercions. -/
private theorem syntheticTupleExpressionHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    {span : Syntax.SourceSpan} {tupleId : ExpressionId}
    {elements : List InferredExpression}
    (contains : ContainsExpression source tupleId {
      id := tupleId
      span
      type := TypeSystem.Ty.productMany (elements.map (·.type))
      form := .tuple (elements.map (·.id))
    })
    (binders : TypeParameterBindersWellFormed target)
    (elementsType : ExpressionsHaveTypes
      (source.applySubstitution outer) target (elements.map (·.id))
      (elements.map fun expression => outer.apply expression.type)) :
    ExpressionHasType (source.applySubstitution outer) target tupleId
      (outer.apply (TypeSystem.Ty.productMany
        (elements.map (·.type)))) := by
  rw [FlexibleSubstitution.apply_productMany]
  simp only [List.map_map, Function.comp_def]
  have appliedContains : ContainsExpression
      (source.applySubstitution outer) tupleId {
        id := tupleId
        span
        type := TypeSystem.Ty.productMany
          (elements.map fun expression => outer.apply expression.type)
        form := .tuple (elements.map (·.id))
      } := by
    simpa [ExpressionNode.applySubstitution,
      ExpressionForm.applySubstitution,
      FlexibleSubstitution.apply_productMany, List.map_map,
      Function.comp_def] using
        (FlexibleSubstitution.ContainsExpression.applySubstitution outer
          contains)
  apply ExpressionHasType.ofOrdinary
    (rawType := TypeSystem.Ty.productMany
      (elements.map fun expression => outer.apply expression.type))
    (owned := []) appliedContains
  · exact .tuple elementsType
  · exact elementsType.product_type_admissible binders
  · exact elementsType.product_type_admissible binders
  · intro requirement member
    simp at member
  · exact .nil _
  · simp [coercionRequirementIds]

/-- Deep soundness of the common match-scrutinee traversal in an eventual
common typed source.  Singleton matches delegate directly to expression
soundness.  Every other list is represented by an uncoerced synthetic tuple;
the explicit node-prefix premise retains that tuple through the later match
case and fallback traversals. -/
theorem inferMatchScrutineesFuel_success_expressionHasType_in
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {state final : Frontend.SourceInference.State}
    {inferred : InferredExpression}
    {source : TypedSource}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (success : inferMatchScrutineesFuel fuel inferenceContext span sources
      state = .ok (inferred, final))
    (nodesPrefix : final.nodes <+: source.nodes)
    (binders : TypeParameterBindersWellFormed target)
    (expressionSound :
      ∀ {childFuel : Nat} {expression : Syntax.Expr}
        {childInitial childFinal : Frontend.SourceInference.State}
        {child : InferredExpression},
        Detail.inferExprFuel childFuel inferenceContext expression none
            childInitial = .ok (child, childFinal) →
          ExpressionHasType (source.applySubstitution outer)
            target child.id (outer.apply child.type)) :
    ExpressionHasType (source.applySubstitution outer)
      target inferred.id (outer.apply inferred.type) := by
  cases sources with
  | nil =>
      unfold inferMatchScrutineesFuel at success
      cases elementsSuccess : Detail.inferExprsFuel fuel inferenceContext []
          state with
      | error error =>
          simp [elementsSuccess, bind, Except.bind] at success
      | ok elementsPair =>
          rcases elementsPair with ⟨elements, elementsState⟩
          simp only [elementsSuccess, bind, Except.bind] at success
          rcases allocation : elementsState.allocateExpressionId with
            ⟨tupleId, allocated⟩
          simp only [allocation, pure, Pure.pure, Except.pure] at success
          injection success with resultEq
          cases resultEq
          have elementsType :=
            inferExprsFuel_success_expressionsHaveTypes expressionSound
              elementsSuccess
          have containsHere := recordNode_containsExpression allocated ({
            id := tupleId
            span
            type := TypeSystem.Ty.productMany (elements.map (·.type))
            form := .tuple (elements.map (·.id))
          } : ExpressionNode)
          have contains : ContainsExpression source tupleId {
              id := tupleId
              span
              type := TypeSystem.Ty.productMany (elements.map (·.type))
              form := .tuple (elements.map (·.id))
            } := by
            apply ContainsExpression.of_nodes_prefix
              (contains := containsHere)
            simpa [Frontend.SourceInference.State.toTypedSource] using
              nodesPrefix
          exact syntheticTupleExpressionHasType_afterSubstitution contains
            binders elementsType
  | cons first rest =>
      cases rest with
      | nil =>
          apply expressionSound
          simpa [inferMatchScrutineesFuel] using success
      | cons second tail =>
          unfold inferMatchScrutineesFuel at success
          cases elementsSuccess : Detail.inferExprsFuel fuel inferenceContext
              (first :: second :: tail) state with
          | error error =>
              simp [elementsSuccess, bind, Except.bind] at success
          | ok elementsPair =>
              rcases elementsPair with ⟨elements, elementsState⟩
              simp only [elementsSuccess, bind, Except.bind] at success
              rcases allocation : elementsState.allocateExpressionId with
                ⟨tupleId, allocated⟩
              simp only [allocation, pure, Pure.pure, Except.pure] at success
              injection success with resultEq
              cases resultEq
              have elementsType :=
                inferExprsFuel_success_expressionsHaveTypes expressionSound
                  elementsSuccess
              have containsHere := recordNode_containsExpression allocated ({
                id := tupleId
                span
                type := TypeSystem.Ty.productMany (elements.map (·.type))
                form := .tuple (elements.map (·.id))
              } : ExpressionNode)
              have contains : ContainsExpression source tupleId {
                  id := tupleId
                  span
                  type := TypeSystem.Ty.productMany (elements.map (·.type))
                  form := .tuple (elements.map (·.id))
                } := by
                apply ContainsExpression.of_nodes_prefix
                  (contains := containsHere)
                simpa [Frontend.SourceInference.State.toTypedSource] using
                  nodesPrefix
              exact syntheticTupleExpressionHasType_afterSubstitution contains
                binders elementsType

/-- The common match-scrutinee step makes monotone inference progress,
preserves readiness, and returns a type bounded by the final allocator.  The
synthetic-tuple branch composes list inference with occurrence allocation and
node recording. -/
theorem inferMatchScrutineesFuel_inferenceProperties
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {state final : Frontend.SourceInference.State}
    {inferred : InferredExpression}
    (ready : state.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (success : inferMatchScrutineesFuel fuel inferenceContext span sources
      state = .ok (inferred, final)) :
    state.InferenceProgress final ∧ final.InferenceReady ∧
      inferred.type.VariablesBelow final.inference.next := by
  have finishTuple
      (elements : List InferredExpression)
      (elementsState : Frontend.SourceInference.State)
      (elementsProgress : state.InferenceProgress elementsState)
      (elementsReady : elementsState.InferenceReady)
      (elementsBelow : ∀ element ∈ elements,
        element.type.VariablesBelow elementsState.inference.next)
      (residualSuccess : (pure ({
          id := elementsState.allocateExpressionId.fst
          type := TypeSystem.Ty.productMany (elements.map (·.type))
        }, elementsState.allocateExpressionId.snd.recordNode (.expression {
          id := elementsState.allocateExpressionId.fst
          span
          type := TypeSystem.Ty.productMany (elements.map (·.type))
          form := .tuple (elements.map (·.id))
        })) : Except Frontend.SourceInference.Error
          (InferredExpression × Frontend.SourceInference.State)) =
            .ok (inferred, final)) :
      state.InferenceProgress final ∧ final.InferenceReady ∧
        inferred.type.VariablesBelow final.inference.next := by
    have resultEq : ({
        id := elementsState.allocateExpressionId.fst
        type := TypeSystem.Ty.productMany (elements.map (·.type))
      }, elementsState.allocateExpressionId.snd.recordNode (.expression {
        id := elementsState.allocateExpressionId.fst
        span
        type := TypeSystem.Ty.productMany (elements.map (·.type))
        form := .tuple (elements.map (·.id))
      })) = (inferred, final) := by
      simpa only [pure, Pure.pure, Except.pure, Except.ok.injEq] using
        residualSuccess
    have inferredEq := congrArg Prod.fst resultEq
    have finalEq := congrArg Prod.snd resultEq
    simp only at inferredEq finalEq
    subst inferred
    subst final
    have tupleTypeBelow :
        (TypeSystem.Ty.productMany
          (elements.map (·.type))).VariablesBelow
            elementsState.inference.next :=
      TypeSystem.Ty.variablesBelow_productMany (by
        intro type member
        rcases List.mem_map.mp member with ⟨element, elementMember, rfl⟩
        exact elementsBelow element elementMember)
    have allocationProgress :=
      Frontend.SourceInference.State.InferenceProgress.allocateExpressionId
        elementsState elementsReady.solved
    have allocationReady :=
      Frontend.SourceInference.State.InferenceReady.allocateExpressionId
        elementsReady
    have recordProgress :=
      Frontend.SourceInference.State.InferenceProgress.recordNode
        elementsState.allocateExpressionId.snd (.expression {
          id := elementsState.allocateExpressionId.fst
          span
          type := TypeSystem.Ty.productMany (elements.map (·.type))
          form := .tuple (elements.map (·.id))
        }) allocationReady.solved
    have recordReady :=
      Frontend.SourceInference.State.InferenceReady.recordNode
        (.expression {
          id := elementsState.allocateExpressionId.fst
          span
          type := TypeSystem.Ty.productMany (elements.map (·.type))
          form := .tuple (elements.map (·.id))
        }) allocationReady
    have suffixProgress := allocationProgress.trans recordProgress
    exact ⟨elementsProgress.trans suffixProgress, recordReady,
      tupleTypeBelow.weaken suffixProgress.next_le⟩
  cases sources with
  | nil =>
      unfold inferMatchScrutineesFuel at success
      cases elementsSuccess : Detail.inferExprsFuel fuel inferenceContext []
          state with
      | error error =>
          simp [elementsSuccess, bind, Except.bind] at success
      | ok elementsPair =>
          rcases elementsPair with ⟨elements, elementsState⟩
          simp only [elementsSuccess, bind, Except.bind] at success
          have elementsProperties :=
            Detail.inferExprsFuel_inferenceProperties ready
              signatureFormation functionsCanonical elementsSuccess
          exact finishTuple elements elementsState elementsProperties.1
            elementsProperties.2.1 elementsProperties.2.2 success
  | cons first rest =>
      cases rest with
      | nil =>
          exact Detail.inferExprFuel_inferenceProperties (expected := none)
            ready signatureFormation functionsCanonical (by simp)
            (by simpa [inferMatchScrutineesFuel] using success)
      | cons second tail =>
          unfold inferMatchScrutineesFuel at success
          cases elementsSuccess : Detail.inferExprsFuel fuel inferenceContext
              (first :: second :: tail) state with
          | error error =>
              simp [elementsSuccess, bind, Except.bind] at success
          | ok elementsPair =>
              rcases elementsPair with ⟨elements, elementsState⟩
              simp only [elementsSuccess, bind, Except.bind] at success
              have elementsProperties :=
                Detail.inferExprsFuel_inferenceProperties ready
                  signatureFormation functionsCanonical elementsSuccess
              exact finishTuple elements elementsState elementsProperties.1
                elementsProperties.2.1 elementsProperties.2.2 success

namespace ActiveLocalContextInvariant

/-- The common match-scrutinee step preserves the caller's active lexical
context in both the singleton path and the synthetic-tuple path. -/
theorem inferMatchScrutineesFuel
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr}
    {state final : Frontend.SourceInference.State}
    {inferred : InferredExpression}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (success : SourceInferenceSoundness.inferMatchScrutineesFuel fuel
      inferenceContext span sources state = .ok (inferred, final)) :
    ActiveLocalContextInvariant final substitution context := by
  cases sources with
  | nil =>
      unfold SourceInferenceSoundness.inferMatchScrutineesFuel at success
      cases elementsSuccess :
          Detail.inferExprsFuel fuel inferenceContext [] state with
      | error error =>
          simp [elementsSuccess, bind, Except.bind] at success
      | ok elementsPair =>
          rcases elementsPair with ⟨elements, elementsState⟩
          simp only [elementsSuccess, bind, Except.bind, pure, Pure.pure,
            Except.pure] at success
          injection success with resultEq
          cases resultEq
          exact (invariant.inferExprsFuel elementsSuccess).congr_localBinders
            rfl
  | cons first rest =>
      cases rest with
      | nil =>
          apply invariant.inferExprFuel
          simpa [SourceInferenceSoundness.inferMatchScrutineesFuel] using
            success
      | cons second tail =>
          unfold SourceInferenceSoundness.inferMatchScrutineesFuel at success
          cases elementsSuccess : Detail.inferExprsFuel fuel inferenceContext
              (first :: second :: tail) state with
          | error error =>
              simp [elementsSuccess, bind, Except.bind] at success
          | ok elementsPair =>
              rcases elementsPair with ⟨elements, elementsState⟩
              simp only [elementsSuccess, bind, Except.bind, pure, Pure.pure,
                Except.pure] at success
              injection success with resultEq
              cases resultEq
              exact
                (invariant.inferExprsFuel elementsSuccess).congr_localBinders
                  rfl

/-- Explicit match-case traversal restores the lexical scope supplied at its
entry, so pattern-local binders and arm-local declarations do not escape. -/
theorem inferMatchCasesFuel
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {scrutineeType expectedReturn : TypeSystem.Ty}
    {cases : List Syntax.MatchCase}
    {state : Frontend.SourceInference.State}
    {result : Detail.MatchCasesResult}
    {substitution : TypeSystem.Substitution}
    {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant state substitution context)
    (success : Detail.inferMatchCasesFuel fuel inferenceContext scrutineeType
      expectedReturn state.lexicalScope cases state = .ok result) :
    ActiveLocalContextInvariant result.state substitution context := by
  apply invariant.congr_localBinders
  have scopeEq := Detail.inferMatchCasesFuel_success_lexicalScope_eq rfl success
  simpa [Frontend.SourceInference.State.lexicalScope] using
    congrArg (fun scope : LexicalScope => scope.binders) scopeEq

end ActiveLocalContextInvariant

/-- A successful `match` without a default arm exposes the common executable
scrutinee step, hidden-local allocation, explicit-case traversal, the passed
exhaustiveness guard, and the exact retained statement.  The existential
Boolean is the result of the implementation's private nominal-coverage test. -/
theorem inferStatementFuel_success_matchWithoutDefault_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ scrutinee scrutineeState hiddenScrutinee hiddenState checked
        nominallyExhaustive,
      inferMatchScrutineesFuel fuel context statement.span
        scrutinees.elements.toList allocated =
          .ok (scrutinee, scrutineeState) ∧
      scrutineeState.allocateHiddenLocal =
        (hiddenScrutinee, hiddenState) ∧
      Detail.inferMatchCasesFuel fuel context scrutinee.type expectedReturn
        hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked ∧
      (checked.hasWildcard || false || nominallyExhaustive) = true ∧
      result = {
        id
        type := if checked.allReturn then
          checked.state.resolve expectedReturn
        else
          .unit
        hasValue := checked.allReturn
        sawReturn := checked.allReturn
        state := checked.state.recordNode (.statement {
          id
          span := statement.span
          type := if checked.allReturn then
            checked.state.resolve expectedReturn
          else
            .unit
          form := .matchWith {
            scrutinee := scrutinee.id
            hiddenScrutinee
            cases := checked.cases
            defaultBody := none
            requirements := checked.cases.flatMap fun arm =>
              arm.pattern.requirements
          }
        })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .matchWith {
          scrutinee := scrutinee.id
          hiddenScrutinee
          cases := checked.cases
          defaultBody := none
          requirements := checked.cases.flatMap fun arm =>
            arm.pattern.requirements
        }
      } := by
  have finish
      (scrutinee : InferredExpression)
      (scrutineeState : Frontend.SourceInference.State)
      (nominalCoverage : Detail.MatchCasesResult → Bool)
      (residualSuccess : (do
    let (hiddenScrutinee, state) := scrutineeState.allocateHiddenLocal
    let outerScope := state.lexicalScope
    let checked ← Detail.inferMatchCasesFuel fuel context scrutinee.type
      expectedReturn outerScope arms.value.cases state
    if checked.hasWildcard = false ∧ nominalCoverage checked = false then
      throw (Frontend.SourceInference.Error.nonExhaustiveMatch statement.span)
    else
      let requirements := checked.cases.flatMap fun arm : TypedMatchCase =>
        arm.pattern.requirements
      let type := if checked.allReturn then
        checked.state.resolve expectedReturn
      else
        .unit
      let finalState := checked.state.recordNode (.statement {
        id
        span := statement.span
        type
        form := .matchWith {
          scrutinee := scrutinee.id
          hiddenScrutinee
          cases := checked.cases
          defaultBody := none
          requirements
        }
      })
      pure ({
        id := id
        type := type
        hasValue := checked.allReturn
        sawReturn := checked.allReturn
        state := finalState
      } : Detail.StatementResult)) = .ok result) :
      ∃ hiddenScrutinee hiddenState checked,
        scrutineeState.allocateHiddenLocal =
          (hiddenScrutinee, hiddenState) ∧
        Detail.inferMatchCasesFuel fuel context scrutinee.type expectedReturn
          hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked ∧
        (checked.hasWildcard || false || nominalCoverage checked) = true ∧
        result = {
          id
          type := if checked.allReturn then
            checked.state.resolve expectedReturn
          else
            .unit
          hasValue := checked.allReturn
          sawReturn := checked.allReturn
          state := checked.state.recordNode (.statement {
            id
            span := statement.span
            type := if checked.allReturn then
              checked.state.resolve expectedReturn
            else
              .unit
            form := .matchWith {
              scrutinee := scrutinee.id
              hiddenScrutinee
              cases := checked.cases
              defaultBody := none
              requirements := checked.cases.flatMap fun arm =>
                arm.pattern.requirements
            }
          })
        } ∧
        ContainsStatement (result.state.toTypedSource roots) result.id {
          id := result.id
          span := statement.span
          type := result.type
          form := .matchWith {
            scrutinee := scrutinee.id
            hiddenScrutinee
            cases := checked.cases
            defaultBody := none
            requirements := checked.cases.flatMap fun arm =>
              arm.pattern.requirements
          }
        } := by
    rcases hiddenAllocation : scrutineeState.allocateHiddenLocal with
      ⟨hiddenScrutinee, hiddenState⟩
    simp only [hiddenAllocation] at residualSuccess
    cases checkedSuccess : Detail.inferMatchCasesFuel fuel context
        scrutinee.type expectedReturn hiddenState.lexicalScope
        arms.value.cases hiddenState with
    | error error =>
        simp [checkedSuccess, bind, Except.bind] at residualSuccess
    | ok checked =>
        simp only [checkedSuccess, bind, Except.bind, pure, Pure.pure,
          Except.pure]
          at residualSuccess
        split at residualSuccess
        · simp_all
        · rename_i guardPassed
          injection residualSuccess with resultEq
          rw [← resultEq]
          refine ⟨hiddenScrutinee, hiddenState, checked, rfl,
            checkedSuccess, ?_, ?_, ?_⟩
          · cases wildcardEq : checked.hasWildcard <;> simp_all
          · simp
          · simpa using
              (recordNode_containsStatement checked.state _ roots)
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases sourcesEq : scrutinees.elements.toList with
  | nil =>
      simp only [sourcesEq] at success
      cases elementsSuccess : Detail.inferExprsFuel fuel context [] allocated with
      | error error =>
          simp [elementsSuccess] at success
      | ok elementsPair =>
          rcases elementsPair with ⟨elements, elementsState⟩
          simp only [elementsSuccess, defaultEq, pure, Pure.pure, Except.pure]
            at success
          let scrutinee : InferredExpression := {
            id := elementsState.allocateExpressionId.1
            type := TypeSystem.Ty.productMany (elements.map (·.type))
          }
          let scrutineeState :=
            elementsState.allocateExpressionId.2.recordNode (.expression {
              id := elementsState.allocateExpressionId.1
              span := statement.span
              type := TypeSystem.Ty.productMany (elements.map (·.type))
              form := .tuple (elements.map (·.id))
            })
          have scrutineeSuccess :
              inferMatchScrutineesFuel fuel context statement.span
                scrutinees.elements.toList allocated =
                  .ok (scrutinee, scrutineeState) := by
            simp only [inferMatchScrutineesFuel, sourcesEq, elementsSuccess]
            rfl
          rcases finish scrutinee scrutineeState _
              (by simpa [scrutinee, scrutineeState, bind, Except.bind,
                pure, Pure.pure, Except.pure] using success) with
            ⟨hiddenScrutinee, hiddenState, checked, hiddenAllocation,
              checkedSuccess, guardPassed, resultEq, contains⟩
          exact ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState,
            checked, _, (by simpa [sourcesEq] using scrutineeSuccess),
            hiddenAllocation, checkedSuccess,
            guardPassed, resultEq, contains⟩
  | cons first rest =>
      cases rest with
      | nil =>
          simp only [sourcesEq] at success
          cases sourceSuccess :
              Detail.inferExprFuel fuel context first none allocated with
          | error error =>
              simp [sourceSuccess] at success
          | ok scrutineePair =>
              rcases scrutineePair with ⟨scrutinee, scrutineeState⟩
              simp only [sourceSuccess, defaultEq, pure, Pure.pure, Except.pure]
                at success
              have scrutineeSuccess :
                  inferMatchScrutineesFuel fuel context statement.span
                    scrutinees.elements.toList allocated =
                      .ok (scrutinee, scrutineeState) := by
                simpa [inferMatchScrutineesFuel, sourcesEq] using sourceSuccess
              rcases finish scrutinee scrutineeState _
                  (by simpa [bind, Except.bind, pure, Pure.pure, Except.pure]
                    using success) with
                ⟨hiddenScrutinee, hiddenState, checked, hiddenAllocation,
                  checkedSuccess, guardPassed, resultEq, contains⟩
              exact ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState,
                checked, _, (by simpa [sourcesEq] using scrutineeSuccess),
                hiddenAllocation, checkedSuccess,
                guardPassed, resultEq, contains⟩
      | cons second tail =>
          simp only [sourcesEq] at success
          cases elementsSuccess : Detail.inferExprsFuel fuel context
              (first :: second :: tail) allocated with
          | error error =>
              simp [elementsSuccess] at success
          | ok elementsPair =>
              rcases elementsPair with ⟨elements, elementsState⟩
              simp only [elementsSuccess, defaultEq, pure, Pure.pure,
                Except.pure] at success
              let scrutinee : InferredExpression := {
                id := elementsState.allocateExpressionId.1
                type := TypeSystem.Ty.productMany (elements.map (·.type))
              }
              let scrutineeState :=
                elementsState.allocateExpressionId.2.recordNode (.expression {
                  id := elementsState.allocateExpressionId.1
                  span := statement.span
                  type := TypeSystem.Ty.productMany (elements.map (·.type))
                  form := .tuple (elements.map (·.id))
                })
              have scrutineeSuccess :
                  inferMatchScrutineesFuel fuel context statement.span
                    scrutinees.elements.toList allocated =
                      .ok (scrutinee, scrutineeState) := by
                simp only [inferMatchScrutineesFuel, sourcesEq, elementsSuccess]
                rfl
              rcases finish scrutinee scrutineeState _
                  (by simpa [scrutinee, scrutineeState, bind, Except.bind,
                    pure, Pure.pure, Except.pure] using success) with
                ⟨hiddenScrutinee, hiddenState, checked, hiddenAllocation,
                  checkedSuccess, guardPassed, resultEq, contains⟩
              exact ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState,
                checked, _, (by simpa [sourcesEq] using scrutineeSuccess),
                hiddenAllocation, checkedSuccess,
                guardPassed, resultEq, contains⟩

/-- A successful `match` with a default arm exposes the same common
scrutinee and explicit-case steps, followed by default-body inference from the
case state and restoration of the hidden-local state's lexical scope.  The
presence of the default arm makes the executable exhaustiveness guard true. -/
theorem inferStatementFuel_success_matchWithDefault_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {defaultBody : Syntax.Block}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ scrutinee scrutineeState hiddenScrutinee hiddenState checked
        defaultResult,
      inferMatchScrutineesFuel fuel context statement.span
        scrutinees.elements.toList allocated =
          .ok (scrutinee, scrutineeState) ∧
      scrutineeState.allocateHiddenLocal =
        (hiddenScrutinee, hiddenState) ∧
      Detail.inferMatchCasesFuel fuel context scrutinee.type expectedReturn
        hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked ∧
      Detail.inferStatementsFuel fuel context defaultBody.value expectedReturn
        checked.state = .ok defaultResult ∧
      (checked.hasWildcard || true) = true ∧
      result = {
        id
        type := if checked.allReturn && defaultResult.sawReturn then
          (defaultResult.state.restoreLexicalScope
            hiddenState.lexicalScope).resolve expectedReturn
        else
          .unit
        hasValue := checked.allReturn && defaultResult.sawReturn
        sawReturn := checked.allReturn && defaultResult.sawReturn
        state :=
          (defaultResult.state.restoreLexicalScope
            hiddenState.lexicalScope).recordNode (.statement {
              id
              span := statement.span
              type := if checked.allReturn && defaultResult.sawReturn then
                (defaultResult.state.restoreLexicalScope
                  hiddenState.lexicalScope).resolve expectedReturn
              else
                .unit
              form := .matchWith {
                scrutinee := scrutinee.id
                hiddenScrutinee
                cases := checked.cases
                defaultBody := some defaultResult.statements
                requirements := checked.cases.flatMap fun arm =>
                  arm.pattern.requirements
              }
            })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .matchWith {
          scrutinee := scrutinee.id
          hiddenScrutinee
          cases := checked.cases
          defaultBody := some defaultResult.statements
          requirements := checked.cases.flatMap fun arm =>
            arm.pattern.requirements
        }
      } := by
  have finish
      (scrutinee : InferredExpression)
      (scrutineeState : Frontend.SourceInference.State)
      (residualSuccess : (do
    let (hiddenScrutinee, state) := scrutineeState.allocateHiddenLocal
    let outerScope := state.lexicalScope
    let checked ← Detail.inferMatchCasesFuel fuel context scrutinee.type
      expectedReturn outerScope arms.value.cases state
    let defaultResult ← Detail.inferStatementsFuel fuel context
      defaultBody.value expectedReturn checked.state
    let defaultState := defaultResult.state.restoreLexicalScope outerScope
    let requirements := checked.cases.flatMap fun arm : TypedMatchCase =>
      arm.pattern.requirements
    let sawReturn := checked.allReturn && defaultResult.sawReturn
    let type := if sawReturn then defaultState.resolve expectedReturn else .unit
    let finalState := defaultState.recordNode (.statement {
      id
      span := statement.span
      type
      form := .matchWith {
        scrutinee := scrutinee.id
        hiddenScrutinee
        cases := checked.cases
        defaultBody := some defaultResult.statements
        requirements
      }
    })
    pure ({
      id := id
      type := type
      hasValue := sawReturn
      sawReturn := sawReturn
      state := finalState
    } : Detail.StatementResult)) = .ok result) :
      ∃ hiddenScrutinee hiddenState checked defaultResult,
        scrutineeState.allocateHiddenLocal =
          (hiddenScrutinee, hiddenState) ∧
        Detail.inferMatchCasesFuel fuel context scrutinee.type expectedReturn
          hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked ∧
        Detail.inferStatementsFuel fuel context defaultBody.value
          expectedReturn checked.state = .ok defaultResult ∧
        result = {
          id
          type := if checked.allReturn && defaultResult.sawReturn then
            (defaultResult.state.restoreLexicalScope
              hiddenState.lexicalScope).resolve expectedReturn
          else
            .unit
          hasValue := checked.allReturn && defaultResult.sawReturn
          sawReturn := checked.allReturn && defaultResult.sawReturn
          state :=
            (defaultResult.state.restoreLexicalScope
              hiddenState.lexicalScope).recordNode (.statement {
                id
                span := statement.span
                type := if checked.allReturn && defaultResult.sawReturn then
                  (defaultResult.state.restoreLexicalScope
                    hiddenState.lexicalScope).resolve expectedReturn
                else
                  .unit
                form := .matchWith {
                  scrutinee := scrutinee.id
                  hiddenScrutinee
                  cases := checked.cases
                  defaultBody := some defaultResult.statements
                  requirements := checked.cases.flatMap fun arm =>
                    arm.pattern.requirements
                }
              })
        } ∧
        ContainsStatement (result.state.toTypedSource roots) result.id {
          id := result.id
          span := statement.span
          type := result.type
          form := .matchWith {
            scrutinee := scrutinee.id
            hiddenScrutinee
            cases := checked.cases
            defaultBody := some defaultResult.statements
            requirements := checked.cases.flatMap fun arm =>
              arm.pattern.requirements
          }
        } := by
    rcases hiddenAllocation : scrutineeState.allocateHiddenLocal with
      ⟨hiddenScrutinee, hiddenState⟩
    simp only [hiddenAllocation] at residualSuccess
    cases checkedSuccess : Detail.inferMatchCasesFuel fuel context
        scrutinee.type expectedReturn hiddenState.lexicalScope
        arms.value.cases hiddenState with
    | error error =>
        simp [checkedSuccess, bind, Except.bind] at residualSuccess
    | ok checked =>
        simp only [checkedSuccess, bind, Except.bind] at residualSuccess
        cases defaultSuccess : Detail.inferStatementsFuel fuel context
            defaultBody.value expectedReturn checked.state with
        | error error =>
            simp [defaultSuccess] at residualSuccess
        | ok defaultResult =>
            simp only [defaultSuccess, pure, Pure.pure, Except.pure]
              at residualSuccess
            injection residualSuccess with resultEq
            rw [← resultEq]
            exact ⟨hiddenScrutinee, hiddenState, checked, defaultResult, rfl,
              checkedSuccess, defaultSuccess, rfl,
              recordNode_containsStatement
                (defaultResult.state.restoreLexicalScope
                  hiddenState.lexicalScope) _ roots⟩
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases sourcesEq : scrutinees.elements.toList with
  | nil =>
      simp only [sourcesEq] at success
      cases elementsSuccess : Detail.inferExprsFuel fuel context [] allocated with
      | error error =>
          simp [elementsSuccess] at success
      | ok elementsPair =>
          rcases elementsPair with ⟨elements, elementsState⟩
          simp only [elementsSuccess, defaultEq] at success
          let scrutinee : InferredExpression := {
            id := elementsState.allocateExpressionId.1
            type := TypeSystem.Ty.productMany (elements.map (·.type))
          }
          let scrutineeState :=
            elementsState.allocateExpressionId.2.recordNode (.expression {
              id := elementsState.allocateExpressionId.1
              span := statement.span
              type := TypeSystem.Ty.productMany (elements.map (·.type))
              form := .tuple (elements.map (·.id))
            })
          have scrutineeSuccess :
              inferMatchScrutineesFuel fuel context statement.span
                scrutinees.elements.toList allocated =
                  .ok (scrutinee, scrutineeState) := by
            simp only [inferMatchScrutineesFuel, sourcesEq, elementsSuccess]
            rfl
          rcases finish scrutinee scrutineeState
              (by simpa [scrutinee, scrutineeState, bind, Except.bind,
                pure, Pure.pure, Except.pure] using success) with
            ⟨hiddenScrutinee, hiddenState, checked, defaultResult,
              hiddenAllocation, checkedSuccess, defaultSuccess, resultEq,
              contains⟩
          exact ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState,
            checked, defaultResult,
            (by simpa [sourcesEq] using scrutineeSuccess), hiddenAllocation,
            checkedSuccess, defaultSuccess, (by simp), resultEq, contains⟩
  | cons first rest =>
      cases rest with
      | nil =>
          simp only [sourcesEq] at success
          cases sourceSuccess :
              Detail.inferExprFuel fuel context first none allocated with
          | error error =>
              simp [sourceSuccess] at success
          | ok scrutineePair =>
              rcases scrutineePair with ⟨scrutinee, scrutineeState⟩
              simp only [sourceSuccess, defaultEq] at success
              have scrutineeSuccess :
                  inferMatchScrutineesFuel fuel context statement.span
                    scrutinees.elements.toList allocated =
                      .ok (scrutinee, scrutineeState) := by
                simpa [inferMatchScrutineesFuel, sourcesEq] using sourceSuccess
              rcases finish scrutinee scrutineeState
                  (by simpa [bind, Except.bind, pure, Pure.pure, Except.pure]
                    using success) with
                ⟨hiddenScrutinee, hiddenState, checked, defaultResult,
                  hiddenAllocation, checkedSuccess, defaultSuccess, resultEq,
                  contains⟩
              exact ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState,
                checked, defaultResult,
                (by simpa [sourcesEq] using scrutineeSuccess), hiddenAllocation,
                checkedSuccess, defaultSuccess, (by simp), resultEq, contains⟩
      | cons second tail =>
          simp only [sourcesEq] at success
          cases elementsSuccess : Detail.inferExprsFuel fuel context
              (first :: second :: tail) allocated with
          | error error =>
              simp [elementsSuccess] at success
          | ok elementsPair =>
              rcases elementsPair with ⟨elements, elementsState⟩
              simp only [elementsSuccess, defaultEq] at success
              let scrutinee : InferredExpression := {
                id := elementsState.allocateExpressionId.1
                type := TypeSystem.Ty.productMany (elements.map (·.type))
              }
              let scrutineeState :=
                elementsState.allocateExpressionId.2.recordNode (.expression {
                  id := elementsState.allocateExpressionId.1
                  span := statement.span
                  type := TypeSystem.Ty.productMany (elements.map (·.type))
                  form := .tuple (elements.map (·.id))
                })
              have scrutineeSuccess :
                  inferMatchScrutineesFuel fuel context statement.span
                    scrutinees.elements.toList allocated =
                      .ok (scrutinee, scrutineeState) := by
                simp only [inferMatchScrutineesFuel, sourcesEq, elementsSuccess]
                rfl
              rcases finish scrutinee scrutineeState
                  (by simpa [scrutinee, scrutineeState, bind, Except.bind,
                    pure, Pure.pure, Except.pure] using success) with
                ⟨hiddenScrutinee, hiddenState, checked, defaultResult,
                  hiddenAllocation, checkedSuccess, defaultSuccess, resultEq,
                  contains⟩
              exact ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState,
                checked, defaultResult,
                (by simpa [sourcesEq] using scrutineeSuccess), hiddenAllocation,
                checkedSuccess, defaultSuccess, (by simp), resultEq, contains⟩

/-- A successful `for` exposes initializer items, its Boolean condition, the
recursive loop body, restored post-item input scope, and the exact canonical
unit statement recorded after restoring the enclosing scope. -/
theorem inferStatementFuel_success_forLoop_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ initializerResult inferredCondition conditionState bodyResult
        postResult,
      Detail.inferForItemsFuel fuel context initializer allocated =
        .ok initializerResult ∧
      Detail.inferExprFuel fuel context condition (some .bool)
        initializerResult.state = .ok (inferredCondition, conditionState) ∧
      Detail.inferStatementsFuel fuel
        { context with loopDepth := context.loopDepth + 1 }
        body.value expectedReturn conditionState = .ok bodyResult ∧
      Detail.inferForItemsFuel fuel
        { context with loopDepth := context.loopDepth + 1 } post
        (bodyResult.state.restoreLexicalScope
          initializerResult.state.lexicalScope) = .ok postResult ∧
      result = {
        id
        type := .unit
        hasValue := false
        sawReturn := false
        state :=
          (postResult.state.restoreLexicalScope
            allocated.lexicalScope).recordNode (.statement {
              id
              span := statement.span
              type := .unit
              form := .forLoop initializerResult.items inferredCondition.id
                postResult.items bodyResult.statements
            })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .forLoop initializerResult.items inferredCondition.id
          postResult.items bodyResult.statements
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases initializerSuccess : Detail.inferForItemsFuel fuel context initializer
      allocated with
  | error error =>
      simp [initializerSuccess] at success
  | ok initializerResult =>
      simp only [initializerSuccess] at success
      cases conditionSuccess : Detail.inferExprFuel fuel context condition
          (some .bool) initializerResult.state with
      | error error =>
          simp [conditionSuccess] at success
      | ok conditionPair =>
          rcases conditionPair with ⟨inferredCondition, conditionState⟩
          simp only [conditionSuccess] at success
          cases bodySuccess : Detail.inferStatementsFuel fuel
              { context with loopDepth := context.loopDepth + 1 }
              body.value expectedReturn conditionState with
          | error error =>
              simp [bodySuccess] at success
          | ok bodyResult =>
              simp only [bodySuccess] at success
              cases postSuccess : Detail.inferForItemsFuel fuel
                  { context with loopDepth := context.loopDepth + 1 } post
                  (bodyResult.state.restoreLexicalScope
                    initializerResult.state.lexicalScope) with
              | error error =>
                  simp [postSuccess] at success
              | ok postResult =>
                  simp only [postSuccess, pure, Pure.pure, Except.pure]
                    at success
                  injection success with resultEq
                  rw [← resultEq]
                  exact ⟨initializerResult, inferredCondition, conditionState,
                    bodyResult, postResult, rfl, conditionSuccess, bodySuccess,
                    postSuccess, rfl,
                    recordNode_containsStatement
                      (postResult.state.restoreLexicalScope
                        allocated.lexicalScope) _ roots⟩

/-- A successful `while` branch exposes the expected-`Bool` condition, the
body checked at one greater loop depth, lexical-scope restoration, and the
canonical unit statement recorded afterwards. -/
theorem inferStatementFuel_success_whileLoop_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    (statementEq : statement.value = .whileLoop condition body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) context statement
      expectedReturn initial = .ok result)
    (roots : List NodeId := []) :
    ∃ inferredCondition conditionState bodyResult,
      Detail.inferExprFuel fuel context condition (some .bool) allocated =
        .ok (inferredCondition, conditionState) ∧
      Detail.inferStatementsFuel fuel
        { context with loopDepth := context.loopDepth + 1 }
        body.value expectedReturn conditionState = .ok bodyResult ∧
      result = {
        id
        type := .unit
        hasValue := false
        sawReturn := false
        state :=
          (bodyResult.state.restoreLexicalScope
            conditionState.lexicalScope).recordNode (.statement {
              id
              span := statement.span
              type := .unit
              form := .whileLoop inferredCondition.id bodyResult.statements
            })
      } ∧
      ContainsStatement (result.state.toTypedSource roots) result.id {
        id := result.id
        span := statement.span
        type := result.type
        form := .whileLoop inferredCondition.id bodyResult.statements
      } := by
  unfold Detail.inferStatementFuel at success
  simp only [allocationEq, statementEq, bind, Except.bind] at success
  cases conditionSuccess : Detail.inferExprFuel fuel context condition
      (some .bool) allocated with
  | error error =>
      simp [conditionSuccess] at success
  | ok conditionPair =>
      rcases conditionPair with ⟨inferredCondition, conditionState⟩
      simp only [conditionSuccess] at success
      cases bodySuccess : Detail.inferStatementsFuel fuel
          { context with loopDepth := context.loopDepth + 1 }
          body.value expectedReturn conditionState with
      | error error =>
          simp [bodySuccess] at success
      | ok bodyResult =>
          simp only [bodySuccess, pure, Pure.pure, Except.pure] at success
          injection success with resultEq
          rw [← resultEq]
          exact ⟨inferredCondition, conditionState, bodyResult,
            rfl, bodySuccess, rfl,
            recordNode_containsStatement
              (bodyResult.state.restoreLexicalScope
                conditionState.lexicalScope) _ roots⟩

/-- A retained semicolon-terminated expression statement discards its child's
value.  Final substitution changes the child proof but leaves the statement's
unit result and ordinary control summary unchanged. -/
theorem expressionStatementDiscardHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {statement : Syntax.Statement} {id : StatementId}
    {inferred : InferredExpression}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := .unit
      form := .expression inferred.id true
    })
    (expressionType : ExpressionHasType
      (source.applySubstitution outer) target inferred.id
      (outer.apply inferred.type)) :
    StatementHasType (source.applySubstitution outer) control target id target {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .ordinary .unit
    } := by
  exact .expressionDiscard
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl expressionType (by simp [StatementNode.applySubstitution])

/-- A retained expression statement without a trailing semicolon exposes its
child's finalized type as both statement value and ordinary fallthrough type. -/
theorem expressionStatementValueHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {statement : Syntax.Statement} {id : StatementId}
    {inferred : InferredExpression}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := inferred.type
      form := .expression inferred.id false
    })
    (expressionType : ExpressionHasType
      (source.applySubstitution outer) target inferred.id
      (outer.apply inferred.type)) :
    StatementHasType (source.applySubstitution outer) control target id target {
      type := outer.apply inferred.type
      hasValue := true
      sawReturn := false
      control := .ordinary (outer.apply inferred.type)
    } := by
  exact .expressionValue
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl expressionType (by simp [StatementNode.applySubstitution])

/-- A retained value-assignment statement is well typed once recursive place
and right-hand-side soundness establish the substituted assignment
resolution. -/
theorem assignValueStatementHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {statement : Syntax.Statement} {id : StatementId}
    {operator : Syntax.ValueAssignOp}
    {assignment : AssignmentResolution} {inferredValue : InferredExpression}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := .unit
      form := .assignValue assignment operator inferredValue.id
    })
    (assignmentType : SourceAssignmentHasType
      (source.applySubstitution outer) target
      (assignment.applySubstitution outer) operator inferredValue.id) :
    StatementHasType (source.applySubstitution outer) control target id target {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .ordinary .unit
    } := by
  exact .assignValue
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl assignmentType (by simp [StatementNode.applySubstitution])

/-- A retained bit-not assignment is well typed after successful `Word`
unification.  Semantic extension transports the inferred place type and the
stored resolved target annotation to the same finalized `Word` type. -/
theorem assignBitNotStatementHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {statement : Syntax.Statement} {id : StatementId}
    {place : PlaceResolution} {unified : Frontend.SourceInference.State}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := .unit
      form := .assignBitNot {
        target := { place with type := unified.resolve place.type }
      }
    })
    (placeType : SourcePlaceHasType (source.applySubstitution outer) target
      (place.applySubstitution outer) (outer.apply place.type))
    (resolvedEq : unified.resolve place.type = .word)
    (extension : outer.SemanticallyExtends
      unified.inference.substitution) :
    StatementHasType (source.applySubstitution outer) control target id target {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .ordinary .unit
    } := by
  have resolvedFinal :
      outer.apply (unified.resolve place.type) = outer.apply place.type := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using extension place.type
  have placeWord : outer.apply place.type = .word := by
    rw [← resolvedFinal, resolvedEq]
    rfl
  have storedPlaceEq :
      ({ place with type := unified.resolve place.type } : PlaceResolution
        ).applySubstitution outer = place.applySubstitution outer := by
    cases place
    simp [PlaceResolution.applySubstitution, resolvedFinal]
  have storedPlaceType : SourcePlaceHasType
      (source.applySubstitution outer) target
      (({ place with type := unified.resolve place.type } : PlaceResolution
        ).applySubstitution outer) .word := by
    rw [storedPlaceEq, ← placeWord]
    exact placeType
  have assignmentType : SourceBitNotAssignmentValid
      (source.applySubstitution outer) target
      (({ target := { place with type := unified.resolve place.type } } :
        AssignmentResolution).applySubstitution outer) := by
    exact .intro storedPlaceType rfl
  exact .assignBitNot
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl assignmentType (by simp [StatementNode.applySubstitution])

/-- A successful expression-statement branch is compositional modulo recursive
typing of its child expression.  Expression inference preserves lexical
locals; recording the parent preserves that invariant again, while the
semicolon flag selects the exact declarative facts and constructor. -/
theorem inferStatementFuel_success_expression_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expression : Syntax.Expr}
    {trailingSemicolon : Bool} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .expression expression trailingSemicolon)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (roots : List NodeId := [])
    (expressionSound :
      ∀ {inferred : InferredExpression}
        {expressionState : Frontend.SourceInference.State},
        Detail.inferExprFuel fuel inferenceContext expression none allocated =
            .ok (inferred, expressionState) →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target inferred.id (outer.apply inferred.type)) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  obtain ⟨inferred, expressionState, expressionSuccess, resultEq,
      contains⟩ :=
    inferStatementFuel_success_expression_facts statementEq allocationEq
      success roots
  have expressionInvariant :
      ActiveLocalContextInvariant expressionState outer target :=
    allocatedInvariant.inferExprFuel expressionSuccess
  have expressionTyping := expressionSound expressionSuccess
  subst result
  cases trailingSemicolon with
  | false =>
      refine ⟨{
          type := outer.apply inferred.type
          hasValue := true
          sawReturn := false
          control := .ordinary (outer.apply inferred.type)
        }, expressionInvariant.recordNode _, ?_, ?_⟩
      · exact expressionStatementValueHasType_afterSubstitution contains
          expressionTyping
      · constructor <;> rfl
  | true =>
      refine ⟨{
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        }, expressionInvariant.recordNode _, ?_, ?_⟩
      · exact expressionStatementDiscardHasType_afterSubstitution contains
          expressionTyping
      · constructor <;> rfl

/-- A retained bare return is well typed once its local unification result is
transported through the final substitution. -/
theorem returnUnitStatementHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {loopDepth : Nat}
    {statement : Syntax.Statement} {id : StatementId}
    {expectedReturn : TypeSystem.Ty}
    {returnState : Frontend.SourceInference.State}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := returnState.resolve expectedReturn
      form := .returnStmt none
    })
    (resolvedEq : returnState.resolve expectedReturn = .unit)
    (extension : outer.SemanticallyExtends
      returnState.inference.substitution) :
    StatementHasType (source.applySubstitution outer) {
      returnType := outer.apply expectedReturn
      loopDepth
    } target id target {
      type := outer.apply expectedReturn
      hasValue := true
      sawReturn := true
      control := .returned
    } := by
  have resolvedFinal :
      outer.apply (returnState.resolve expectedReturn) =
        outer.apply expectedReturn := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using extension expectedReturn
  have expectedUnit : outer.apply expectedReturn = .unit := by
    rw [← resolvedFinal, resolvedEq]
    rfl
  exact .returnUnit
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl expectedUnit (by
      simpa [StatementNode.applySubstitution] using resolvedFinal)

/-- A value return is well typed after final substitution once recursive
expression typing and expected-type coherence identify the child's finalized
type with the declaration return type. -/
theorem returnValueStatementHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {loopDepth : Nat}
    {statement : Syntax.Statement} {id : StatementId}
    {expectedReturn : TypeSystem.Ty}
    {valueState : Frontend.SourceInference.State}
    {inferred : InferredExpression}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := valueState.resolve expectedReturn
      form := .returnStmt (some inferred.id)
    })
    (valueType : ExpressionHasType (source.applySubstitution outer) target
      inferred.id (outer.apply inferred.type))
    (expectedEq : outer.apply inferred.type = outer.apply expectedReturn)
    (extension : outer.SemanticallyExtends
      valueState.inference.substitution) :
    StatementHasType (source.applySubstitution outer) {
      returnType := outer.apply expectedReturn
      loopDepth
    } target id target {
      type := outer.apply expectedReturn
      hasValue := true
      sawReturn := true
      control := .returned
    } := by
  have resolvedFinal :
      outer.apply (valueState.resolve expectedReturn) =
        outer.apply expectedReturn := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using extension expectedReturn
  have valueExpected : ExpressionHasType
      (source.applySubstitution outer) target inferred.id
      (outer.apply expectedReturn) := by
    rw [← expectedEq]
    exact valueType
  exact .returnValue
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl valueExpected (by
      simpa [StatementNode.applySubstitution] using resolvedFinal)

/-- `break` is substitution-invariant; successful frontend loop validation is
exactly the declarative loop-availability premise. -/
theorem breakStatementHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {returnType : TypeSystem.Ty}
    {loopDepth : Nat} {statement : Syntax.Statement} {id : StatementId}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := .unit
      form := .breakStmt
    })
    (allowed : loopDepth ≠ 0) :
    StatementHasType (source.applySubstitution outer) {
      returnType
      loopDepth
    } target id target {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .breaking
    } := by
  exact .breakStmt
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl (Nat.zero_lt_of_ne_zero allowed)
    (by simp [StatementNode.applySubstitution])

/-- `continue` has the same substitution-invariant typing boundary as
`break`, with its distinct control summary retained. -/
theorem continueStatementHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {returnType : TypeSystem.Ty}
    {loopDepth : Nat} {statement : Syntax.Statement} {id : StatementId}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := .unit
      form := .continueStmt
    })
    (allowed : loopDepth ≠ 0) :
    StatementHasType (source.applySubstitution outer) {
      returnType
      loopDepth
    } target id target {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .continuing
    } := by
  exact .continueStmt
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl (Nat.zero_lt_of_ne_zero allowed)
    (by simp [StatementNode.applySubstitution])

/-- The proof-facing facts of a finalized statement sequence agree with the
type and return summary retained by executable block inference. -/
structure BlockResultMatchesFactsAfterSubstitution
    (substitution : TypeSystem.Substitution)
    (result : Detail.BlockResult) (facts : BodyFacts) : Prop where
  type_eq : facts.type = substitution.apply result.type
  sawReturn_eq : facts.sawReturn = result.sawReturn

/-- An `if` without an `else` is declaratively typed from its finalized
condition and recursively reconstructed then-body.  The explicit condition
equality records the expected-type fact supplied by expression inference. -/
theorem ifWithoutElseStatementHasType_afterSubstitution
    {source : TypedSource} {target thenFinal : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {statement : Syntax.Statement} {id : StatementId}
    {inferredCondition : InferredExpression}
    {thenResult : Detail.BlockResult} {thenFacts : BodyFacts}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := .unit
      form := .ifThen inferredCondition.id thenResult.statements none
    })
    (conditionType : ExpressionHasType (source.applySubstitution outer) target
      inferredCondition.id (outer.apply inferredCondition.type))
    (conditionEq : outer.apply inferredCondition.type = .bool)
    (thenType : StatementsHaveType (source.applySubstitution outer) control
      target thenResult.statements thenFinal thenFacts) :
    StatementHasType (source.applySubstitution outer) control target id target {
      type := .unit
      hasValue := false
      sawReturn := false
      control := thenFacts.control.branches (.ordinary .unit)
    } := by
  have conditionBool : ExpressionHasType (source.applySubstitution outer) target
      inferredCondition.id .bool := by
    rw [← conditionEq]
    exact conditionType
  exact .ifWithoutElse
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl conditionBool thenType (by simp [StatementNode.applySubstitution])

/-- An `if` with an `else` is declaratively typed from both finalized branch
derivations.  Their executable agreements align the branch-return test, while
the final substitution's exact extension of the else state identifies the
stored resolved return type with the declaration return type. -/
theorem ifWithElseStatementHasType_afterSubstitution
    {source : TypedSource} {target thenFinal elseFinal : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {loopDepth : Nat}
    {statement : Syntax.Statement} {id : StatementId}
    {expectedReturn : TypeSystem.Ty}
    {inferredCondition : InferredExpression}
    {thenResult elseResult : Detail.BlockResult}
    {thenFacts elseFacts : BodyFacts}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := if thenResult.sawReturn && elseResult.sawReturn then
        elseResult.state.resolve expectedReturn
      else
        .unit
      form := .ifThen inferredCondition.id thenResult.statements
        (some elseResult.statements)
    })
    (conditionType : ExpressionHasType (source.applySubstitution outer) target
      inferredCondition.id (outer.apply inferredCondition.type))
    (conditionEq : outer.apply inferredCondition.type = .bool)
    (thenType : StatementsHaveType (source.applySubstitution outer) {
      returnType := outer.apply expectedReturn
      loopDepth
    } target thenResult.statements thenFinal thenFacts)
    (elseType : StatementsHaveType (source.applySubstitution outer) {
      returnType := outer.apply expectedReturn
      loopDepth
    } target elseResult.statements elseFinal elseFacts)
    (thenAgreement : BlockResultMatchesFactsAfterSubstitution outer thenResult
      thenFacts)
    (elseAgreement : BlockResultMatchesFactsAfterSubstitution outer elseResult
      elseFacts)
    (extension : outer.SemanticallyExtends
      elseResult.state.inference.substitution) :
    StatementHasType (source.applySubstitution outer) {
      returnType := outer.apply expectedReturn
      loopDepth
    } target id target {
      type := if thenFacts.sawReturn && elseFacts.sawReturn then
        outer.apply expectedReturn
      else
        .unit
      hasValue := thenFacts.sawReturn && elseFacts.sawReturn
      sawReturn := thenFacts.sawReturn && elseFacts.sawReturn
      control := thenFacts.control.branches elseFacts.control
    } := by
  have conditionBool : ExpressionHasType (source.applySubstitution outer) target
      inferredCondition.id .bool := by
    rw [← conditionEq]
    exact conditionType
  have resolvedFinal :
      outer.apply (elseResult.state.resolve expectedReturn) =
        outer.apply expectedReturn := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using extension expectedReturn
  have typeEq :
      outer.apply
          (if thenResult.sawReturn && elseResult.sawReturn then
            elseResult.state.resolve expectedReturn
          else
            .unit) =
        if thenFacts.sawReturn && elseFacts.sawReturn then
          outer.apply expectedReturn
        else
          .unit := by
    rw [thenAgreement.sawReturn_eq, elseAgreement.sawReturn_eq]
    cases thenResult.sawReturn <;> cases elseResult.sawReturn <;>
      simp [resolvedFinal]
  exact .ifWithElse
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl conditionBool thenType elseType (by
      simpa [StatementNode.applySubstitution] using typeEq)

/-- A retained block is typed by the recursively reconstructed statement
sequence.  The sequence agreement supplies the final type annotation on the
substituted block node, while lexical effects remain scoped to the body. -/
theorem blockStatementHasType_afterSubstitution
    {source : TypedSource} {target innerFinal : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {statement : Syntax.Statement} {id : StatementId}
    {bodyResult : Detail.BlockResult} {bodyFacts : BodyFacts}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := bodyResult.type
      form := .block bodyResult.statements
    })
    (bodyType : StatementsHaveType (source.applySubstitution outer) control
      target bodyResult.statements innerFinal bodyFacts)
    (agreement : BlockResultMatchesFactsAfterSubstitution outer bodyResult
      bodyFacts) :
    StatementHasType (source.applySubstitution outer) control target id target {
      type := bodyFacts.type
      hasValue := bodyFacts.sawReturn
      sawReturn := bodyFacts.sawReturn
      control := bodyFacts.control.eraseValue
    } := by
  exact .block
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl bodyType (by
      simpa [StatementNode.applySubstitution] using agreement.type_eq.symm)

/-- A retained default-free match is typed from its finalized scrutinee and
explicit cases.  Case agreement transports the executable all-return flag,
while semantic extension identifies the stored resolved return annotation. -/
theorem matchWithoutDefaultStatementHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {loopDepth : Nat}
    {statement : Syntax.Statement} {id : StatementId}
    {expectedReturn : TypeSystem.Ty}
    {scrutinee : InferredExpression} {hiddenScrutinee : Resolved.LocalId}
    {checked : Detail.MatchCasesResult}
    {caseFacts : List BodyFacts} {summary : ControlSummary}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := if checked.allReturn then
        checked.state.resolve expectedReturn
      else
        .unit
      form := .matchWith {
        scrutinee := scrutinee.id
        hiddenScrutinee
        cases := checked.cases
        defaultBody := none
        requirements := checked.cases.flatMap fun arm =>
          arm.pattern.requirements
      }
    })
    (scrutineeType : ExpressionHasType (source.applySubstitution outer)
      target scrutinee.id (outer.apply scrutinee.type))
    (casesType : MatchCasesHaveType (source.applySubstitution outer) {
      returnType := outer.apply expectedReturn
      loopDepth
    } target (outer.apply scrutinee.type)
      (checked.cases.map (TypedMatchCase.applySubstitution outer)) caseFacts)
    (exhaustive : MatchExhaustive target (outer.apply scrutinee.type)
      (checked.cases.map (TypedMatchCase.applySubstitution outer)) none)
    (allReturnEq : allBodiesSawReturn caseFacts = checked.allReturn)
    (merged : mergeBodyControls caseFacts none = some summary)
    (extension : outer.SemanticallyExtends
      checked.state.inference.substitution) :
    StatementHasType (source.applySubstitution outer) {
      returnType := outer.apply expectedReturn
      loopDepth
    } target id target {
      type := if allBodiesSawReturn caseFacts then
        outer.apply expectedReturn
      else
        .unit
      hasValue := allBodiesSawReturn caseFacts
      sawReturn := allBodiesSawReturn caseFacts
      control := summary.eraseValue
    } := by
  have resolvedFinal :
      outer.apply (checked.state.resolve expectedReturn) =
        outer.apply expectedReturn := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using extension expectedReturn
  have typeEq :
      outer.apply (if checked.allReturn then
          checked.state.resolve expectedReturn
        else
          .unit) =
        if allBodiesSawReturn caseFacts then
          outer.apply expectedReturn
        else
          .unit := by
    rw [← allReturnEq]
    cases checked.allReturn <;> simp [resolvedFinal]
  exact .matchWithoutDefault
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl rfl scrutineeType casesType
    (by simp [MatchResolution.applySubstitution]) exhaustive merged
    (by simpa [StatementNode.applySubstitution] using typeEq)

/-- Adding a default body makes `mergeBodyControls` total independently of
the number of explicit cases. -/
theorem mergeBodyControls_withDefault_eq_some
    (caseFacts : List BodyFacts) (defaultFacts : BodyFacts) :
    ∃ summary,
      mergeBodyControls caseFacts (some defaultFacts) = some summary := by
  induction caseFacts with
  | nil => exact ⟨defaultFacts.control, rfl⟩
  | cons head tail induction =>
      obtain ⟨summary, merged⟩ := induction
      exact ⟨head.control.branches summary, by
        simp [mergeBodyControls, merged]⟩

/-- A retained match with a default arm is typed from its finalized
scrutinee, explicit cases, and fallback body.  The fallback itself supplies
exhaustiveness, so only the common body-control merge remains. -/
theorem matchWithDefaultStatementHasType_afterSubstitution
    {source : TypedSource} {target defaultFinal : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {loopDepth : Nat}
    {statement : Syntax.Statement} {id : StatementId}
    {expectedReturn : TypeSystem.Ty}
    {scrutinee : InferredExpression} {hiddenScrutinee : Resolved.LocalId}
    {checked : Detail.MatchCasesResult} {defaultResult : Detail.BlockResult}
    {outerScope : LexicalScope}
    {caseFacts : List BodyFacts} {defaultFacts : BodyFacts}
    {summary : ControlSummary}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := if checked.allReturn && defaultResult.sawReturn then
        (defaultResult.state.restoreLexicalScope
          outerScope).resolve expectedReturn
      else
        .unit
      form := .matchWith {
        scrutinee := scrutinee.id
        hiddenScrutinee
        cases := checked.cases
        defaultBody := some defaultResult.statements
        requirements := checked.cases.flatMap fun arm =>
          arm.pattern.requirements
      }
    })
    (scrutineeType : ExpressionHasType (source.applySubstitution outer)
      target scrutinee.id (outer.apply scrutinee.type))
    (casesType : MatchCasesHaveType (source.applySubstitution outer) {
      returnType := outer.apply expectedReturn
      loopDepth
    } target (outer.apply scrutinee.type)
      (checked.cases.map (TypedMatchCase.applySubstitution outer)) caseFacts)
    (defaultType : StatementsHaveType (source.applySubstitution outer) {
      returnType := outer.apply expectedReturn
      loopDepth
    } target defaultResult.statements defaultFinal defaultFacts)
    (caseReturnEq : allBodiesSawReturn caseFacts = checked.allReturn)
    (defaultAgreement : BlockResultMatchesFactsAfterSubstitution outer
      defaultResult defaultFacts)
    (merged : mergeBodyControls caseFacts (some defaultFacts) = some summary)
    (extension : outer.SemanticallyExtends
      defaultResult.state.inference.substitution) :
    StatementHasType (source.applySubstitution outer) {
      returnType := outer.apply expectedReturn
      loopDepth
    } target id target {
      type := if allBodiesSawReturn caseFacts && defaultFacts.sawReturn then
        outer.apply expectedReturn
      else
        .unit
      hasValue := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      sawReturn := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      control := summary.eraseValue
    } := by
  have resolvedFinal :
      outer.apply (defaultResult.state.resolve expectedReturn) =
        outer.apply expectedReturn := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using extension expectedReturn
  have restoredResolve :
      (defaultResult.state.restoreLexicalScope outerScope).resolve
          expectedReturn =
        defaultResult.state.resolve expectedReturn := by
    rfl
  have typeEq :
      outer.apply (if checked.allReturn && defaultResult.sawReturn then
          (defaultResult.state.restoreLexicalScope outerScope).resolve
            expectedReturn
        else
          .unit) =
        if allBodiesSawReturn caseFacts && defaultFacts.sawReturn then
          outer.apply expectedReturn
        else
          .unit := by
    rw [restoredResolve]
    rw [← caseReturnEq, ← defaultAgreement.sawReturn_eq]
    cases checked.allReturn <;> cases defaultResult.sawReturn <;>
      simp [resolvedFinal]
  exact .matchWithDefault
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl rfl scrutineeType casesType defaultType
    (by simp [MatchResolution.applySubstitution]) merged
    (by
      simpa [StatementNode.applySubstitution] using typeEq)

/-- A retained `for` statement is typed from its finalized initializer and
post-item sequences, Boolean condition, and recursively reconstructed body.
The executable statement restores the enclosing lexical scope after these
loop-local judgments have been checked. -/
theorem forLoopStatementHasType_afterSubstitution
    {source : TypedSource}
    {target loopContext postContext bodyFinal : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {statement : Syntax.Statement} {id : StatementId}
    {initializerResult postResult : Detail.InferredForItems}
    {inferredCondition : InferredExpression}
    {bodyResult : Detail.BlockResult} {bodyFacts : BodyFacts}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := .unit
      form := .forLoop initializerResult.items inferredCondition.id
        postResult.items bodyResult.statements
    })
    (initializerType : ForItemsHaveType (source.applySubstitution outer)
      control target
      (initializerResult.items.map (ForItemForm.applySubstitution outer))
      loopContext)
    (conditionType : ExpressionHasType (source.applySubstitution outer)
      loopContext inferredCondition.id .bool)
    (bodyType : StatementsHaveType (source.applySubstitution outer)
      control.enterLoop loopContext bodyResult.statements bodyFinal bodyFacts)
    (postType : ForItemsHaveType (source.applySubstitution outer)
      control.enterLoop loopContext
      (postResult.items.map (ForItemForm.applySubstitution outer))
      postContext) :
    StatementHasType (source.applySubstitution outer) control target id target {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .loop bodyFacts.control
    } := by
  exact .forLoop
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl initializerType conditionType bodyType postType
    (by simp [StatementNode.applySubstitution])

/-- A retained `while` statement is typed from its finalized Boolean
condition and recursively reconstructed body at one greater loop depth.
Lexical effects of the body remain scoped to the loop. -/
theorem whileLoopStatementHasType_afterSubstitution
    {source : TypedSource} {target bodyFinal : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {statement : Syntax.Statement} {id : StatementId}
    {inferredCondition : InferredExpression}
    {bodyResult : Detail.BlockResult} {bodyFacts : BodyFacts}
    (contains : ContainsStatement source id {
      id
      span := statement.span
      type := .unit
      form := .whileLoop inferredCondition.id bodyResult.statements
    })
    (conditionType : ExpressionHasType (source.applySubstitution outer) target
      inferredCondition.id (outer.apply inferredCondition.type))
    (conditionEq : outer.apply inferredCondition.type = .bool)
    (bodyType : StatementsHaveType (source.applySubstitution outer)
      control.enterLoop target bodyResult.statements bodyFinal bodyFacts) :
    StatementHasType (source.applySubstitution outer) control target id target {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .loop bodyFacts.control
    } := by
  have conditionBool : ExpressionHasType (source.applySubstitution outer)
      target inferredCondition.id .bool := by
    rw [← conditionEq]
    exact conditionType
  exact .whileLoop
    (FlexibleSubstitution.ContainsStatement.applySubstitution outer contains)
    rfl conditionBool bodyType (by simp [StatementNode.applySubstitution])

namespace StatementResultMatchesFactsAfterSubstitution

/-- Every executable statement with the canonical unit/non-value/non-returning
projection agrees with the declarative ordinary-unit summary. -/
theorem ordinaryUnit
    (substitution : TypeSystem.Substitution) (id : StatementId)
    (state : Frontend.SourceInference.State) :
    StatementResultMatchesFactsAfterSubstitution substitution {
      id
      type := .unit
      hasValue := false
      sawReturn := false
      state
    } {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .ordinary .unit
    } := by
  constructor <;> rfl

/-- Every executable local declaration returns the canonical ordinary-unit
summary, independently of the declared scheme and initializer. -/
theorem letDecl
    (substitution : TypeSystem.Substitution) (id : StatementId)
    (state : Frontend.SourceInference.State) :
    StatementResultMatchesFactsAfterSubstitution substitution {
      id
      type := .unit
      hasValue := false
      sawReturn := false
      state
    } {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .ordinary .unit
    } := by
  exact ordinaryUnit substitution id state

/-- The executable result shared by bare and value returns agrees with the
declarative returned summary after any semantically extending substitution. -/
theorem returned
    {substitution : TypeSystem.Substitution}
    {returnState resultState : Frontend.SourceInference.State}
    {expectedReturn : TypeSystem.Ty} {id : StatementId}
    (extension : substitution.SemanticallyExtends
      returnState.inference.substitution) :
    StatementResultMatchesFactsAfterSubstitution substitution {
      id
      type := returnState.resolve expectedReturn
      hasValue := true
      sawReturn := true
      state := resultState
    } {
      type := substitution.apply expectedReturn
      hasValue := true
      sawReturn := true
      control := .returned
    } := by
  have resolvedFinal :
      substitution.apply (returnState.resolve expectedReturn) =
        substitution.apply expectedReturn := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using extension expectedReturn
  exact ⟨resolvedFinal.symm, rfl, rfl⟩

/-- The canonical executable `break` result agrees with its declarative
control summary under every substitution. -/
theorem breakStmt
    (substitution : TypeSystem.Substitution) (id : StatementId)
    (state : Frontend.SourceInference.State) :
    StatementResultMatchesFactsAfterSubstitution substitution {
      id
      type := .unit
      hasValue := false
      sawReturn := false
      state
    } {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .breaking
    } := by
  constructor <;> rfl

/-- The canonical executable `continue` result agrees with its declarative
control summary under every substitution. -/
theorem continueStmt
    (substitution : TypeSystem.Substitution) (id : StatementId)
    (state : Frontend.SourceInference.State) :
    StatementResultMatchesFactsAfterSubstitution substitution {
      id
      type := .unit
      hasValue := false
      sawReturn := false
      state
    } {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .continuing
    } := by
  constructor <;> rfl

/-- The canonical executable result of an `if` without an `else` always agrees
with its unit, non-value, non-returning declarative projections. -/
theorem ifWithoutElse
    (substitution : TypeSystem.Substitution) (thenFacts : BodyFacts)
    (id : StatementId) (state : Frontend.SourceInference.State) :
    StatementResultMatchesFactsAfterSubstitution substitution {
      id
      type := .unit
      hasValue := false
      sawReturn := false
      state
    } {
      type := .unit
      hasValue := false
      sawReturn := false
      control := thenFacts.control.branches (.ordinary .unit)
    } := by
  constructor <;> rfl

/-- Both branch agreements align the executable return conjunction with the
declarative one.  Exact semantic extension of the final else state then closes
the only nontrivial type projection. -/
theorem ifWithElse
    {substitution : TypeSystem.Substitution}
    {expectedReturn : TypeSystem.Ty}
    {thenResult elseResult : Detail.BlockResult}
    {thenFacts elseFacts : BodyFacts}
    (thenAgreement : BlockResultMatchesFactsAfterSubstitution substitution
      thenResult thenFacts)
    (elseAgreement : BlockResultMatchesFactsAfterSubstitution substitution
      elseResult elseFacts)
    (extension : substitution.SemanticallyExtends
      elseResult.state.inference.substitution)
    (id : StatementId) (state : Frontend.SourceInference.State) :
    StatementResultMatchesFactsAfterSubstitution substitution {
      id
      type := if thenResult.sawReturn && elseResult.sawReturn then
        elseResult.state.resolve expectedReturn
      else
        .unit
      hasValue := thenResult.sawReturn && elseResult.sawReturn
      sawReturn := thenResult.sawReturn && elseResult.sawReturn
      state
    } {
      type := if thenFacts.sawReturn && elseFacts.sawReturn then
        substitution.apply expectedReturn
      else
        .unit
      hasValue := thenFacts.sawReturn && elseFacts.sawReturn
      sawReturn := thenFacts.sawReturn && elseFacts.sawReturn
      control := thenFacts.control.branches elseFacts.control
    } := by
  have resolvedFinal :
      substitution.apply (elseResult.state.resolve expectedReturn) =
        substitution.apply expectedReturn := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using extension expectedReturn
  constructor
  · rw [thenAgreement.sawReturn_eq, elseAgreement.sawReturn_eq]
    cases thenResult.sawReturn <;> cases elseResult.sawReturn <;>
      simp [resolvedFinal]
  · rw [thenAgreement.sawReturn_eq, elseAgreement.sawReturn_eq]
  · rw [thenAgreement.sawReturn_eq, elseAgreement.sawReturn_eq]

/-- Case agreement aligns the executable all-return flag of a default-free
match with the declarative fold; semantic extension closes its result type. -/
theorem matchWithoutDefault
    {substitution : TypeSystem.Substitution}
    {expectedReturn : TypeSystem.Ty}
    {checked : Detail.MatchCasesResult} {caseFacts : List BodyFacts}
    {summary : ControlSummary}
    (allReturnEq : allBodiesSawReturn caseFacts = checked.allReturn)
    (extension : substitution.SemanticallyExtends
      checked.state.inference.substitution)
    (id : StatementId) (state : Frontend.SourceInference.State) :
    StatementResultMatchesFactsAfterSubstitution substitution {
      id
      type := if checked.allReturn then
        checked.state.resolve expectedReturn
      else
        .unit
      hasValue := checked.allReturn
      sawReturn := checked.allReturn
      state
    } {
      type := if allBodiesSawReturn caseFacts then
        substitution.apply expectedReturn
      else
        .unit
      hasValue := allBodiesSawReturn caseFacts
      sawReturn := allBodiesSawReturn caseFacts
      control := summary.eraseValue
    } := by
  have resolvedFinal :
      substitution.apply (checked.state.resolve expectedReturn) =
        substitution.apply expectedReturn := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using extension expectedReturn
  constructor
  · rw [← allReturnEq]
    cases checked.allReturn <;> simp [resolvedFinal]
  · exact allReturnEq
  · exact allReturnEq

/-- Explicit-case and fallback agreements align both Boolean projections of a
match with default; the fallback state's substitution closes the result type. -/
theorem matchWithDefault
    {substitution : TypeSystem.Substitution}
    {expectedReturn : TypeSystem.Ty}
    {checked : Detail.MatchCasesResult} {defaultResult : Detail.BlockResult}
    {caseFacts : List BodyFacts} {defaultFacts : BodyFacts}
    {summary : ControlSummary} {outerScope : LexicalScope}
    (caseReturnEq : allBodiesSawReturn caseFacts = checked.allReturn)
    (defaultAgreement : BlockResultMatchesFactsAfterSubstitution substitution
      defaultResult defaultFacts)
    (extension : substitution.SemanticallyExtends
      defaultResult.state.inference.substitution)
    (id : StatementId) (state : Frontend.SourceInference.State) :
    StatementResultMatchesFactsAfterSubstitution substitution {
      id
      type := if checked.allReturn && defaultResult.sawReturn then
        (defaultResult.state.restoreLexicalScope outerScope).resolve
          expectedReturn
      else
        .unit
      hasValue := checked.allReturn && defaultResult.sawReturn
      sawReturn := checked.allReturn && defaultResult.sawReturn
      state
    } {
      type := if allBodiesSawReturn caseFacts && defaultFacts.sawReturn then
        substitution.apply expectedReturn
      else
        .unit
      hasValue := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      sawReturn := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      control := summary.eraseValue
    } := by
  have resolvedFinal :
      substitution.apply (defaultResult.state.resolve expectedReturn) =
        substitution.apply expectedReturn := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using extension expectedReturn
  have restoredResolve :
      (defaultResult.state.restoreLexicalScope outerScope).resolve
          expectedReturn =
        defaultResult.state.resolve expectedReturn := by
    rfl
  constructor
  · rw [← caseReturnEq, ← defaultAgreement.sawReturn_eq]
    rw [restoredResolve]
    cases checked.allReturn <;> cases defaultResult.sawReturn <;>
      simp [resolvedFinal]
  · rw [caseReturnEq, defaultAgreement.sawReturn_eq]
  · rw [caseReturnEq, defaultAgreement.sawReturn_eq]

/-- A scoped block statement inherits the finalized type and return flag of
its recursively inferred body; erasing the body's ordinary value affects only
the control summary. -/
theorem block
    {substitution : TypeSystem.Substitution}
    {bodyResult : Detail.BlockResult} {bodyFacts : BodyFacts}
    (agreement : BlockResultMatchesFactsAfterSubstitution substitution
      bodyResult bodyFacts)
    (id : StatementId) (state : Frontend.SourceInference.State) :
    StatementResultMatchesFactsAfterSubstitution substitution {
      id
      type := bodyResult.type
      hasValue := bodyResult.sawReturn
      sawReturn := bodyResult.sawReturn
      state
    } {
      type := bodyFacts.type
      hasValue := bodyFacts.sawReturn
      sawReturn := bodyFacts.sawReturn
      control := bodyFacts.control.eraseValue
    } := by
  exact ⟨agreement.type_eq, agreement.sawReturn_eq,
    agreement.sawReturn_eq⟩

/-- A loop statement always has the executable unit/non-returning summary;
the declarative body control is retained only inside the loop summary. -/
theorem whileLoop
    (substitution : TypeSystem.Substitution) (bodyFacts : BodyFacts)
    (id : StatementId) (state : Frontend.SourceInference.State) :
    StatementResultMatchesFactsAfterSubstitution substitution {
      id
      type := .unit
      hasValue := false
      sawReturn := false
      state
    } {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .loop bodyFacts.control
    } := by
  constructor <;> rfl

/-- The canonical executable `for` result has the same unit/non-returning
projection as `while`; initializer and post typing affect only its premises. -/
theorem forLoop
    (substitution : TypeSystem.Substitution) (bodyFacts : BodyFacts)
    (id : StatementId) (state : Frontend.SourceInference.State) :
    StatementResultMatchesFactsAfterSubstitution substitution {
      id
      type := .unit
      hasValue := false
      sawReturn := false
      state
    } {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .loop bodyFacts.control
    } := by
  constructor <;> rfl

end StatementResultMatchesFactsAfterSubstitution

/-- A successful value-assignment statement is compositional modulo recursive
soundness of the delegated place/RHS inference.  That traversal and parent
recording both preserve the active lexical context. -/
theorem inferStatementFuel_success_assignValue_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .assignValue targetExpression operator value)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (roots : List NodeId := [])
    (assignmentSound :
      ∀ {assignment : AssignmentResolution}
        {inferredValue : InferredExpression}
        {assignmentState : Frontend.SourceInference.State},
        Detail.inferAssignedValueFuel fuel inferenceContext targetExpression
            operator.value value allocated =
              .ok (assignment, inferredValue, assignmentState) →
          SourceAssignmentHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target (assignment.applySubstitution outer) operator.value
            inferredValue.id) :
    ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id target {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } ∧
      StatementResultMatchesFactsAfterSubstitution outer result {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      } := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  obtain ⟨assignment, inferredValue, assignmentState, assignmentSuccess,
      resultEq, contains⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq
      success roots
  have assignmentInvariant :
      ActiveLocalContextInvariant assignmentState outer target :=
    allocatedInvariant.inferAssignedValueFuel assignmentSuccess
  have assignmentTyping := assignmentSound assignmentSuccess
  subst result
  refine ⟨assignmentInvariant.recordNode _, ?_, ?_⟩
  · exact assignValueStatementHasType_afterSubstitution contains
      assignmentTyping
  · exact StatementResultMatchesFactsAfterSubstitution.ordinaryUnit outer id _

/-- The deep value-assignment branch closes both delegated place inference and
RHS expression inference in the statement's finalized typed source. -/
theorem inferStatementFuel_success_assignValue_deep_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .assignValue targetExpression operator value)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical :
      ∀ signature ∈ inferenceContext.signatures.functions,
        signature.scheme.body = .function
          (TypeSystem.Ty.productMany signature.parameterTypes)
          (TypeSystem.Ty.productMany signature.returnTypes))
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (expressionSound :
      ∀ {expressionFuel : Nat} {expression : Syntax.Expr}
        {expected : Option TypeSystem.Ty}
        {expressionInitial expressionFinal : Frontend.SourceInference.State}
        {inferred : InferredExpression},
        Detail.inferExprFuel expressionFuel inferenceContext expression
            expected expressionInitial = .ok (inferred, expressionFinal) →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target inferred.id (outer.apply inferred.type)) :
    ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id target {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } ∧
      StatementResultMatchesFactsAfterSubstitution outer result {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      } := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have preserved :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    rw [allocationEq] at preserved
    exact preserved
  obtain ⟨assignment, inferredValue, assignmentState, assignmentSuccess,
      resultEq, contains⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq
      success roots
  have assignmentInvariant :
      ActiveLocalContextInvariant assignmentState outer target :=
    allocatedInvariant.inferAssignedValueFuel assignmentSuccess
  subst result
  have assignmentExtension : outer.SemanticallyExtends
      assignmentState.inference.substitution := by
    change outer.SemanticallyExtends assignmentState.inference.substitution
      at outerExtension
    exact outerExtension
  have assignmentType := inferAssignedValueFuel_success_sound allocatedReady
    signatureFormation functionsCanonical allocatedInvariant
    assignmentExtension expressionSound assignmentSuccess
  refine ⟨assignmentInvariant.recordNode _, ?_, ?_⟩
  · exact assignValueStatementHasType_afterSubstitution contains
      assignmentType
  · exact StatementResultMatchesFactsAfterSubstitution.ordinaryUnit outer id _

/-- A successful bit-not assignment is compositional modulo recursive place
soundness.  The statement layer discharges the `Word` unification, transports
the finalized place annotation, and preserves the active lexical context. -/
theorem inferStatementFuel_success_assignBitNot_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .assignBitNot targetExpression operatorSpan)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (placeSound :
      ∀ {place : PlaceResolution}
        {placeState : Frontend.SourceInference.State},
        Detail.inferPlaceFuel fuel inferenceContext targetExpression allocated =
            .ok (place, placeState) →
          SourcePlaceHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target (place.applySubstitution outer) (outer.apply place.type)) :
    ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id target {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } ∧
      StatementResultMatchesFactsAfterSubstitution outer result {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      } := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  obtain ⟨place, placeState, unified, placeSuccess, unifySuccess, resolvedEq,
      resultEq, contains⟩ :=
    inferStatementFuel_success_assignBitNot_facts statementEq allocationEq
      success roots
  have placeInvariant : ActiveLocalContextInvariant placeState outer target :=
    allocatedInvariant.inferPlaceFuel placeSuccess
  have unifiedInvariant : ActiveLocalContextInvariant unified outer target :=
    placeInvariant.unify unifySuccess
  have placeTyping := placeSound placeSuccess
  subst result
  have unifiedExtension : outer.SemanticallyExtends
      unified.inference.substitution := by
    change outer.SemanticallyExtends unified.inference.substitution at outerExtension
    exact outerExtension
  refine ⟨unifiedInvariant.recordNode _, ?_, ?_⟩
  · exact assignBitNotStatementHasType_afterSubstitution contains placeTyping
      resolvedEq unifiedExtension
  · exact StatementResultMatchesFactsAfterSubstitution.ordinaryUnit outer id _

/-- The deep bit-not assignment branch reconstructs its place typing directly
from executable place inference and the final `Word` unification. -/
theorem inferStatementFuel_success_assignBitNot_deep_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .assignBitNot targetExpression operatorSpan)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical :
      ∀ signature ∈ inferenceContext.signatures.functions,
        signature.scheme.body = .function
          (TypeSystem.Ty.productMany signature.parameterTypes)
          (TypeSystem.Ty.productMany signature.returnTypes))
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (expressionSound :
      ∀ {expressionFuel : Nat} {expression : Syntax.Expr}
        {expected : Option TypeSystem.Ty}
        {expressionInitial expressionFinal : Frontend.SourceInference.State}
        {inferred : InferredExpression},
        Detail.inferExprFuel expressionFuel inferenceContext expression
            expected expressionInitial = .ok (inferred, expressionFinal) →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target inferred.id (outer.apply inferred.type)) :
    ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id target {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } ∧
      StatementResultMatchesFactsAfterSubstitution outer result {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      } := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have preserved :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    rw [allocationEq] at preserved
    exact preserved
  obtain ⟨place, placeState, unified, placeSuccess, unifySuccess, resolvedEq,
      resultEq, contains⟩ :=
    inferStatementFuel_success_assignBitNot_facts statementEq allocationEq
      success roots
  have placeInvariant : ActiveLocalContextInvariant placeState outer target :=
    allocatedInvariant.inferPlaceFuel placeSuccess
  have unifiedInvariant : ActiveLocalContextInvariant unified outer target :=
    placeInvariant.unify unifySuccess
  have placeProperties := Detail.inferPlaceFuel_inferenceProperties
    allocatedReady signatureFormation functionsCanonical placeSuccess
  have unifyProgress := Detail.unify_inferenceProgress
    placeProperties.2.1.solved placeProperties.2.2
    (TypeSystem.Ty.variablesBelow_constructor _ _) unifySuccess
  subst result
  have unifiedExtension : outer.SemanticallyExtends
      unified.inference.substitution := by
    change outer.SemanticallyExtends unified.inference.substitution
      at outerExtension
    exact outerExtension
  have placeExtension : outer.SemanticallyExtends
      placeState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans unifiedExtension
      unifyProgress.substitution_extends
  have placeType := inferPlaceFuel_success_sound allocatedReady
    signatureFormation functionsCanonical allocatedInvariant placeExtension
    expressionSound placeSuccess
  refine ⟨unifiedInvariant.recordNode _, ?_, ?_⟩
  · exact assignBitNotStatementHasType_afterSubstitution contains placeType
      resolvedEq unifiedExtension
  · exact StatementResultMatchesFactsAfterSubstitution.ordinaryUnit outer id _

/-- A successful bare return preserves the active lexical context and is
declaratively typed once the final substitution extends its unification
state. -/
theorem inferStatementFuel_success_returnUnit_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value = .returnStmt none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := []) :
    ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target {
          type := outer.apply expectedReturn
          hasValue := true
          sawReturn := true
          control := .returned
        } ∧
      StatementResultMatchesFactsAfterSubstitution outer result {
        type := outer.apply expectedReturn
        hasValue := true
        sawReturn := true
        control := .returned
      } := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  obtain ⟨unified, unifySuccess, resolvedEq, resultEq, contains⟩ :=
    inferStatementFuel_success_returnUnit_facts statementEq allocationEq
      success roots
  have unifiedInvariant :
      ActiveLocalContextInvariant unified outer target :=
    allocatedInvariant.unify unifySuccess
  subst result
  refine ⟨unifiedInvariant.recordNode _, ?_, ?_⟩
  · exact returnUnitStatementHasType_afterSubstitution contains resolvedEq
      outerExtension
  · exact StatementResultMatchesFactsAfterSubstitution.returned outerExtension

/-- A successful value return is compositional modulo typing of its child
expression.  Expected-type coherence identifies the finalized child type
with the function return type, and recording the parent keeps the active
lexical context unchanged. -/
theorem inferStatementFuel_success_returnValue_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {value : Syntax.Expr}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value = .returnStmt (some value))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (valueSound :
      ∀ {inferred : InferredExpression}
        {valueState : Frontend.SourceInference.State},
        Detail.inferExprFuel fuel inferenceContext value
            (some expectedReturn) allocated = .ok (inferred, valueState) →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target inferred.id (outer.apply inferred.type)) :
    ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target {
          type := outer.apply expectedReturn
          hasValue := true
          sawReturn := true
          control := .returned
        } ∧
      StatementResultMatchesFactsAfterSubstitution outer result {
        type := outer.apply expectedReturn
        hasValue := true
        sawReturn := true
        control := .returned
      } := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  obtain ⟨inferred, valueState, valueSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_returnValue_facts statementEq allocationEq
      success roots
  have valueInvariant :
      ActiveLocalContextInvariant valueState outer target :=
    allocatedInvariant.inferExprFuel valueSuccess
  have valueTyping := valueSound valueSuccess
  subst result
  have valueExtension : outer.SemanticallyExtends
      valueState.inference.substitution := by
    change outer.SemanticallyExtends valueState.inference.substitution at outerExtension
    exact outerExtension
  have expectedEq :
      outer.apply inferred.type = outer.apply expectedReturn :=
    Detail.inferExprFuel_expected_type_apply_eq valueSuccess valueExtension
  refine ⟨valueInvariant.recordNode _, ?_, ?_⟩
  · exact returnValueStatementHasType_afterSubstitution contains valueTyping
      expectedEq valueExtension
  · exact StatementResultMatchesFactsAfterSubstitution.returned valueExtension

/-- Successful `break` inference preserves the active lexical context.  The
frontend loop-depth guard is exactly the premise needed by declarative
typing. -/
theorem inferStatementFuel_success_break_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value = .breakStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (roots : List NodeId := []) :
    ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .breaking
        } ∧
      StatementResultMatchesFactsAfterSubstitution outer result {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .breaking
      } := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  obtain ⟨allowed, resultEq, contains⟩ :=
    inferStatementFuel_success_break_facts statementEq allocationEq success
      roots
  subst result
  refine ⟨allocatedInvariant.recordNode _, ?_, ?_⟩
  · exact breakStatementHasType_afterSubstitution contains allowed
  · exact StatementResultMatchesFactsAfterSubstitution.breakStmt outer id _

/-- Successful `continue` inference has the same stable-context boundary as
`break`, while retaining its distinct declarative control result. -/
theorem inferStatementFuel_success_continue_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value = .continueStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (roots : List NodeId := []) :
    ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .continuing
        } ∧
      StatementResultMatchesFactsAfterSubstitution outer result {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .continuing
      } := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  obtain ⟨allowed, resultEq, contains⟩ :=
    inferStatementFuel_success_continue_facts statementEq allocationEq success
      roots
  subst result
  refine ⟨allocatedInvariant.recordNode _, ?_, ?_⟩
  · exact continueStatementHasType_afterSubstitution contains allowed
  · exact StatementResultMatchesFactsAfterSubstitution.continueStmt outer id _

/-- A successful scoped block is compositional modulo recursive soundness of
its body.  The body may extend its own semantic context, but restoring the
saved lexical scope makes the enclosing statement preserve the caller's
active-local invariant and semantic context. -/
theorem inferStatementFuel_success_block_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {body : List Syntax.Statement}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (statementEq : statement.value = .block body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (roots : List NodeId := [])
    (bodySound :
      ∀ {bodyResult : Detail.BlockResult},
        Detail.inferStatementsFuel fuel inferenceContext body expectedReturn
            allocated = .ok bodyResult →
          ∃ finalContext bodyFacts,
            ActiveLocalContextInvariant bodyResult.state outer finalContext ∧
            StatementsHaveType
              ((result.state.toTypedSource roots).applySubstitution outer)
              control target bodyResult.statements finalContext bodyFacts ∧
            BlockResultMatchesFactsAfterSubstitution outer bodyResult
              bodyFacts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        control target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  obtain ⟨bodyResult, bodySuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_block_facts statementEq allocationEq success
      roots
  obtain ⟨finalContext, bodyFacts, _bodyInvariant, bodyTyping,
      bodyAgreement⟩ := bodySound bodySuccess
  subst result
  refine ⟨{
      type := bodyFacts.type
      hasValue := bodyFacts.sawReturn
      sawReturn := bodyFacts.sawReturn
      control := bodyFacts.control.eraseValue
    }, allocatedInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact blockStatementHasType_afterSubstitution contains bodyTyping
      bodyAgreement
  · exact StatementResultMatchesFactsAfterSubstitution.block bodyAgreement
      id _

/-- A successful conditional without an `else` is compositional modulo
typing its condition and then-body in the common final typed source.  The
inference-progress witness for the body transports the condition's expected
`Bool` type through the final substitution. -/
theorem inferStatementFuel_success_ifWithoutElse_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value = .ifThen condition thenBody none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      Frontend.ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (ready : initial.InferenceReady)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (conditionSound :
      ∀ {inferredCondition : InferredExpression}
        {conditionState : Frontend.SourceInference.State},
        Detail.inferExprFuel fuel inferenceContext condition (some .bool)
            allocated = .ok (inferredCondition, conditionState) →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target inferredCondition.id
            (outer.apply inferredCondition.type))
    (thenSound :
      ∀ {conditionState : Frontend.SourceInference.State}
        {thenResult : Detail.BlockResult},
        ActiveLocalContextInvariant conditionState outer target →
          Detail.inferStatementsFuel fuel inferenceContext thenBody.value
            expectedReturn conditionState = .ok thenResult →
          ∃ thenFinal thenFacts,
            ActiveLocalContextInvariant thenResult.state outer thenFinal ∧
            StatementsHaveType
              ((result.state.toTypedSource roots).applySubstitution outer) {
                returnType := outer.apply expectedReturn
                loopDepth := inferenceContext.loopDepth
              } target thenResult.statements thenFinal thenFacts ∧
            BlockResultMatchesFactsAfterSubstitution outer thenResult
              thenFacts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have preserved :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [finalEq] at preserved
    exact preserved
  have allocatedReturnBelow :
      expectedReturn.VariablesBelow allocated.inference.next := by
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← finalEq]
    exact returnBelow
  obtain ⟨inferredCondition, conditionState, thenResult, conditionSuccess,
      thenSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_ifWithoutElse_facts statementEq allocationEq
      success roots
  have conditionProperties :=
    Detail.inferExprFuel_inferenceProperties allocatedReady signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [TypeSystem.Ty.bool]) conditionSuccess
  have conditionInvariant :
      ActiveLocalContextInvariant conditionState outer target :=
    allocatedInvariant.inferExprFuel conditionSuccess
  have conditionTyping := conditionSound conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedReturnBelow.weaken conditionProperties.1.next_le
  have thenProperties :=
    Detail.inferStatementsFuel_inferenceProperties conditionProperties.2.1
      signatureFormation functionsCanonical conditionReturnBelow thenSuccess
  obtain ⟨thenFinal, thenFacts, _thenInvariant, thenTyping,
      thenAgreement⟩ := thenSound conditionInvariant thenSuccess
  subst result
  have thenExtension : outer.SemanticallyExtends
      thenResult.state.inference.substitution := by
    change outer.SemanticallyExtends
      thenResult.state.inference.substitution at outerExtension
    exact outerExtension
  have conditionExtension : outer.SemanticallyExtends
      conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans thenExtension
      thenProperties.1.substitution_extends
  have conditionEq : outer.apply inferredCondition.type = .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess
      conditionExtension
  refine ⟨{
      type := .unit
      hasValue := false
      sawReturn := false
      control := thenFacts.control.branches (.ordinary .unit)
    }, conditionInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact ifWithoutElseStatementHasType_afterSubstitution contains
      conditionTyping conditionEq thenTyping
  · exact
      StatementResultMatchesFactsAfterSubstitution.ifWithoutElse outer
        thenFacts id _

/-- A successful two-branch conditional is compositional modulo condition and
branch soundness in the common final typed source.  Both branch scopes start
from the condition context; executable restoration prevents declarations in
the then-branch from leaking into the else-branch or the enclosing context. -/
theorem inferStatementFuel_success_ifWithElse_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .ifThen condition thenBody (some elseBody))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      Frontend.ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (ready : initial.InferenceReady)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (conditionSound :
      ∀ {inferredCondition : InferredExpression}
        {conditionState : Frontend.SourceInference.State},
        Detail.inferExprFuel fuel inferenceContext condition (some .bool)
            allocated = .ok (inferredCondition, conditionState) →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target inferredCondition.id
            (outer.apply inferredCondition.type))
    (thenSound :
      ∀ {conditionState : Frontend.SourceInference.State}
        {thenResult : Detail.BlockResult},
        ActiveLocalContextInvariant conditionState outer target →
          Detail.inferStatementsFuel fuel inferenceContext thenBody.value
              expectedReturn conditionState = .ok thenResult →
            ∃ thenFinal thenFacts,
              ActiveLocalContextInvariant thenResult.state outer thenFinal ∧
              StatementsHaveType
                ((result.state.toTypedSource roots).applySubstitution outer) {
                  returnType := outer.apply expectedReturn
                  loopDepth := inferenceContext.loopDepth
                } target thenResult.statements thenFinal thenFacts ∧
              BlockResultMatchesFactsAfterSubstitution outer thenResult
                thenFacts)
    (elseSound :
      ∀ {elseInput : Frontend.SourceInference.State}
        {elseResult : Detail.BlockResult},
        ActiveLocalContextInvariant elseInput outer target →
          Detail.inferStatementsFuel fuel inferenceContext elseBody.value
              expectedReturn elseInput = .ok elseResult →
            ∃ elseFinal elseFacts,
              ActiveLocalContextInvariant elseResult.state outer elseFinal ∧
              StatementsHaveType
                ((result.state.toTypedSource roots).applySubstitution outer) {
                  returnType := outer.apply expectedReturn
                  loopDepth := inferenceContext.loopDepth
                } target elseResult.statements elseFinal elseFacts ∧
              BlockResultMatchesFactsAfterSubstitution outer elseResult
                elseFacts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have preserved :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [finalEq] at preserved
    exact preserved
  have allocatedReturnBelow :
      expectedReturn.VariablesBelow allocated.inference.next := by
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← finalEq]
    exact returnBelow
  obtain ⟨inferredCondition, conditionState, thenResult, elseResult,
      conditionSuccess, thenSuccess, elseSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_ifWithElse_facts statementEq allocationEq
      success roots
  have conditionProperties :=
    Detail.inferExprFuel_inferenceProperties allocatedReady signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [TypeSystem.Ty.bool]) conditionSuccess
  have conditionInvariant :
      ActiveLocalContextInvariant conditionState outer target :=
    allocatedInvariant.inferExprFuel conditionSuccess
  have conditionTyping := conditionSound conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedReturnBelow.weaken conditionProperties.1.next_le
  have thenProperties :=
    Detail.inferStatementsFuel_inferenceProperties conditionProperties.2.1
      signatureFormation functionsCanonical conditionReturnBelow thenSuccess
  obtain ⟨thenFinal, thenFacts, _thenInvariant, thenTyping,
      thenAgreement⟩ := thenSound conditionInvariant thenSuccess
  have restoredProperties :=
    Frontend.SourceInference.State.restoreLexicalScope_inferenceProperties
      conditionProperties.2.1 thenProperties.1
  have elseInputInvariant : ActiveLocalContextInvariant
      (thenResult.state.restoreLexicalScope conditionState.lexicalScope) outer
      target :=
    conditionInvariant.restoreLexicalScope
  have elseReturnBelow : expectedReturn.VariablesBelow
      (thenResult.state.restoreLexicalScope
        conditionState.lexicalScope).inference.next :=
    conditionReturnBelow.weaken restoredProperties.1.next_le
  have elseProperties :=
    Detail.inferStatementsFuel_inferenceProperties restoredProperties.2
      signatureFormation functionsCanonical elseReturnBelow elseSuccess
  obtain ⟨elseFinal, elseFacts, _elseInvariant, elseTyping,
      elseAgreement⟩ := elseSound elseInputInvariant elseSuccess
  subst result
  have elseExtension : outer.SemanticallyExtends
      elseResult.state.inference.substitution := by
    change outer.SemanticallyExtends
      elseResult.state.inference.substitution at outerExtension
    exact outerExtension
  have restoredExtension : outer.SemanticallyExtends
      (thenResult.state.restoreLexicalScope
        conditionState.lexicalScope).inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans elseExtension
      elseProperties.1.substitution_extends
  have conditionExtension : outer.SemanticallyExtends
      conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans restoredExtension
      restoredProperties.1.substitution_extends
  have conditionEq : outer.apply inferredCondition.type = .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess
      conditionExtension
  refine ⟨{
      type := if thenFacts.sawReturn && elseFacts.sawReturn then
        outer.apply expectedReturn
      else
        .unit
      hasValue := thenFacts.sawReturn && elseFacts.sawReturn
      sawReturn := thenFacts.sawReturn && elseFacts.sawReturn
      control := thenFacts.control.branches elseFacts.control
    }, conditionInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact ifWithElseStatementHasType_afterSubstitution contains
      conditionTyping conditionEq thenTyping elseTyping thenAgreement
      elseAgreement elseExtension
  · exact StatementResultMatchesFactsAfterSubstitution.ifWithElse
      thenAgreement elseAgreement elseExtension id _

/-- A successful default-free match is compositional modulo semantic typing
of the common scrutinee step, explicit cases, and the accepted exhaustiveness
certificate.  The case callback also supplies the nonempty control merge that
is not implied by inference success for arbitrary parser-independent ASTs. -/
theorem inferStatementFuel_success_matchWithoutDefault_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (scrutineeSound :
      ∀ {scrutinee : InferredExpression}
        {scrutineeState : Frontend.SourceInference.State},
        inferMatchScrutineesFuel fuel inferenceContext statement.span
            scrutinees.elements.toList allocated =
              .ok (scrutinee, scrutineeState) →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target scrutinee.id (outer.apply scrutinee.type))
    (casesSound :
      ∀ {scrutinee : InferredExpression}
        {hiddenState : Frontend.SourceInference.State}
        {checked : Detail.MatchCasesResult},
        ActiveLocalContextInvariant hiddenState outer target →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target scrutinee.id (outer.apply scrutinee.type) →
          Detail.inferMatchCasesFuel fuel inferenceContext scrutinee.type
              expectedReturn hiddenState.lexicalScope arms.value.cases
              hiddenState = .ok checked →
            ∃ caseFacts summary,
              MatchCasesHaveType
                ((result.state.toTypedSource roots).applySubstitution outer) {
                  returnType := outer.apply expectedReturn
                  loopDepth := inferenceContext.loopDepth
                } target (outer.apply scrutinee.type)
                (checked.cases.map
                  (TypedMatchCase.applySubstitution outer)) caseFacts ∧
              allBodiesSawReturn caseFacts = checked.allReturn ∧
              mergeBodyControls caseFacts none = some summary)
    (exhaustivenessSound :
      ∀ {scrutinee : InferredExpression}
        {scrutineeState hiddenState : Frontend.SourceInference.State}
        {checked : Detail.MatchCasesResult} {nominallyExhaustive : Bool},
        inferMatchScrutineesFuel fuel inferenceContext statement.span
            scrutinees.elements.toList allocated =
              .ok (scrutinee, scrutineeState) →
          Detail.inferMatchCasesFuel fuel inferenceContext scrutinee.type
              expectedReturn hiddenState.lexicalScope arms.value.cases
              hiddenState = .ok checked →
          (checked.hasWildcard || false || nominallyExhaustive) = true →
          MatchExhaustive target (outer.apply scrutinee.type)
            (checked.cases.map
              (TypedMatchCase.applySubstitution outer)) none) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      nominallyExhaustive, scrutineeSuccess, hiddenAllocation, casesSuccess,
      guardPassed, resultEq, contains⟩ :=
    inferStatementFuel_success_matchWithoutDefault_facts statementEq defaultEq
      allocationEq success roots
  have scrutineeInvariant :
      ActiveLocalContextInvariant scrutineeState outer target :=
    allocatedInvariant.inferMatchScrutineesFuel scrutineeSuccess
  have hiddenInvariant :
      ActiveLocalContextInvariant hiddenState outer target :=
    scrutineeInvariant.allocateHiddenLocal hiddenAllocation
  have checkedInvariant :
      ActiveLocalContextInvariant checked.state outer target :=
    hiddenInvariant.inferMatchCasesFuel casesSuccess
  have scrutineeTyping := scrutineeSound scrutineeSuccess
  obtain ⟨caseFacts, summary, casesTyping, allReturnEq, merged⟩ :=
    casesSound hiddenInvariant scrutineeTyping casesSuccess
  have exhaustive := exhaustivenessSound scrutineeSuccess casesSuccess
    guardPassed
  subst result
  have checkedExtension : outer.SemanticallyExtends
      checked.state.inference.substitution := by
    change outer.SemanticallyExtends checked.state.inference.substitution at outerExtension
    exact outerExtension
  refine ⟨{
      type := if allBodiesSawReturn caseFacts then
        outer.apply expectedReturn
      else
        .unit
      hasValue := allBodiesSawReturn caseFacts
      sawReturn := allBodiesSawReturn caseFacts
      control := summary.eraseValue
    }, checkedInvariant.recordNode _, ?_, ?_⟩
  · exact matchWithoutDefaultStatementHasType_afterSubstitution contains
      scrutineeTyping casesTyping exhaustive allReturnEq merged
      checkedExtension
  · exact StatementResultMatchesFactsAfterSubstitution.matchWithoutDefault
      allReturnEq checkedExtension id _

/-- A successful match with a fallback arm is compositional modulo semantic
typing of the common scrutinee, explicit cases, and fallback statement list.
The fallback makes both exhaustiveness and body-control merging total. -/
theorem inferStatementFuel_success_matchWithDefault_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {defaultBody : Syntax.Block}
    {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value = .matchWith scrutinees arms)
    (defaultEq : arms.value.defaultBody = some defaultBody)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (scrutineeSound :
      ∀ {scrutinee : InferredExpression}
        {scrutineeState : Frontend.SourceInference.State},
        inferMatchScrutineesFuel fuel inferenceContext statement.span
            scrutinees.elements.toList allocated =
              .ok (scrutinee, scrutineeState) →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target scrutinee.id (outer.apply scrutinee.type))
    (casesSound :
      ∀ {scrutinee : InferredExpression}
        {hiddenState : Frontend.SourceInference.State}
        {checked : Detail.MatchCasesResult},
        ActiveLocalContextInvariant hiddenState outer target →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target scrutinee.id (outer.apply scrutinee.type) →
          Detail.inferMatchCasesFuel fuel inferenceContext scrutinee.type
              expectedReturn hiddenState.lexicalScope arms.value.cases
              hiddenState = .ok checked →
            ∃ caseFacts,
              MatchCasesHaveType
                ((result.state.toTypedSource roots).applySubstitution outer) {
                  returnType := outer.apply expectedReturn
                  loopDepth := inferenceContext.loopDepth
                } target (outer.apply scrutinee.type)
                (checked.cases.map
                  (TypedMatchCase.applySubstitution outer)) caseFacts ∧
              allBodiesSawReturn caseFacts = checked.allReturn)
    (defaultSound :
      ∀ {checked : Detail.MatchCasesResult}
        {defaultResult : Detail.BlockResult},
        ActiveLocalContextInvariant checked.state outer target →
          Detail.inferStatementsFuel fuel inferenceContext defaultBody.value
              expectedReturn checked.state = .ok defaultResult →
            ∃ defaultFinal defaultFacts,
              ActiveLocalContextInvariant defaultResult.state outer
                  defaultFinal ∧
              StatementsHaveType
                ((result.state.toTypedSource roots).applySubstitution outer) {
                  returnType := outer.apply expectedReturn
                  loopDepth := inferenceContext.loopDepth
                } target defaultResult.statements defaultFinal defaultFacts ∧
              BlockResultMatchesFactsAfterSubstitution outer defaultResult
                defaultFacts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  obtain ⟨scrutinee, scrutineeState, hiddenScrutinee, hiddenState, checked,
      defaultResult, scrutineeSuccess, hiddenAllocation, casesSuccess,
      defaultSuccess, _guardPassed, resultEq, contains⟩ :=
    inferStatementFuel_success_matchWithDefault_facts statementEq defaultEq
      allocationEq success roots
  have scrutineeInvariant :
      ActiveLocalContextInvariant scrutineeState outer target :=
    allocatedInvariant.inferMatchScrutineesFuel scrutineeSuccess
  have hiddenInvariant :
      ActiveLocalContextInvariant hiddenState outer target :=
    scrutineeInvariant.allocateHiddenLocal hiddenAllocation
  have checkedInvariant :
      ActiveLocalContextInvariant checked.state outer target :=
    hiddenInvariant.inferMatchCasesFuel casesSuccess
  have scrutineeTyping := scrutineeSound scrutineeSuccess
  obtain ⟨caseFacts, casesTyping, caseReturnEq⟩ :=
    casesSound hiddenInvariant scrutineeTyping casesSuccess
  obtain ⟨defaultFinal, defaultFacts, _defaultInvariant, defaultTyping,
      defaultAgreement⟩ := defaultSound checkedInvariant defaultSuccess
  obtain ⟨summary, merged⟩ :=
    mergeBodyControls_withDefault_eq_some caseFacts defaultFacts
  subst result
  have defaultExtension : outer.SemanticallyExtends
      defaultResult.state.inference.substitution := by
    change outer.SemanticallyExtends
      defaultResult.state.inference.substitution at outerExtension
    exact outerExtension
  refine ⟨{
      type := if allBodiesSawReturn caseFacts && defaultFacts.sawReturn then
        outer.apply expectedReturn
      else
        .unit
      hasValue := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      sawReturn := allBodiesSawReturn caseFacts && defaultFacts.sawReturn
      control := summary.eraseValue
    }, hiddenInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact matchWithDefaultStatementHasType_afterSubstitution contains
      scrutineeTyping casesTyping defaultTyping caseReturnEq defaultAgreement
      merged defaultExtension
  · exact StatementResultMatchesFactsAfterSubstitution.matchWithDefault
      caseReturnEq defaultAgreement defaultExtension id _

/-- Uniform conditional obligations used by the restricted `for`-header
dispatchers below.  Every callback is indexed by the active semantic context
and its matching executable-local invariant, so a source-ordered item list can
extend the context after a declaration.  This bundle deliberately assumes
typing for every supplied successful child computation in one already chosen
eventual source; it does not itself prove that the child belongs to that
source.  Discharging that provenance boundary is a later deep-recursion step. -/
structure ForItemInferenceSoundnessCallbacks
    (inferenceContext : Frontend.SourceInference.Context)
    (source : TypedSource) (outer : TypeSystem.Substitution) : Prop where
  unannotatedInitializedLet :
    ∀ {childFuel : Nat} {semanticContext : SourceSemantics.Context}
      {initial : Frontend.SourceInference.State}
      {name : Syntax.Identifier} {initializer : Syntax.Expr}
      {inferred : InferredExpression}
      {initializerState : Frontend.SourceInference.State}
      {locals : TypeSystem.Environment} {valueType : TypeSystem.Ty}
      {generalized : Detail.GeneralizedValue}
      {binding : TypedBinder × Frontend.SourceInference.State},
      ActiveLocalContextInvariant initial outer semanticContext →
      Detail.inferExprFuel childFuel inferenceContext initializer none initial =
        .ok (inferred, initializerState) →
      locals = initializerState.binderEnvironment.apply
        initializerState.inference.substitution →
      valueType = initializerState.resolve inferred.type →
      generalized = Detail.generalizeValue initializerState locals
        initial.nextRequirement valueType →
      (initializerState.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false generalized.requirements =
          binding →
      UnannotatedInitializedLetCertificate source semanticContext outer
        binding.1 inferred.id
  expression :
    ∀ {childFuel : Nat} {semanticContext : SourceSemantics.Context}
      {expression : Syntax.Expr} {expected : Option TypeSystem.Ty}
      {initial final : Frontend.SourceInference.State}
      {inferred : InferredExpression},
      ActiveLocalContextInvariant initial outer semanticContext →
      Detail.inferExprFuel childFuel inferenceContext expression expected initial =
        .ok (inferred, final) →
      ExpressionHasType (source.applySubstitution outer) semanticContext
        inferred.id (outer.apply inferred.type)
  assignedValue :
    ∀ {childFuel : Nat} {semanticContext : SourceSemantics.Context}
      {targetExpression value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp}
      {initial final : Frontend.SourceInference.State}
      {assignment : AssignmentResolution}
      {inferredValue : InferredExpression},
      initial.InferenceReady →
      ActiveLocalContextInvariant initial outer semanticContext →
      outer.SemanticallyExtends final.inference.substitution →
      Detail.inferAssignedValueFuel childFuel inferenceContext targetExpression
          operator value initial = .ok (assignment, inferredValue, final) →
      SourceAssignmentHasType (source.applySubstitution outer)
        semanticContext (assignment.applySubstitution outer) operator
        inferredValue.id
  place :
    ∀ {childFuel : Nat} {semanticContext : SourceSemantics.Context}
      {targetExpression : Syntax.Expr}
      {initial final : Frontend.SourceInference.State}
      {place : PlaceResolution},
      initial.InferenceReady →
      ActiveLocalContextInvariant initial outer semanticContext →
      outer.SemanticallyExtends final.inference.substitution →
      Detail.inferPlaceFuel childFuel inferenceContext targetExpression initial =
        .ok (place, final) →
      SourcePlaceHasType (source.applySubstitution outer) semanticContext
        (place.applySubstitution outer) (outer.apply place.type)

/-- Uniform callback evidence available in an intermediate typed source
remains valid after later inference appends nodes.  This transports an already
discharged callback boundary; it does not establish the child/source
provenance needed to construct that boundary. -/
theorem ForItemInferenceSoundnessCallbacks.weakenSource
    {inferenceContext : Frontend.SourceInference.Context}
    {before after : TypedSource} {outer : TypeSystem.Substitution}
    (extension : TypingSourceExtends before after)
    (callbacks : ForItemInferenceSoundnessCallbacks inferenceContext before
      outer) :
    ForItemInferenceSoundnessCallbacks inferenceContext after outer := by
  let appliedExtension := extension.applySubstitution outer
  constructor
  · intro childFuel semanticContext initial name initializer inferred
      initializerState locals valueType generalized binding invariant success
      localsEq valueTypeEq generalizedEq bindingEq
    have certificate := callbacks.unannotatedInitializedLet invariant success
      localsEq valueTypeEq generalizedEq bindingEq
    exact {
      initializer_type := ExpressionHasType.weakenSource appliedExtension
        certificate.initializer_type
      requirements_well_formed := certificate.requirements_well_formed
      generalizes := certificate.generalizes
      quantified_fresh := certificate.quantified_fresh
    }
  · intro childFuel semanticContext expression expected initial final
      inferred invariant success
    exact ExpressionHasType.weakenSource appliedExtension
      (callbacks.expression invariant success)
  · intro childFuel semanticContext targetExpression value operator initial
      final assignment inferredValue ready invariant outerExtension success
    exact SourceAssignmentHasType.weakenSource appliedExtension
      (callbacks.assignedValue ready invariant outerExtension success)
  · intro childFuel semanticContext targetExpression initial final place
      ready invariant outerExtension success
    exact SourcePlaceHasType.weakenSource appliedExtension
      (callbacks.place ready invariant outerExtension success)

private theorem forItemHasType_context_fields
    {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {item : ForItemForm}
    (typing : ForItemHasType source control context item final) :
    final.signatures = context.signatures ∧
      final.typeParameters = context.typeParameters ∧
      final.currentDeclaration = context.currentDeclaration := by
  cases typing with
  | letUninitialized _ _ extension =>
      exact ⟨extension.context_fields.1, extension.context_fields.2.2.1,
        extension.context_fields.2.1⟩
  | letInitialized _ _ _ extension =>
      exact ⟨extension.context_fields.1, extension.context_fields.2.2.1,
        extension.context_fields.2.1⟩
  | letInitializedGeneralized _ _ _ _ extension =>
      exact ⟨extension.context_fields.1, extension.context_fields.2.2.1,
        extension.context_fields.2.1⟩
  | expression | assignValue | assignBitNot => exact ⟨rfl, rfl, rfl⟩

/-- Install the generalized binder produced by an unannotated initialized
`for` item.  This is the node-free counterpart of the ordinary statement
wrapper: the semantic certificate supplies the genuine generalization facts,
while allocation alignment supplies the final lexical context. -/
private theorem unannotatedInitializedForItemHasType_afterSubstitution
    {source : TypedSource} {outer : TypeSystem.Substitution}
    {control : ControlContext} {target : SourceSemantics.Context}
    {name : Syntax.Identifier} {initializer : ExpressionId}
    {state final : Frontend.SourceInference.State}
    {requirementStart : Nat}
    {locals : TypeSystem.Environment} {valueType : TypeSystem.Ty}
    {generalized : Detail.GeneralizedValue} {binder : TypedBinder}
    (generalized_eq : generalized = Detail.generalizeValue state locals
      requirementStart valueType)
    (allocated : (state.withLocals locals).allocateBinder name.value
      generalized.scheme (some name.span) false generalized.requirements =
        (binder, final))
    (invariant : ActiveLocalContextInvariant state outer target)
    (below : state.LocalBindersBelowNextLocal)
    (sourceOwner : source.owner = state.owner)
    (certificate : UnannotatedInitializedLetCertificate source target outer
      binder initializer) :
    ∃ finalContext,
      ActiveLocalContextInvariant final outer finalContext ∧
      ForItemHasType (source.applySubstitution outer) control target
        (.letDecl (binder.applySubstitution outer) (some initializer))
        finalContext := by
  have binderEq :
      ((state.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false
        generalized.requirements).1 = binder :=
    congrArg Prod.fst allocated
  have rawSchemeEq : binder.scheme = generalized.scheme := by
    rw [← binderEq]
    rfl
  have rawRequirementsEq :
      binder.schemeRequirements = generalized.requirements := by
    rw [← binderEq]
    rfl
  have rawQuantifiedNodup : binder.scheme.quantified.Nodup := by
    rw [rawSchemeEq, generalized_eq]
    exact Detail.generalizeValue_scheme_quantified_nodup state locals
      requirementStart valueType
  have closedQuantifiedNodup :
      (binder.applySubstitution outer).scheme.quantified.Nodup := by
    simpa using rawQuantifiedNodup
  have schemeWellFormed : SchemeWellFormed target
      (binder.applySubstitution outer).scheme :=
    StructuralSubstitution.SchemeWellFormed.ofLocalSchemeInitializerAdmissible
      certificate.initializer_type.type_admissible closedQuantifiedNodup
  have monomorphicRequirementsEmpty :
      (binder.applySubstitution outer).scheme.quantified = [] →
        (binder.applySubstitution outer).schemeRequirements = [] := by
    intro closedQuantifiedEmpty
    have rawQuantifiedEmpty : binder.scheme.quantified = [] := by
      simpa using closedQuantifiedEmpty
    have generalizedQuantifiedEmpty : generalized.scheme.quantified = [] := by
      rw [← rawSchemeEq]
      exact rawQuantifiedEmpty
    have canonicalQuantifiedEmpty :
        (Detail.generalizeValue state locals requirementStart
          valueType).scheme.quantified = [] := by
      rw [← generalized_eq]
      exact generalizedQuantifiedEmpty
    have canonicalRequirementsEmpty :=
      Detail.generalizeValue_requirements_empty_of_quantified_eq_nil state
        locals requirementStart valueType canonicalQuantifiedEmpty
    have generalizedRequirementsEmpty : generalized.requirements = [] := by
      rw [generalized_eq]
      exact canonicalRequirementsEmpty
    have rawRequirementsEmpty : binder.schemeRequirements = [] := by
      rw [rawRequirementsEq, generalizedRequirementsEmpty]
    simp [rawRequirementsEmpty]
  let finalContext := target.withLocal binder.id
    (binder.applySubstitution outer).scheme
    (binder.applySubstitution outer).schemeRequirements
  have finalInvariant : ActiveLocalContextInvariant final outer
      finalContext := by
    exact (invariant.withLocals locals)
      |>.allocateBinder_of_localBindersBelowNextLocal name.value
        generalized.scheme (some name.span) false generalized.requirements
        allocated
        (Frontend.SourceInference.State.withLocals_preserves_localBindersBelowNextLocal
          state locals below)
        schemeWellFormed certificate.requirements_well_formed
  have extended : BinderExtends source.owner target
      (binder.applySubstitution outer) finalContext := by
    have rawExtension : BinderExtends (state.withLocals locals).owner target
        (binder.applySubstitution outer) finalContext :=
      (invariant.aligned.withLocals locals)
        |>.binderExtends_of_allocateBinder
          (Frontend.SourceInference.State.withLocals_preserves_localBindersBelowNextLocal
            state locals below)
          allocated schemeWellFormed certificate.quantified_fresh
          monomorphicRequirementsEmpty
    rw [sourceOwner]
    simpa [Frontend.SourceInference.State.withLocals] using rawExtension
  refine ⟨finalContext, finalInvariant, ?_⟩
  by_cases monomorphic :
      (binder.applySubstitution outer).scheme.quantified = []
  · have requirementsEmpty := monomorphicRequirementsEmpty monomorphic
    have initializerContextEq :
        localSchemeInitializerContext target
            (binder.applySubstitution outer) = target := by
      rw [localSchemeInitializerContext_eq_withTypeVariables target _
        requirementsEmpty, monomorphic]
      exact SourceSemantics.Context.withTypeVariables_nil target
    have initializerType : ExpressionHasType
        (source.applySubstitution outer) target initializer
        (binder.applySubstitution outer).scheme.body := by
      simpa only [initializerContextEq] using certificate.initializer_type
    have generalizes : SchemeGeneralizes target
        (binder.applySubstitution outer).scheme := by
      have exactGeneralizes := certificate.generalizes
      have templateIdsEmpty : localSchemeTemplateIds
          (binder.applySubstitution outer) = [] :=
        localSchemeTemplateIds_eq_nil _ requirementsEmpty
      rw [templateIdsEmpty] at exactGeneralizes
      exact (SchemeGeneralizesExcept_nil target _).mp exactGeneralizes
    exact .letInitialized initializerType monomorphic generalizes extended
  · exact .letInitializedGeneralized monomorphic
      certificate.requirements_well_formed certificate.generalizes
      certificate.initializer_type extended

/-- Successful inference of one restricted `for` item reconstructs its
declarative typing in an eventual common typed source and advances the active
semantic local context exactly when the item declares a binder. -/
theorem inferForItemFuel_success_forItemHasType_of_callbacks
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {item : Syntax.ForItem}
    {initial final : Frontend.SourceInference.State}
    {inferred : ForItemForm} {source : TypedSource}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical :
      ∀ signature ∈ inferenceContext.signatures.functions,
        signature.scheme.body = .function
          (TypeSystem.Ty.productMany signature.parameterTypes)
          (TypeSystem.Ty.productMany signature.returnTypes))
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (parameters_eq : target.typeParameters = inferenceContext.typeParameters)
    (declaration_eq : target.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (below : initial.LocalBindersBelowNextLocal)
    (sourceOwner : source.owner = initial.owner)
    (outerExtension : outer.SemanticallyExtends
      final.inference.substitution)
    (callbacks : ForItemInferenceSoundnessCallbacks inferenceContext
      source outer)
    (success : Detail.inferForItemFuel fuel inferenceContext item initial =
      .ok (inferred, final)) :
    ∃ finalContext,
      ActiveLocalContextInvariant final outer finalContext ∧
      ForItemHasType (source.applySubstitution outer) control target
        (inferred.applySubstitution outer) finalContext := by
  have ownerPreserved :=
    Detail.inferForItemFuel_preserves_owner success
  cases fuel with
  | zero => simp [Detail.inferForItemFuel] at success
  | succ fuel =>
      cases itemEq : item.value with
      | letDecl name sourceType initializer =>
          unfold Detail.inferForItemFuel at success
          simp only [itemEq, bind, Except.bind] at success
          cases sourceType with
          | none =>
              cases initializer with
              | none => simp at success
              | some initializer =>
                  cases initializerResult : Detail.inferExprFuel fuel
                      inferenceContext initializer none initial with
                  | error error => simp [initializerResult] at success
                  | ok initializerPair =>
                      rcases initializerPair with
                        ⟨inferredInitializer, initializerState⟩
                      simp only [initializerResult, pure, Pure.pure,
                        Except.pure] at success
                      let locals := initializerState.binderEnvironment.apply
                        initializerState.inference.substitution
                      let valueType :=
                        initializerState.resolve inferredInitializer.type
                      let generalized := Detail.generalizeValue
                        initializerState locals initial.nextRequirement
                        valueType
                      let binding :=
                        (initializerState.withLocals locals).allocateBinder
                          name.value generalized.scheme (some name.span) false
                          generalized.requirements
                      injection success with resultEq
                      injection resultEq with inferredEq finalEq
                      subst inferred
                      subst final
                      have initializerInvariant :
                          ActiveLocalContextInvariant initializerState outer
                            target :=
                        invariant.inferExprFuel initializerResult
                      have initializerBelow :
                          initializerState.LocalBindersBelowNextLocal :=
                        Detail.inferExprFuel_preserves_localBindersBelowNextLocal
                          below initializerResult
                      have certificate :=
                        callbacks.unannotatedInitializedLet
                          (name := name) (binding := binding) invariant
                          initializerResult rfl rfl rfl rfl
                      have initializerOwner :
                          source.owner = initializerState.owner := by
                        calc
                          source.owner = initial.owner := sourceOwner
                          _ = binding.2.owner := ownerPreserved.symm
                          _ = initializerState.owner := by rfl
                      exact
                        unannotatedInitializedForItemHasType_afterSubstitution
                          (control := control) (name := name)
                          (initializer := inferredInitializer.id)
                          (requirementStart := initial.nextRequirement)
                          (generalized_eq := rfl)
                          (allocated := rfl) initializerInvariant
                          initializerBelow initializerOwner certificate
          | some sourceType =>
              cases initializer with
              | none =>
                  cases resolution : Detail.resolveSourceType inferenceContext
                      sourceType with
                  | error error => simp [resolution] at success
                  | ok resolvedType =>
                      simp only [resolution, pure, Pure.pure, Except.pure]
                        at success
                      let locals := initial.binderEnvironment.apply
                        initial.inference.substitution
                      let valueType := initial.resolve resolvedType
                      let generalized := Detail.generalizeValue initial locals
                        initial.nextRequirement valueType
                      let binding :=
                        (initial.withLocals locals).allocateBinder name.value
                          generalized.scheme (some name.span) false
                          generalized.requirements
                      injection success with resultEq
                      injection resultEq with inferredEq finalEq
                      subst inferred
                      subst final
                      obtain ⟨typeWellFormed, closedSchemeEq,
                          closedRequirementsEq, generalizes⟩ :=
                        resolvedAnnotationBinderFacts_afterSubstitution
                          (target := target) (outer := outer)
                          (inferenceContext := inferenceContext)
                          (name := name) (sourceType := sourceType)
                          (state := initial) (final := binding.2)
                          (requirementStart := initial.nextRequirement)
                          (resolvedType := resolvedType)
                          (valueType := valueType) (locals := locals)
                          (generalized := generalized) (binder := binding.1)
                          resolution rfl rfl rfl canonical signatures_eq
                          parameters_eq declaration_eq
                      let finalContext := target.withLocal binding.1.id
                        (binding.1.applySubstitution outer).scheme
                        (binding.1.applySubstitution outer).schemeRequirements
                      have finalInvariant : ActiveLocalContextInvariant
                          binding.2 outer finalContext :=
                        resolvedAnnotationBinderPreservesActiveLocalContextInvariant_afterSubstitution
                          (target := target) (outer := outer)
                          (inferenceContext := inferenceContext)
                          (name := name) (sourceType := sourceType)
                          (state := initial) (final := binding.2)
                          (requirementStart := initial.nextRequirement)
                          (resolvedType := resolvedType)
                          (valueType := valueType) (locals := locals)
                          (generalized := generalized) (binder := binding.1)
                          resolution rfl rfl rfl canonical signatures_eq
                          parameters_eq declaration_eq invariant below
                      have rawExtension : BinderExtends
                          (initial.withLocals locals).owner target
                          (binding.1.applySubstitution outer) finalContext := by
                        apply (invariant.aligned.withLocals locals)
                          |>.monomorphicBinderExtends_of_allocateBinder
                            (Frontend.SourceInference.State.withLocals_preserves_localBindersBelowNextLocal
                              initial locals below)
                            rfl closedSchemeEq closedRequirementsEq
                            typeWellFormed
                      have semanticExtension : BinderExtends source.owner
                          target (binding.1.applySubstitution outer)
                          finalContext := by
                        rw [sourceOwner]
                        simpa [Frontend.SourceInference.State.withLocals]
                          using rawExtension
                      refine ⟨finalContext, finalInvariant, ?_⟩
                      have monomorphic :
                          (binding.1.applySubstitution outer).scheme.quantified =
                            [] := by
                        rw [closedSchemeEq]
                        rfl
                      exact .letUninitialized monomorphic generalizes
                        semanticExtension
              | some initializer =>
                  cases resolution : Detail.resolveSourceType inferenceContext
                      sourceType with
                  | error error => simp [resolution] at success
                  | ok resolvedType =>
                      simp only [resolution] at success
                      cases initializerResult : Detail.inferExprFuel fuel
                          inferenceContext initializer (some resolvedType)
                          initial with
                      | error error => simp [initializerResult] at success
                      | ok initializerPair =>
                          rcases initializerPair with
                            ⟨inferredInitializer, initializerState⟩
                          simp only [initializerResult, pure,
                            Pure.pure, Except.pure] at success
                          let locals :=
                            initializerState.binderEnvironment.apply
                              initializerState.inference.substitution
                          let valueType := initializerState.resolve
                            inferredInitializer.type
                          let generalized := Detail.generalizeValue
                            initializerState locals initial.nextRequirement
                            valueType
                          let binding :=
                            (initializerState.withLocals locals).allocateBinder
                              name.value generalized.scheme (some name.span)
                              false generalized.requirements
                          injection success with resultEq
                          injection resultEq with inferredEq finalEq
                          subst inferred
                          subst final
                          have resolvedBelow : resolvedType.VariablesBelow
                              initial.inference.next :=
                            Detail.resolveSourceType_success_variablesBelow
                              resolution _
                          have initializerProperties :=
                            Detail.inferExprFuel_inferenceProperties ready
                              signatureFormation functionsCanonical (by
                                intro expected member
                                simp only [Option.mem_def] at member
                                injection member with typeEq
                                subst expected
                                exact resolvedBelow) initializerResult
                          have initializerInvariant :
                              ActiveLocalContextInvariant initializerState
                                outer target :=
                            invariant.inferExprFuel initializerResult
                          have initializerBelow :
                              initializerState.LocalBindersBelowNextLocal :=
                            Detail.inferExprFuel_preserves_localBindersBelowNextLocal
                              below initializerResult
                          have rawExpected :
                              initializerState.resolve inferredInitializer.type =
                                initializerState.resolve resolvedType :=
                            inferExprFuel_success_expected_type_afterProgress
                              initializerResult
                              (Frontend.SourceInference.State.InferenceProgress.refl
                                initializerProperties.2.1.solved)
                          obtain ⟨typeWellFormed, closedSchemeEq,
                              closedRequirementsEq, generalizes⟩ :=
                            resolvedAnnotationBinderFacts_afterSubstitution
                              (target := target) (outer := outer)
                              (inferenceContext := inferenceContext)
                              (name := name) (sourceType := sourceType)
                              (state := initializerState)
                              (final := binding.2)
                              (requirementStart := initial.nextRequirement)
                              (resolvedType := resolvedType)
                              (valueType := valueType) (locals := locals)
                              (generalized := generalized)
                              (binder := binding.1)
                              resolution rawExpected rfl rfl canonical
                              signatures_eq parameters_eq declaration_eq
                          have initializerExtension :
                              outer.SemanticallyExtends
                                initializerState.inference.substitution := by
                            simpa [binding, Frontend.SourceInference.State.withLocals,
                              Frontend.SourceInference.State.allocateBinder]
                              using outerExtension
                          have outerExpected : outer.apply
                              inferredInitializer.type =
                                outer.apply resolvedType :=
                            Detail.inferExprFuel_expected_type_apply_eq
                              initializerResult initializerExtension
                          have resolvedByOuter : outer.apply resolvedType =
                              resolvedType :=
                            Detail.resolveSourceType_success_apply_eq_self outer
                              resolution
                          have initializerTypeRaw := callbacks.expression
                            invariant initializerResult
                          have initializerType : ExpressionHasType
                              (source.applySubstitution outer) target
                              inferredInitializer.id
                              (binding.1.applySubstitution outer).scheme.body := by
                            rw [closedSchemeEq]
                            change ExpressionHasType
                              (source.applySubstitution outer) target
                              inferredInitializer.id resolvedType
                            rw [← resolvedByOuter, ← outerExpected]
                            exact initializerTypeRaw
                          let finalContext := target.withLocal binding.1.id
                            (binding.1.applySubstitution outer).scheme
                            (binding.1.applySubstitution outer).schemeRequirements
                          have finalInvariant : ActiveLocalContextInvariant
                              binding.2 outer finalContext :=
                            resolvedAnnotationBinderPreservesActiveLocalContextInvariant_afterSubstitution
                              (target := target) (outer := outer)
                              (inferenceContext := inferenceContext)
                              (name := name) (sourceType := sourceType)
                              (state := initializerState)
                              (final := binding.2)
                              (requirementStart := initial.nextRequirement)
                              (resolvedType := resolvedType)
                              (valueType := valueType) (locals := locals)
                              (generalized := generalized)
                              (binder := binding.1)
                              resolution rawExpected rfl rfl canonical
                              signatures_eq parameters_eq declaration_eq
                              initializerInvariant initializerBelow
                          have initializerOwner : source.owner =
                              initializerState.owner := by
                            calc
                              source.owner = initial.owner := sourceOwner
                              _ = binding.2.owner := ownerPreserved.symm
                              _ = initializerState.owner := by rfl
                          have rawExtension : BinderExtends
                              (initializerState.withLocals locals).owner target
                              (binding.1.applySubstitution outer)
                              finalContext := by
                            apply (initializerInvariant.aligned.withLocals locals)
                              |>.monomorphicBinderExtends_of_allocateBinder
                                (Frontend.SourceInference.State.withLocals_preserves_localBindersBelowNextLocal
                                  initializerState locals initializerBelow)
                                rfl closedSchemeEq closedRequirementsEq
                                typeWellFormed
                          have semanticExtension : BinderExtends source.owner
                              target (binding.1.applySubstitution outer)
                              finalContext := by
                            rw [initializerOwner]
                            simpa [Frontend.SourceInference.State.withLocals]
                              using rawExtension
                          refine ⟨finalContext, finalInvariant, ?_⟩
                          have monomorphic :
                              (binding.1.applySubstitution outer).scheme.quantified =
                                [] := by
                            rw [closedSchemeEq]
                            rfl
                          exact .letInitialized initializerType monomorphic
                            generalizes semanticExtension
      | expression expression =>
          unfold Detail.inferForItemFuel at success
          simp only [itemEq, bind, Except.bind] at success
          cases expressionResult : Detail.inferExprFuel fuel inferenceContext
              expression none initial with
          | error error => simp [expressionResult] at success
          | ok expressionPair =>
              rcases expressionPair with ⟨inferredExpression, expressionState⟩
              simp only [expressionResult, pure, Pure.pure,
                Except.pure] at success
              injection success with resultEq
              injection resultEq with inferredEq finalEq
              subst inferred
              subst final
              exact ⟨target, invariant.inferExprFuel expressionResult,
                .expression (callbacks.expression invariant expressionResult)⟩
      | assignValue targetExpression operator value =>
          unfold Detail.inferForItemFuel at success
          simp only [itemEq, bind, Except.bind] at success
          cases assignmentResult : Detail.inferAssignedValueFuel fuel
              inferenceContext targetExpression operator.value value initial with
          | error error => simp [assignmentResult] at success
          | ok assignmentTriple =>
              rcases assignmentTriple with
                ⟨assignment, inferredValue, assignmentState⟩
              simp only [assignmentResult, pure, Pure.pure,
                Except.pure] at success
              injection success with resultEq
              injection resultEq with inferredEq finalEq
              subst inferred
              subst final
              exact ⟨target, invariant.inferAssignedValueFuel assignmentResult,
                .assignValue
                  (callbacks.assignedValue ready invariant outerExtension
                    assignmentResult)⟩
      | assignBitNot targetExpression operatorSpan =>
          unfold Detail.inferForItemFuel at success
          simp only [itemEq, bind, Except.bind] at success
          cases placeResult : Detail.inferPlaceFuel fuel inferenceContext
              targetExpression initial with
          | error error => simp [placeResult] at success
          | ok placePair =>
              rcases placePair with ⟨place, placeState⟩
              simp only [placeResult] at success
              cases unifyResult : Detail.unify placeState place.type .word with
              | error error => simp [unifyResult] at success
              | ok unifiedState =>
                  simp only [unifyResult, pure, Pure.pure, Except.pure]
                    at success
                  injection success with resultEq
                  injection resultEq with inferredEq finalEq
                  subst inferred
                  subst final
                  have placeProperties :=
                    Detail.inferPlaceFuel_inferenceProperties ready
                      signatureFormation functionsCanonical placeResult
                  have unifyProgress := Detail.unify_inferenceProgress
                    placeProperties.2.1.solved placeProperties.2.2
                    (TypeSystem.Ty.variablesBelow_constructor _ _) unifyResult
                  have placeExtension : outer.SemanticallyExtends
                      placeState.inference.substitution :=
                    TypeSystem.Substitution.SemanticallyExtends.trans
                      outerExtension unifyProgress.substitution_extends
                  have placeType := callbacks.place ready invariant
                    placeExtension placeResult
                  have resolvedWord :
                      unifiedState.resolve place.type = .word :=
                    (Detail.unify_resolve_eq unifyResult).trans (by rfl)
                  have resolvedFinal : outer.apply
                      (unifiedState.resolve place.type) =
                        outer.apply place.type := by
                    simpa [Frontend.SourceInference.State.resolve,
                      TypeSystem.InferState.resolve] using
                        outerExtension place.type
                  have placeWord : outer.apply place.type = .word := by
                    rw [← resolvedFinal, resolvedWord]
                    rfl
                  have storedPlaceEq :
                      ({ place with type := unifiedState.resolve place.type } :
                        PlaceResolution).applySubstitution outer =
                          place.applySubstitution outer := by
                    cases place
                    simp [PlaceResolution.applySubstitution, resolvedFinal]
                  have assignmentType : SourceBitNotAssignmentValid
                      (source.applySubstitution outer) target
                      (({ target := { place with
                        type := unifiedState.resolve place.type } } :
                          AssignmentResolution).applySubstitution outer) := by
                    apply SourceBitNotAssignmentValid.intro
                    · change SourcePlaceHasType
                        (source.applySubstitution outer) target
                        (({ place with
                          type := unifiedState.resolve place.type } :
                            PlaceResolution).applySubstitution outer) .word
                      rw [storedPlaceEq, ← placeWord]
                      exact placeType
                    · rfl
                  exact ⟨target, (invariant.inferPlaceFuel placeResult).unify
                    unifyResult, .assignBitNot assignmentType⟩

/-- Source-ordered `for`-item inference composes the single-item callback
dispatcher, threading both executable and declarative lexical contexts.  All
items are typed in the same eventual source; the final substitution is
transported back across the tail's monotone inference progress before typing
the head. -/
theorem inferForItemsFuel_success_forItemsHaveType_of_callbacks
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {items : List Syntax.ForItem}
    {initial : Frontend.SourceInference.State}
    {result : Detail.InferredForItems} {source : TypedSource}
    {outer : TypeSystem.Substitution} {control : ControlContext}
    {target : SourceSemantics.Context}
    (ready : initial.InferenceReady)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical :
      ∀ signature ∈ inferenceContext.signatures.functions,
        signature.scheme.body = .function
          (TypeSystem.Ty.productMany signature.parameterTypes)
          (TypeSystem.Ty.productMany signature.returnTypes))
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (parameters_eq : target.typeParameters = inferenceContext.typeParameters)
    (declaration_eq : target.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (below : initial.LocalBindersBelowNextLocal)
    (sourceOwner : source.owner = initial.owner)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (callbacks : ForItemInferenceSoundnessCallbacks inferenceContext
      source outer)
    (success : Detail.inferForItemsFuel fuel inferenceContext items initial =
      .ok result) :
    ∃ finalContext,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      ForItemsHaveType (source.applySubstitution outer) control target
        (result.items.map (ForItemForm.applySubstitution outer))
        finalContext := by
  induction items generalizing initial result target with
  | nil =>
      simp only [Detail.inferForItemsFuel, pure, Pure.pure, Except.pure]
        at success
      injection success with resultEq
      subst result
      exact ⟨target, invariant, .nil control target⟩
  | cons item items induction =>
      unfold Detail.inferForItemsFuel at success
      cases itemResult : Detail.inferForItemFuel fuel inferenceContext item
          initial with
      | error error => simp [itemResult, bind, Except.bind] at success
      | ok itemPair =>
          rcases itemPair with ⟨inferredItem, itemState⟩
          simp only [itemResult, bind, Except.bind] at success
          cases tailResult : Detail.inferForItemsFuel fuel inferenceContext
              items itemState with
          | error error => simp [tailResult] at success
          | ok tail =>
              simp only [tailResult, pure, Pure.pure, Except.pure] at success
              injection success with resultEq
              subst result
              have itemProperties :=
                Detail.inferForItemFuel_inferenceProperties ready
                  signatureFormation functionsCanonical itemResult
              have tailProperties :=
                Detail.inferForItemsFuel_inferenceProperties
                  itemProperties.2 signatureFormation functionsCanonical
                  tailResult
              have itemExtension : outer.SemanticallyExtends
                  itemState.inference.substitution :=
                TypeSystem.Substitution.SemanticallyExtends.trans
                  outerExtension tailProperties.1.substitution_extends
              obtain ⟨middleContext, itemInvariant, itemTyping⟩ :=
                inferForItemFuel_success_forItemHasType_of_callbacks
                  (control := control)
                  ready signatureFormation functionsCanonical canonical
                  signatures_eq parameters_eq declaration_eq invariant below
                  sourceOwner itemExtension callbacks itemResult
              have fields := forItemHasType_context_fields itemTyping
              have tailBelow : itemState.LocalBindersBelowNextLocal :=
                Detail.inferForItemFuel_preserves_localBindersBelowNextLocal
                  below itemResult
              have tailSourceOwner : source.owner = itemState.owner :=
                sourceOwner.trans
                  (Detail.inferForItemFuel_preserves_owner itemResult).symm
              obtain ⟨finalContext, finalInvariant, tailTyping⟩ :=
                induction (initial := itemState) (result := tail)
                  (target := middleContext) itemProperties.2
                  (fields.1.trans signatures_eq)
                  (fields.2.1.trans parameters_eq)
                  (fields.2.2.trans declaration_eq) itemInvariant tailBelow
                  tailSourceOwner outerExtension tailResult
              refine ⟨finalContext, finalInvariant, ?_⟩
              exact .cons itemTyping tailTyping

/-- A successful `for` statement is compositional modulo recursive typing of
its initializer, condition, body, and post-item sequence in one finalized
typed source.  Executable scope restoration keeps all loop-local binders from
escaping the enclosing statement. -/
theorem inferStatementFuel_success_forLoop_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (roots : List NodeId := [])
    (initializerSound :
      ∀ {initializerResult : Detail.InferredForItems},
        Detail.inferForItemsFuel fuel inferenceContext initializer allocated =
            .ok initializerResult →
          ∃ loopContext,
            ActiveLocalContextInvariant initializerResult.state outer
                loopContext ∧
              ForItemsHaveType
                ((result.state.toTypedSource roots).applySubstitution outer) {
                  returnType := outer.apply expectedReturn
                  loopDepth := inferenceContext.loopDepth
                } target
                (initializerResult.items.map
                  (ForItemForm.applySubstitution outer)) loopContext)
    (conditionSound :
      ∀ {loopContext : SourceSemantics.Context}
        {initializerState conditionState : Frontend.SourceInference.State}
        {inferredCondition : InferredExpression},
        ActiveLocalContextInvariant initializerState outer loopContext →
          Detail.inferExprFuel fuel inferenceContext condition (some .bool)
              initializerState = .ok (inferredCondition, conditionState) →
            ExpressionHasType
              ((result.state.toTypedSource roots).applySubstitution outer)
              loopContext inferredCondition.id .bool)
    (bodySound :
      ∀ {loopContext : SourceSemantics.Context}
        {conditionState : Frontend.SourceInference.State}
        {bodyResult : Detail.BlockResult},
        ActiveLocalContextInvariant conditionState outer loopContext →
          Detail.inferStatementsFuel fuel {
              inferenceContext with
              loopDepth := inferenceContext.loopDepth + 1
            } body.value expectedReturn conditionState = .ok bodyResult →
            ∃ bodyFinal bodyFacts,
              ActiveLocalContextInvariant bodyResult.state outer bodyFinal ∧
                StatementsHaveType
                  ((result.state.toTypedSource roots).applySubstitution outer)
                  ({
                    returnType := outer.apply expectedReturn
                    loopDepth := inferenceContext.loopDepth
                  } : ControlContext).enterLoop loopContext
                  bodyResult.statements bodyFinal bodyFacts)
    (postSound :
      ∀ {loopContext : SourceSemantics.Context}
        {postInput : Frontend.SourceInference.State}
        {postResult : Detail.InferredForItems},
        ActiveLocalContextInvariant postInput outer loopContext →
          Detail.inferForItemsFuel fuel {
              inferenceContext with
              loopDepth := inferenceContext.loopDepth + 1
            } post postInput = .ok postResult →
            ∃ postContext,
              ActiveLocalContextInvariant postResult.state outer postContext ∧
                ForItemsHaveType
                  ((result.state.toTypedSource roots).applySubstitution outer)
                  ({
                    returnType := outer.apply expectedReturn
                    loopDepth := inferenceContext.loopDepth
                  } : ControlContext).enterLoop loopContext
                  (postResult.items.map (ForItemForm.applySubstitution outer))
                  postContext) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
      postResult, initializerSuccess, conditionSuccess, bodySuccess,
      postSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq success
      roots
  obtain ⟨loopContext, initializerInvariant, initializerTyping⟩ :=
    initializerSound initializerSuccess
  have conditionInvariant :
      ActiveLocalContextInvariant conditionState outer loopContext :=
    initializerInvariant.inferExprFuel conditionSuccess
  have conditionTyping :=
    conditionSound initializerInvariant conditionSuccess
  obtain ⟨bodyFinal, bodyFacts, _bodyInvariant, bodyTyping⟩ :=
    bodySound conditionInvariant bodySuccess
  have postInputInvariant : ActiveLocalContextInvariant
      (bodyResult.state.restoreLexicalScope
        initializerResult.state.lexicalScope) outer loopContext :=
    initializerInvariant.restoreLexicalScope
  obtain ⟨postContext, _postInvariant, postTyping⟩ :=
    postSound postInputInvariant postSuccess
  subst result
  refine ⟨{
      type := .unit
      hasValue := false
      sawReturn := false
      control := .loop bodyFacts.control
    }, allocatedInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact forLoopStatementHasType_afterSubstitution contains
      initializerTyping conditionTyping bodyTyping postTyping
  · exact StatementResultMatchesFactsAfterSubstitution.forLoop outer
      bodyFacts id _

/-- A successful `while` statement is compositional modulo condition and body
soundness in the common final typed source.  Executable and declarative loop
depths advance together for the body, and lexical restoration returns the
enclosing statement to its input semantic context. -/
theorem inferStatementFuel_success_whileLoop_sound
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (statementEq : statement.value = .whileLoop condition body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      Frontend.ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (ready : initial.InferenceReady)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (conditionSound :
      ∀ {inferredCondition : InferredExpression}
        {conditionState : Frontend.SourceInference.State},
        Detail.inferExprFuel fuel inferenceContext condition (some .bool)
            allocated = .ok (inferredCondition, conditionState) →
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution outer)
            target inferredCondition.id
            (outer.apply inferredCondition.type))
    (bodySound :
      ∀ {conditionState : Frontend.SourceInference.State}
        {bodyResult : Detail.BlockResult},
        ActiveLocalContextInvariant conditionState outer target →
          Detail.inferStatementsFuel fuel {
              inferenceContext with
              loopDepth := inferenceContext.loopDepth + 1
            } body.value expectedReturn conditionState = .ok bodyResult →
            ∃ bodyFinal bodyFacts,
              ActiveLocalContextInvariant bodyResult.state outer bodyFinal ∧
              StatementsHaveType
                ((result.state.toTypedSource roots).applySubstitution outer)
                ({
                  returnType := outer.apply expectedReturn
                  loopDepth := inferenceContext.loopDepth
                } : ControlContext).enterLoop target bodyResult.statements
                bodyFinal bodyFacts ∧
              BlockResultMatchesFactsAfterSubstitution outer bodyResult
                bodyFacts) :
    ∃ facts,
      ActiveLocalContextInvariant result.state outer target ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id target facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  have allocatedReady : allocated.InferenceReady := by
    have preserved :=
      Frontend.SourceInference.State.InferenceReady.allocateStatementId ready
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [finalEq] at preserved
    exact preserved
  have allocatedReturnBelow :
      expectedReturn.VariablesBelow allocated.inference.next := by
    have finalEq : (initial.allocateStatementId).2 = allocated :=
      congrArg Prod.snd allocationEq
    rw [← finalEq]
    exact returnBelow
  obtain ⟨inferredCondition, conditionState, bodyResult, conditionSuccess,
      bodySuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_whileLoop_facts statementEq allocationEq
      success roots
  have conditionProperties :=
    Detail.inferExprFuel_inferenceProperties allocatedReady signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [TypeSystem.Ty.bool]) conditionSuccess
  have conditionInvariant :
      ActiveLocalContextInvariant conditionState outer target :=
    allocatedInvariant.inferExprFuel conditionSuccess
  have conditionTyping := conditionSound conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedReturnBelow.weaken conditionProperties.1.next_le
  have bodyProperties :=
    Detail.inferStatementsFuel_inferenceProperties
      (context := {
        inferenceContext with
        loopDepth := inferenceContext.loopDepth + 1
      }) conditionProperties.2.1 signatureFormation functionsCanonical
      conditionReturnBelow bodySuccess
  obtain ⟨bodyFinal, bodyFacts, _bodyInvariant, bodyTyping,
      bodyAgreement⟩ := bodySound conditionInvariant bodySuccess
  subst result
  have bodyExtension : outer.SemanticallyExtends
      bodyResult.state.inference.substitution := by
    change outer.SemanticallyExtends
      bodyResult.state.inference.substitution at outerExtension
    exact outerExtension
  have conditionExtension : outer.SemanticallyExtends
      conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans bodyExtension
      bodyProperties.1.substitution_extends
  have conditionEq : outer.apply inferredCondition.type = .bool := by
    simpa using Detail.inferExprFuel_expected_type_apply_eq conditionSuccess
      conditionExtension
  refine ⟨{
      type := .unit
      hasValue := false
      sawReturn := false
      control := .loop bodyFacts.control
    }, conditionInvariant.restoreLexicalScope_recordNode _, ?_, ?_⟩
  · exact whileLoopStatementHasType_afterSubstitution contains conditionTyping
      conditionEq bodyTyping
  · exact StatementResultMatchesFactsAfterSubstitution.whileLoop outer
      bodyFacts id _

/-- Semantic callbacks shared by the successful statement dispatcher.  The
eventual typed source is fixed at the enclosing statement result, so recursive
children may be typed after all later nodes have been recorded.  The two
expression callbacks separate the strong fixed-context premise needed by
deep assignment traversal from the invariant-indexed premise needed after a
`for` initializer extends the lexical context. -/
structure StatementInferenceSoundnessCallbacks
    (fuel : Nat)
    (inferenceContext : Frontend.SourceInference.Context)
    (statement : Syntax.Statement) (expectedReturn : TypeSystem.Ty)
    (allocated : Frontend.SourceInference.State)
    (result : Detail.StatementResult)
    (outer : TypeSystem.Substitution)
    (target : SourceSemantics.Context) (roots : List NodeId) : Prop where
  unannotatedInitializedLet :
    ∀ {name : Syntax.Identifier} {initializer : Syntax.Expr}
      {inferred : InferredExpression}
      {initializerState : Frontend.SourceInference.State}
      {locals : TypeSystem.Environment} {valueType : TypeSystem.Ty}
      {generalized : Detail.GeneralizedValue}
      {binding : TypedBinder × Frontend.SourceInference.State},
      statement.value = .letDecl name none (some initializer) →
      Detail.inferExprFuel fuel inferenceContext initializer none allocated =
        .ok (inferred, initializerState) →
      locals = initializerState.binderEnvironment.apply
        initializerState.inference.substitution →
      valueType = initializerState.resolve inferred.type →
      generalized = Detail.generalizeValue initializerState locals
        allocated.nextRequirement valueType →
      (initializerState.withLocals locals).allocateBinder name.value
        generalized.scheme (some name.span) false generalized.requirements =
          binding →
      UnannotatedInitializedLetCertificate
        (result.state.toTypedSource roots) target outer binding.1 inferred.id
  expression :
    ∀ {childFuel : Nat} {expression : Syntax.Expr}
      {expected : Option TypeSystem.Ty}
      {childInitial childFinal : Frontend.SourceInference.State}
      {inferred : InferredExpression},
      Detail.inferExprFuel childFuel inferenceContext expression expected
          childInitial = .ok (inferred, childFinal) →
        ExpressionHasType
          ((result.state.toTypedSource roots).applySubstitution outer)
          target inferred.id (outer.apply inferred.type)
  booleanExpressionInContext :
    ∀ {childFuel : Nat} {expression : Syntax.Expr}
      {childInitial childFinal : Frontend.SourceInference.State}
      {inferred : InferredExpression}
      {semanticContext : SourceSemantics.Context},
      ActiveLocalContextInvariant childInitial outer semanticContext →
      Detail.inferExprFuel childFuel inferenceContext expression (some .bool)
          childInitial = .ok (inferred, childFinal) →
        ExpressionHasType
          ((result.state.toTypedSource roots).applySubstitution outer)
          semanticContext inferred.id .bool
  statements :
    ∀ {childFuel : Nat}
      {childContext : Frontend.SourceInference.Context}
      {statements : List Syntax.Statement}
      {childInitial : Frontend.SourceInference.State}
      {childResult : Detail.BlockResult}
      {semanticContext : SourceSemantics.Context},
      ActiveLocalContextInvariant childInitial outer semanticContext →
      Detail.inferStatementsFuel childFuel childContext statements
          expectedReturn childInitial = .ok childResult →
        ∃ finalContext facts,
          ActiveLocalContextInvariant childResult.state outer finalContext ∧
          StatementsHaveType
            ((result.state.toTypedSource roots).applySubstitution outer) {
              returnType := outer.apply expectedReturn
              loopDepth := childContext.loopDepth
            } semanticContext childResult.statements finalContext facts ∧
          BlockResultMatchesFactsAfterSubstitution outer childResult facts
  forItems :
    ∀ {childFuel : Nat}
      {childContext : Frontend.SourceInference.Context}
      {items : List Syntax.ForItem}
      {childInitial : Frontend.SourceInference.State}
      {childResult : Detail.InferredForItems}
      {semanticContext : SourceSemantics.Context},
      ActiveLocalContextInvariant childInitial outer semanticContext →
      Detail.inferForItemsFuel childFuel childContext items childInitial =
          .ok childResult →
        ∃ finalContext,
          ActiveLocalContextInvariant childResult.state outer finalContext ∧
          ForItemsHaveType
            ((result.state.toTypedSource roots).applySubstitution outer) {
              returnType := outer.apply expectedReturn
              loopDepth := childContext.loopDepth
            } semanticContext
              (childResult.items.map (ForItemForm.applySubstitution outer))
              finalContext
  matchScrutinee :
    ∀ {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {scrutinee : InferredExpression}
      {scrutineeState : Frontend.SourceInference.State},
      inferMatchScrutineesFuel fuel inferenceContext statement.span
          scrutinees.elements.toList allocated =
            .ok (scrutinee, scrutineeState) →
        ExpressionHasType
          ((result.state.toTypedSource roots).applySubstitution outer)
          target scrutinee.id (outer.apply scrutinee.type)
  matchCasesWithoutDefault :
    ∀ {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms} {scrutinee : InferredExpression}
      {hiddenState : Frontend.SourceInference.State}
      {checked : Detail.MatchCasesResult},
      statement.value = .matchWith scrutinees arms →
      arms.value.defaultBody = none →
      ActiveLocalContextInvariant hiddenState outer target →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        target scrutinee.id (outer.apply scrutinee.type) →
      Detail.inferMatchCasesFuel fuel inferenceContext scrutinee.type
          expectedReturn hiddenState.lexicalScope arms.value.cases
          hiddenState = .ok checked →
        ∃ caseFacts summary,
          MatchCasesHaveType
            ((result.state.toTypedSource roots).applySubstitution outer) {
              returnType := outer.apply expectedReturn
              loopDepth := inferenceContext.loopDepth
            } target (outer.apply scrutinee.type)
              (checked.cases.map (TypedMatchCase.applySubstitution outer))
              caseFacts ∧
          allBodiesSawReturn caseFacts = checked.allReturn ∧
          mergeBodyControls caseFacts none = some summary
  matchCasesWithDefault :
    ∀ {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms} {defaultBody : Syntax.Block}
      {scrutinee : InferredExpression}
      {hiddenState : Frontend.SourceInference.State}
      {checked : Detail.MatchCasesResult},
      statement.value = .matchWith scrutinees arms →
      arms.value.defaultBody = some defaultBody →
      ActiveLocalContextInvariant hiddenState outer target →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution outer)
        target scrutinee.id (outer.apply scrutinee.type) →
      Detail.inferMatchCasesFuel fuel inferenceContext scrutinee.type
          expectedReturn hiddenState.lexicalScope arms.value.cases
          hiddenState = .ok checked →
        ∃ caseFacts,
          MatchCasesHaveType
            ((result.state.toTypedSource roots).applySubstitution outer) {
              returnType := outer.apply expectedReturn
              loopDepth := inferenceContext.loopDepth
            } target (outer.apply scrutinee.type)
              (checked.cases.map (TypedMatchCase.applySubstitution outer))
              caseFacts ∧
          allBodiesSawReturn caseFacts = checked.allReturn
  matchExhaustiveWithoutDefault :
    ∀ {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms} {scrutinee : InferredExpression}
      {scrutineeState hiddenState : Frontend.SourceInference.State}
      {checked : Detail.MatchCasesResult} {nominallyExhaustive : Bool},
      statement.value = .matchWith scrutinees arms →
      arms.value.defaultBody = none →
      inferMatchScrutineesFuel fuel inferenceContext statement.span
          scrutinees.elements.toList allocated =
            .ok (scrutinee, scrutineeState) →
      Detail.inferMatchCasesFuel fuel inferenceContext scrutinee.type
          expectedReturn hiddenState.lexicalScope arms.value.cases
          hiddenState = .ok checked →
      (checked.hasWildcard || false || nominallyExhaustive) = true →
        MatchExhaustive target (outer.apply scrutinee.type)
          (checked.cases.map (TypedMatchCase.applySubstitution outer)) none

/-- Conditional statement soundness for the fixed control context carried by
executable inference.  This theorem is the constructor dispatcher: it selects
one of the branch wrappers above, while the uniform callback bundle contains
recursive semantic obligations in the already chosen eventual source.  It
does not itself discharge the callback bundle or establish child/source
provenance. -/
theorem inferStatementFuel_success_sound_of_callbacks
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : StatementId} {result : Detail.StatementResult}
    {outer : TypeSystem.Substitution} {target : SourceSemantics.Context}
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation :
      Frontend.ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (TypeSystem.Ty.productMany signature.parameterTypes)
        (TypeSystem.Ty.productMany signature.returnTypes))
    (canonical : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (signatures_eq : target.signatures = inferenceContext.signatures)
    (parameters_eq : target.typeParameters = inferenceContext.typeParameters)
    (declaration_eq : target.currentDeclaration =
      some inferenceContext.scope.genericOwner)
    (ready : initial.InferenceReady)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (invariant : ActiveLocalContextInvariant initial outer target)
    (below : initial.LocalBindersBelowNextLocal)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (roots : List NodeId := [])
    (callbacks : StatementInferenceSoundnessCallbacks fuel inferenceContext
      statement expectedReturn allocated result outer target roots) :
    ∃ finalContext facts,
      ActiveLocalContextInvariant result.state outer finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution outer) {
          returnType := outer.apply expectedReturn
          loopDepth := inferenceContext.loopDepth
        } target result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution outer result facts := by
  have allocatedInvariant :
      ActiveLocalContextInvariant allocated outer target :=
    invariant.allocateStatementId allocationEq
  cases statement with
  | mk statementSpan statementValue =>
      cases statementValue with
      | letDecl name sourceType initializer =>
          cases sourceType with
          | none =>
              cases initializer with
              | none =>
                  simp [Detail.inferStatementFuel, bind, Except.bind] at success
              | some initializer =>
                  exact inferStatementFuel_success_letUnannotatedInitialized_sound
                    rfl allocationEq success invariant below roots
                    (fun initializerSuccess localsEq valueTypeEq generalizedEq
                      bindingEq =>
                        callbacks.unannotatedInitializedLet rfl
                          initializerSuccess localsEq valueTypeEq generalizedEq
                          bindingEq)
          | some sourceType =>
              cases initializer with
              | none =>
                  exact inferStatementFuel_success_letAnnotatedUninitialized_sound
                    rfl allocationEq success canonical signatures_eq
                    parameters_eq declaration_eq invariant below roots
              | some initializer =>
                  exact inferStatementFuel_success_letAnnotatedInitialized_sound
                    rfl allocationEq success signatureFormation
                    functionsCanonical canonical signatures_eq parameters_eq
                    declaration_eq ready invariant below outerExtension roots
                    (fun _ initializerSuccess =>
                      callbacks.expression initializerSuccess)
      | returnStmt value =>
          cases value with
          | none =>
              refine ⟨target, {
                  type := outer.apply expectedReturn
                  hasValue := true
                  sawReturn := true
                  control := .returned
                }, ?_⟩
              exact inferStatementFuel_success_returnUnit_sound rfl
                allocationEq success invariant outerExtension roots
          | some value =>
              refine ⟨target, {
                  type := outer.apply expectedReturn
                  hasValue := true
                  sawReturn := true
                  control := .returned
                }, ?_⟩
              exact inferStatementFuel_success_returnValue_sound rfl
                allocationEq success invariant outerExtension roots
                (fun valueSuccess => callbacks.expression valueSuccess)
      | expression expression trailingSemicolon =>
          obtain ⟨facts, finalInvariant, typing, agreement⟩ :=
            inferStatementFuel_success_expression_sound rfl allocationEq
              success invariant roots
              (fun expressionSuccess =>
                callbacks.expression expressionSuccess)
          exact ⟨target, facts, finalInvariant, typing, agreement⟩
      | assignValue targetExpression operator value =>
          refine ⟨target, {
              type := .unit
              hasValue := false
              sawReturn := false
              control := .ordinary .unit
            }, ?_⟩
          exact inferStatementFuel_success_assignValue_deep_sound rfl
            allocationEq success ready signatureFormation functionsCanonical
            invariant outerExtension roots callbacks.expression
      | assignBitNot targetExpression operatorSpan =>
          refine ⟨target, {
              type := .unit
              hasValue := false
              sawReturn := false
              control := .ordinary .unit
            }, ?_⟩
          exact inferStatementFuel_success_assignBitNot_deep_sound rfl
            allocationEq success ready signatureFormation functionsCanonical
            invariant outerExtension roots callbacks.expression
      | matchWith scrutinees arms =>
          cases defaultEq : arms.value.defaultBody with
          | none =>
              obtain ⟨facts, finalInvariant, typing, agreement⟩ :=
                inferStatementFuel_success_matchWithoutDefault_sound rfl
                  defaultEq allocationEq success invariant outerExtension roots
                  callbacks.matchScrutinee
                  (fun hiddenInvariant scrutineeTyping casesSuccess =>
                    callbacks.matchCasesWithoutDefault rfl defaultEq
                      hiddenInvariant scrutineeTyping casesSuccess)
                  (fun scrutineeSuccess casesSuccess guardPassed =>
                    callbacks.matchExhaustiveWithoutDefault rfl defaultEq
                      scrutineeSuccess casesSuccess guardPassed)
              exact ⟨target, facts, finalInvariant, typing, agreement⟩
          | some defaultBody =>
              obtain ⟨facts, finalInvariant, typing, agreement⟩ :=
                inferStatementFuel_success_matchWithDefault_sound rfl
                  defaultEq allocationEq success invariant outerExtension roots
                  callbacks.matchScrutinee
                  (fun hiddenInvariant scrutineeTyping casesSuccess =>
                    callbacks.matchCasesWithDefault rfl defaultEq
                      hiddenInvariant scrutineeTyping casesSuccess)
                  (fun checkedInvariant defaultSuccess =>
                    callbacks.statements checkedInvariant defaultSuccess)
              exact ⟨target, facts, finalInvariant, typing, agreement⟩
      | forLoop headerSpan initializer condition post body =>
          obtain ⟨facts, finalInvariant, typing, agreement⟩ :=
            inferStatementFuel_success_forLoop_sound rfl allocationEq success
              invariant roots
              (fun initializerSuccess => by
                simpa using callbacks.forItems allocatedInvariant
                  initializerSuccess)
              (fun initializerInvariant conditionSuccess =>
                callbacks.booleanExpressionInContext initializerInvariant
                  conditionSuccess)
              (fun conditionInvariant bodySuccess => by
                obtain ⟨bodyFinal, bodyFacts, bodyInvariant, bodyTyping,
                    _bodyAgreement⟩ :=
                  callbacks.statements conditionInvariant bodySuccess
                exact ⟨bodyFinal, bodyFacts, bodyInvariant, by
                  simpa [ControlContext.enterLoop] using bodyTyping⟩)
              (fun postInvariant postSuccess => by
                obtain ⟨postContext, finalInvariant, postTyping⟩ :=
                  callbacks.forItems postInvariant postSuccess
                exact ⟨postContext, finalInvariant, by
                  simpa [ControlContext.enterLoop] using postTyping⟩)
          exact ⟨target, facts, finalInvariant, typing, agreement⟩
      | whileLoop condition body =>
          obtain ⟨facts, finalInvariant, typing, agreement⟩ :=
            inferStatementFuel_success_whileLoop_sound rfl allocationEq
              success signatureFormation functionsCanonical ready returnBelow
              invariant outerExtension roots
              (fun conditionSuccess => callbacks.expression conditionSuccess)
              (fun conditionInvariant bodySuccess => by
                obtain ⟨bodyFinal, bodyFacts, bodyInvariant, bodyTyping,
                    bodyAgreement⟩ :=
                  callbacks.statements conditionInvariant bodySuccess
                exact ⟨bodyFinal, bodyFacts, bodyInvariant, by
                  simpa [ControlContext.enterLoop] using bodyTyping,
                  bodyAgreement⟩)
          exact ⟨target, facts, finalInvariant, typing, agreement⟩
      | ifThen condition thenBody elseBody =>
          cases elseBody with
          | none =>
              obtain ⟨facts, finalInvariant, typing, agreement⟩ :=
                inferStatementFuel_success_ifWithoutElse_sound rfl
                  allocationEq success signatureFormation functionsCanonical
                  ready returnBelow invariant outerExtension roots
                  (fun conditionSuccess =>
                    callbacks.expression conditionSuccess)
                  (fun conditionInvariant thenSuccess =>
                    callbacks.statements conditionInvariant thenSuccess)
              exact ⟨target, facts, finalInvariant, typing, agreement⟩
          | some elseBody =>
              obtain ⟨facts, finalInvariant, typing, agreement⟩ :=
                inferStatementFuel_success_ifWithElse_sound rfl allocationEq
                  success signatureFormation functionsCanonical ready
                  returnBelow invariant outerExtension roots
                  (fun conditionSuccess =>
                    callbacks.expression conditionSuccess)
                  (fun conditionInvariant thenSuccess =>
                    callbacks.statements conditionInvariant thenSuccess)
                  (fun elseInvariant elseSuccess =>
                    callbacks.statements elseInvariant elseSuccess)
              exact ⟨target, facts, finalInvariant, typing, agreement⟩
      | block body =>
          obtain ⟨facts, finalInvariant, typing, agreement⟩ :=
            inferStatementFuel_success_block_sound rfl allocationEq success
              invariant roots (fun bodySuccess => by
                simpa using callbacks.statements allocatedInvariant
                  bodySuccess)
          exact ⟨target, facts, finalInvariant, typing, agreement⟩
      | assembly body =>
          simp [Detail.inferStatementFuel] at success
      | breakStmt =>
          refine ⟨target, {
              type := .unit
              hasValue := false
              sawReturn := false
              control := .breaking
            }, ?_⟩
          exact inferStatementFuel_success_break_sound rfl allocationEq
            success invariant roots
      | continueStmt =>
          refine ⟨target, {
              type := .unit
              hasValue := false
              sawReturn := false
              control := .continuing
            }, ?_⟩
          exact inferStatementFuel_success_continue_sound rfl allocationEq
            success invariant roots
      | error =>
          simp [Detail.inferStatementFuel] at success

/-- Empty executable block inference returns the canonical empty block
without changing its input state. -/
theorem inferStatementsFuel_success_nil_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expectedReturn : TypeSystem.Ty}
    {state : Frontend.SourceInference.State} {result : Detail.BlockResult}
    (success : Detail.inferStatementsFuel (fuel + 1) context [] expectedReturn
      state = .ok result) :
    result = {
      statements := []
      type := .unit
      sawReturn := false
      state
    } := by
  unfold Detail.inferStatementsFuel at success
  injection success with resultEq
  subst result
  rfl

/-- Singleton executable block inference exposes its exact statement result
and the canonical projection from that result into `BlockResult`. -/
theorem inferStatementsFuel_success_singleton_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : TypeSystem.Ty}
    {state : Frontend.SourceInference.State} {result : Detail.BlockResult}
    (success : Detail.inferStatementsFuel (fuel + 1) context [statement]
      expectedReturn state = .ok result) :
    ∃ head,
      Detail.inferStatementFuel fuel context statement expectedReturn state =
        .ok head ∧
      result = {
        statements := [head.id]
        type := if head.sawReturn || head.hasValue then head.type else .unit
        sawReturn := head.sawReturn
        state := head.state
      } := by
  unfold Detail.inferStatementsFuel at success
  cases headSuccess :
      Detail.inferStatementFuel fuel context statement expectedReturn state with
  | error error =>
      simp [headSuccess, bind, Except.bind] at success
  | ok head =>
      simp only [headSuccess, bind, Except.bind] at success
      injection success with resultEq
      subst result
      exact ⟨head, rfl, rfl⟩

/-- Non-singleton executable block inference exposes the exact head and tail
computations and the canonical sequential `BlockResult` assembled from them. -/
theorem inferStatementsFuel_success_cons_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement next : Syntax.Statement} {rest : List Syntax.Statement}
    {expectedReturn : TypeSystem.Ty}
    {state : Frontend.SourceInference.State} {result : Detail.BlockResult}
    (success : Detail.inferStatementsFuel (fuel + 1) context
      (statement :: next :: rest) expectedReturn state = .ok result) :
    ∃ head tail,
      Detail.inferStatementFuel fuel context statement expectedReturn state =
        .ok head ∧
      Detail.inferStatementsFuel fuel context (next :: rest) expectedReturn
        head.state = .ok tail ∧
      result = {
        statements := head.id :: tail.statements
        type := if tail.sawReturn then tail.type
          else if head.sawReturn then head.type else tail.type
        sawReturn := head.sawReturn || tail.sawReturn
        state := tail.state
      } := by
  unfold Detail.inferStatementsFuel at success
  cases headSuccess :
      Detail.inferStatementFuel fuel context statement expectedReturn state with
  | error error =>
      simp [headSuccess, bind, Except.bind] at success
  | ok head =>
      simp only [headSuccess, bind, Except.bind] at success
      cases tailSuccess : Detail.inferStatementsFuel fuel context
          (next :: rest) expectedReturn head.state with
      | error error =>
          simp [tailSuccess] at success
      | ok tail =>
          simp only [tailSuccess] at success
          injection success with resultEq
          subst result
          exact ⟨head, tail, rfl, tailSuccess, rfl⟩

/-- Successful inference of a nonempty source statement list returns a
nonempty list of retained statement occurrences. -/
theorem inferStatementsFuel_success_statements_eq_cons
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {rest : List Syntax.Statement}
    {expectedReturn : TypeSystem.Ty}
    {state : Frontend.SourceInference.State} {result : Detail.BlockResult}
    (success : Detail.inferStatementsFuel fuel context (statement :: rest)
      expectedReturn state = .ok result) :
    ∃ id ids, result.statements = id :: ids := by
  cases fuel with
  | zero =>
      simp [Detail.inferStatementsFuel] at success
  | succ fuel =>
      cases rest with
      | nil =>
          obtain ⟨head, _, resultEq⟩ :=
            inferStatementsFuel_success_singleton_facts success
          rw [resultEq]
          exact ⟨head.id, [], rfl⟩
      | cons next rest =>
          obtain ⟨head, tail, _, _, resultEq⟩ :=
            inferStatementsFuel_success_cons_facts success
          rw [resultEq]
          exact ⟨head.id, tail.statements, rfl⟩

namespace BlockResultMatchesFactsAfterSubstitution

/-- The canonical empty executable block matches `BodyFacts.empty` under any
final substitution. -/
theorem empty (substitution : TypeSystem.Substitution)
    (state : Frontend.SourceInference.State) :
    BlockResultMatchesFactsAfterSubstitution substitution {
      statements := []
      type := .unit
      sawReturn := false
      state
    } .empty := by
  constructor <;> rfl

/-- Matching one executable statement is exactly enough to match the
singleton block assembled from it. -/
theorem singleton
    {substitution : TypeSystem.Substitution}
    {result : Detail.StatementResult} {facts : StatementFacts}
    (agreement : StatementResultMatchesFactsAfterSubstitution substitution
      result facts) :
    BlockResultMatchesFactsAfterSubstitution substitution {
      statements := [result.id]
      type := if result.sawReturn || result.hasValue then result.type else .unit
      sawReturn := result.sawReturn
      state := result.state
    } (.singleton facts) := by
  rcases agreement with ⟨typeEq, hasValueEq, sawReturnEq⟩
  constructor
  · simp only [BodyFacts.singleton]
    rw [typeEq, hasValueEq, sawReturnEq]
    cases result.sawReturn <;> cases result.hasValue <;> rfl
  · exact sawReturnEq

/-- Head and tail matches compose according to the executable and declarative
sequence folds. -/
theorem cons
    {substitution : TypeSystem.Substitution}
    {head : Detail.StatementResult} {headFacts : StatementFacts}
    {tail : Detail.BlockResult} {tailFacts : BodyFacts}
    (headMatches : StatementResultMatchesFactsAfterSubstitution substitution
      head headFacts)
    (tailMatches : BlockResultMatchesFactsAfterSubstitution substitution
      tail tailFacts) :
    BlockResultMatchesFactsAfterSubstitution substitution {
      statements := head.id :: tail.statements
      type := if tail.sawReturn then tail.type
        else if head.sawReturn then head.type else tail.type
      sawReturn := head.sawReturn || tail.sawReturn
      state := tail.state
    } (.cons headFacts tailFacts) := by
  rcases headMatches with ⟨headTypeEq, headHasValueEq, headSawReturnEq⟩
  rcases tailMatches with ⟨tailTypeEq, tailSawReturnEq⟩
  constructor
  · simp only [BodyFacts.cons]
    rw [tailTypeEq, headTypeEq, tailSawReturnEq, headSawReturnEq]
    cases tail.sawReturn <;> cases head.sawReturn <;> rfl
  · simp only [BodyFacts.cons]
    rw [headSawReturnEq, tailSawReturnEq]

end BlockResultMatchesFactsAfterSubstitution

/-! ## Match-pattern inference certificates

Pattern inference is the one statement sub-pass which deliberately grows the
visible lexical scope while recursively flattening a nested source pattern.
The following certificates keep the three results of that pass together: the
typed prefix program, the exact semantic binder extension, and the active
local-state invariant needed by the arm body.
-/

/-- Semantic result of one successful internal flat-pattern traversal.  The
typing field is suffix-polymorphic so source-ordered prefix programs compose
without a separate weakening theorem. -/
structure MatchPatternFlatInferenceCertificate
    (source : TypedSource) (semanticContext activeContext : SourceSemantics.Context)
    (outer : TypeSystem.Substitution) (expected : TypeSystem.Ty)
    (seen : List String) (initial : Frontend.SourceInference.State)
    (result : Detail.InferredPattern) where
  binders : List TypedBinder
  rootArity : Nat
  finalContext : SourceSemantics.Context
  source_represents : MatchPatternSourceRepresents semanticContext result.source
    (result.resolution.applySubstitution outer) rootArity
  instructions_eq : result.instructions =
    matchPatternResolutionInstructions result.resolution rootArity
  instruction_type : ∀ suffix,
    PatternInstructionHasType semanticContext
      (result.instructions.map
          (MatchPatternInstruction.applySubstitution outer) ++ suffix)
      (outer.apply expected) result.requirements binders suffix
  binders_extend : BindersExtend source.owner activeContext binders finalContext
  invariant : ActiveLocalContextInvariant result.state outer finalContext
  progress : initial.InferenceProgress result.state
  ready : result.state.InferenceReady
  below : result.state.LocalBindersBelowNextLocal
  owner_eq : result.state.owner = initial.owner
  names_eq : result.names = seen ++ binders.map (fun binder => binder.name)
  names_nodup : result.names.Nodup

/-- Source-ordered companion certificate for a row of flattened children. -/
structure MatchPatternsFlatInferenceCertificate
    (source : TypedSource) (semanticContext activeContext : SourceSemantics.Context)
    (outer : TypeSystem.Substitution) (expected : List TypeSystem.Ty)
    (seen : List String) (initial : Frontend.SourceInference.State)
    (result : Detail.InferredPatterns) where
  binders : List TypedBinder
  finalContext : SourceSemantics.Context
  instructions_type : ∀ suffix,
    PatternInstructionsHaveTypes semanticContext
      (result.instructions.map
          (MatchPatternInstruction.applySubstitution outer) ++ suffix)
      (expected.map outer.apply) result.requirements binders suffix
  binders_extend : BindersExtend source.owner activeContext binders finalContext
  invariant : ActiveLocalContextInvariant result.state outer finalContext
  progress : initial.InferenceProgress result.state
  ready : result.state.InferenceReady
  below : result.state.LocalBindersBelowNextLocal
  owner_eq : result.state.owner = initial.owner
  names_eq : result.names = seen ++ binders.map (fun binder => binder.name)
  names_nodup : result.names.Nodup

/-- Public pattern-level package consumed by match-arm inference. -/
structure MatchPatternInferenceCertificate
    (source : TypedSource) (semanticContext : SourceSemantics.Context)
    (outer : TypeSystem.Substitution) (expected : TypeSystem.Ty)
    (pattern : TypedMatchPattern)
    (patternState : Frontend.SourceInference.State) where
  binders : List TypedBinder
  rootArity : Nat
  armContext : SourceSemantics.Context
  pattern_type : TypedMatchPatternHasType semanticContext
    (pattern.applySubstitution outer) (outer.apply expected) binders rootArity
  binders_extend : BindersExtend source.owner semanticContext binders armContext
  pattern_invariant : ActiveLocalContextInvariant patternState outer armContext

/-- Algorithmic state facts used by the semantic dispatcher.  Keeping the two
frontend theorems in one package lets the private branch helpers share a
uniform interface without making them assumptions of the public soundness
theorems. -/
structure MatchPatternFlatStateCallbacks
    (inferenceContext : Frontend.SourceInference.Context) : Prop where
  pattern :
    ∀ {fuel : Nat} {pattern : Syntax.Pattern} {expected : TypeSystem.Ty}
      {seen : List String} {initial : Frontend.SourceInference.State}
      {result : Detail.InferredPattern},
      initial.InferenceReady →
      expected.VariablesBelow initial.inference.next →
      ProgramSignatureFormationValidated inferenceContext.signatures →
      initial.LocalBindersBelowNextLocal →
      Detail.inferMatchPatternFlatFuel fuel inferenceContext pattern expected
          seen initial = .ok result →
      initial.InferenceProgress result.state ∧
        result.state.InferenceReady ∧
        result.state.LocalBindersBelowNextLocal ∧
        result.state.owner = initial.owner
  patterns :
    ∀ {fuel : Nat} {patterns : List Syntax.Pattern}
      {expected : List TypeSystem.Ty} {seen : List String}
      {initial : Frontend.SourceInference.State}
      {result : Detail.InferredPatterns},
      initial.InferenceReady →
      (∀ type ∈ expected,
        type.VariablesBelow initial.inference.next) →
      ProgramSignatureFormationValidated inferenceContext.signatures →
      initial.LocalBindersBelowNextLocal →
      Detail.inferMatchPatternsFlatFuel fuel inferenceContext patterns expected
          seen initial = .ok result →
      initial.InferenceProgress result.state ∧
        result.state.InferenceReady ∧
        result.state.LocalBindersBelowNextLocal ∧
        result.state.owner = initial.owner

/-- The canonical flat-pattern state package, discharged entirely by the
public frontend preservation theorems. -/
theorem matchPatternFlatStateCallbacks
    (inferenceContext : Frontend.SourceInference.Context) :
    MatchPatternFlatStateCallbacks inferenceContext := {
  pattern := fun ready expectedBelow validated below success =>
    Detail.inferMatchPatternFlatFuel_stateProperties ready expectedBelow
      validated below success
  patterns := fun ready expectedBelow validated below success =>
    Detail.inferMatchPatternsFlatFuel_stateProperties ready expectedBelow
      validated below success
}

/-- Recursive obligations of the one-layer pattern dispatcher.  They mention
only strict recursive calls made by `inferMatchPatternFlatFuel`; all leaf and
assembly reasoning stays in the dispatcher below. -/
structure MatchPatternRecursiveSoundnessCallbacks
    (source : TypedSource)
    (inferenceContext : Frontend.SourceInference.Context)
    (semanticContext : SourceSemantics.Context)
    (outer : TypeSystem.Substitution) where
  pattern :
    ∀ {fuel : Nat} {pattern : Syntax.Pattern} {expected : TypeSystem.Ty}
      {seen : List String} {initial : Frontend.SourceInference.State}
      {result : Detail.InferredPattern}
      {activeContext : SourceSemantics.Context},
      initial.InferenceReady →
      expected.VariablesBelow initial.inference.next →
      initial.LocalBindersBelowNextLocal →
      source.owner = initial.owner →
      seen.Nodup →
      TypeAdmissible semanticContext (outer.apply expected) →
      TypeAdmissible activeContext (outer.apply expected) →
      ActiveLocalContextInvariant initial outer activeContext →
      outer.SemanticallyExtends result.state.inference.substitution →
      Detail.inferMatchPatternFlatFuel fuel inferenceContext pattern expected
          seen initial = .ok result →
      Nonempty (MatchPatternFlatInferenceCertificate source semanticContext
        activeContext outer expected seen initial result)
  patterns :
    ∀ {fuel : Nat} {patterns : List Syntax.Pattern}
      {expected : List TypeSystem.Ty} {seen : List String}
      {initial : Frontend.SourceInference.State}
      {result : Detail.InferredPatterns}
      {activeContext : SourceSemantics.Context},
      initial.InferenceReady →
      (∀ type ∈ expected,
        type.VariablesBelow initial.inference.next) →
      initial.LocalBindersBelowNextLocal →
      source.owner = initial.owner →
      seen.Nodup →
      (∀ type ∈ expected,
        TypeAdmissible semanticContext (outer.apply type)) →
      (∀ type ∈ expected,
        TypeAdmissible activeContext (outer.apply type)) →
      ActiveLocalContextInvariant initial outer activeContext →
      outer.SemanticallyExtends result.state.inference.substitution →
      Detail.inferMatchPatternsFlatFuel fuel inferenceContext patterns expected
          seen initial = .ok result →
      Nonempty (MatchPatternsFlatInferenceCertificate source semanticContext
        activeContext outer expected seen initial result)

/-- Exact semantic frontiers for literal and constructor patterns.  The
certificate-producing callbacks are tied to one concrete syntax
constructor, its successful executable call, and the complete premises used
by that call; in particular this is not a catch-all certificate oracle.
Wildcards, binders, groups, and tuple assembly are proved by the dispatcher. -/
structure MatchPatternBranchSoundnessCallbacks
    (source : TypedSource)
    (inferenceContext : Frontend.SourceInference.Context)
    (semanticContext : SourceSemantics.Context)
    (outer : TypeSystem.Substitution) where
  literal :
    ∀ {fuel : Nat} {pattern : Syntax.Pattern}
      {literal : Syntax.CoreLiteral} {expected : TypeSystem.Ty}
      {seen : List String} {initial : Frontend.SourceInference.State}
      {result : Detail.InferredPattern}
      {activeContext : SourceSemantics.Context},
      pattern.value = .literal literal →
      initial.InferenceReady →
      expected.VariablesBelow initial.inference.next →
      ProgramSignatureFormationValidated inferenceContext.signatures →
      initial.LocalBindersBelowNextLocal →
      source.owner = initial.owner →
      semanticContext.currentDeclaration = some source.owner →
      seen.Nodup →
      TypeAdmissible semanticContext (outer.apply expected) →
      TypeAdmissible activeContext (outer.apply expected) →
      ActiveLocalContextInvariant initial outer activeContext →
      outer.SemanticallyExtends result.state.inference.substitution →
      Detail.inferMatchPatternFlatFuel fuel inferenceContext pattern expected
          seen initial = .ok result →
      Nonempty (MatchPatternFlatInferenceCertificate source semanticContext
        activeContext outer expected seen initial result)
  constructor :
    ∀ {fuel : Nat} {pattern : Syntax.Pattern}
      {leadingDot : Option Syntax.SourceSpan}
      {qualifiers : List Syntax.Identifier} {name : Syntax.Identifier}
      {arguments : Option
        (Syntax.NonemptyDelimitedList (Syntax.Located Syntax.PatternValue))}
      {expected : TypeSystem.Ty} {seen : List String}
      {initial : Frontend.SourceInference.State}
      {result : Detail.InferredPattern}
      {activeContext : SourceSemantics.Context},
      pattern.value = .constructor leadingDot qualifiers name arguments →
      initial.InferenceReady →
      expected.VariablesBelow initial.inference.next →
      ProgramSignatureFormationValidated inferenceContext.signatures →
      initial.LocalBindersBelowNextLocal →
      source.owner = initial.owner →
      semanticContext.currentDeclaration = some source.owner →
      seen.Nodup →
      TypeAdmissible semanticContext (outer.apply expected) →
      TypeAdmissible activeContext (outer.apply expected) →
      ActiveLocalContextInvariant initial outer activeContext →
      outer.SemanticallyExtends result.state.inference.substitution →
      Detail.inferMatchPatternFlatFuel fuel inferenceContext pattern expected
          seen initial = .ok result →
      Nonempty (MatchPatternFlatInferenceCertificate source semanticContext
        activeContext outer expected seen initial result)

private theorem bindersExtend_append
    {owner : Resolved.DeclarationId}
    {first middle final : SourceSemantics.Context}
    {head tail : List TypedBinder}
    (headExtension : BindersExtend owner first head middle)
    (tailExtension : BindersExtend owner middle tail final) :
    BindersExtend owner first (head ++ tail) final := by
  induction headExtension with
  | nil => simpa using tailExtension
  | cons head rest induction =>
      simpa only [List.cons_append] using
        BindersExtend.cons head (induction tailExtension)

private theorem typeAdmissible_withLocal
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (admissible : TypeAdmissible context type)
    (id : Resolved.LocalId) (scheme : TypeSystem.Scheme)
    (requirements : List LocalSchemeRequirement) :
    TypeAdmissible (context.withLocal id scheme requirements) type := by
  exact StructuralSubstitution.TypeAdmissible.transportContext
    (source := context)
    (target := context.withLocal id scheme requirements)
    rfl rfl rfl rfl rfl admissible

private theorem typeAdmissible_of_bindersExtend
    {owner : Resolved.DeclarationId}
    {context final : SourceSemantics.Context} {binders : List TypedBinder}
    {type : TypeSystem.Ty}
    (extension : BindersExtend owner context binders final)
    (admissible : TypeAdmissible context type) :
    TypeAdmissible final type := by
  induction extension with
  | nil => exact admissible
  | cons head tail induction =>
      apply induction
      cases head with
      | intro wellFormed fresh =>
          exact typeAdmissible_withLocal admissible _ _ _

/-- One source-ordered list layer of flat pattern inference is semantically
sound once its strict head and tail calls are supplied by the recursive
callback bundle. -/
theorem inferMatchPatternsFlatFuel_success_sound_of_callbacks
    {source : TypedSource}
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext activeContext : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    {fuel : Nat} {patterns : List Syntax.Pattern}
    {expected : List TypeSystem.Ty} {seen : List String}
    {initial : Frontend.SourceInference.State}
    {result : Detail.InferredPatterns}
    (validated : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (recursive : MatchPatternRecursiveSoundnessCallbacks source
      inferenceContext semanticContext outer)
    (ready : initial.InferenceReady)
    (expectedBelow : ∀ type ∈ expected,
      type.VariablesBelow initial.inference.next)
    (below : initial.LocalBindersBelowNextLocal)
    (owner_eq : source.owner = initial.owner)
    (seen_nodup : seen.Nodup)
    (semanticAdmissible : ∀ type ∈ expected,
      TypeAdmissible semanticContext (outer.apply type))
    (activeAdmissible : ∀ type ∈ expected,
      TypeAdmissible activeContext (outer.apply type))
    (invariant : ActiveLocalContextInvariant initial outer activeContext)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (success : Detail.inferMatchPatternsFlatFuel fuel inferenceContext patterns
      expected seen initial = .ok result) :
    Nonempty (MatchPatternsFlatInferenceCertificate source semanticContext
      activeContext outer expected seen initial result) := by
  let stateCallbacks := matchPatternFlatStateCallbacks inferenceContext
  have properties := stateCallbacks.patterns ready expectedBelow validated below
    success
  cases patterns with
  | nil =>
      cases expected with
      | nil =>
          simp only [Detail.inferMatchPatternsFlatFuel, pure, Pure.pure,
            Except.pure] at success
          injection success with resultEq
          subst result
          exact ⟨{
            binders := []
            finalContext := activeContext
            instructions_type := fun suffix => by
              simpa using (PatternInstructionsHaveTypes.nil
                (context := semanticContext) (instructions := suffix))
            binders_extend := .nil activeContext
            invariant
            progress := properties.1
            ready := properties.2.1
            below := properties.2.2.1
            owner_eq := properties.2.2.2
            names_eq := by simp
            names_nodup := seen_nodup
          }⟩
      | cons type types =>
          simp [Detail.inferMatchPatternsFlatFuel] at success
  | cons pattern patterns =>
      cases expected with
      | nil => simp [Detail.inferMatchPatternsFlatFuel] at success
      | cons type types =>
          simp only [Detail.inferMatchPatternsFlatFuel, bind, Except.bind]
            at success
          cases headSuccess : Detail.inferMatchPatternFlatFuel fuel
              inferenceContext pattern type seen initial with
          | error error => simp [headSuccess] at success
          | ok head =>
              simp only [headSuccess] at success
              cases tailSuccess : Detail.inferMatchPatternsFlatFuel fuel
                  inferenceContext patterns types head.names head.state with
              | error error => simp [tailSuccess] at success
              | ok tail =>
                  simp only [tailSuccess, pure, Pure.pure, Except.pure]
                    at success
                  injection success with resultEq
                  subst result
                  have headProperties := stateCallbacks.pattern ready
                    (expectedBelow type (by simp)) validated below headSuccess
                  have tailExpectedBelow : ∀ candidate ∈ types,
                      candidate.VariablesBelow head.state.inference.next := by
                    intro candidate member
                    exact (expectedBelow candidate (by simp [member])).weaken
                      headProperties.1.next_le
                  have tailProperties := stateCallbacks.patterns
                    headProperties.2.1 tailExpectedBelow validated
                    headProperties.2.2.1 tailSuccess
                  have outerHead : outer.SemanticallyExtends
                      head.state.inference.substitution :=
                    TypeSystem.Substitution.SemanticallyExtends.trans
                      outerExtension tailProperties.1.substitution_extends
                  obtain ⟨headCertificate⟩ := recursive.pattern ready
                    (expectedBelow type (by simp)) below owner_eq seen_nodup
                    (semanticAdmissible type (by simp))
                    (activeAdmissible type (by simp)) invariant outerHead
                    headSuccess
                  have tailOwner : source.owner = head.state.owner :=
                    owner_eq.trans headProperties.2.2.2.symm
                  have tailSemanticAdmissible : ∀ candidate ∈ types,
                      TypeAdmissible semanticContext
                        (outer.apply candidate) := by
                    intro candidate member
                    exact semanticAdmissible candidate (by simp [member])
                  have tailActiveAdmissible : ∀ candidate ∈ types,
                      TypeAdmissible headCertificate.finalContext
                        (outer.apply candidate) := by
                    intro candidate member
                    exact typeAdmissible_of_bindersExtend
                      headCertificate.binders_extend
                      (activeAdmissible candidate (by simp [member]))
                  obtain ⟨tailCertificate⟩ := recursive.patterns
                    (result := tail)
                    headProperties.2.1 tailExpectedBelow
                    headProperties.2.2.1 tailOwner
                    headCertificate.names_nodup tailSemanticAdmissible
                    tailActiveAdmissible headCertificate.invariant
                    outerExtension tailSuccess
                  exact ⟨{
                    binders := headCertificate.binders ++
                      tailCertificate.binders
                    finalContext := tailCertificate.finalContext
                    instructions_type := fun suffix => by
                      simp only [List.map_append]
                      simpa only [List.append_assoc, List.map_cons] using
                        (PatternInstructionsHaveTypes.cons
                          (headCertificate.instruction_type
                            (tail.instructions.map
                              (MatchPatternInstruction.applySubstitution outer) ++
                              suffix))
                          (tailCertificate.instructions_type suffix))
                    binders_extend := bindersExtend_append
                      headCertificate.binders_extend
                      tailCertificate.binders_extend
                    invariant := tailCertificate.invariant
                    progress := properties.1
                    ready := properties.2.1
                    below := properties.2.2.1
                    owner_eq := properties.2.2.2
                    names_eq := by
                      calc
                        tail.names = head.names ++
                            tailCertificate.binders.map
                              (fun binder => binder.name) :=
                          tailCertificate.names_eq
                        _ = (seen ++ headCertificate.binders.map
                              (fun binder => binder.name)) ++
                            tailCertificate.binders.map
                              (fun binder => binder.name) := by
                          exact congrArg
                            (fun names => names ++
                              tailCertificate.binders.map
                                (fun binder => binder.name))
                            headCertificate.names_eq
                        _ = seen ++
                            (headCertificate.binders ++
                              tailCertificate.binders).map
                                (fun binder => binder.name) := by
                          simp [List.map_append, List.append_assoc]
                    names_nodup := tailCertificate.names_nodup
                  }⟩

/-- The wildcard leaf performs no state or lexical update and emits the
single wildcard instruction. -/
private theorem inferMatchPatternFlatFuel_success_wildcard_sound
    {source : TypedSource}
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext activeContext : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {fuel : Nat}
    {pattern : Syntax.Pattern} {marker : Syntax.SourceSpan}
    {expected : TypeSystem.Ty} {seen : List String}
    {initial : Frontend.SourceInference.State}
    {result : Detail.InferredPattern}
    (pattern_eq : pattern.value = .wildcard marker)
    (stateCallbacks : MatchPatternFlatStateCallbacks inferenceContext)
    (ready : initial.InferenceReady)
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (validated : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (below : initial.LocalBindersBelowNextLocal)
    (_owner_eq : source.owner = initial.owner)
    (seen_nodup : seen.Nodup)
    (invariant : ActiveLocalContextInvariant initial outer activeContext)
    (success : Detail.inferMatchPatternFlatFuel (fuel + 1) inferenceContext
      pattern expected seen initial = .ok result) :
    Nonempty (MatchPatternFlatInferenceCertificate source semanticContext
      activeContext outer expected seen initial result) := by
  have properties := stateCallbacks.pattern ready expectedBelow validated below
    success
  unfold Detail.inferMatchPatternFlatFuel at success
  simp only [pattern_eq, pure, Pure.pure, Except.pure] at success
  injection success with resultEq
  subst result
  exact ⟨{
    binders := []
    rootArity := 0
    finalContext := activeContext
    source_represents := .wildcard
    instructions_eq := rfl
    instruction_type := fun suffix => by
      exact PatternInstructionHasType.wildcard
    binders_extend := .nil activeContext
    invariant
    progress := properties.1
    ready := properties.2.1
    below := properties.2.2.1
    owner_eq := properties.2.2.2
    names_eq := by simp
    names_nodup := seen_nodup
  }⟩

/-- A successful binder pattern installs exactly one closed monomorphic
binder in the active arm context. -/
private theorem inferMatchPatternFlatFuel_success_binder_sound
    {source : TypedSource}
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext activeContext : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {fuel : Nat}
    {pattern : Syntax.Pattern} {name : Syntax.Identifier}
    {expected : TypeSystem.Ty} {seen : List String}
    {initial : Frontend.SourceInference.State}
    {result : Detail.InferredPattern}
    (pattern_eq : pattern.value = .binder name)
    (stateCallbacks : MatchPatternFlatStateCallbacks inferenceContext)
    (ready : initial.InferenceReady)
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (validated : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (below : initial.LocalBindersBelowNextLocal)
    (owner_eq : source.owner = initial.owner)
    (semanticOwner : semanticContext.currentDeclaration = some source.owner)
    (seen_nodup : seen.Nodup)
    (semanticAdmissible :
      TypeAdmissible semanticContext (outer.apply expected))
    (activeAdmissible :
      TypeAdmissible activeContext (outer.apply expected))
    (invariant : ActiveLocalContextInvariant initial outer activeContext)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (success : Detail.inferMatchPatternFlatFuel (fuel + 1) inferenceContext
      pattern expected seen initial = .ok result) :
    Nonempty (MatchPatternFlatInferenceCertificate source semanticContext
      activeContext outer expected seen initial result) := by
  have properties := stateCallbacks.pattern ready expectedBelow validated below
    success
  unfold Detail.inferMatchPatternFlatFuel at success
  simp only [pattern_eq] at success
  by_cases duplicate : seen.contains name.value = true
  · have duplicateMem : name.value ∈ seen := by
      simpa using duplicate
    simp [duplicateMem, bind, Except.bind] at success
  · let binder := (initial.allocateBinder name.value
        (.mono (initial.resolve expected)) (some name.span)).1
    let final := (initial.allocateBinder name.value
        (.mono (initial.resolve expected)) (some name.span)).2
    have allocated : initial.allocateBinder name.value
        (.mono (initial.resolve expected)) (some name.span)
          = (binder, final) := by
      exact (Prod.eta _).symm
    simp only [duplicate, bind, Except.bind, allocated, pure,
      Pure.pure, Except.pure] at success
    injection success with resultEq
    subst result
    have binderEq :
        (initial.allocateBinder name.value
          (.mono (initial.resolve expected)) (some name.span)).1 = binder :=
      congrArg Prod.fst allocated
    have finalEq :
        (initial.allocateBinder name.value
          (.mono (initial.resolve expected)) (some name.span)).2 = final :=
      congrArg Prod.snd allocated
    have finalInferenceEq : final.inference = initial.inference := by
      rw [← finalEq]
      rfl
    have initialExtension : outer.SemanticallyExtends
        initial.inference.substitution := by
      rw [← finalInferenceEq]
      exact outerExtension
    have closedExpectedEq :
        outer.apply (initial.resolve expected) = outer.apply expected := by
      simpa [Frontend.SourceInference.State.resolve,
        TypeSystem.InferState.resolve] using initialExtension expected
    have closedSchemeEq :
        (binder.applySubstitution outer).scheme =
          .mono (outer.apply expected) := by
      rw [← binderEq]
      simp [Frontend.SourceInference.State.allocateBinder,
        TypedBinder.applySubstitution, TypeSystem.Scheme.apply,
        TypeSystem.Scheme.mono, TypeSystem.Substitution.without,
        closedExpectedEq]
    have closedRequirementsEq :
        (binder.applySubstitution outer).schemeRequirements = [] := by
      rw [← binderEq]
      simp [Frontend.SourceInference.State.allocateBinder,
        TypedBinder.applySubstitution]
    have semanticWellFormed : BinderWellFormed semanticContext source.owner
        (binder.applySubstitution outer) := by
      refine {
        owned := ?_
        scheme := ?_
        quantified_fresh := ?_
        monomorphic_requirements_empty := ?_
      }
      · rw [← binderEq]
        simp [Frontend.SourceInference.State.allocateBinder,
          TypedBinder.applySubstitution, ← owner_eq]
      · rw [closedSchemeEq]
        exact SchemeWellFormed.monoAdmissible semanticAdmissible
      · rw [closedSchemeEq]
        simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]
      · intro _
        exact closedRequirementsEq
    have binderValid : PatternBinderValid semanticContext
        (outer.apply expected) (binder.applySubstitution outer) := by
      refine {
        scheme_eq := closedSchemeEq
        runtime := ?_
        wellFormed := ?_
      }
      · rw [← binderEq]
        rfl
      · intro declaration declarationEq
        have declarationOwner : declaration = source.owner :=
          Option.some.inj (declarationEq.symm.trans semanticOwner)
        subst declaration
        exact semanticWellFormed
    have activeSchemeWellFormed : SchemeWellFormed activeContext
        (binder.applySubstitution outer).scheme := by
      rw [closedSchemeEq]
      exact SchemeWellFormed.monoAdmissible activeAdmissible
    have activeRequirementsWellFormed :
        LocalSchemeRequirementsWellFormed activeContext
          (binder.applySubstitution outer) :=
      LocalSchemeRequirementsWellFormed.empty activeContext _
        closedRequirementsEq
    let finalContext := activeContext.withLocal binder.id
      (binder.applySubstitution outer).scheme
      (binder.applySubstitution outer).schemeRequirements
    have finalInvariant : ActiveLocalContextInvariant final outer
        finalContext := by
      exact invariant.allocateBinder_of_localBindersBelowNextLocal
        name.value (.mono (initial.resolve expected)) (some name.span)
        false [] allocated below activeSchemeWellFormed
        activeRequirementsWellFormed
    have rawExtension : BinderExtends initial.owner activeContext
        (binder.applySubstitution outer) finalContext := by
      exact invariant.aligned.binderExtends_of_allocateBinder below allocated
        activeSchemeWellFormed (by
          rw [closedSchemeEq]
          simp [SchemeQuantifiersFresh, TypeSystem.Scheme.mono]) (by
          intro _
          exact closedRequirementsEq)
    have extension : BindersExtend source.owner activeContext
        [binder.applySubstitution outer] finalContext := by
      apply BindersExtend.cons
      · simpa [owner_eq] using rawExtension
      · exact .nil finalContext
    have nameAbsent : name.value ∉ seen := by
      simpa using duplicate
    have binderNameEq : binder.name = name.value := by
      simpa [Frontend.SourceInference.State.allocateBinder] using
        (congrArg TypedBinder.name binderEq).symm
    exact ⟨{
      binders := [binder.applySubstitution outer]
      rootArity := 0
      finalContext
      source_represents := MatchPatternSourceRepresents.binder binderNameEq
      instructions_eq := rfl
      instruction_type := fun suffix => by
        simpa [MatchPatternInstruction.applySubstitution] using
          (PatternInstructionHasType.binder
            (rest := suffix) binderValid)
      binders_extend := extension
      invariant := finalInvariant
      progress := properties.1
      ready := properties.2.1
      below := properties.2.2.1
      owner_eq := properties.2.2.2
      names_eq := by simp [binderNameEq]
      names_nodup := by
        rw [List.nodup_append]
        refine ⟨seen_nodup, by simp, ?_⟩
        intro candidate candidateMem appended appendedMem same
        simp only [List.mem_singleton] at appendedMem
        have candidateEq : candidate = name.value := same.trans appendedMem
        exact nameAbsent (candidateEq ▸ candidateMem)
    }⟩

private theorem freshTypes_length
    (count : Nat) (state : Frontend.SourceInference.State) :
    (Detail.freshTypes count state).1.length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count induction =>
      simp only [Detail.freshTypes, List.length_cons]
      rw [induction state.fresh.2]

private theorem freshTypes_preserves_localBinders
    (count : Nat) (state : Frontend.SourceInference.State) :
    (Detail.freshTypes count state).2.localBinders = state.localBinders := by
  induction count generalizing state with
  | zero => rfl
  | succ count induction =>
      simp only [Detail.freshTypes]
      exact (induction state.fresh.2).trans rfl

private theorem freshTypes_preserves_owner
    (count : Nat) (state : Frontend.SourceInference.State) :
    (Detail.freshTypes count state).2.owner = state.owner := by
  induction count generalizing state with
  | zero => rfl
  | succ count induction =>
      simp only [Detail.freshTypes]
      exact (induction state.fresh.2).trans rfl

/-- Tuple-pattern inference allocates one fresh expected type per source
element, unifies their product with the caller's expected type, and delegates
the source-ordered children to the recursive list theorem.  Admissibility of
each child follows structurally from the unified product type. -/
private theorem inferMatchPatternFlatFuel_success_tuple_sound
    {source : TypedSource}
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext activeContext : SourceSemantics.Context}
    {outer : TypeSystem.Substitution} {fuel : Nat}
    {pattern : Syntax.Pattern}
    {elements : Syntax.DelimitedList (Syntax.Located Syntax.PatternValue)}
    {expected : TypeSystem.Ty} {seen : List String}
    {initial : Frontend.SourceInference.State}
    {result : Detail.InferredPattern}
    (pattern_eq : pattern.value = .tuple elements)
    (validated : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (stateCallbacks : MatchPatternFlatStateCallbacks inferenceContext)
    (recursive : MatchPatternRecursiveSoundnessCallbacks source
      inferenceContext semanticContext outer)
    (ready : initial.InferenceReady)
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (below : initial.LocalBindersBelowNextLocal)
    (owner_eq : source.owner = initial.owner)
    (seen_nodup : seen.Nodup)
    (semanticAdmissible :
      TypeAdmissible semanticContext (outer.apply expected))
    (activeAdmissible :
      TypeAdmissible activeContext (outer.apply expected))
    (invariant : ActiveLocalContextInvariant initial outer activeContext)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (success : Detail.inferMatchPatternFlatFuel (fuel + 1) inferenceContext
      pattern expected seen initial = .ok result) :
    Nonempty (MatchPatternFlatInferenceCertificate source semanticContext
      activeContext outer expected seen initial result) := by
  have properties := stateCallbacks.pattern ready expectedBelow validated below
    success
  unfold Detail.inferMatchPatternFlatFuel at success
  simp only [pattern_eq, bind, Except.bind] at success
  let elementTypes :=
    (Detail.freshTypes elements.elements.length initial).1
  let allocated :=
    (Detail.freshTypes elements.elements.length initial).2
  have freshEq : Detail.freshTypes elements.elements.length initial =
      (elementTypes, allocated) := by
    exact (Prod.eta _).symm
  simp only [freshEq] at success
  cases unifyResult : Detail.unify allocated expected
      (TypeSystem.Ty.productMany elementTypes) with
  | error error => simp [unifyResult] at success
  | ok unified =>
      simp only [unifyResult] at success
      cases childrenResult : Detail.inferMatchPatternsFlatFuel fuel
          inferenceContext elements.elements elementTypes seen unified with
      | error error => simp [childrenResult] at success
      | ok children =>
          simp only [childrenResult, pure, Pure.pure, Except.pure] at success
          injection success with resultEq
          subst result
          have allocatedProperties := Detail.freshTypes_inferenceProperties
            elements.elements.length initial ready
          simp only [freshEq] at allocatedProperties
          have expectedBelowAllocated :=
            expectedBelow.weaken allocatedProperties.1.next_le
          have productBelow :
              (TypeSystem.Ty.productMany elementTypes).VariablesBelow
                allocated.inference.next :=
            TypeSystem.Ty.variablesBelow_productMany
              allocatedProperties.2.2
          have unifiedProgress := Detail.unify_inferenceProgress
            allocatedProperties.2.1.solved expectedBelowAllocated productBelow
            unifyResult
          have unifiedReady := Detail.unify_preserves_inferenceReady
            allocatedProperties.2.1 expectedBelowAllocated productBelow
            unifyResult
          have allocatedBelow : allocated.LocalBindersBelowNextLocal := by
            have preserved := Detail.freshTypes_preserves_localBindersBelowNextLocal
              elements.elements.length initial below
            simpa only [freshEq] using preserved
          have unifiedBelow : unified.LocalBindersBelowNextLocal :=
            Detail.unify_preserves_localBindersBelowNextLocal allocatedBelow
              unifyResult
          have elementTypesBelow : ∀ type ∈ elementTypes,
              type.VariablesBelow unified.inference.next := by
            intro type member
            exact (allocatedProperties.2.2 type member).weaken
              unifiedProgress.next_le
          have childrenProperties := stateCallbacks.patterns unifiedReady
            elementTypesBelow validated unifiedBelow childrenResult
          have outerUnified : outer.SemanticallyExtends
              unified.inference.substitution :=
            TypeSystem.Substitution.SemanticallyExtends.trans outerExtension
              childrenProperties.1.substitution_extends
          have productEq : outer.apply expected =
              TypeSystem.Ty.productMany (elementTypes.map outer.apply) := by
            calc
              outer.apply expected =
                  outer.apply (unified.resolve expected) :=
                (outerUnified expected).symm
              _ = outer.apply
                  (unified.resolve
                    (TypeSystem.Ty.productMany elementTypes)) :=
                congrArg outer.apply
                  (Detail.unify_resolve_eq unifyResult)
              _ = outer.apply (TypeSystem.Ty.productMany elementTypes) :=
                outerUnified (TypeSystem.Ty.productMany elementTypes)
              _ = TypeSystem.Ty.productMany
                  (elementTypes.map outer.apply) :=
                FlexibleSubstitution.apply_productMany outer elementTypes
          have semanticProduct : TypeAdmissible semanticContext
              (TypeSystem.Ty.productMany (elementTypes.map outer.apply)) := by
            rw [← productEq]
            exact semanticAdmissible
          have activeProduct : TypeAdmissible activeContext
              (TypeSystem.Ty.productMany (elementTypes.map outer.apply)) := by
            rw [← productEq]
            exact activeAdmissible
          have eachSemantic : ∀ type ∈ elementTypes,
              TypeAdmissible semanticContext (outer.apply type) := by
            intro type member
            apply TypeAdmissible.productMany_member semanticProduct
            exact List.mem_map.mpr ⟨type, member, rfl⟩
          have eachActive : ∀ type ∈ elementTypes,
              TypeAdmissible activeContext (outer.apply type) := by
            intro type member
            apply TypeAdmissible.productMany_member activeProduct
            exact List.mem_map.mpr ⟨type, member, rfl⟩
          have allocatedInvariant : ActiveLocalContextInvariant allocated outer
              activeContext := by
            apply invariant.congr_localBinders
            have preserved := freshTypes_preserves_localBinders
              elements.elements.length initial
            simpa only [freshEq] using preserved
          have unifiedInvariant : ActiveLocalContextInvariant unified outer
              activeContext :=
            allocatedInvariant.unify unifyResult
          have allocatedOwner : allocated.owner = initial.owner := by
            have preserved := freshTypes_preserves_owner
              elements.elements.length initial
            simpa only [freshEq] using preserved
          have unifiedOwner : unified.owner = allocated.owner := by
            have headerEq := Detail.unify_state_header unifyResult
            simpa [Frontend.SourceInference.State.header] using
              congrArg Frontend.SourceInference.State.Header.owner headerEq
          have recursiveOwner : source.owner = unified.owner :=
            owner_eq.trans (allocatedOwner.symm.trans unifiedOwner.symm)
          obtain ⟨childrenCertificate⟩ := recursive.patterns
            unifiedReady elementTypesBelow unifiedBelow recursiveOwner
            seen_nodup
            eachSemantic eachActive
            unifiedInvariant outerExtension childrenResult
          have arity : elements.elements.length =
              (elementTypes.map outer.apply).length := by
            have lengthEq := freshTypes_length elements.elements.length initial
            simp only [freshEq] at lengthEq
            simpa using lengthEq.symm
          exact ⟨{
            binders := childrenCertificate.binders
            rootArity := elements.elements.length
            finalContext := childrenCertificate.finalContext
            source_represents := .tuple
            instructions_eq := rfl
            instruction_type := fun suffix => by
              have typed := PatternInstructionHasType.tuple
                (context := semanticContext)
                (instructions := children.instructions.map
                  (MatchPatternInstruction.applySubstitution outer) ++ suffix)
                (rest := suffix)
                (elementCount := elements.elements.length)
                (elementTypes := elementTypes.map outer.apply)
                (requirements := children.requirements)
                (binders := childrenCertificate.binders)
                arity (childrenCertificate.instructions_type suffix)
              rw [productEq]
              simpa [MatchPatternInstruction.applySubstitution] using typed
            binders_extend := childrenCertificate.binders_extend
            invariant := childrenCertificate.invariant
            progress := properties.1
            ready := properties.2.1
            below := properties.2.2.1
            owner_eq := properties.2.2.2
            names_eq := childrenCertificate.names_eq
            names_nodup := childrenCertificate.names_nodup
          }⟩

/-- Public one-layer dispatcher for successful flat pattern inference.

The dispatcher rules out the two executable error-only forms, proves
wildcards directly, and transports every field of a strict recursive
certificate through grouping.  Literal and constructor forms cross the
  explicit branch-specific certificate boundary above.  Tuple assembly and
admissibility projection are proved directly. -/
theorem inferMatchPatternFlatFuel_success_sound_of_callbacks
    {source : TypedSource}
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext activeContext : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    {fuel : Nat} {pattern : Syntax.Pattern} {expected : TypeSystem.Ty}
    {seen : List String} {initial : Frontend.SourceInference.State}
    {result : Detail.InferredPattern}
    (validated : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (recursive : MatchPatternRecursiveSoundnessCallbacks source
      inferenceContext semanticContext outer)
    (branches : MatchPatternBranchSoundnessCallbacks source
      inferenceContext semanticContext outer)
    (ready : initial.InferenceReady)
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (below : initial.LocalBindersBelowNextLocal)
    (owner_eq : source.owner = initial.owner)
    (semanticOwner : semanticContext.currentDeclaration = some source.owner)
    (seen_nodup : seen.Nodup)
    (semanticAdmissible :
      TypeAdmissible semanticContext (outer.apply expected))
    (activeAdmissible :
      TypeAdmissible activeContext (outer.apply expected))
    (invariant : ActiveLocalContextInvariant initial outer activeContext)
    (outerExtension : outer.SemanticallyExtends
      result.state.inference.substitution)
    (success : Detail.inferMatchPatternFlatFuel fuel inferenceContext pattern
      expected seen initial = .ok result) :
    Nonempty (MatchPatternFlatInferenceCertificate source semanticContext
      activeContext outer expected seen initial result) := by
  let stateCallbacks := matchPatternFlatStateCallbacks inferenceContext
  cases fuel with
  | zero =>
      simp [Detail.inferMatchPatternFlatFuel] at success
  | succ fuel =>
      cases valueEq : pattern.value with
      | wildcard marker =>
          exact inferMatchPatternFlatFuel_success_wildcard_sound
            valueEq stateCallbacks ready expectedBelow validated below owner_eq
            seen_nodup invariant (by
              simpa only [Nat.succ_eq_add_one] using success)
      | literal literal =>
          exact branches.literal valueEq ready expectedBelow validated below
            owner_eq semanticOwner seen_nodup semanticAdmissible
            activeAdmissible invariant outerExtension success
      | binder name =>
          exact inferMatchPatternFlatFuel_success_binder_sound valueEq
            stateCallbacks ready expectedBelow validated below owner_eq
            semanticOwner seen_nodup semanticAdmissible activeAdmissible
            invariant outerExtension (by
              simpa only [Nat.succ_eq_add_one] using success)
      | constructor leadingDot qualifiers name arguments =>
          exact branches.constructor valueEq ready expectedBelow validated below
            owner_eq semanticOwner seen_nodup semanticAdmissible
            activeAdmissible invariant outerExtension success
      | comptime keyword expression =>
          simp [Detail.inferMatchPatternFlatFuel, valueEq] at success
      | group inner =>
          unfold Detail.inferMatchPatternFlatFuel at success
          simp only [valueEq, bind, Except.bind] at success
          cases innerSuccess : Detail.inferMatchPatternFlatFuel fuel
              inferenceContext inner expected seen initial with
          | error error => simp [innerSuccess] at success
          | ok innerResult =>
              simp only [innerSuccess, pure, Pure.pure, Except.pure] at success
              injection success with resultEq
              subst result
              have innerOuter : outer.SemanticallyExtends
                  innerResult.state.inference.substitution := outerExtension
              obtain ⟨certificate⟩ := recursive.pattern
                (result := innerResult) ready expectedBelow
                below owner_eq seen_nodup semanticAdmissible activeAdmissible
                invariant innerOuter innerSuccess
              exact ⟨{
                binders := certificate.binders
                rootArity := certificate.rootArity
                finalContext := certificate.finalContext
                source_represents :=
                  MatchPatternSourceRepresents.group
                    certificate.source_represents
                instructions_eq := certificate.instructions_eq
                instruction_type := certificate.instruction_type
                binders_extend := certificate.binders_extend
                invariant := certificate.invariant
                progress := certificate.progress
                ready := certificate.ready
                below := certificate.below
                owner_eq := certificate.owner_eq
                names_eq := certificate.names_eq
                names_nodup := certificate.names_nodup
              }⟩
      | tuple elements =>
          exact inferMatchPatternFlatFuel_success_tuple_sound valueEq validated
            stateCallbacks recursive ready expectedBelow below owner_eq
            seen_nodup semanticAdmissible activeAdmissible invariant
            outerExtension (by
              simpa only [Nat.succ_eq_add_one] using success)
      | error =>
          simp [Detail.inferMatchPatternFlatFuel, valueEq] at success

/-- The semantic certificate for one successfully inferred explicit match
arm.  Pattern inference supplies the substituted pattern typing and the exact
binder extension; statement inference starts from the corresponding active
arm context and supplies both declarative body typing and executable-fact
agreement.  Keeping all witnesses explicit makes this a small assembly
boundary rather than another recursive soundness proof. -/
structure MatchCaseInferenceCertificate
    (source : TypedSource) (control : ControlContext)
    (semanticContext : SourceSemantics.Context)
    (outer : TypeSystem.Substitution)
    (scrutineeType : TypeSystem.Ty)
    (pattern : TypedMatchPattern)
    (patternState : Frontend.SourceInference.State)
    (bodyResult : Detail.BlockResult) where
  binders : List TypedBinder
  rootArity : Nat
  armContext : SourceSemantics.Context
  finalContext : SourceSemantics.Context
  facts : BodyFacts
  pattern_type : TypedMatchPatternHasType semanticContext
    (pattern.applySubstitution outer) (outer.apply scrutineeType) binders
      rootArity
  binders_extend : BindersExtend source.owner semanticContext binders
    armContext
  pattern_invariant : ActiveLocalContextInvariant patternState outer armContext
  body_type : StatementsHaveType source control armContext
    bodyResult.statements finalContext facts
  body_matches : BlockResultMatchesFactsAfterSubstitution outer bodyResult facts

/-- A complete semantic certificate assembles directly into declarative match
arm typing and executable body-fact agreement.  This is only the final adapter:
constructing the certificate from successful pattern and body inference is the
remaining recursive soundness obligation. -/
theorem MatchCaseInferenceCertificate.toMatchCaseHasType
    {scrutineeType : TypeSystem.Ty}
    {patternState : Frontend.SourceInference.State}
    {arm : Syntax.MatchCase} {pattern : TypedMatchPattern}
    {bodyResult : Detail.BlockResult}
    {source : TypedSource} {control : ControlContext}
    {outer : TypeSystem.Substitution}
    {semanticContext : SourceSemantics.Context}
    (certificate : MatchCaseInferenceCertificate source control
      semanticContext outer scrutineeType pattern patternState bodyResult) :
    ∃ facts,
      MatchCaseHasType source control semanticContext
        (outer.apply scrutineeType)
        (({
          span := arm.span
          pattern
          body := bodyResult.statements
        } : TypedMatchCase).applySubstitution outer) facts ∧
      BlockResultMatchesFactsAfterSubstitution outer bodyResult facts := by
  refine ⟨certificate.facts, ?_, certificate.body_matches⟩
  simpa [TypedMatchCase.applySubstitution] using
    (MatchCaseHasType.intro certificate.pattern_type
      certificate.binders_extend certificate.body_type)

/-- Explicit match-case inference is a generic source-ordered traversal over
soundness for one arm.  Restoring the saved lexical scope after every body
reestablishes the common outer invariant for the remaining arms; the supplied
arm callback reconstructs declarative case typing in one finalized source.
The returned facts also agree exactly with the executable all-return fold. -/
theorem inferMatchCasesFuel_success_matchCasesHaveType
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {scrutineeType expectedReturn : TypeSystem.Ty}
    {outerScope : LexicalScope} {cases : List Syntax.MatchCase}
    {state : Frontend.SourceInference.State}
    {result : Detail.MatchCasesResult}
    {source : TypedSource} {control : ControlContext}
    {outer : TypeSystem.Substitution}
    {semanticContext : SourceSemantics.Context}
    (initialInvariant :
      ActiveLocalContextInvariant state outer semanticContext)
    (scopeEq : state.lexicalScope = outerScope)
    (caseSound :
      ∀ {childFuel : Nat} {input : Frontend.SourceInference.State}
        {arm : Syntax.MatchCase} {pattern : TypedMatchPattern}
        {patternState : Frontend.SourceInference.State}
        {bodyResult : Detail.BlockResult},
        ActiveLocalContextInvariant input outer semanticContext →
        Detail.inferMatchPatternFuel childFuel inferenceContext
            arm.value.pattern scrutineeType input =
          .ok (pattern, patternState) →
        Detail.inferStatementsFuel childFuel inferenceContext
            arm.value.body.value expectedReturn patternState = .ok bodyResult →
        ∃ facts,
          MatchCaseHasType source control semanticContext
            (outer.apply scrutineeType)
            (({
              span := arm.span
              pattern
              body := bodyResult.statements
            } : TypedMatchCase).applySubstitution outer) facts ∧
          BlockResultMatchesFactsAfterSubstitution outer bodyResult facts)
    (success : Detail.inferMatchCasesFuel fuel inferenceContext scrutineeType
      expectedReturn outerScope cases state = .ok result) :
    ∃ caseFacts,
      MatchCasesHaveType source control semanticContext
        (outer.apply scrutineeType)
        (result.cases.map (TypedMatchCase.applySubstitution outer)) caseFacts ∧
      allBodiesSawReturn caseFacts = result.allReturn := by
  induction fuel generalizing outerScope cases state result with
  | zero =>
      simp [Detail.inferMatchCasesFuel] at success
  | succ fuel induction =>
      cases cases with
      | nil =>
          unfold Detail.inferMatchCasesFuel at success
          injection success with resultEq
          subst result
          exact ⟨[], .nil control semanticContext
            (outer.apply scrutineeType), rfl⟩
      | cons arm rest =>
          unfold Detail.inferMatchCasesFuel at success
          simp only [bind, Except.bind] at success
          cases patternSuccess : Detail.inferMatchPatternFuel fuel
              inferenceContext arm.value.pattern scrutineeType state with
          | error error =>
              simp [patternSuccess] at success
          | ok patternPair =>
              rcases patternPair with ⟨pattern, patternState⟩
              simp only [patternSuccess] at success
              cases bodySuccess : Detail.inferStatementsFuel fuel
                  inferenceContext arm.value.body.value expectedReturn
                  patternState with
              | error error =>
                  simp [bodySuccess] at success
              | ok bodyResult =>
                  simp only [bodySuccess] at success
                  cases tailSuccess : Detail.inferMatchCasesFuel fuel
                      inferenceContext scrutineeType expectedReturn outerScope
                      rest
                      (bodyResult.state.restoreLexicalScope outerScope) with
                  | error error =>
                      simp [tailSuccess] at success
                  | ok tail =>
                      simp only [tailSuccess] at success
                      injection success with resultEq
                      subst result
                      obtain ⟨headFacts, headTyping, headAgreement⟩ :=
                        caseSound initialInvariant patternSuccess bodySuccess
                      have tailInvariant : ActiveLocalContextInvariant
                          (bodyResult.state.restoreLexicalScope outerScope)
                          outer semanticContext := by
                        rw [← scopeEq]
                        exact initialInvariant.restoreLexicalScope
                      have tailScopeEq :
                          (bodyResult.state.restoreLexicalScope outerScope
                            ).lexicalScope = outerScope := by
                        simp
                      obtain ⟨tailFacts, tailTyping, tailAgreement⟩ :=
                        induction tailInvariant tailScopeEq tailSuccess
                      refine ⟨headFacts :: tailFacts, ?_, ?_⟩
                      · simpa only [List.map_cons] using
                          (MatchCasesHaveType.cons headTyping tailTyping)
                      · change (headFacts.sawReturn &&
                            allBodiesSawReturn tailFacts) =
                          (bodyResult.sawReturn && tail.allReturn)
                        rw [headAgreement.sawReturn_eq, tailAgreement]

/-- Statement-list inference is a generic sequencing layer over soundness for
one statement.  The caller chooses the relation connecting executable states
to lexical semantic contexts and supplies one-statement soundness in the final
common typed source; this theorem threads that relation, builds
`StatementsHaveType`, and proves exact agreement with the executable block
summary. -/
theorem inferStatementsFuel_success_statementsHaveType
    (invariant : Frontend.SourceInference.State →
      SourceSemantics.Context → Prop)
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statements : List Syntax.Statement}
    {expectedReturn : TypeSystem.Ty}
    {state : Frontend.SourceInference.State} {result : Detail.BlockResult}
    {source : TypedSource} {control : ControlContext}
    {substitution : TypeSystem.Substitution}
    {semanticContext : SourceSemantics.Context}
    (initialInvariant : invariant state semanticContext)
    (statementSound :
      ∀ {childFuel : Nat} {input : Frontend.SourceInference.State}
        {inputContext : SourceSemantics.Context}
        {statement : Syntax.Statement} {head : Detail.StatementResult},
        invariant input inputContext →
        Detail.inferStatementFuel childFuel inferenceContext statement
          expectedReturn input = .ok head →
        ∃ outputContext facts,
          invariant head.state outputContext ∧
          StatementHasType source control inputContext head.id outputContext
            facts ∧
          StatementResultMatchesFactsAfterSubstitution substitution head facts)
    (success : Detail.inferStatementsFuel fuel inferenceContext statements
      expectedReturn state = .ok result) :
    ∃ finalContext facts,
      invariant result.state finalContext ∧
      StatementsHaveType source control semanticContext result.statements
        finalContext facts ∧
      BlockResultMatchesFactsAfterSubstitution substitution result facts := by
  induction fuel generalizing statements state semanticContext result with
  | zero =>
      simp [Detail.inferStatementsFuel] at success
  | succ fuel induction =>
      cases statements with
      | nil =>
          have resultEq := inferStatementsFuel_success_nil_facts success
          subst result
          exact ⟨semanticContext, .empty, initialInvariant,
            .nil control semanticContext,
            BlockResultMatchesFactsAfterSubstitution.empty substitution state⟩
      | cons statement rest =>
          cases rest with
          | nil =>
              obtain ⟨head, headSuccess, resultEq⟩ :=
                inferStatementsFuel_success_singleton_facts success
              obtain ⟨finalContext, headFacts, finalInvariant, headTyping,
                  headMatches⟩ :=
                statementSound initialInvariant headSuccess
              subst result
              exact ⟨finalContext, .singleton headFacts, finalInvariant,
                .singleton headTyping,
                BlockResultMatchesFactsAfterSubstitution.singleton headMatches⟩
          | cons next rest =>
              obtain ⟨head, tail, headSuccess, tailSuccess, resultEq⟩ :=
                inferStatementsFuel_success_cons_facts success
              obtain ⟨middleContext, headFacts, middleInvariant, headTyping,
                  headMatches⟩ :=
                statementSound initialInvariant headSuccess
              obtain ⟨finalContext, tailFacts, finalInvariant, tailTyping,
                  tailMatches⟩ :=
                induction middleInvariant tailSuccess
              obtain ⟨tailHead, tailRest, tailStatementsEq⟩ :=
                inferStatementsFuel_success_statements_eq_cons tailSuccess
              have sequenceTyping : StatementsHaveType source control
                  semanticContext (head.id :: tail.statements) finalContext
                  (.cons headFacts tailFacts) := by
                rw [tailStatementsEq]
                exact .cons headTyping
                  (by simpa [tailStatementsEq] using tailTyping)
              subst result
              exact ⟨finalContext, .cons headFacts tailFacts, finalInvariant,
                sequenceTyping,
                BlockResultMatchesFactsAfterSubstitution.cons headMatches
                  tailMatches⟩

/-- A successful local-identifier branch materializes the exact local
reference node used by source semantics.  In particular, the node retains the
canonical allocator position from immediately before scheme instantiation and
keeps the local-scheme requirements as the prefix of any fitted coercion
requirements. -/
theorem inferExprFuel_success_localIdentifier_containsExpression
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier} {binder : TypedBinder}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) context expression expected
      initial = .ok result)
    (roots : List NodeId := []) :
    (let instantiationStart := allocated.inference.next
     let instantiated :=
       binder.scheme.instantiateWithSubstitution instantiationStart
     let inference := {
       allocated.inference with next := instantiated.next
     }
     let advanced : Frontend.SourceInference.State := {
       allocated with inference
     }
     let predicates := binder.schemeRequirements.map fun requirement =>
       Detail.applyPredicate advanced
         (TypedTraitResolution.applySubstitution instantiated.substitution
           requirement.predicate)
     let requirementAllocation := advanced.addRequirementsWithIds predicates
     ∃ coercions,
       ContainsExpression (result.2.toTypedSource roots) result.1.id {
         id := result.1.id
         span := expression.span
         type := result.1.type
         form := .reference name.value (.local binder.id)
         requirements := requirementAllocation.1 ++
           Detail.coercionRequirements coercions
         coercions
         localSchemeInstantiationStart := some instantiationStart
       }) := by
  let instantiationStart := allocated.inference.next
  let instantiated :=
    binder.scheme.instantiateWithSubstitution instantiationStart
  let inference := {
    allocated.inference with next := instantiated.next
  }
  let advanced : Frontend.SourceInference.State := {
    allocated with inference
  }
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution instantiated.substitution
        requirement.predicate)
  let requirementAllocation := advanced.addRequirementsWithIds predicates
  have recorded :
      Detail.recordExpressionWithExpected context expression id
        (advanced.resolve instantiated.body)
        (.reference name.value (.local binder.id)) requirementAllocation.1
        expected requirementAllocation.2
        (localSchemeInstantiationStart := some instantiationStart) =
          .ok result := by
    exact Detail.inferExprFuel_success_localIdentifier_record expressionEq
      allocationEq lookupEq success
  exact recordExpressionWithExpected_success_containsExpression recorded roots

/-- The concrete local-identifier branch exposes, in one place, the exact
recorded node and the three allocation facts later consumed by declarative
local-scheme instantiation.  Keeping this inversion separate from semantic
context closure avoids hiding the executable branch under a large soundness
theorem. -/
theorem inferExprFuel_success_localIdentifier_facts
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier} {binder : TypedBinder}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = some binder)
    (success : Detail.inferExprFuel (fuel + 1) context expression expected
      initial = .ok result)
    (certificate :
      let instantiationStart := allocated.inference.next
      let instantiated :=
        binder.scheme.instantiateWithSubstitution instantiationStart
      let inference := {
        allocated.inference with next := instantiated.next
      }
      let advanced : Frontend.SourceInference.State := {
        allocated with inference
      }
      let predicates := binder.schemeRequirements.map fun requirement =>
        Detail.applyPredicate advanced
          (TypedTraitResolution.applySubstitution instantiated.substitution
            requirement.predicate)
      Frontend.SourceInference.State.LookupBinderRequirementAllocationCertificate
        advanced binder predicates)
    (roots : List NodeId := []) :
    (let instantiationStart := allocated.inference.next
     let instantiated :=
       binder.scheme.instantiateWithSubstitution instantiationStart
     let inference := {
       allocated.inference with next := instantiated.next
     }
     let advanced : Frontend.SourceInference.State := {
       allocated with inference
     }
     let predicates := binder.schemeRequirements.map fun requirement =>
       Detail.applyPredicate advanced
         (TypedTraitResolution.applySubstitution instantiated.substitution
           requirement.predicate)
     let requirementAllocation := advanced.addRequirementsWithIds predicates
     ∃ coercions,
       ContainsExpression (result.2.toTypedSource roots) result.1.id {
         id := result.1.id
         span := expression.span
         type := result.1.type
         form := .reference name.value (.local binder.id)
         requirements := requirementAllocation.1 ++
           Detail.coercionRequirements coercions
         coercions
         localSchemeInstantiationStart := some instantiationStart
       } ∧
       requirementAllocation.1.Nodup ∧
       (∀ requirement, requirement ∈ requirementAllocation.1 →
         requirement ∉ localSchemeTemplateIds binder) ∧
       RequirementPredicatesCorrespond result.2.requirements
         ((instantiateLocalSchemePredicates instantiated.substitution
            binder).map (Detail.applyPredicate advanced))
         requirementAllocation.1) := by
  let instantiationStart := allocated.inference.next
  let instantiated :=
    binder.scheme.instantiateWithSubstitution instantiationStart
  let inference := {
    allocated.inference with next := instantiated.next
  }
  let advanced : Frontend.SourceInference.State := {
    allocated with inference
  }
  let predicates := binder.schemeRequirements.map fun requirement =>
    Detail.applyPredicate advanced
      (TypedTraitResolution.applySubstitution instantiated.substitution
        requirement.predicate)
  let requirementAllocation := advanced.addRequirementsWithIds predicates
  change
    Frontend.SourceInference.State.LookupBinderRequirementAllocationCertificate
      advanced binder predicates at certificate
  change ∃ coercions,
    ContainsExpression (result.2.toTypedSource roots) result.1.id {
      id := result.1.id
      span := expression.span
      type := result.1.type
      form := .reference name.value (.local binder.id)
      requirements := requirementAllocation.1 ++
        Detail.coercionRequirements coercions
      coercions
      localSchemeInstantiationStart := some instantiationStart
    } ∧
    requirementAllocation.1.Nodup ∧
    (∀ requirement, requirement ∈ requirementAllocation.1 →
      requirement ∉ localSchemeTemplateIds binder) ∧
    RequirementPredicatesCorrespond result.2.requirements
      ((instantiateLocalSchemePredicates instantiated.substitution binder).map
        (Detail.applyPredicate advanced)) requirementAllocation.1
  have containsResult :=
    inferExprFuel_success_localIdentifier_containsExpression expressionEq
      allocationEq lookupEq success roots
  change ∃ coercions,
    ContainsExpression (result.2.toTypedSource roots) result.1.id {
      id := result.1.id
      span := expression.span
      type := result.1.type
      form := .reference name.value (.local binder.id)
      requirements := requirementAllocation.1 ++
        Detail.coercionRequirements coercions
      coercions
      localSchemeInstantiationStart := some instantiationStart
    } at containsResult
  obtain ⟨coercions, contains⟩ := containsResult
  have recorded := Detail.inferExprFuel_success_localIdentifier_record
    expressionEq allocationEq lookupEq success
  change Detail.recordExpressionWithExpected context expression id
    (advanced.resolve instantiated.body)
    (.reference name.value (.local binder.id)) requirementAllocation.1
    expected requirementAllocation.2
    (localSchemeInstantiationStart := some instantiationStart) = .ok result
      at recorded
  have correspondence := certificate.correspondence.mono
    (Detail.recordExpressionWithExpected_requirements_subset recorded)
  refine ⟨coercions, contains, certificate.ids_nodup, ?_, ?_⟩
  · intro requirement member
    simpa [localSchemeTemplateIds] using
      certificate.actual_ids_fresh_for_templates requirement member
  · simpa [predicates, instantiateLocalSchemePredicates, List.map_map,
      Function.comp_def] using correspondence

/-- A successful builtin-boolean identifier branch materializes the exact
reference node retained by source semantics.  The form owns no primary
requirements, so every retained requirement belongs to the fitted output
coercion path. -/
theorem inferExprFuel_success_builtinBoolean_containsExpression
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {expression : Syntax.Expr} {expected : Option TypeSystem.Ty}
    {initial allocated : Frontend.SourceInference.State}
    {id : ExpressionId} {name : Syntax.Identifier}
    {result : InferredExpression × Frontend.SourceInference.State}
    (expressionEq : expression.value = .identifier name)
    (allocationEq : initial.allocateExpressionId = (id, allocated))
    (lookupEq : allocated.lookupBinder? name.value = none)
    (booleanName :
      (name.value == "true" || name.value == "false") = true)
    (success : Detail.inferExprFuel (fuel + 1) context expression expected
      initial = .ok result)
    (roots : List NodeId := []) :
    ∃ coercions,
      ContainsExpression (result.2.toTypedSource roots) result.1.id {
        id := result.1.id
        span := expression.span
        type := result.1.type
        form := .reference name.value
          (.builtinBoolean (name.value == "true"))
        requirements := Detail.coercionRequirements coercions
        coercions
      } := by
  have recorded :
      Detail.recordExpressionWithExpected context expression id .bool
        (.reference name.value (.builtinBoolean (name.value == "true"))) []
        expected allocated = .ok result := by
    unfold Detail.inferExprFuel at success
    simp only [allocationEq, expressionEq, lookupEq, booleanName, if_true]
      at success
    exact success
  obtain ⟨coercions, contains⟩ :=
    recordExpressionWithExpected_success_containsExpression recorded roots
  exact ⟨coercions, by simpa using contains⟩

/-- A retained builtin-boolean reference with a valid finalized output path
is a declaratively typed expression.  This is the requirement-free leaf used
by the whole-expression soundness induction. -/
theorem builtinBooleanExpressionHasType_afterSubstitution
    {source : TypedSource} {target : SourceSemantics.Context}
    {outer : TypeSystem.Substitution}
    {expression : Syntax.Expr} {name : Syntax.Identifier}
    {result : InferredExpression} {coercions : List CoercionStep}
    (contains : ContainsExpression source result.id {
      id := result.id
      span := expression.span
      type := result.type
      form := .reference name.value
        (.builtinBoolean (name.value == "true"))
      requirements := Detail.coercionRequirements coercions
      coercions
    })
    (binders : TypeParameterBindersWellFormed target)
    (finalAdmissible : TypeAdmissible target (outer.apply result.type))
    (path : CoercionPathValid target .bool (outer.apply result.type)
      (coercions.map (CoercionStep.applySubstitution outer))) :
    ExpressionHasType (source.applySubstitution outer) target result.id
      (outer.apply result.type) := by
  apply ExpressionHasType.ofOrdinary
    (rawType := .bool) (owned := [])
    (FlexibleSubstitution.ContainsExpression.applySubstitution outer contains)
  · exact .reference (.builtinBoolean (name.value == "true"))
  · exact TypeAdmissible.bool binders
  · exact finalAdmissible
  · intro requirement member
    simp at member
  · exact path
  · change Detail.coercionRequirements coercions =
      coercionRequirementIds
        (coercions.map (CoercionStep.applySubstitution outer))
    rw [FlexibleSubstitution.coercionRequirementIds_applySubstitution]
    rfl

/-- Successful executable graph validation establishes the complete initial
declarative occurrence-graph well-formedness layer. -/
theorem validateSourceGraph_success_occurrenceGraphWellFormed
    {source : TypedSource}
    (success : Detail.validateSourceGraph source = .ok ()) :
    OccurrenceGraphWellFormed source := by
  have unique :=
    Detail.validateSourceGraph_success_nodeOccurrencesUnique success
  have nodesOwned := Detail.validateSourceGraph_success_nodesOwned success
  have rootsExist := Detail.validateSourceGraph_success_rootsExist success
  have childEdges :=
    Detail.validateSourceGraph_success_childEdgesExist success
  refine {
    nodeOccurrencesUnique := by
      simpa [NodeOccurrencesUnique, nodeOccurrenceIds] using unique
    nodesOwned := by
      simpa [NodesOwned, OccurrenceOwnedBy] using nodesOwned
    rootsOwned := rootsOwned_of_nodesOwned_of_rootsExist
      (by simpa [NodesOwned, OccurrenceOwnedBy] using nodesOwned)
      (by simpa [RootsExist, nodeIds] using rootsExist)
    rootsExist := by
      simpa [RootsExist, nodeIds] using rootsExist
    childEdgesExist := by
      simpa [ChildEdgesExist, nodeChildIds, nodeIds] using childEdges
  }

/-- Executable local-identity validation establishes the declarative global
binder ownership invariant over the same canonical source inventory. -/
theorem validateSourceLocalIdentities_success_localIdentityOwnership
    {source : TypedSource}
    (success : Detail.validateSourceLocalIdentities source = .ok ()) :
    LocalIdentityOwnership source := by
  constructor
  · simpa using
      (Detail.validateSourceLocalIdentities_success_unique success)
  · intro id member
    exact Detail.validateSourceLocalIdentities_success_owned success id
      (by simpa using member)

private theorem lookupNodeId?_sound
    {source : TypedSource} {id : NodeId} {node : Node}
    (found : source.lookupNodeId? id = some node) :
    ContainsNode source id node := by
  have rawFound :
      source.nodes.find? (fun candidate => decide (candidate.id = id)) =
        some node := by
    simpa [TypedSource.lookupNodeId?] using found
  have member : node ∈ source.nodes :=
    List.mem_of_find?_eq_some rawFound
  have accepted : decide (node.id = id) = true :=
    List.find?_some
      (p := fun candidate : Node => decide (candidate.id = id)) rawFound
  exact ⟨member, of_decide_eq_true accepted⟩

/-- Every identity returned by the bounded root worklist is declaratively
reachable, provided its pending and already-collected inputs are reachable. -/
private theorem collectReachableNodeIdsFuel_sound
    {source : TypedSource} {fuel : Nat}
    {pending visited : List NodeId}
    (pendingReachable :
      ∀ id, id ∈ pending → Reachable source id)
    (visitedReachable :
      ∀ id, id ∈ visited → Reachable source id) :
    ∀ id,
      id ∈ Detail.collectReachableNodeIdsFuel source fuel pending visited →
        Reachable source id := by
  induction fuel generalizing pending visited with
  | zero =>
      simpa [Detail.collectReachableNodeIdsFuel] using visitedReachable
  | succ fuel induction =>
      cases pending with
      | nil =>
          simpa [Detail.collectReachableNodeIdsFuel] using visitedReachable
      | cons head tail =>
          cases alreadyVisited : Detail.nodeIdMember visited head with
          | true =>
              simp only [Detail.collectReachableNodeIdsFuel, alreadyVisited]
              apply induction
              · intro id member
                exact pendingReachable id (by simp [member])
              · exact visitedReachable
          | false =>
              cases found : source.lookupNodeId? head with
              | none =>
                  simp only [Detail.collectReachableNodeIdsFuel,
                    alreadyVisited, found]
                  apply induction
                  · intro id member
                    exact pendingReachable id (by simp [member])
                  · exact visitedReachable
              | some node =>
                  simp only [Detail.collectReachableNodeIdsFuel,
                    alreadyVisited, found]
                  have headReachable : Reachable source head :=
                    pendingReachable head (by simp)
                  have contains : ContainsNode source head node :=
                    lookupNodeId?_sound found
                  apply induction
                  · intro id member
                    rcases List.mem_append.mp member with childMember | tailMember
                    · exact .child headReachable
                        ⟨node, contains, childMember⟩
                    · exact pendingReachable id (by simp [tailMember])
                  · intro id member
                    rcases List.mem_cons.mp member with rfl | visitedMember
                    · exact headReachable
                    · exact visitedReachable id visitedMember

/-- Every identity collected by the public root worklist is reachable from a
declaration root in the declarative occurrence graph. -/
theorem sourceReachableNodeIds_sound
    (source : TypedSource) :
    ∀ id, id ∈ Detail.sourceReachableNodeIds source →
      Reachable source id := by
  unfold Detail.sourceReachableNodeIds
  apply collectReachableNodeIdsFuel_sound
  · intro id member
    exact .root member
  · simp

private theorem reachableFromSingletonRoot_inReflexiveSubtree
    {source : TypedSource} {root id : NodeId}
    (reachable : Reachable { source with roots := [root] } id) :
    InReflexiveSubtree source root id := by
  induction reachable with
  | @root found member =>
      exact Or.inl (by simpa using member)
  | @child parent child parentReachable edge induction =>
      have sourceEdge : DirectChild source parent child := by
        simpa [DirectChild, ContainsNode] using edge
      rcases induction with parentEq | parentPath
      · subst parent
        exact Or.inr (.direct sourceEdge)
      · exact Or.inr (Descends.trans parentPath (.direct sourceEdge))

/-- Every identity returned by the arbitrary-root executable worklist lies in
the declarative reflexive subtree rooted at that exact occurrence. -/
theorem sourceSubtreeNodeIds_sound
    (source : TypedSource) (root : NodeId) :
    ∀ id, id ∈ Detail.sourceSubtreeNodeIds source root →
      InReflexiveSubtree source root id := by
  intro id member
  apply reachableFromSingletonRoot_inReflexiveSubtree
  exact sourceReachableNodeIds_sound { source with roots := [root] } id (by
    simpa [Detail.sourceSubtreeNodeIds] using member)

/-- The executable template-scope validator and raw-ledger identity
uniqueness construct the exact declarative scoped-row witness for any source
template row. -/
theorem validateSourceTemplateScopes_success_rowScoped
    {source : TypedSource} {state : Frontend.SourceInference.State}
    (scopeSuccess : Detail.validateSourceTemplateScopes source state = .ok ())
    (ledgerUnique :
      (state.requirements.map fun requirement => requirement.id).Nodup)
    {requirement : Requirement}
    (requirementMember : requirement ∈ state.requirements)
    (templateMember :
      requirement.id ∈ sourceLocalSchemeTemplateIds source) :
    LocalSchemeTemplateRowScoped source {
      id := requirement.id
      predicate := Detail.applyPredicate state requirement.predicate
      evidence := .assumption
        (Detail.applyPredicate state requirement.predicate)
    } := by
  have executableTemplateMember :
      requirement.id ∈ source.localSchemeTemplateIds := by
    simpa using templateMember
  rw [typedSourceLocalSchemeTemplateIds_eq_sites] at executableTemplateMember
  rcases List.mem_map.mp executableTemplateMember with
    ⟨site, siteMember, siteIdEq⟩
  obtain ⟨selected, primary, selectedMember, selectedId,
      predicateEq, primaryMember, primaryId, primaryScoped⟩ :=
    Detail.validateSourceTemplateScopes_success scopeSuccess site siteMember
  have selectedEq : selected = requirement :=
    StructuralSubstitution.eq_of_mem_of_mapped_nodup ledgerUnique
      selectedMember requirementMember (selectedId.trans siteIdEq)
  subst selected
  have contains : ContainsLocalSchemeTemplate source site := by
    unfold ContainsLocalSchemeTemplate
    rw [← typedSourceLocalSchemeTemplateSites_eq_carrier]
    exact siteMember
  have primaryRequirementEq : primary.requirement = requirement.id :=
    primaryId.trans siteIdEq
  have occurs : PrimaryRequirementOccursAt source primary.occurrence
      requirement.id := by
    unfold PrimaryRequirementOccursAt
    rw [← typedSourcePrimaryRequirementSites_eq_carrier]
    cases primary with
    | mk occurrence primaryRequirement =>
        simp only at primaryRequirementEq ⊢
        subst primaryRequirement
        exact primaryMember
  exact .intro site contains siteIdEq.symm predicateEq
    (congrArg PredicateEvidence.assumption predicateEq)
    primary.occurrence occurs
    ⟨contains, sourceSubtreeNodeIds_sound source site.initializer
      primary.occurrence primaryScoped⟩

/-- Successful executable graph validation proves that every retained node is
reachable from one of the exact declaration roots. -/
theorem validateSourceGraph_success_allNodesReachable
    {source : TypedSource}
    (success : Detail.validateSourceGraph source = .ok ()) :
    AllNodesReachable source := by
  intro node member
  exact sourceReachableNodeIds_sound source node.id
    (Detail.validateSourceGraph_success_allNodesReached success node member)

/-- Successful executable validation establishes full rooted-forest closure,
including unique parents, total reachability, and acyclicity. -/
theorem validateSourceGraph_success_occurrenceGraphClosed
    {source : TypedSource}
    (success : Detail.validateSourceGraph source = .ok ()) :
    OccurrenceGraphClosed source :=
  OccurrenceGraphClosed.of_wellFormed_incomingUnique_reachable
    (validateSourceGraph_success_occurrenceGraphWellFormed success)
    (Detail.validateSourceGraph_success_incomingNodeIds_nodup success)
    (validateSourceGraph_success_allNodesReachable success)

/-- Successful finalization emits a source whose occurrence table, roots, and
direct child edges satisfy the declarative graph invariant. -/
theorem finalize_occurrenceGraphWellFormed
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    OccurrenceGraphWellFormed result.typedSource := by
  have inputWellFormed :
      OccurrenceGraphWellFormed (state.toTypedSource roots) :=
    validateSourceGraph_success_occurrenceGraphWellFormed
      (Detail.finalize_validateSourceGraph success)
  rw [Detail.finalize_typedSource success]
  exact FlexibleSubstitution.OccurrenceGraphWellFormed.applySubstitution
    result.substitution inputWellFormed

/-- Successful finalization emits a fully closed rooted occurrence forest. -/
theorem finalize_occurrenceGraphClosed
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    OccurrenceGraphClosed result.typedSource := by
  have inputClosed : OccurrenceGraphClosed (state.toTypedSource roots) :=
    validateSourceGraph_success_occurrenceGraphClosed
      (Detail.finalize_validateSourceGraph success)
  rw [Detail.finalize_typedSource success]
  exact FlexibleSubstitution.OccurrenceGraphClosed.applySubstitution
    result.substitution inputClosed

/-- Every successfully checked function body retains a closed occurrence
forest, including exact ownership, incoming-edge uniqueness and reachability. -/
theorem checkFunctionBody_success_occurrenceGraphClosed
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    OccurrenceGraphClosed checked.typedBody := by
  obtain ⟨_, _, _, _, _, _, _, finalizeSuccess, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  exact finalize_occurrenceGraphClosed finalizeSuccess

/-- Successful finalization validates every local definition before closing
types, and final substitution preserves those stable identities exactly. -/
theorem finalize_localIdentityOwnership
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    LocalIdentityOwnership result.typedSource := by
  rw [Detail.finalize_typedSource success]
  exact FlexibleSubstitution.LocalIdentityOwnership.applySubstitution
    result.substitution
    (validateSourceLocalIdentities_success_localIdentityOwnership
      (Detail.finalize_validateSourceLocalIdentities success))

/-- Every successfully checked function body carries globally unique stable
locals owned by that function declaration. -/
theorem checkFunctionBody_success_localIdentityOwnership
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    LocalIdentityOwnership checked.typedBody := by
  obtain ⟨_, _, _, _, _, _, _, finalizeSuccess, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  exact finalize_localIdentityOwnership finalizeSuccess

/-- Every expression entry root supplied to successful finalization has a
concrete expression node in the emitted source. -/
theorem finalize_expression_root_exists
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    {id : ExpressionId} (member : NodeId.expression id ∈ roots) :
    ∃ node, ContainsExpression result.typedSource id node := by
  apply (finalize_occurrenceGraphWellFormed success).expression_root_exists
  rw [Detail.finalize_typedSource success]
  simpa [Frontend.SourceInference.State.toTypedSource] using member

/-- Every statement entry root supplied to successful finalization has a
concrete statement node in the emitted source. -/
theorem finalize_statement_root_exists
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    {id : StatementId} (member : NodeId.statement id ∈ roots) :
    ∃ node, ContainsStatement result.typedSource id node := by
  apply (finalize_occurrenceGraphWellFormed success).statement_root_exists
  rw [Detail.finalize_typedSource success]
  simpa [Frontend.SourceInference.State.toTypedSource] using member

/-- Finalization transports every retained expression node into the emitted
typed source under exactly the substitution returned to callers. -/
theorem finalize_containsExpression_of_mem
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    {node : ExpressionNode}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    (member : Node.expression node ∈ state.nodes) :
    ContainsExpression result.typedSource node.id
      (node.applySubstitution result.substitution) := by
  rw [Detail.finalize_typedSource success]
  exact FlexibleSubstitution.ContainsExpression.applySubstitution
    result.substitution
    (toTypedSource_containsExpression_of_mem member roots)

/-- Finalization transports every retained statement node into the emitted
typed source under exactly the substitution returned to callers. -/
theorem finalize_containsStatement_of_mem
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty} {state : Frontend.SourceInference.State}
    {roots : List NodeId} {result : Frontend.SourceInference.Result}
    {node : StatementNode}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    (member : Node.statement node ∈ state.nodes) :
    ContainsStatement result.typedSource node.id
      (node.applySubstitution result.substitution) := by
  rw [Detail.finalize_typedSource success]
  exact FlexibleSubstitution.ContainsStatement.applySubstitution
    result.substitution
    (toTypedSource_containsStatement_of_mem member roots)

/-- The executable binary dispatch table agrees exactly with the declarative
trait dispatch relation on every trait-backed spelling. -/
theorem binaryOperatorDispatch_traitMethod
    {operator : Syntax.BinaryOp} {traitName methodName : String}
    (dispatch : Detail.binaryOperatorDispatch operator =
      .traitMethod traitName methodName) :
    BinaryTraitDispatch operator traitName methodName := by
  cases operator <;>
    simp [Detail.binaryOperatorDispatch] at dispatch
  all_goals rcases dispatch with ⟨rfl, rfl⟩
  all_goals constructor

/-- The executable unary dispatch table agrees exactly with the declarative
trait dispatch relation on its trait-backed spelling. -/
theorem unaryOperatorDispatch_traitMethod
    {operator : Syntax.UnaryOp} {traitName methodName : String}
    (dispatch : Detail.unaryOperatorDispatch operator =
      .traitMethod traitName methodName) :
    UnaryTraitDispatch operator traitName methodName := by
  cases operator <;>
    simp [Detail.unaryOperatorDispatch] at dispatch
  rcases dispatch with ⟨rfl, rfl⟩
  constructor

/-- Exact successful branch retained by unary-operator inference before final
substitution.  The only non-semantic primitive case is an open integer-literal
target deliberately deferred to finalization. -/
inductive UnaryOperatorInferenceCase
    (inferenceContext : Frontend.SourceInference.Context)
    (semanticContext : SourceSemantics.Context)
    (initial : Frontend.SourceInference.State)
    (operator : Syntax.UnaryOp) (operandType : TypeSystem.Ty)
    (integerLiterals : List IntegerLiteralOrigin)
    (result : Detail.OperatorInferenceResult) : Prop where
  | primitive
      (typing : UnaryOperatorHasType semanticContext operator
        (result.state.resolve operandType) result.type result.requirements) :
      UnaryOperatorInferenceCase inferenceContext semanticContext initial
        operator operandType integerLiterals result
  | deferredBitNot
      (operator_eq : operator = .bitNot)
      (requirements_eq : result.requirements = [])
      (type_eq : result.type = result.state.resolve operandType)
      (deferred : Detail.isDeferredBuiltinOperatorTarget result.state
        (Detail.isOpenIntegerLiteralTarget initial integerLiterals operandType)
        .word (result.state.resolve operandType) = true) :
      UnaryOperatorInferenceCase inferenceContext semanticContext initial
        operator operandType integerLiterals result
  | trait
      {trait : Resolved.DeclarationId} {traitName methodName : String}
      {predicates : List ProgramPredicate}
      (dispatch : UnaryTraitDispatch operator traitName methodName)
      (selected : Detail.operatorTrait? inferenceContext traitName =
        .ok (some trait))
      (profile : Detail.operatorTraitPredicates inferenceContext trait
        methodName (result.state.resolve operandType)
        [result.state.resolve operandType] [result.type] = .ok predicates)
      (corresponds : RequirementPredicatesCorrespond result.state.requirements
        predicates result.requirements) :
      UnaryOperatorInferenceCase inferenceContext semanticContext initial
        operator operandType integerLiterals result

/-- Exact successful branch retained by binary-operator inference before final
substitution.  Direct builtins already carry declarative typing, trait calls retain
their selected profile and requirement correspondence, and the literal-only
fallback is isolated for final defaulting. -/
inductive BinaryOperatorInferenceCase
    (inferenceContext : Frontend.SourceInference.Context)
    (semanticContext : SourceSemantics.Context)
    (initial : Frontend.SourceInference.State)
    (operator : Syntax.BinaryOp) (left right : TypeSystem.Ty)
    (integerLiterals : List IntegerLiteralOrigin)
    (result : Detail.OperatorInferenceResult) : Prop where
  | primitive
      (typing : BinaryOperatorHasType semanticContext operator
        (result.state.resolve left) (result.state.resolve right)
        result.type result.requirements) :
      BinaryOperatorInferenceCase inferenceContext semanticContext initial
        operator left right integerLiterals result
  | literalFallback
      (requirements_eq : result.requirements = [])
      (operands_eq : result.state.resolve left = result.state.resolve right)
      (type_eq : result.type = if Detail.binaryResultIsBool operator
        then .bool else result.state.resolve left)
      (fallback :
        Detail.isDeferredBuiltinOperatorTarget result.state
            (Detail.isOpenIntegerLiteralTarget initial integerLiterals left ||
              Detail.isOpenIntegerLiteralTarget initial integerLiterals right)
            (Detail.binaryBuiltinType operator)
            (result.state.resolve left) = true ∨
          Detail.isStagedIntegerOperatorTarget result.state
            (Detail.isOpenIntegerLiteralTarget initial integerLiterals left ||
              Detail.isOpenIntegerLiteralTarget initial integerLiterals right)
            (Detail.binaryBuiltinType operator)
            (result.state.resolve left) = true) :
      BinaryOperatorInferenceCase inferenceContext semanticContext initial
        operator left right integerLiterals result
  | trait
      {trait : Resolved.DeclarationId} {traitName methodName : String}
      {predicates : List ProgramPredicate}
      (operands_eq : result.state.resolve left = result.state.resolve right)
      (dispatch : BinaryTraitDispatch operator traitName methodName)
      (selected : Detail.operatorTrait? inferenceContext traitName =
        .ok (some trait))
      (profile : Detail.operatorTraitPredicates inferenceContext trait
        methodName (result.state.resolve left)
        [result.state.resolve left, result.state.resolve left] [result.type] =
          .ok predicates)
      (corresponds : RequirementPredicatesCorrespond result.state.requirements
        predicates result.requirements) :
      BinaryOperatorInferenceCase inferenceContext semanticContext initial
        operator left right integerLiterals result

/-- The fixed builtin type and result table is a declarative binary typing
table for every operator spelling. -/
theorem binaryBuiltin_hasType
    (context : SourceSemantics.Context) (operator : Syntax.BinaryOp) :
    BinaryOperatorHasType context operator
      (Detail.binaryBuiltinType operator)
      (Detail.binaryBuiltinType operator)
      (if Detail.binaryResultIsBool operator then .bool
        else Detail.binaryBuiltinType operator) [] := by
  cases operator <;>
    simp [Detail.binaryBuiltinType, Detail.binaryResultIsBool]
  all_goals constructor
  all_goals constructor

/-- Every Word-backed binary builtin also has the staged integer typing used
while literal targets are being finalized. -/
theorem binaryInteger_hasType
    (context : SourceSemantics.Context) (operator : Syntax.BinaryOp)
    (word_builtin : Detail.binaryBuiltinType operator = TypeSystem.Ty.word) :
    BinaryOperatorHasType context operator .integer .integer
      (if Detail.binaryResultIsBool operator then .bool else .integer) [] := by
  cases operator <;>
    simp [Detail.binaryBuiltinType, Detail.binaryResultIsBool,
      TypeSystem.Ty.bool, TypeSystem.Ty.word] at word_builtin ⊢
  all_goals constructor
  all_goals constructor

/-- Requirement allocation leaves the inference substitution, and therefore
type resolution, unchanged. -/
@[simp] theorem addRequirementsWithIds_resolve
    (state : Frontend.SourceInference.State)
    (predicates : List ProgramPredicate) (type : TypeSystem.Ty) :
    (state.addRequirementsWithIds predicates).2.resolve type =
      state.resolve type := by
  induction predicates generalizing state with
  | nil => rfl
  | cons predicate rest induction =>
      simp only [Frontend.SourceInference.State.addRequirementsWithIds]
      rw [induction]
      rfl

/-- Allocating a source-ordered predicate row records exactly the returned
requirement identities in the enlarged canonical ledger. -/
theorem addRequirementsWithIds_correspond
    (state : Frontend.SourceInference.State)
    (predicates : List ProgramPredicate) :
    RequirementPredicatesCorrespond
      (state.addRequirementsWithIds predicates).2.requirements predicates
      (state.addRequirementsWithIds predicates).1 :=
  Frontend.SourceInference.State.addRequirementsWithIds_correspond
    state predicates

/-- Every successful unary-operator inference step is already a declarative
primitive or trait typing, except for the one open Word-literal target which
is intentionally left to final defaulting.  Solvedness is explicit because
the staged-integer test normalizes an already resolved operand once more. -/
theorem inferUnaryOperator_success_case
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext : SourceSemantics.Context}
    {operator : Syntax.UnaryOp} {operandType : TypeSystem.Ty}
    {expected : Option TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {initial : Frontend.SourceInference.State}
    {result : Detail.OperatorInferenceResult}
    (success : Detail.inferUnaryOperator inferenceContext operator operandType
      expected integerLiterals initial = .ok result)
    (result_solved : result.state.inference.Solved) :
    UnaryOperatorInferenceCase inferenceContext semanticContext initial
      operator operandType integerLiterals result := by
  have resolve_idempotent :
      result.state.resolve (result.state.resolve operandType) =
        result.state.resolve operandType := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
        result_solved.apply_idempotent operandType
  have logicalNot_beq :
      (Syntax.UnaryOp.logicalNot == Syntax.UnaryOp.logicalNot) = true := rfl
  have bitNot_beq :
      (Syntax.UnaryOp.bitNot == Syntax.UnaryOp.logicalNot) = false := rfl
  have bool_word_beq :
      (TypeSystem.Ty.bool == TypeSystem.Ty.word) = false := rfl
  have word_word_beq :
      (TypeSystem.Ty.word == TypeSystem.Ty.word) = true := rfl
  cases operator <;>
    unfold Detail.inferUnaryOperator at success <;>
    simp_all [bind, Except.bind] <;>
    repeat' first | split at success
  all_goals try cases success
  all_goals try simp_all [Detail.unaryOperatorDispatch]
  all_goals try exact .primitive (by
    simp_all
    first | exact .logicalNot | exact .wordBitNot | exact .integerBitNot)
  all_goals try simp_all [Detail.isDeferredBuiltinOperatorTarget,
    Detail.isStagedIntegerOperatorTarget, bool_word_beq, word_word_beq]
  all_goals try grind [Detail.isDeferredBuiltinOperatorTarget,
    Detail.isStagedIntegerOperatorTarget, TypeSystem.Ty.bool,
    TypeSystem.Ty.word, TypeSystem.Ty.integer]
  all_goals try obtain ⟨rfl, rfl⟩ := ‹"BitNot" = _ ∧ "bnot" = _›
  all_goals subst_vars
  all_goals first
    | exact UnaryOperatorInferenceCase.trait
        (dispatch := UnaryTraitDispatch.bitNot)
        (selected := by assumption)
        (profile := by simpa using (by assumption))
        (corresponds := addRequirementsWithIds_correspond _ _)
    | skip
  all_goals
    rcases ‹_ ∨ _› with deferred | staged
    · exact UnaryOperatorInferenceCase.deferredBitNot rfl rfl rfl (by simp_all)
    · exact UnaryOperatorInferenceCase.primitive (by
        simp_all [Detail.isStagedIntegerOperatorTarget, TypeSystem.Ty.word]
        exact UnaryOperatorHasType.integerBitNot)

/-- The tail shared by all expected-type branches of binary inference.  This
is definitionally the suffix of `Detail.inferBinaryOperator`; naming it keeps
the successful branch inversion local and readable. -/
private def finishBinaryOperator
    (context : Frontend.SourceInference.Context) (operator : Syntax.BinaryOp)
    (left right : TypeSystem.Ty)
    (integerLiterals : List IntegerLiteralOrigin)
    (initial state : Frontend.SourceInference.State) :
    Except Frontend.SourceInference.Error Detail.OperatorInferenceResult := do
  let hasOpenLiteralOperand :=
    Detail.isOpenIntegerLiteralTarget initial integerLiterals left ||
      Detail.isOpenIntegerLiteralTarget initial integerLiterals right
  let operand := state.resolve left
  let builtin := Detail.binaryBuiltinType operator
  if operand = builtin then
    pure {
      type := if Detail.binaryResultIsBool operator then .bool else builtin
      requirements := []
      state
    }
  else
    match Detail.binaryOperatorDispatch operator with
    | .function name =>
        if Detail.isDeferredBuiltinOperatorTarget state hasOpenLiteralOperand
              builtin operand ||
            Detail.isStagedIntegerOperatorTarget state hasOpenLiteralOperand
              builtin operand then
          pure {
            type := if Detail.binaryResultIsBool operator then .bool else operand
            requirements := []
            state
          }
        else
          throw (.unknownVariable name)
    | .traitMethod traitName methodName =>
        match ← Detail.operatorTrait? context traitName with
        | some trait =>
            let result := if Detail.binaryResultIsBool operator then .bool
              else operand
            let predicates ←
              Detail.operatorTraitPredicates context trait methodName operand
                [operand, operand] [result]
            let (requirements, state) :=
              state.addRequirementsWithIds predicates
            pure { type := result, requirements, state }
        | none =>
            if Detail.isDeferredBuiltinOperatorTarget state
                  hasOpenLiteralOperand builtin operand ||
                Detail.isStagedIntegerOperatorTarget state
                  hasOpenLiteralOperand builtin operand then
              pure {
                type := if Detail.binaryResultIsBool operator then .bool
                  else operand
                requirements := []
                state
              }
            else
              throw (.operatorNotSupported traitName operand)

private theorem finishBinaryOperator_success_case
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext : SourceSemantics.Context}
    {operator : Syntax.BinaryOp} {left right : TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {initial state : Frontend.SourceInference.State}
    {result : Detail.OperatorInferenceResult}
    (operands_eq : state.resolve left = state.resolve right)
    (success : finishBinaryOperator inferenceContext operator left right
      integerLiterals initial state = .ok result) :
    BinaryOperatorInferenceCase inferenceContext semanticContext initial
      operator left right integerLiterals result := by
  unfold finishBinaryOperator at success
  simp only [pure, Pure.pure, Except.pure, bind, Except.bind] at success
  by_cases operand_builtin :
      state.resolve left = Detail.binaryBuiltinType operator
  · simp [operand_builtin] at success
    cases success
    exact .primitive (by
      rw [← operands_eq, operand_builtin]
      exact binaryBuiltin_hasType semanticContext operator)
  · cases dispatch_eq : Detail.binaryOperatorDispatch operator with
    | function name =>
        simp only [operand_builtin, ↓reduceIte, dispatch_eq] at success
        by_cases fallback :
            (Detail.isDeferredBuiltinOperatorTarget state
                  (Detail.isOpenIntegerLiteralTarget initial integerLiterals
                    left ||
                    Detail.isOpenIntegerLiteralTarget initial integerLiterals
                      right)
                  (Detail.binaryBuiltinType operator) (state.resolve left) ||
              Detail.isStagedIntegerOperatorTarget state
                  (Detail.isOpenIntegerLiteralTarget initial integerLiterals
                    left ||
                    Detail.isOpenIntegerLiteralTarget initial integerLiterals
                      right)
                  (Detail.binaryBuiltinType operator) (state.resolve left)) =
              true
        · simp [fallback] at success
          cases success
          exact .literalFallback rfl operands_eq rfl (by simpa using fallback)
        · simp [fallback] at success
    | traitMethod traitName methodName =>
        simp only [operand_builtin, ↓reduceIte, dispatch_eq] at success
        cases selected : Detail.operatorTrait? inferenceContext traitName with
        | error error => simp [selected] at success
        | ok selection =>
            cases selection with
            | none =>
                by_cases fallback :
                    (Detail.isDeferredBuiltinOperatorTarget state
                          (Detail.isOpenIntegerLiteralTarget initial
                              integerLiterals left ||
                            Detail.isOpenIntegerLiteralTarget initial
                              integerLiterals right)
                          (Detail.binaryBuiltinType operator)
                          (state.resolve left) ||
                      Detail.isStagedIntegerOperatorTarget state
                          (Detail.isOpenIntegerLiteralTarget initial
                              integerLiterals left ||
                            Detail.isOpenIntegerLiteralTarget initial
                              integerLiterals right)
                          (Detail.binaryBuiltinType operator)
                          (state.resolve left)) = true
                · simp [selected, fallback] at success
                  cases success
                  exact .literalFallback rfl operands_eq rfl
                    (by simpa using fallback)
                · simp [selected, fallback] at success
            | some trait =>
                cases profile : Detail.operatorTraitPredicates inferenceContext
                    trait methodName (state.resolve left)
                    [state.resolve left, state.resolve left]
                    [if Detail.binaryResultIsBool operator then .bool
                      else state.resolve left] with
                | error error => simp [selected, profile] at success
                | ok predicates =>
                    simp [selected, profile] at success
                    cases success
                    exact .trait
                      (operands_eq := by simpa using operands_eq)
                      (dispatch :=
                        binaryOperatorDispatch_traitMethod dispatch_eq)
                      (selected := selected)
                      (profile := by simpa using profile)
                      (corresponds :=
                        addRequirementsWithIds_correspond state predicates)

/-- Every successful binary-operator inference step is exactly a direct
builtin, a selected trait profile with its allocated evidence rows, or the
literal-only fallback deliberately left to final defaulting. -/
theorem inferBinaryOperator_success_case
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext : SourceSemantics.Context}
    {operator : Syntax.BinaryOp} {left right : TypeSystem.Ty}
    {expected : Option TypeSystem.Ty}
    {integerLiterals : List IntegerLiteralOrigin}
    {initial : Frontend.SourceInference.State}
    {result : Detail.OperatorInferenceResult}
    (success : Detail.inferBinaryOperator inferenceContext operator left right
      expected integerLiterals initial = .ok result) :
    BinaryOperatorInferenceCase inferenceContext semanticContext initial
      operator left right integerLiterals result := by
  unfold Detail.inferBinaryOperator at success
  simp only [bind, Except.bind] at success
  cases first_unify : Detail.unify initial left right with
  | error error => simp [first_unify] at success
  | ok unified =>
      have unified_eq := Detail.unify_resolve_eq first_unify
      simp only [first_unify] at success
      cases expected with
      | none =>
          simp only [pure, Pure.pure, Except.pure]
            at success
          exact finishBinaryOperator_success_case unified_eq success
      | some expected =>
          simp only [pure, Pure.pure, Except.pure]
            at success
          split at success
          · exact finishBinaryOperator_success_case unified_eq success
          · cases second_unify : Detail.unify unified
                (unified.resolve left) expected with
            | error error => simp [second_unify] at success
            | ok prepared =>
                have prepared_eq :=
                  Detail.unify_preserves_resolve_eq unified_eq second_unify
                simp only [second_unify] at success
                exact finishBinaryOperator_success_case prepared_eq success

/-- A successfully loaded coercion-method profile and its successfully
instantiated predicate row supply the declarative `Coerce` profile used by
source typing.  The explicit name premise isolates the remaining
environment-to-signature catalog alignment obligation; independently assembled
inference contexts are not otherwise required to keep those names aligned. -/
theorem coercionMethodProfile?_some_instantiates
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext : SourceSemantics.Context}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {source target : TypeSystem.Ty}
    {methodPredicates : List ProgramPredicate}
    (signatures_eq :
      semanticContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (predicates_success :
      Detail.coercionMethodPredicates (some profile) source target =
        .ok methodPredicates) :
    CoercionProfileInstantiates semanticContext source target {
      trait := .declaration trait
      subject := source
      arguments := [target]
    } methodPredicates := by
  cases signature_lookup : inferenceContext.signatures.trait? trait with
  | none =>
      simp [signature_lookup] at trait_name
  | some signature =>
      have signature_name : signature.name = "Coerce" := by
        simpa [signature_lookup] using trait_name
      have signature_facts := trait?_eq_some_facts signature_lookup
      simp only [Detail.coercionMethodProfile?, signature_lookup, pure,
        Pure.pure, Except.pure, bind, Except.bind] at profile_success
      by_cases arity : signature.parameters.length = 2
      · rw [if_pos arity] at profile_success
        obtain ⟨fromParameter, toParameter, parameters_eq⟩ :=
          list_eq_pair_of_length_eq_two arity
        cases methods_eq : signature.methods.filter
            (fun candidate => candidate.name == "coerce") with
        | nil =>
            rw [methods_eq] at profile_success
            simp at profile_success
        | cons method rest =>
            cases rest with
            | nil =>
                rw [methods_eq] at profile_success
                simp only [Except.ok.injEq, Option.some.injEq] at profile_success
                subst profile
                by_cases parameter_types_eq :
                    method.parameterTypes.map
                        (TypeSystem.ParameterSubstitution.apply
                          [(fromParameter, source), (toParameter, target)]) =
                      [source]
                · by_cases return_types_eq :
                      method.returnTypes.map
                          (TypeSystem.ParameterSubstitution.apply
                            [(fromParameter, source), (toParameter, target)]) =
                        [target]
                  · have predicate_eq :
                        method.wherePredicates.map
                            (ProgramPredicate.applyParameters
                              [(fromParameter, source),
                                (toParameter, target)]) =
                          methodPredicates := by
                      simpa [Detail.coercionMethodPredicates, parameters_eq,
                        parameter_types_eq, return_types_eq] using
                          predicates_success
                    rw [← signature_facts.2, ← predicate_eq]
                    exact .intro
                      (by rw [signatures_eq]; exact signature_facts.1)
                      signature_name parameters_eq methods_eq
                      parameter_types_eq return_types_eq
                  · simp [Detail.coercionMethodPredicates, parameters_eq,
                      parameter_types_eq, return_types_eq, bind, Except.bind]
                      at predicates_success
                · simp [Detail.coercionMethodPredicates, parameters_eq,
                    parameter_types_eq, bind, Except.bind]
                    at predicates_success
            | cons second tail =>
                rw [methods_eq] at profile_success
                simp at profile_success
      · rw [if_neg arity] at profile_success
        simp at profile_success

/-- Successful operator-method profile validation supplies the declarative
profile used by unary and binary source typing.  The explicit trait-name
premise isolates the environment-to-signature alignment obligation in the
same way as the coercion-profile bridge above. -/
theorem operatorTraitPredicates_instantiates
    {inferenceContext : Frontend.SourceInference.Context}
    {semanticContext : SourceSemantics.Context}
    {trait : Resolved.DeclarationId} {traitName methodName : String}
    {operand : TypeSystem.Ty}
    {expectedParameters expectedReturns : List TypeSystem.Ty}
    {predicates : List ProgramPredicate}
    (signatures_eq :
      semanticContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some traitName)
    (success : Detail.operatorTraitPredicates inferenceContext trait methodName
      operand expectedParameters expectedReturns = .ok predicates) :
    OperatorProfileInstantiates semanticContext traitName methodName operand
      expectedParameters expectedReturns predicates := by
  cases signature_lookup : inferenceContext.signatures.trait? trait with
  | none =>
      simp [signature_lookup] at trait_name
  | some signature =>
      have signature_name : signature.name = traitName := by
        simpa [signature_lookup] using trait_name
      have signature_facts := trait?_eq_some_facts signature_lookup
      simp only [Detail.operatorTraitPredicates,
        Detail.exactOperatorTraitMethod, signature_lookup, pure, Pure.pure,
        Except.pure, bind, Except.bind] at success
      cases methods_eq : signature.methods.filter
          (fun candidate => candidate.name == methodName) with
      | nil =>
          rw [methods_eq] at success
          simp at success
      | cons method rest =>
          cases rest with
          | nil =>
              rw [methods_eq] at success
              simp only at success
              by_cases arity : signature.parameters.length = 1
              · rw [if_pos arity] at success
                obtain ⟨parameter, parameters_eq⟩ :=
                  list_eq_singleton_of_length_eq_one arity
                by_cases parameter_types_eq :
                    method.parameterTypes.map
                        (TypeSystem.ParameterSubstitution.apply
                          [(parameter, operand)]) = expectedParameters
                · by_cases return_types_eq :
                      method.returnTypes.map
                          (TypeSystem.ParameterSubstitution.apply
                            [(parameter, operand)]) = expectedReturns
                  · have predicates_eq :
                        ({
                          trait
                          subject := operand
                          arguments := []
                        } : ProgramPredicate) ::
                            method.wherePredicates.map
                              (ProgramPredicate.applyParameters
                                [(parameter, operand)]) = predicates := by
                      simpa [parameters_eq, parameter_types_eq,
                        return_types_eq] using success
                    subst predicates
                    rw [← signature_facts.2]
                    exact .intro
                      (by rw [signatures_eq]; exact signature_facts.1)
                      signature_name parameters_eq methods_eq
                      parameter_types_eq return_types_eq
                  · simp [parameters_eq, parameter_types_eq,
                      return_types_eq] at success
                · simp [parameters_eq, parameter_types_eq] at success
              · rw [if_neg arity] at success
                simp at success
          | cons second tail =>
              rw [methods_eq] at success
              simp at success

/-- The operator profile selected before finalization remains valid after the
same semantic substitution used to normalize operand, result, and evidence
predicates. -/
theorem operatorTraitPredicates_instantiatesAfterSubstitution
    {inferenceContext : Frontend.SourceInference.Context}
    {sourceContext targetContext : SourceSemantics.Context}
    {substitution : TypeSystem.Substitution}
    {closedVariables : List TypeSystem.TypeVarId}
    {trait : Resolved.DeclarationId} {traitName methodName : String}
    {operand : TypeSystem.Ty}
    {expectedParameters expectedReturns : List TypeSystem.Ty}
    {predicates : List ProgramPredicate}
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid substitution
      closedVariables sourceContext targetContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some traitName)
    (success : Detail.operatorTraitPredicates inferenceContext trait methodName
      operand expectedParameters expectedReturns = .ok predicates) :
    OperatorProfileInstantiates targetContext traitName methodName
      (substitution.apply operand)
      (expectedParameters.map substitution.apply)
      (expectedReturns.map substitution.apply)
      (predicates.map
        (TypedTraitResolution.applySubstitution substitution)) := by
  apply FlexibleSubstitution.OperatorProfileInstantiates.applySubstitution
    catalog contextValid
  exact operatorTraitPredicates_instantiates signatures_eq trait_name success

/-- A profile-consistent planned coercion edge remains a declaratively valid
`Coerce` profile after the ambient inference substitution closes its endpoint
types and ordered method predicates. -/
theorem plannedCoercionStep_profileInstantiatesAfterSubstitution
    {inferenceContext : Frontend.SourceInference.Context}
    {sourceContext targetContext : SourceSemantics.Context}
    {substitution : TypeSystem.Substitution}
    {closedVariables : List TypeSystem.TypeVarId}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {planned : Detail.PlannedCoercionStep}
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid substitution
      closedVariables sourceContext targetContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (consistent :
      Detail.PlannedCoercionStep.ProfileConsistent trait profile planned) :
    CoercionProfileInstantiates targetContext
      (substitution.apply planned.source)
      (substitution.apply planned.target)
      (TypedTraitResolution.applySubstitution substitution planned.predicate)
      (planned.methodPredicates.map
        (TypedTraitResolution.applySubstitution substitution)) := by
  have raw : CoercionProfileInstantiates sourceContext planned.source
      planned.target planned.predicate planned.methodPredicates := by
    simpa [consistent.predicate_eq] using
      coercionMethodProfile?_some_instantiates signatures_eq trait_name
        profile_success consistent.methodPredicates_eq
  exact FlexibleSubstitution.CoercionProfileInstantiates.applySubstitution
    catalog contextValid raw

/-- The frontend's canonical constructor freshening is a declaratively
admissible occurrence in every residually open semantic context carrying the
same well-formed data catalog. -/
theorem freshDataConstructorInstantiation_admissible
    {semanticContext : SourceSemantics.Context}
    {dataType : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature}
    {state next : Frontend.SourceInference.State}
    {instantiation : DataConstructorInstantiation}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (dataType_mem : dataType ∈ semanticContext.signatures.dataTypes)
    (constructor_mem : constructor ∈ dataType.constructors)
    (fresh : Detail.freshDataConstructorInstantiation dataType constructor
      state = (instantiation, next)) :
    SourceSemantics.DataConstructorInstantiation.Admissible semanticContext
      instantiation := by
  obtain ⟨arguments, arguments_length, arguments_are_variables,
    instantiation_eq⟩ :=
    Detail.freshDataConstructorInstantiation_success_shape fresh
  subst instantiation
  have dataWellFormed := catalog.data_semantic dataType dataType_mem
  refine .intro dataType constructor dataType_mem constructor_mem
    (dataWellFormed.constructor_owners constructor constructor_mem) rfl ?_ ?_
      rfl ?_
  · exact ParameterSubstitution.exact_zip
      dataWellFormed.parameters_nodup arguments_length
  · intro parameter replacement member
    have argument_mem : replacement ∈ arguments :=
      (List.of_mem_zip member).2
    obtain ⟨metavariable, rfl⟩ :=
      arguments_are_variables replacement argument_mem
    exact TypeAdmissible.variableOfResidual binders residual metavariable
  · change TypeSystem.Ty.nominal dataType.id arguments =
      TypeSystem.Ty.nominal dataType.id
        (ParameterSubstitution.orderedArguments
          (dataType.parameters.zip arguments) dataType.parameters)
    rw [ParameterSubstitution.orderedArguments_zip
      dataWellFormed.parameters_nodup arguments_length]

/-- A successful executable candidate check retains a declaratively
admissible occurrence of the candidate signature.  Argument fitting,
expected-type fitting, predicate validation, and ledger allocation happen
after the canonical fresh generic instantiation and cannot replace it. -/
theorem tryFunctionCandidate_instantiationAdmissible
    {inferenceContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {signature : ProgramFunctionSignature}
    {result : Detail.CandidateAttemptResult}
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (member : signature ∈ semanticContext.signatures.functions)
    (success : Detail.tryFunctionCandidate inferenceContext arguments
      integerLiteralOrigins call expected state signature = .ok (some result)) :
    DeclarationInstantiation.Admissible semanticContext
      result.instantiation := by
  rw [Detail.tryFunctionCandidate_some_instantiation success]
  exact DeclarationInstantiation.ofInstantiated_admissible catalog binders
    residual member state.inference.next

/-- The retained candidate instantiation also supplies the exact declarative
application profile needed by the direct-call typing rule.  Its parameter row
and result are the catalog projections under the one shared fresh rigid
substitution; later argument/result fitting is deliberately outside this raw
application fact. -/
theorem tryFunctionCandidate_declarationApplicationValid
    {inferenceContext : Frontend.SourceInference.Context}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {signature : ProgramFunctionSignature}
    {result : Detail.CandidateAttemptResult}
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (member : signature ∈ semanticContext.signatures.functions)
    (success : Detail.tryFunctionCandidate inferenceContext arguments
      integerLiteralOrigins call expected state signature = .ok (some result)) :
    DeclarationApplicationValid semanticContext result.instantiation
      (signature.parameterTypes.map
        (TypeSystem.ParameterSubstitution.apply
          (signature.scheme.instantiate
            state.inference.next).parameterSubstitution))
      ((signature.scheme.instantiate state.inference.next)
        |>.parameterSubstitution.apply
          (TypeSystem.Ty.productMany signature.returnTypes))
      (signature.scheme.instantiate state.inference.next).predicates := by
  rw [Detail.tryFunctionCandidate_some_instantiation success]
  let instantiated := signature.scheme.instantiate state.inference.next
  refine .intro member
    (DeclarationInstantiation.ofInstantiated_admissible catalog binders
      residual member state.inference.next) rfl rfl rfl ?_ rfl
  change instantiated.body = .function
    (TypeSystem.Ty.productMany
      (signature.parameterTypes.map
        (TypeSystem.ParameterSubstitution.apply
          instantiated.parameterSubstitution)))
    (instantiated.parameterSubstitution.apply
      (TypeSystem.Ty.productMany signature.returnTypes))
  rw [Frontend.ConstrainedDeclarationScheme.instantiate_body,
    (catalog.functions_semantic signature member).scheme_body,
    StructuralSubstitution.apply_function,
    StructuralSubstitution.apply_productMany]

/-- Fresh generic instantiation preserves admissibility of every function
parameter exposed to argument fitting. -/
theorem instantiatedFunctionParameterTypesAdmissible
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ semanticContext.signatures.functions)
    (next : Nat) :
    ∀ type, type ∈ signature.parameterTypes.map
        (TypeSystem.ParameterSubstitution.apply
          (signature.scheme.instantiate next).parameterSubstitution) →
      TypeAdmissible semanticContext type := by
  intro type typeMember
  rcases List.mem_map.mp typeMember with ⟨rawType, rawMember, rfl⟩
  have signatureWellFormed := catalog.functions_semantic signature member
  exact StructuralSubstitution.TypeWellScoped.applyParametersAdmissibleTo
    (source := signatureContext semanticContext.signatures signature.id
      signature.scheme.parameters signature.scheme.predicates)
    (target := semanticContext)
    (signature.scheme.instantiate next).parameterSubstitution
    (DeclarationInstantiation.instantiate_parameterSubstitution_exact
      signature.scheme next
      (catalog.function_parameters signature member).1)
    (DeclarationInstantiation.instantiate_parameterSubstitution_rangeAdmissible
      binders residual signature.scheme next)
    rfl binders (signatureWellFormed.parameter_types rawType rawMember).typeWellScoped

/-- The bundled result of a fresh generic function instantiation is
admissible before overload-result or contextual coercions are attached. -/
theorem instantiatedFunctionResultTypeAdmissible
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    {signature : ProgramFunctionSignature}
    (member : signature ∈ semanticContext.signatures.functions)
    (next : Nat) :
    TypeAdmissible semanticContext
      ((signature.scheme.instantiate next).parameterSubstitution.apply
        (TypeSystem.Ty.productMany signature.returnTypes)) := by
  have signatureWellFormed := catalog.functions_semantic signature member
  exact StructuralSubstitution.TypeWellScoped.applyParametersAdmissibleTo
    (source := signatureContext semanticContext.signatures signature.id
      signature.scheme.parameters signature.scheme.predicates)
    (target := semanticContext)
    (signature.scheme.instantiate next).parameterSubstitution
    (DeclarationInstantiation.instantiate_parameterSubstitution_exact
      signature.scheme next
      (catalog.function_parameters signature member).1)
    (DeclarationInstantiation.instantiate_parameterSubstitution_rangeAdmissible
      binders residual signature.scheme next)
    rfl binders
    (StructuralSubstitution.TypesWellScoped.productMany
      (StructuralSubstitution.TypesWellFormed.toTypesWellScoped
        signatureWellFormed.return_types))

/-- A successful overload selection comes from one semantic-catalog member
in the supplied candidate list and retains that member's exact declarative
application profile.  This theorem intentionally forgets ranking optimality;
only origin and static validity are needed by direct-call typing. -/
theorem selectFunctionCandidateFrom_declarationApplicationValid
    {inferenceContext : Frontend.SourceInference.Context}
    {name : String} {candidates : List ProgramFunctionSignature}
    {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {result : Detail.CandidateAttemptResult}
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (candidates_subset : candidates ⊆
      semanticContext.signatures.functions)
    (success : Detail.selectFunctionCandidateFrom inferenceContext name
      candidates arguments integerLiteralOrigins call expected state =
        .ok result) :
    ∃ signature, signature ∈ candidates ∧
      DeclarationApplicationValid semanticContext result.instantiation
        (signature.parameterTypes.map
          (TypeSystem.ParameterSubstitution.apply
            (signature.scheme.instantiate
              state.inference.next).parameterSubstitution))
        ((signature.scheme.instantiate state.inference.next)
          |>.parameterSubstitution.apply
            (TypeSystem.Ty.productMany signature.returnTypes))
        (signature.scheme.instantiate state.inference.next).predicates := by
  obtain ⟨signature, member, candidateSuccess⟩ :=
    Detail.selectFunctionCandidateFrom_success_candidate success
  refine ⟨signature, member, ?_⟩
  exact tryFunctionCandidate_declarationApplicationValid catalog binders
    residual (candidates_subset member) candidateSuccess

/-- Ordinary unqualified overload selection inherits the same declarative
application guarantee because successful visible-name lookup returns only
members of the inference catalog.  Catalog equality transports that origin
to the semantic context used by source typing. -/
theorem selectFunctionCandidate_declarationApplicationValid
    {inferenceContext : Frontend.SourceInference.Context}
    {name : String} {arguments : List InferredExpression}
    {integerLiteralOrigins : List IntegerLiteralOrigin}
    {call : ExpressionId} {expected : Option TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {result : Detail.CandidateAttemptResult}
    {semanticContext : SourceSemantics.Context}
    (catalog : SignatureCatalogWellFormed semanticContext.signatures)
    (binders : TypeParameterBindersWellFormed semanticContext)
    (residual : semanticContext.residualTypeVariables = true)
    (signatures_eq : semanticContext.signatures =
      inferenceContext.signatures)
    (success : Detail.selectFunctionCandidate inferenceContext name arguments
      integerLiteralOrigins call expected state = .ok result) :
    ∃ signature, signature ∈ semanticContext.signatures.functions ∧
      DeclarationApplicationValid semanticContext result.instantiation
        (signature.parameterTypes.map
          (TypeSystem.ParameterSubstitution.apply
            (signature.scheme.instantiate
              state.inference.next).parameterSubstitution))
        ((signature.scheme.instantiate state.inference.next)
          |>.parameterSubstitution.apply
            (TypeSystem.Ty.productMany signature.returnTypes))
        (signature.scheme.instantiate state.inference.next).predicates := by
  unfold Detail.selectFunctionCandidate at success
  cases candidatesResult : Detail.functionsNamed inferenceContext name with
  | error error =>
      simp [candidatesResult, bind, Except.bind] at success
  | ok candidates =>
      have selection : Detail.selectFunctionCandidateFrom inferenceContext
          name candidates arguments integerLiteralOrigins call expected state =
          .ok result := by
        simpa [candidatesResult, bind, Except.bind] using success
      have inferenceSubset :=
        Detail.functionsNamed_success_subset_catalog candidatesResult
      have semanticSubset : candidates ⊆
          semanticContext.signatures.functions := by
        intro signature member
        rw [signatures_eq]
        exact inferenceSubset member
      obtain ⟨signature, member, valid⟩ :=
        selectFunctionCandidateFrom_declarationApplicationValid catalog
          binders residual semanticSubset selection
      exact ⟨signature, semanticSubset member, valid⟩

private theorem requirementId_beq_iff_eq
    (left right : RequirementId) :
    (left == right) = true ↔ left = right := by
  rw [show (left == right) = (left.index == right.index) by rfl]
  rw [beq_iff_eq]
  constructor
  · intro indices_eq
    cases left
    cases right
    cases indices_eq
    rfl
  · intro same
    exact congrArg RequirementId.index same

private theorem requirementId_contains_iff_mem
    (id : RequirementId) (ids : List RequirementId) :
    ids.contains id = true ↔ id ∈ ids := by
  induction ids with
  | nil => simp
  | cons head tail induction =>
      rw [List.contains_cons, List.mem_cons]
      rw [Bool.or_eq_true, requirementId_beq_iff_eq, induction]

/-- Successful normalized predicate solving retains declaratively valid
evidence.  The available assumptions are normalized exactly once by the same
inference substitution used by the executable solver. -/
theorem solveNormalizedPredicate_sound
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {goal : ProgramPredicate}
    {retained : PredicateEvidence}
    (success : Detail.solveNormalizedPredicate context state goal =
      .ok retained) :
    RetainedEvidenceValid
      (context.assumptions.map (Detail.applyPredicate state))
      context.signatures.resolutionRules goal retained := by
  unfold Detail.solveNormalizedPredicate at success
  cases assumed : Detail.requirementAssumption? context state goal with
  | true =>
      simp only [assumed, ↓reduceIte, Except.ok.injEq] at success
      subst retained
      apply RetainedEvidenceValid.intro (.assumption goal)
      apply EvidenceValid.assumption
      unfold Detail.requirementAssumption? at assumed
      obtain ⟨assumption, member, equal⟩ := List.any_eq_true.mp assumed
      apply List.mem_map.mpr
      exact ⟨assumption, member, of_decide_eq_true equal⟩
  | false =>
      cases resolved : TypedTraitResolution.resolve
          context.signatures.resolutionRules context.traitDepth goal with
      | mk outcome statistics =>
          cases outcome with
          | noSolution =>
              simp [assumed, resolved] at success
          | inconclusive reason =>
              simp [assumed, resolved] at success
          | success evidence =>
              simp [assumed, resolved] at success
              subst retained
              apply RetainedEvidenceValid.weakenAssumptions
                (smaller := [])
              · simp
              · exact
                  TraitResolutionSoundness.resolve_success_retainedEvidenceValid
                    (rules := context.signatures.resolutionRules)
                    (maxDepth := context.traitDepth)
                    (goal := goal)
                    (retained := evidence)
                    (by simp [resolved])

/-- `solvePredicate` first normalizes its source predicate and then delegates
to `solveNormalizedPredicate`, so its successful result has the same retained
evidence guarantee at the normalized goal. -/
theorem solvePredicate_sound
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {source : ProgramPredicate}
    {retained : PredicateEvidence}
    (success : Detail.solvePredicate context state source = .ok retained) :
    RetainedEvidenceValid
      (context.assumptions.map (Detail.applyPredicate state))
      context.signatures.resolutionRules
      (Detail.applyPredicate state source) retained := by
  exact solveNormalizedPredicate_sound success

/-- An ordinary solved ledger row inherits the predicate solver's evidence
validity once the executable and declarative contexts agree on the catalog and
on the normalized declaration assumptions. -/
theorem solveRequirementEvidence_ordinary_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirement : Requirement}
    {retained : PredicateEvidence}
    {semanticContext : SourceSemantics.Context}
    (ordinary : requirement.id ∉ state.localSchemeAssumptions)
    (signatures_eq : semanticContext.signatures = inferenceContext.signatures)
    (assumptions_eq : semanticContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (success : Detail.solveRequirementEvidence inferenceContext state
      requirement = .ok retained) :
    SolvedRequirementValid semanticContext {
      id := requirement.id
      predicate := Detail.applyPredicate state requirement.predicate
      evidence := retained
    } := by
  have ordinaryContains :
      state.localSchemeAssumptions.contains requirement.id = false := by
    cases containsEq : state.localSchemeAssumptions.contains requirement.id with
    | false => rfl
    | true =>
        exact False.elim
          (ordinary ((requirementId_contains_iff_mem _ _).mp containsEq))
  have normalizedSuccess :
      Detail.solveNormalizedPredicate inferenceContext state
          (Detail.applyPredicate state requirement.predicate) = .ok retained := by
    unfold Detail.solveRequirementEvidence at success
    rw [ordinaryContains] at success
    simpa using success
  apply SolvedRequirementValid.intro
  rw [signatures_eq, assumptions_eq]
  exact solveNormalizedPredicate_sound normalizedSuccess

/-- Qualified-local template rows bypass trait search and retain exactly an
assumption for their normalized predicate. -/
theorem solveRequirementEvidence_template_eq
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirement : Requirement}
    {retained : PredicateEvidence}
    (template : requirement.id ∈ state.localSchemeAssumptions)
    (success : Detail.solveRequirementEvidence context state requirement =
      .ok retained) :
    retained = .assumption
      (Detail.applyPredicate state requirement.predicate) := by
  have templateContains :
      state.localSchemeAssumptions.contains requirement.id = true := by
    exact (requirementId_contains_iff_mem _ _).mpr template
  have retainedEq :
      (.assumption (Detail.applyPredicate state requirement.predicate) :
        PredicateEvidence) = retained := by
    unfold Detail.solveRequirementEvidence at success
    rw [templateContains] at success
    change Except.ok (.assumption
      (Detail.applyPredicate state requirement.predicate)) =
        Except.ok retained at success
    exact Except.ok.inj success
  exact retainedEq.symm

/-- Successful ledger solving preserves source order and records, for every
output row, its exact input identity, normalized predicate, and evidence-solver
equation. -/
theorem solveRequirements_corresponds
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    (success : Detail.solveRequirements context state requirements =
      .ok solved) :
    Forall₂ (fun requirement row =>
      row.id = requirement.id ∧
        row.predicate = Detail.applyPredicate state requirement.predicate ∧
        Detail.solveRequirementEvidence context state requirement =
          .ok row.evidence) requirements solved := by
  induction requirements generalizing solved with
  | nil =>
      simp only [Detail.solveRequirements, Except.ok.injEq] at success
      subst solved
      exact .nil
  | cons requirement rest induction =>
      cases evidenceResult :
          Detail.solveRequirementEvidence context state requirement with
      | error error =>
          simp [Detail.solveRequirements, evidenceResult, bind, Except.bind]
            at success
      | ok evidence =>
          cases tailResult : Detail.solveRequirements context state rest with
          | error error =>
              simp [Detail.solveRequirements, evidenceResult, tailResult,
                bind, Except.bind] at success
          | ok tail =>
              let solvedHead : SolvedRequirement := {
                id := requirement.id
                predicate := Detail.applyPredicate state requirement.predicate
                evidence := evidence
              }
              simp [Detail.solveRequirements, evidenceResult, tailResult,
                bind, Except.bind] at success
              subst solved
              exact .cons (by simp [evidenceResult])
                (induction tailResult)

private theorem solved_row_of_requirement_mem
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    (corresponds : Forall₂ (fun requirement row =>
      row.id = requirement.id ∧
        row.predicate = Detail.applyPredicate state requirement.predicate ∧
        Detail.solveRequirementEvidence inferenceContext state requirement =
          .ok row.evidence) requirements solved)
    {requirement : Requirement}
    (member : requirement ∈ requirements) :
    ∃ row, row ∈ solved ∧
      row.id = requirement.id ∧
      row.predicate = Detail.applyPredicate state requirement.predicate := by
  induction corresponds with
  | nil => simp at member
  | @cons head row tail rows headCorresponds tailCorresponds induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨row, by simp, headCorresponds.1, headCorresponds.2.1⟩
      · obtain ⟨found, foundMember, idEq, predicateEq⟩ := induction member
        exact ⟨found, by simp [foundMember], idEq, predicateEq⟩

/-- Every identity in a successfully solved input ledger names independently
valid evidence in the corresponding declarative solved ledger. -/
theorem solveRequirements_requirementIdsValid
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    RequirementIdsValid semanticContext (requirements.map (·.id)) := by
  intro id member
  obtain ⟨requirement, requirementMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨row, rowMember, idEq, predicateEq⟩ :=
    solved_row_of_requirement_mem (solveRequirements_corresponds success)
      requirementMember
  exact ⟨Detail.applyPredicate state requirement.predicate, row,
    ⟨by simpa [solved_eq] using rowMember, idEq⟩, predicateEq,
    valid row rowMember⟩

/-- Any occurrence-owned identity subset of a successfully solved input
ledger is independently valid in the corresponding declarative context. -/
theorem solveRequirements_requirementIdsValid_of_subset
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {ids : List RequirementId}
    (included : ids ⊆ requirements.map (·.id))
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    RequirementIdsValid semanticContext ids :=
  RequirementIdsValid.of_subset included
    (solveRequirements_requirementIdsValid success solved_eq valid)

/-- A source-ordered predicate/identity correspondence into a successfully
solved final ledger supplies the declarative evidence sequence for exactly
those normalized predicates. -/
theorem solveRequirements_correspondingSequenceProves
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {predicates : List ProgramPredicate}
    {ids : List RequirementId}
    (corresponds : RequirementPredicatesCorrespond requirements predicates ids)
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    RequirementSequenceProves semanticContext ids
      (predicates.map (Detail.applyPredicate state)) := by
  have solverCorresponds := solveRequirements_corresponds success
  clear success
  induction corresponds with
  | nil => exact .nil
  | @cons predicate id predicates ids member tail induction =>
      apply RequirementSequenceProves.cons
      · obtain ⟨row, rowMember, idEq, predicateEq⟩ :=
          solved_row_of_requirement_mem solverCorresponds member
        exact ⟨row, ⟨by simpa [solved_eq] using rowMember, idEq⟩,
          predicateEq, valid row rowMember⟩
      · exact induction

/-- A source-ordered predicate/identity correspondence into a successfully
solved scoped ledger supplies the exact declarative evidence sequence at one
covered source occurrence.  Qualified local-scheme template rows are justified
by their occurrence-local assumptions rather than by declaration-wide solved
requirement validity. -/
theorem solveRequirements_correspondingSequenceProvesAt
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {source : TypedSource}
    {occurrence : NodeId}
    {predicates : List ProgramPredicate}
    {ids : List RequirementId}
    (corresponds : RequirementPredicatesCorrespond requirements predicates ids)
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base source)
    (ownership : RequirementOwnership base source)
    (signatures_eq : active.signatures = base.signatures)
    (requirements_eq : active.solvedRequirements = base.solvedRequirements)
    (assumptions_mono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered source active occurrence)
    (occurs : ∀ id, id ∈ ids →
      PrimaryRequirementOccursAt source occurrence id) :
    RequirementSequenceProves active ids
      (predicates.map (Detail.applyPredicate state)) := by
  have solverCorresponds := solveRequirements_corresponds success
  clear success
  induction corresponds with
  | nil => exact .nil
  | @cons predicate id predicates ids member tail induction =>
      apply RequirementSequenceProves.cons
      · obtain ⟨row, rowMember, idEq, predicateEq⟩ :=
          solved_row_of_requirement_mem solverCorresponds member
        have baseMember : row ∈ base.solvedRequirements := by
          simpa [solved_eq] using rowMember
        have rowOccurs :
            PrimaryRequirementOccursAt source occurrence row.id := by
          simpa [idEq] using occurs id (by simp)
        simpa [idEq, predicateEq] using
          (ledger.requirementProvesAt ownership signatures_eq requirements_eq
            assumptions_mono covered baseMember rowOccurs)
      · apply induction
        intro tailId tailMember
        exact occurs tailId (by simp [tailMember])

/-- The ordered evidence row allocated for one canonical local-scheme
instantiation remains valid after the enclosing inference traversal advances
to its final state.  Requirement solving normalizes the already-normalized
allocation row once more; semantic substitution extension removes that
redundant earlier normalization. -/
theorem localReferenceRequirementSequenceProves_afterProgress
    {inferenceContext : Frontend.SourceInference.Context}
    {instantiationState finalState : Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context}
    {source : TypedSource}
    {occurrence : NodeId}
    {binder : TypedBinder}
    {instantiationStart : Nat}
    {ids : List RequirementId}
    (progress : instantiationState.InferenceProgress finalState)
    (corresponds : RequirementPredicatesCorrespond finalState.requirements
      ((instantiateLocalSchemePredicates
          (binder.scheme.instantiateWithSubstitution
            instantiationStart).substitution binder).map
        (Detail.applyPredicate instantiationState)) ids)
    (success : Detail.solveRequirements inferenceContext finalState
      finalState.requirements = .ok solved)
    (solved_eq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base source)
    (ownership : RequirementOwnership base source)
    (signatures_eq : active.signatures = base.signatures)
    (requirements_eq : active.solvedRequirements = base.solvedRequirements)
    (assumptions_mono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered source active occurrence)
    (occurs : ∀ id, id ∈ ids →
      PrimaryRequirementOccursAt source occurrence id) :
    RequirementSequenceProves active ids
      ((instantiateLocalSchemePredicates
          (binder.scheme.instantiateWithSubstitution
            instantiationStart).substitution binder).map
        (TypedTraitResolution.applySubstitution
          finalState.inference.substitution)) := by
  have proves := solveRequirements_correspondingSequenceProvesAt corresponds
    success solved_eq ledger ownership signatures_eq requirements_eq
    assumptions_mono covered occurs
  simpa only [List.map_map, Function.comp_def, Detail.applyPredicate,
    TypedTraitResolution.applySubstitution_semanticallyExtends
      progress.substitution_extends] using proves

/-- The exact node and allocation facts exposed by the executable
local-identifier branch assemble into declarative expression typing after the
enclosing inference traversal reaches its final substitution.  Global solver
and scope premises remain explicit because they belong to whole-body
finalization, not to identifier inference itself. -/
theorem localIdentifierBranchExpressionHasType_afterProgress
    {inferenceContext : Frontend.SourceInference.Context}
    {lookupState instantiationState finalState :
      Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {base target : SourceSemantics.Context}
    {source ledgerSource : TypedSource}
    {expression : Syntax.Expr} {name : Syntax.Identifier}
    {binder : TypedBinder} {result : InferredExpression}
    {instantiationStart : Nat} {actualRequirements : List RequirementId}
    {coercions : List CoercionStep}
    (lookupEq : lookupState.lookupBinder? name.value = some binder)
    (contains : ContainsExpression source result.id {
      id := result.id
      span := expression.span
      type := result.type
      form := .reference name.value (.local binder.id)
      requirements := actualRequirements ++
        Detail.coercionRequirements coercions
      coercions
      localSchemeInstantiationStart := some instantiationStart
    })
    (aligned : LocalEnvironmentAligned lookupState
      finalState.inference.substitution target)
    (formation : ActiveLocalFormation lookupState
      finalState.inference.substitution target)
    (binders : TypeParameterBindersWellFormed target)
    (residual : target.residualTypeVariables = true)
    (outerRange : SubstitutionRangeAdmissible target
      finalState.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture
      finalState.inference.substitution binder)
    (actualUnique : actualRequirements.Nodup)
    (actualDisjoint : ∀ requirement,
      requirement ∈ actualRequirements →
        requirement ∉ localSchemeTemplateIds binder)
    (progress : instantiationState.InferenceProgress finalState)
    (corresponds : RequirementPredicatesCorrespond finalState.requirements
      ((instantiateLocalSchemePredicates
          (binder.scheme.instantiateWithSubstitution
            instantiationStart).substitution binder).map
        (Detail.applyPredicate instantiationState)) actualRequirements)
    (solveSuccess : Detail.solveRequirements inferenceContext finalState
      finalState.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (signaturesEq : target.signatures = base.signatures)
    (requirementsEq : target.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ target.assumptions)
    (covered : TemplateScopeCovered ledgerSource target
      (.expression result.id))
    (occurs : ∀ requirement, requirement ∈ actualRequirements →
      PrimaryRequirementOccursAt ledgerSource (.expression result.id)
        requirement)
    (finalAdmissible : TypeAdmissible target
      (finalState.inference.substitution.apply result.type))
    (path : CoercionPathValid target
      (finalState.inference.substitution.apply
        (binder.scheme.instantiateWithSubstitution
          instantiationStart).body)
      (finalState.inference.substitution.apply result.type)
      (coercions.map (CoercionStep.applySubstitution
        finalState.inference.substitution))) :
    ExpressionHasType
      (source.applySubstitution finalState.inference.substitution)
      target result.id
      (finalState.inference.substitution.apply result.type) := by
  let outer := finalState.inference.substitution
  have environment := localReferenceEnvironmentFacts_of_lookupBinder?
    aligned formation lookupEq
  have requirements := localReferenceRequirementSequenceProves_afterProgress
    progress corresponds solveSuccess solvedEq ledger ownership signaturesEq
    requirementsEq assumptionsMono covered occurs
  have appliedDisjoint : ∀ requirement,
      requirement ∈ actualRequirements →
        requirement ∉
          localSchemeTemplateIds (binder.applySubstitution outer) := by
    simpa only
      [FlexibleSubstitution.localSchemeTemplateIds_applySubstitution] using
        actualDisjoint
  have instantiationValid :=
    canonicalLocalSchemeInstantiationValid_afterSubstitution binders residual
      outerRange environment.2.2.2 environment.2.2.1 noCapture
      instantiationStart actualUnique appliedDisjoint requirements
  exact canonicalLocalReferenceExpressionHasType_afterSubstitution
    (source := source.applySubstitution outer)
    (outer := outer) (target := target) (id := result.id)
    (node := ({
      id := result.id
      span := expression.span
      type := result.type
      form := .reference name.value (.local binder.id)
      requirements := actualRequirements ++
        Detail.coercionRequirements coercions
      coercions
      localSchemeInstantiationStart := some instantiationStart
    } : ExpressionNode).applySubstitution outer)
    (name := name.value) (binder := binder)
    (actualRequirements := actualRequirements)
    (FlexibleSubstitution.ContainsExpression.applySubstitution outer contains)
    rfl environment.1 environment.2.1 binders residual outerRange
    environment.2.2.2 environment.2.2.1 noCapture instantiationStart
    actualUnique appliedDisjoint requirements instantiationValid.type_admissible
    finalAdmissible path (by
      change actualRequirements ++ Detail.coercionRequirements coercions =
        actualRequirements ++ coercionRequirementIds
          (coercions.map (CoercionStep.applySubstitution outer))
      rw [FlexibleSubstitution.coercionRequirementIds_applySubstitution]
      rfl)

/-- Decoding, final carrier closure, exact ledger ownership, and solver
soundness compose into the declarative validity judgment for one inferred
integer literal. -/
theorem integerLiteralValid_of_solved
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (decoded : Frontend.numericLiteralValue? source = some resolution.rawValue)
    (target_supported :
      (resolution.applySubstitution state.inference.substitution).targetType =
          .word ∨
        (resolution.applySubstitution state.inference.substitution).targetType =
          .integer)
    (requirement_mem :
      ({ id := resolution.requirement, predicate := resolution.predicate } :
        Requirement) ∈ state.requirements)
    (solve_success : Detail.solveRequirements inferenceContext state
      state.requirements = .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    IntegerLiteralValid semanticContext source
      (resolution.applySubstitution state.inference.substitution) := by
  have proves : RequirementSequenceProves semanticContext
      [resolution.requirement] [Detail.applyPredicate state
        resolution.predicate] :=
    solveRequirements_correspondingSequenceProves
      (.cons requirement_mem .nil) solve_success solved_eq valid
  have evidence : RequirementProves semanticContext
      (resolution.applySubstitution state.inference.substitution).requirement
      (resolution.applySubstitution state.inference.substitution).predicate := by
    rw [IntegerLiteralResolution.applySubstitution_requirement,
      IntegerLiteralResolution.applySubstitution_predicate]
    simpa [Detail.applyPredicate] using proves.head
  have meaning : Frontend.NumericLiteralDenotes source
      (resolution.applySubstitution state.inference.substitution).rawValue := by
    simpa using Frontend.numericLiteralValue?_sound decoded
  rcases target_supported with target_eq | target_eq
  · exact .word meaning target_eq
      (by simpa [IntegerLiteralResolution.predicate] using evidence)
  · exact .integer meaning target_eq
      (by simpa [IntegerLiteralResolution.predicate] using evidence)

/-- A validated unary trait profile and its source-ordered rows in the final
solved ledger assemble the declarative unary-operator judgment after applying
the final inference substitution. -/
theorem unaryOperatorTrait_hasTypeAfterSubstitution
    {inferenceContext : Frontend.SourceInference.Context}
    {sourceContext targetContext : SourceSemantics.Context}
    {state : Frontend.SourceInference.State}
    {closedVariables : List TypeSystem.TypeVarId}
    {solved : List SolvedRequirement}
    {operator : Syntax.UnaryOp} {trait : Resolved.DeclarationId}
    {traitName methodName : String} {operand result : TypeSystem.Ty}
    {predicates : List ProgramPredicate} {requirements : List RequirementId}
    (dispatch : UnaryTraitDispatch operator traitName methodName)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      state.inference.substitution closedVariables sourceContext targetContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some traitName)
    (profile_success : Detail.operatorTraitPredicates inferenceContext trait
      methodName operand [operand] [result] = .ok predicates)
    (corresponds : RequirementPredicatesCorrespond state.requirements
      predicates requirements)
    (solve_success : Detail.solveRequirements inferenceContext state
      state.requirements = .ok solved)
    (solved_eq : targetContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid targetContext solved) :
    UnaryOperatorHasType targetContext operator
      (state.inference.substitution.apply operand)
      (state.inference.substitution.apply result) requirements := by
  apply UnaryOperatorHasType.trait dispatch
  · simpa using
      operatorTraitPredicates_instantiatesAfterSubstitution catalog contextValid
        signatures_eq trait_name profile_success
  · change RequirementSequenceProves targetContext requirements
      (predicates.map (Detail.applyPredicate state))
    exact solveRequirements_correspondingSequenceProves corresponds
      solve_success solved_eq valid

/-- Binary trait inference has the analogous composition: a validated
two-operand profile plus the corresponding solved ledger rows yields the
declarative binary-operator judgment under the final substitution. -/
theorem binaryOperatorTrait_hasTypeAfterSubstitution
    {inferenceContext : Frontend.SourceInference.Context}
    {sourceContext targetContext : SourceSemantics.Context}
    {state : Frontend.SourceInference.State}
    {closedVariables : List TypeSystem.TypeVarId}
    {solved : List SolvedRequirement}
    {operator : Syntax.BinaryOp} {trait : Resolved.DeclarationId}
    {traitName methodName : String} {operand result : TypeSystem.Ty}
    {predicates : List ProgramPredicate} {requirements : List RequirementId}
    (dispatch : BinaryTraitDispatch operator traitName methodName)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      state.inference.substitution closedVariables sourceContext targetContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some traitName)
    (profile_success : Detail.operatorTraitPredicates inferenceContext trait
      methodName operand [operand, operand] [result] = .ok predicates)
    (corresponds : RequirementPredicatesCorrespond state.requirements
      predicates requirements)
    (solve_success : Detail.solveRequirements inferenceContext state
      state.requirements = .ok solved)
    (solved_eq : targetContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid targetContext solved) :
    BinaryOperatorHasType targetContext operator
      (state.inference.substitution.apply operand)
      (state.inference.substitution.apply operand)
      (state.inference.substitution.apply result) requirements := by
  apply BinaryOperatorHasType.trait dispatch
  · simpa using
      operatorTraitPredicates_instantiatesAfterSubstitution catalog contextValid
        signatures_eq trait_name profile_success
  · change RequirementSequenceProves targetContext requirements
      (predicates.map (Detail.applyPredicate state))
    exact solveRequirements_correspondingSequenceProves corresponds
      solve_success solved_eq valid

/-- A committed coercion edge inherits the primary and method evidence rows
owned by its planned edge, in the exact order expected by
`CoercionStepValid`. -/
theorem solveRequirements_committedCoercionStepSequenceProves
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {planned : Detail.PlannedCoercionStep}
    {committed : CoercionStep}
    (corresponds : Detail.PlannedCoercionStep.CommitCorresponds requirements
      planned committed)
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    RequirementSequenceProves semanticContext
      (committed.requirement :: committed.methodRequirements)
      (Detail.applyPredicate state planned.predicate ::
        planned.methodPredicates.map (Detail.applyPredicate state)) := by
  apply RequirementSequenceProves.cons
  · have primaryCorresponds : RequirementPredicatesCorrespond requirements
        [planned.predicate] [committed.requirement] :=
      .cons corresponds.primary_mem .nil
    exact (solveRequirements_correspondingSequenceProves primaryCorresponds
      success solved_eq valid).head
  · exact solveRequirements_correspondingSequenceProves
      corresponds.methods success solved_eq valid

/-- Once its normalized profile and solved ledger are valid, a committed
frontend edge is a declaratively valid coercion step after applying the same
inference substitution used to normalize its requirements. -/
theorem committedCoercionStepValid
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {planned : Detail.PlannedCoercionStep}
    {committed : CoercionStep}
    (corresponds : Detail.PlannedCoercionStep.CommitCorresponds requirements
      planned committed)
    (profile : CoercionProfileInstantiates semanticContext
      (state.resolve planned.source) (state.resolve planned.target)
      (Detail.applyPredicate state planned.predicate)
      (planned.methodPredicates.map (Detail.applyPredicate state)))
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    CoercionStepValid semanticContext
      (committed.applySubstitution state.inference.substitution) := by
  apply CoercionStepValid.intro
      (primary := Detail.applyPredicate state planned.predicate)
      (methodPredicates :=
        planned.methodPredicates.map (Detail.applyPredicate state))
  · simpa [CoercionStep.applySubstitution, State.resolve,
      TypeSystem.InferState.resolve, corresponds.source_eq,
      corresponds.target_eq] using profile
  · simpa [CoercionStep.applySubstitution] using
      solveRequirements_committedCoercionStepSequenceProves corresponds
        success solved_eq valid

/-- A committed coercion edge is also valid against a scoped solved ledger at
one covered source occurrence.  This form admits qualified local-scheme rows:
their evidence is justified by the occurrence-local template assumptions
rather than by declaration-wide solved-row validity. -/
theorem committedCoercionStepValidAt
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement} {solved : List SolvedRequirement}
    {base active : SourceSemantics.Context} {ledgerSource : TypedSource}
    {occurrence : NodeId} {planned : Detail.PlannedCoercionStep}
    {committed : CoercionStep}
    (corresponds : Detail.PlannedCoercionStep.CommitCorresponds requirements
      planned committed)
    (profile : CoercionProfileInstantiates active
      (state.resolve planned.source) (state.resolve planned.target)
      (Detail.applyPredicate state planned.predicate)
      (planned.methodPredicates.map (Detail.applyPredicate state)))
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (signaturesEq : active.signatures = base.signatures)
    (requirementsEq :
      active.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ active.assumptions)
    (covered : TemplateScopeCovered ledgerSource active occurrence)
    (occurs : ∀ id, id ∈ committed.requirements →
      PrimaryRequirementOccursAt ledgerSource occurrence id) :
    CoercionStepValid active
      (committed.applySubstitution state.inference.substitution) := by
  apply CoercionStepValid.intro
      (primary := Detail.applyPredicate state planned.predicate)
      (methodPredicates :=
        planned.methodPredicates.map (Detail.applyPredicate state))
  · simpa [CoercionStep.applySubstitution, State.resolve,
      TypeSystem.InferState.resolve, corresponds.source_eq,
      corresponds.target_eq] using profile
  · have sequence := solveRequirements_correspondingSequenceProvesAt
        (.cons corresponds.primary_mem corresponds.methods) success solvedEq
        ledger ownership signaturesEq requirementsEq assumptionsMono covered
        (fun id member => occurs id (by
          simpa [CoercionStep.requirements] using member))
    simpa [CoercionStep.applySubstitution] using sequence

private theorem committed_member_has_planned_correspondence
    {requirements : List Requirement}
    {plan : List Detail.PlannedCoercionStep}
    {steps : List CoercionStep}
    (corresponds : Detail.CoercionPlanCommitCorresponds requirements
      plan steps)
    {committed : CoercionStep}
    (member : committed ∈ steps) :
    ∃ planned, planned ∈ plan ∧
      Detail.PlannedCoercionStep.CommitCorresponds requirements
        planned committed := by
  induction corresponds with
  | nil => simp at member
  | @cons planned committed plan steps head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨planned, by simp, head⟩
      · obtain ⟨candidate, candidateMember, candidateCorresponds⟩ :=
          induction member
        exact ⟨candidate, by simp [candidateMember], candidateCorresponds⟩

/-- Structural search validity, exact commit correspondence, normalized
profile validity for every planned edge, and a valid solved ledger compose to
the declarative validity of the complete committed coercion path. -/
theorem committedCoercionPlanValid
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {source target : TypeSystem.Ty}
    {plan : List Detail.PlannedCoercionStep}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    (structural : Detail.PlannedCoercionPath.isValid source target plan = true)
    (profiles : ∀ planned, planned ∈ plan →
      CoercionProfileInstantiates semanticContext
        ((Detail.commitCoercionPlan state plan).2.resolve planned.source)
        ((Detail.commitCoercionPlan state plan).2.resolve planned.target)
        (Detail.applyPredicate (Detail.commitCoercionPlan state plan).2
          planned.predicate)
        (planned.methodPredicates.map
          (Detail.applyPredicate (Detail.commitCoercionPlan state plan).2)))
    (success : Detail.solveRequirements inferenceContext
      (Detail.commitCoercionPlan state plan).2
      (Detail.commitCoercionPlan state plan).2.requirements = .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    CoercionPathValid semanticContext
      ((Detail.commitCoercionPlan state plan).2.resolve source)
      ((Detail.commitCoercionPlan state plan).2.resolve target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution
          (Detail.commitCoercionPlan state plan).2.inference.substitution)) := by
  let committed := Detail.commitCoercionPlan state plan
  have committedStructural :
      Frontend.SourceInference.CoercionPath.isValid source target
        committed.1 = true :=
    Detail.commitCoercionPlan_isValid state plan structural
  have normalizedStructural :
      Frontend.SourceInference.CoercionPath.isValid
        (committed.2.resolve source) (committed.2.resolve target)
        (committed.1.map
          (CoercionStep.applySubstitution
            committed.2.inference.substitution)) = true := by
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve] using
      Frontend.SourceInference.CoercionPath.isValid_applySubstitution
        committed.2.inference.substitution committedStructural
  apply CoercionPathValid.of_isValid normalizedStructural
  intro step stepMember
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp stepMember
  have correspondences := Detail.commitCoercionPlan_corresponds state plan
  obtain ⟨planned, plannedMember, correspondence⟩ :=
    committed_member_has_planned_correspondence correspondences originalMember
  exact committedCoercionStepValid correspondence
    (profiles planned plannedMember) success solved_eq valid

/-- Successful coercion planning, profile lookup, commit, and requirement
solving form a declaratively valid normalized coercion path once the final
inference substitution is a valid semantic context closure. -/
theorem coercionPlan?_some_committedPathValid
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {source target : TypeSystem.Ty}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {plan : List Detail.PlannedCoercionStep}
    {solved : List SolvedRequirement}
    {sourceContext semanticContext : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (trait_success :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (plan_success :
      Detail.coercionPlan? inferenceContext state source target =
        .ok (some plan))
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      (Detail.commitCoercionPlan state plan).2.inference.substitution
      closedVariables sourceContext semanticContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solve_success : Detail.solveRequirements inferenceContext
      (Detail.commitCoercionPlan state plan).2
      (Detail.commitCoercionPlan state plan).2.requirements = .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    CoercionPathValid semanticContext
      ((Detail.commitCoercionPlan state plan).2.resolve source)
      ((Detail.commitCoercionPlan state plan).2.resolve target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution
          (Detail.commitCoercionPlan state plan).2.inference.substitution)) := by
  apply committedCoercionPlanValid
      (Detail.coercionPlan?_some_isValid plan_success) ?_ solve_success
      solved_eq valid
  intro planned member
  have consistent := Detail.coercionPlan?_some_profileConsistent
    trait_success profile_success plan_success planned member
  have methodPredicates_eq :
      planned.methodPredicates.map
          (Detail.applyPredicate (Detail.commitCoercionPlan state plan).2) =
        planned.methodPredicates.map
          (TypedTraitResolution.applySubstitution
            (Detail.commitCoercionPlan state plan).2.inference.substitution) := by
    apply List.map_congr_left
    intro predicate predicateMember
    rfl
  rw [methodPredicates_eq]
  simpa [Frontend.SourceInference.State.resolve,
    TypeSystem.InferState.resolve, Detail.applyPredicate] using
    plannedCoercionStep_profileInstantiatesAfterSubstitution
      (substitution :=
        (Detail.commitCoercionPlan state plan).2.inference.substitution)
      catalog contextValid signatures_eq trait_name profile_success consistent

/-- A committed coercion plan remains semantically valid when later inference
extends its requirement ledger and the whole enlarged ledger is solved under a
later closing substitution.  This is the form needed by expression inference:
coercions are committed locally, but their evidence is solved only after the
rest of the declaration has been traversed. -/
theorem coercionPlan?_some_committedPathValid_at
    {inferenceContext : Frontend.SourceInference.Context}
    {state later : Frontend.SourceInference.State}
    {source target : TypeSystem.Ty}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {plan : List Detail.PlannedCoercionStep}
    {solved : List SolvedRequirement}
    {sourceContext semanticContext : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (trait_success :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (plan_success :
      Detail.coercionPlan? inferenceContext state source target =
        .ok (some plan))
    (requirements_subset :
      (Detail.commitCoercionPlan state plan).2.requirements ⊆
        later.requirements)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext
        semanticContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solve_success : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    CoercionPathValid semanticContext
      (later.inference.substitution.apply source)
      (later.inference.substitution.apply target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution later.inference.substitution)) := by
  have corresponds : Detail.CoercionPlanCommitCorresponds later.requirements
      plan (Detail.commitCoercionPlan state plan).1 :=
    (Detail.commitCoercionPlan_corresponds state plan).mono
      requirements_subset
  have retainedStructural : Frontend.SourceInference.CoercionPath.isValid
      source target (Detail.commitCoercionPlan state plan).1 = true :=
    corresponds.isValid (Detail.coercionPlan?_some_isValid plan_success)
  have normalizedStructural : Frontend.SourceInference.CoercionPath.isValid
      (later.inference.substitution.apply source)
      (later.inference.substitution.apply target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution later.inference.substitution)) = true :=
    Frontend.SourceInference.CoercionPath.isValid_applySubstitution
      later.inference.substitution retainedStructural
  apply CoercionPathValid.of_isValid normalizedStructural
  intro step stepMember
  obtain ⟨committed, committedMember, rfl⟩ := List.mem_map.mp stepMember
  obtain ⟨planned, plannedMember, correspondence⟩ :=
    committed_member_has_planned_correspondence corresponds committedMember
  have consistent := Detail.coercionPlan?_some_profileConsistent
    trait_success profile_success plan_success planned plannedMember
  have methodPredicates_eq :
      planned.methodPredicates.map (Detail.applyPredicate later) =
        planned.methodPredicates.map
          (TypedTraitResolution.applySubstitution
            later.inference.substitution) := by
    apply List.map_congr_left
    intro predicate predicateMember
    rfl
  have profile :=
    plannedCoercionStep_profileInstantiatesAfterSubstitution
      (substitution := later.inference.substitution) catalog contextValid
      signatures_eq trait_name profile_success consistent
  have normalizedProfile : CoercionProfileInstantiates semanticContext
      (later.resolve planned.source) (later.resolve planned.target)
      (Detail.applyPredicate later planned.predicate)
      (planned.methodPredicates.map (Detail.applyPredicate later)) := by
    rw [methodPredicates_eq]
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve, Detail.applyPredicate] using profile
  exact committedCoercionStepValid (state := later) correspondence
    normalizedProfile solve_success solved_eq valid

/-- The later-state coercion bridge with occurrence-scoped evidence.  Every
edge obligation is discharged at the expression occurrence that owns the
committed path, so qualified local-scheme rows remain valid inside their
initializer scope without requiring global solved-row validity. -/
theorem coercionPlan?_some_committedPathValid_at_scoped
    {inferenceContext : Frontend.SourceInference.Context}
    {state later : Frontend.SourceInference.State}
    {source target : TypeSystem.Ty}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {plan : List Detail.PlannedCoercionStep}
    {solved : List SolvedRequirement}
    {sourceContext base semanticContext : SourceSemantics.Context}
    {ledgerSource : TypedSource} {occurrence : NodeId}
    {closedVariables : List TypeSystem.TypeVarId}
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (planSuccess :
      Detail.coercionPlan? inferenceContext state source target =
        .ok (some plan))
    (requirementsSubset :
      (Detail.commitCoercionPlan state plan).2.requirements ⊆
        later.requirements)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext
        semanticContext)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : semanticContext.signatures = base.signatures)
    (activeRequirementsEq :
      semanticContext.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ semanticContext.assumptions)
    (covered : TemplateScopeCovered ledgerSource semanticContext occurrence)
    (occurs : ∀ id,
      id ∈ coercionRequirementIds
        (Detail.commitCoercionPlan state plan).1 →
      PrimaryRequirementOccursAt ledgerSource occurrence id) :
    CoercionPathValid semanticContext
      (later.inference.substitution.apply source)
      (later.inference.substitution.apply target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution later.inference.substitution)) := by
  have corresponds : Detail.CoercionPlanCommitCorresponds later.requirements
      plan (Detail.commitCoercionPlan state plan).1 :=
    (Detail.commitCoercionPlan_corresponds state plan).mono
      requirementsSubset
  have retainedStructural : Frontend.SourceInference.CoercionPath.isValid
      source target (Detail.commitCoercionPlan state plan).1 = true :=
    corresponds.isValid (Detail.coercionPlan?_some_isValid planSuccess)
  have normalizedStructural : Frontend.SourceInference.CoercionPath.isValid
      (later.inference.substitution.apply source)
      (later.inference.substitution.apply target)
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution later.inference.substitution)) = true :=
    Frontend.SourceInference.CoercionPath.isValid_applySubstitution
      later.inference.substitution retainedStructural
  apply CoercionPathValid.of_isValid normalizedStructural
  intro step stepMember
  obtain ⟨committed, committedMember, rfl⟩ := List.mem_map.mp stepMember
  obtain ⟨planned, plannedMember, correspondence⟩ :=
    committed_member_has_planned_correspondence corresponds committedMember
  have consistent := Detail.coercionPlan?_some_profileConsistent
    traitSuccess profileSuccess planSuccess planned plannedMember
  have methodPredicatesEq :
      planned.methodPredicates.map (Detail.applyPredicate later) =
        planned.methodPredicates.map
          (TypedTraitResolution.applySubstitution
            later.inference.substitution) := by
    apply List.map_congr_left
    intro predicate predicateMember
    rfl
  have profileInstantiates :=
    plannedCoercionStep_profileInstantiatesAfterSubstitution
      (substitution := later.inference.substitution) catalog contextValid
      signaturesEq traitName profileSuccess consistent
  have normalizedProfile : CoercionProfileInstantiates semanticContext
      (later.resolve planned.source) (later.resolve planned.target)
      (Detail.applyPredicate later planned.predicate)
      (planned.methodPredicates.map (Detail.applyPredicate later)) := by
    rw [methodPredicatesEq]
    simpa [Frontend.SourceInference.State.resolve,
      TypeSystem.InferState.resolve, Detail.applyPredicate] using
      profileInstantiates
  apply committedCoercionStepValidAt (state := later) correspondence
    normalizedProfile solveSuccess solvedEq ledger ownership
    activeSignaturesEq activeRequirementsEq assumptionsMono covered
  intro id member
  apply occurs id
  unfold coercionRequirementIds
  exact List.mem_flatMap.mpr ⟨committed, committedMember, member⟩

/-- Expected-type fitting yields a semantically valid output-coercion path
after the enclosing inference traversal has finished.  An absent expectation
or successful unification gives the empty path; a mismatch reuses the exact
planned and committed path exposed by `withExpected_success_cases`. -/
theorem withExpected_success_coercionPathValid_afterFinalization
    {inferenceContext : Frontend.SourceInference.Context}
    {state later : Frontend.SourceInference.State}
    {actual : InferredExpression}
    {expected : Option TypeSystem.Ty}
    {result : Detail.ExpectationResult}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext semanticContext : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (success : Detail.withExpected inferenceContext state actual expected =
      .ok result)
    (trait_success :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profile_success :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (requirements_subset : result.state.requirements ⊆ later.requirements)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext
        semanticContext)
    (signatures_eq : sourceContext.signatures = inferenceContext.signatures)
    (trait_name :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solve_success : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solved_eq : semanticContext.solvedRequirements = solved)
    (valid : SolvedRequirementsValid semanticContext solved) :
    CoercionPathValid semanticContext
      (later.inference.substitution.apply
        (result.state.resolve actual.type))
      (later.inference.substitution.apply result.expression.type)
      (result.coercions.map
        (CoercionStep.applySubstitution later.inference.substitution)) := by
  rcases Detail.withExpected_success_cases success with
    ⟨coercions_eq, requirements_eq, type_eq⟩ |
      ⟨expectedType, plan, expected_eq, plan_success, result_eq⟩
  · rw [coercions_eq]
    simp only [List.map_nil]
    rw [type_eq]
    exact .nil _
  · subst expected
    subst result
    change CoercionPathValid semanticContext
      (later.inference.substitution.apply
        ((Detail.commitCoercionPlan state plan).2.resolve actual.type))
      (later.inference.substitution.apply (state.resolve expectedType))
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution later.inference.substitution))
    rw [Detail.commitCoercionPlan_resolve]
    exact coercionPlan?_some_committedPathValid_at trait_success
      profile_success plan_success requirements_subset catalog contextValid
      signatures_eq trait_name solve_success solved_eq valid

/-- Expected-type fitting with occurrence-scoped final evidence.  Unlike the
global solved-row variant, this theorem remains applicable inside generalized
local initializers whose qualified template rows are valid only at covered
source occurrences. -/
theorem withExpected_success_coercionPathValid_afterFinalization_scoped
    {inferenceContext : Frontend.SourceInference.Context}
    {state later : Frontend.SourceInference.State}
    {actual : InferredExpression}
    {expected : Option TypeSystem.Ty}
    {result : Detail.ExpectationResult}
    {trait : Resolved.DeclarationId}
    {profile : Detail.CoercionMethodProfile}
    {solved : List SolvedRequirement}
    {sourceContext base semanticContext : SourceSemantics.Context}
    {ledgerSource : TypedSource} {occurrence : NodeId}
    {closedVariables : List TypeSystem.TypeVarId}
    (success : Detail.withExpected inferenceContext state actual expected =
      .ok result)
    (traitSuccess :
      Detail.conventionalTraitWithArity? inferenceContext "Coerce" 2 =
        .ok (some trait))
    (profileSuccess :
      Detail.coercionMethodProfile? inferenceContext trait =
        .ok (some profile))
    (requirementsSubset : result.state.requirements ⊆ later.requirements)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : FlexibleSubstitution.ContextSubstitutionValid
      later.inference.substitution closedVariables sourceContext
        semanticContext)
    (signaturesEq : sourceContext.signatures = inferenceContext.signatures)
    (traitName :
      (inferenceContext.signatures.trait? trait).map (·.name) =
        some "Coerce")
    (solveSuccess : Detail.solveRequirements inferenceContext later
      later.requirements = .ok solved)
    (solvedEq : base.solvedRequirements = solved)
    (ledger : ScopedRequirementLedgerWellFormed base ledgerSource)
    (ownership : RequirementOwnership base ledgerSource)
    (activeSignaturesEq : semanticContext.signatures = base.signatures)
    (activeRequirementsEq :
      semanticContext.solvedRequirements = base.solvedRequirements)
    (assumptionsMono : base.assumptions ⊆ semanticContext.assumptions)
    (covered : TemplateScopeCovered ledgerSource semanticContext occurrence)
    (occurs : ∀ id, id ∈ coercionRequirementIds result.coercions →
      PrimaryRequirementOccursAt ledgerSource occurrence id) :
    CoercionPathValid semanticContext
      (later.inference.substitution.apply
        (result.state.resolve actual.type))
      (later.inference.substitution.apply result.expression.type)
      (result.coercions.map
        (CoercionStep.applySubstitution later.inference.substitution)) := by
  rcases Detail.withExpected_success_cases success with
    ⟨coercionsEq, requirementsEq, typeEq⟩ |
      ⟨expectedType, plan, expectedEq, planSuccess, resultEq⟩
  · rw [coercionsEq]
    simp only [List.map_nil]
    rw [typeEq]
    exact .nil _
  · subst expected
    subst result
    change CoercionPathValid semanticContext
      (later.inference.substitution.apply
        ((Detail.commitCoercionPlan state plan).2.resolve actual.type))
      (later.inference.substitution.apply (state.resolve expectedType))
      ((Detail.commitCoercionPlan state plan).1.map
        (CoercionStep.applySubstitution later.inference.substitution))
    rw [Detail.commitCoercionPlan_resolve]
    exact coercionPlan?_some_committedPathValid_at_scoped traitSuccess
      profileSuccess planSuccess requirementsSubset catalog contextValid
      signaturesEq traitName solveSuccess solvedEq ledger ownership
      activeSignaturesEq activeRequirementsEq assumptionsMono covered occurs

/-- Every solved row classified as a qualified-local template by the input
state retains the canonical assumption evidence for its normalized
predicate. -/
theorem solveRequirements_template_evidence
    {context : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    (success : Detail.solveRequirements context state requirements =
      .ok solved) :
    ∀ row, row ∈ solved → row.id ∈ state.localSchemeAssumptions →
      row.evidence = .assumption row.predicate := by
  have corresponds := solveRequirements_corresponds success
  clear success
  induction corresponds with
  | nil =>
      intro row member
      simp at member
  | @cons requirement row requirements rows head tail induction =>
      intro candidate member template
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · rcases head with ⟨id_eq, predicate_eq, evidence_success⟩
        have requirement_template :
            requirement.id ∈ state.localSchemeAssumptions := by
          rw [← id_eq]
          exact template
        have evidence_eq := solveRequirementEvidence_template_eq
          requirement_template evidence_success
        rw [predicate_eq]
        exact evidence_eq
      · exact induction candidate member template

/-- When no input row is a qualified-local template, successful ledger
solving validates every output row in a declarative context with the same
catalog and normalized declaration assumptions. -/
theorem solveRequirements_ordinary_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    (ordinary : ∀ requirement, requirement ∈ requirements →
      requirement.id ∉ state.localSchemeAssumptions)
    (signatures_eq : semanticContext.signatures = inferenceContext.signatures)
    (assumptions_eq : semanticContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved) :
    SolvedRequirementsValid semanticContext solved := by
  have corresponds := solveRequirements_corresponds success
  clear success
  unfold SolvedRequirementsValid
  revert ordinary
  induction corresponds with
  | nil =>
      intro _ row member
      simp at member
  | @cons requirement row requirements rows head tail induction =>
      intro ordinary candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · rcases head with ⟨id_eq, predicate_eq, evidence_success⟩
        have valid := solveRequirementEvidence_ordinary_sound
          (semanticContext := semanticContext)
          (ordinary requirement (by simp)) signatures_eq assumptions_eq
          evidence_success
        have candidate_eq : candidate = {
            id := requirement.id
            predicate := Detail.applyPredicate state requirement.predicate
            evidence := candidate.evidence
          } := by
          cases candidate
          simp_all
        rw [candidate_eq]
        exact valid
      · exact induction (fun tailRequirement tailMember =>
          ordinary tailRequirement (by simp [tailMember])) candidate member

/-- Successful ledger solving validates ordinary rows through retained trait
evidence and qualified-local template rows through their exact
initializer-scoped source ownership. -/
theorem solveRequirements_scoped_entries_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {requirements : List Requirement}
    {solved : List SolvedRequirement}
    {semanticContext : SourceSemantics.Context}
    {source : TypedSource}
    (signatures_eq : semanticContext.signatures = inferenceContext.signatures)
    (assumptions_eq : semanticContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (template_iff : ∀ requirement, requirement ∈ requirements →
      (requirement.id ∈ state.localSchemeAssumptions ↔
        requirement.id ∈ sourceLocalSchemeTemplateIds source))
    (template_scoped : ∀ requirement, requirement ∈ requirements →
      requirement.id ∈ state.localSchemeAssumptions →
      LocalSchemeTemplateRowScoped source {
        id := requirement.id
        predicate := Detail.applyPredicate state requirement.predicate
        evidence := .assumption
          (Detail.applyPredicate state requirement.predicate)
      })
    (success : Detail.solveRequirements inferenceContext state requirements =
      .ok solved) :
    ∀ row, row ∈ solved →
      ScopedRequirementEntryValid semanticContext source row := by
  have corresponds := solveRequirements_corresponds success
  clear success
  revert template_iff template_scoped
  induction corresponds with
  | nil =>
      intro _ _ row member
      simp at member
  | @cons requirement row requirements rows head tail induction =>
      intro template_iff template_scoped candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · rcases head with ⟨id_eq, predicate_eq, evidence_success⟩
        by_cases template : requirement.id ∈ state.localSchemeAssumptions
        · have evidence_eq := solveRequirementEvidence_template_eq template
            evidence_success
          have candidate_eq : candidate = {
              id := requirement.id
              predicate := Detail.applyPredicate state requirement.predicate
              evidence := .assumption
                (Detail.applyPredicate state requirement.predicate)
            } := by
            cases candidate
            simp_all
          rw [candidate_eq]
          exact .template (template_scoped requirement (by simp) template)
        · have valid := solveRequirementEvidence_ordinary_sound
            (semanticContext := semanticContext) template signatures_eq
            assumptions_eq evidence_success
          have not_template : requirement.id ∉
              sourceLocalSchemeTemplateIds source := by
            intro source_member
            exact template ((template_iff requirement (by simp)).mpr
              source_member)
          have candidate_eq : candidate = {
              id := requirement.id
              predicate := Detail.applyPredicate state requirement.predicate
              evidence := candidate.evidence
            } := by
            cases candidate
            simp_all
          rw [candidate_eq]
          exact .ordinary not_template valid
      · exact induction
          (fun tailRequirement tailMember =>
            template_iff tailRequirement (by simp [tailMember]))
          (fun tailRequirement tailMember template =>
            template_scoped tailRequirement (by simp [tailMember]) template)
          candidate member

/-- A duplicate-free inference ledger with complete source-template coverage
becomes a whole-body scoped requirement ledger after successful solving. -/
theorem solveRequirements_scoped_ledger_sound_of_nodup
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {baseContext : SourceSemantics.Context}
    {source : TypedSource}
    (ledgerUnique :
      (state.requirements.map fun requirement => requirement.id).Nodup)
    (signatures_eq : baseContext.signatures = inferenceContext.signatures)
    (assumptions_eq : baseContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (templateOwnership : LocalSchemeTemplateOwnership source)
    (template_iff : ∀ requirement, requirement ∈ state.requirements →
      (requirement.id ∈ state.localSchemeAssumptions ↔
        requirement.id ∈ sourceLocalSchemeTemplateIds source))
    (templates_subset : sourceLocalSchemeTemplateIds source ⊆
      state.requirements.map (fun requirement => requirement.id))
    (template_scoped : ∀ requirement, requirement ∈ state.requirements →
      requirement.id ∈ state.localSchemeAssumptions →
      LocalSchemeTemplateRowScoped source {
        id := requirement.id
        predicate := Detail.applyPredicate state requirement.predicate
        evidence := .assumption
          (Detail.applyPredicate state requirement.predicate)
      })
    (success : Detail.solveRequirements inferenceContext state
      state.requirements = .ok solved) :
    ScopedRequirementLedgerWellFormed
      (baseContext.withSolvedRequirements solved) source := by
  refine {
    idsUnique := ?_
    templateOwnership := templateOwnership
    entriesValid := ?_
    templatesComplete := ?_
  }
  · change (solved.map (fun requirement => requirement.id)).Nodup
    rw [Detail.solveRequirements_preserves_ids inferenceContext state
      state.requirements solved success]
    exact ledgerUnique
  · exact solveRequirements_scoped_entries_sound
      (semanticContext := baseContext.withSolvedRequirements solved)
      signatures_eq assumptions_eq template_iff template_scoped success
  · intro owner contains
    have templateMember : owner.requirement.templateRequirement ∈
        sourceLocalSchemeTemplateIds source :=
      sourceLocalSchemeTemplateIds_mem_iff.mpr ⟨owner, contains, rfl⟩
    have inputMember : owner.requirement.templateRequirement ∈
        state.requirements.map (fun requirement => requirement.id) :=
      templates_subset templateMember
    have ids_eq := Detail.solveRequirements_preserves_ids inferenceContext state
      state.requirements solved success
    have outputMember : owner.requirement.templateRequirement ∈
        solved.map (fun requirement => requirement.id) := by
      rw [ids_eq]
      exact inputMember
    rcases List.mem_map.mp outputMember with ⟨row, member, id_eq⟩
    exact ⟨row, member, id_eq⟩

/-- Compatibility form deriving duplicate-free raw requirement identities
from the canonical allocation invariant. -/
theorem solveRequirements_scoped_ledger_sound
    {inferenceContext : Frontend.SourceInference.Context}
    {state : Frontend.SourceInference.State}
    {solved : List SolvedRequirement}
    {baseContext : SourceSemantics.Context}
    {source : TypedSource}
    (stateWellFormed : state.RequirementsWellFormed)
    (signatures_eq : baseContext.signatures = inferenceContext.signatures)
    (assumptions_eq : baseContext.assumptions =
      inferenceContext.assumptions.map (Detail.applyPredicate state))
    (templateOwnership : LocalSchemeTemplateOwnership source)
    (template_iff : ∀ requirement, requirement ∈ state.requirements →
      (requirement.id ∈ state.localSchemeAssumptions ↔
        requirement.id ∈ sourceLocalSchemeTemplateIds source))
    (templates_subset : sourceLocalSchemeTemplateIds source ⊆
      state.requirements.map (fun requirement => requirement.id))
    (template_scoped : ∀ requirement, requirement ∈ state.requirements →
      requirement.id ∈ state.localSchemeAssumptions →
      LocalSchemeTemplateRowScoped source {
        id := requirement.id
        predicate := Detail.applyPredicate state requirement.predicate
        evidence := .assumption
          (Detail.applyPredicate state requirement.predicate)
      })
    (success : Detail.solveRequirements inferenceContext state
      state.requirements = .ok solved) :
    ScopedRequirementLedgerWellFormed
      (baseContext.withSolvedRequirements solved) source := by
  apply solveRequirements_scoped_ledger_sound_of_nodup
    (Frontend.SourceInference.State.requirementIds_nodup state stateWellFormed)
    signatures_eq assumptions_eq templateOwnership template_iff
    templates_subset template_scoped success

/-- Qualified-local template identities materialized directly by one source
node.  Expression nodes never materialize binders; statement nodes may retain
an initialized `let` directly or in a `for` header. -/
def nodeLocalSchemeTemplateIds : Node → List RequirementId
  | .expression _ => []
  | .statement statement =>
      (statementInitializedLetBindings statement.form).flatMap fun binding =>
        binding.binder.schemeRequirements.map
          (fun requirement => requirement.templateRequirement)

/-- Appending one node appends exactly that node's qualified-local template
identity inventory. -/
theorem recordNode_sourceLocalSchemeTemplateIds
    (state : Frontend.SourceInference.State) (node : Node)
    (roots : List NodeId) :
    sourceLocalSchemeTemplateIds ((state.recordNode node).toTypedSource roots) =
      sourceLocalSchemeTemplateIds (state.toTypedSource roots) ++
        nodeLocalSchemeTemplateIds node := by
  cases node with
  | expression expression =>
      simp [Frontend.SourceInference.State.recordNode,
        Frontend.SourceInference.State.toTypedSource,
        sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
        initializedLetBindings, nodeLocalSchemeTemplateIds]
  | statement statement =>
      simp [Frontend.SourceInference.State.recordNode,
        Frontend.SourceInference.State.toTypedSource,
        sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
        initializedLetBindings, InitializedLetBinding.templateOwners,
        nodeLocalSchemeTemplateIds, List.map_flatMap,
        List.map_map, Function.comp_def]

/-- ID-only ghost invariant for source-inference template tracking.  The
`pending` suffix contains template identities allocated into binders whose
owning statement node has not yet been recorded. -/
structure TemplateTracking (state : Frontend.SourceInference.State)
    (pending : List RequirementId) : Prop where
  classified : state.localSchemeAssumptions.Perm
    (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ pending)
  unique : state.localSchemeAssumptions.Nodup
  covered : ∀ id, id ∈ state.localSchemeAssumptions →
    id ∈ state.requirements.map (fun requirement => requirement.id)

namespace TemplateTracking

/-- Initial inference states contain neither source-owned nor pending local
scheme templates. -/
theorem initial (owner : Resolved.DeclarationId)
    (locals : TypeSystem.Environment := [])
    (comptime : List Bool := []) :
    TemplateTracking
      (Frontend.SourceInference.State.initial owner locals comptime) [] := by
  constructor <;>
    simp [Frontend.SourceInference.State.initial,
      Frontend.SourceInference.State.toTypedSource,
      sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings]

/-- Executable finalization-boundary validation reconstructs the proof-facing
template tracking invariant with no pending binder materialization. -/
theorem ofValidation
    {state : Frontend.SourceInference.State} {roots : List NodeId}
    (success : Detail.validateSourceTemplateTracking
      (state.toTypedSource roots) state = .ok ()) :
    TemplateTracking state [] := by
  have validated := Detail.validateSourceTemplateTracking_success success
  constructor
  · simpa [Frontend.SourceInference.State.toTypedSource,
      sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
      initializedLetBindings] using validated.2.2.1
  · exact validated.2.1
  · exact validated.2.2.2

/-- Replacing only the executable local type environment leaves template
classification, uniqueness, and requirement-ledger coverage unchanged.  This
is the exact state update performed immediately before let-binder allocation. -/
theorem replaceLocals
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (locals : TypeSystem.Environment) :
    TemplateTracking { state with locals := locals } pending := by
  constructor
  · change state.localSchemeAssumptions.Perm
      (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ pending)
    exact tracked.classified
  · change state.localSchemeAssumptions.Nodup
    exact tracked.unique
  · change ∀ id, id ∈ state.localSchemeAssumptions →
      id ∈ state.requirements.map (fun requirement => requirement.id)
    exact tracked.covered

/-- Allocating a batch of ordinary use-site requirements leaves template
classification and uniqueness unchanged.  Its only effect on template
tracking is to extend the requirement ledger that covers every classified
template identity. -/
theorem addRequirementsWithIds
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (predicates : List ProgramPredicate) :
    TemplateTracking
      (state.addRequirementsWithIds predicates).2 pending := by
  have assumptions_eq :
      (state.addRequirementsWithIds predicates).2.localSchemeAssumptions =
        state.localSchemeAssumptions := by
    clear tracked
    induction predicates generalizing state with
    | nil => rfl
    | cons predicate rest induction =>
        simp only [Frontend.SourceInference.State.addRequirementsWithIds]
        simpa [Frontend.SourceInference.State.addRequirementWithId] using
          (induction (state := (state.addRequirementWithId predicate).2))
  have source_eq :
      (state.addRequirementsWithIds predicates).2.toTypedSource [] =
        state.toTypedSource [] := by
    clear tracked assumptions_eq
    induction predicates generalizing state with
    | nil => rfl
    | cons predicate rest induction =>
        simp only [Frontend.SourceInference.State.addRequirementsWithIds]
        simpa [Frontend.SourceInference.State.addRequirementWithId,
          Frontend.SourceInference.State.toTypedSource] using
          (induction (state := (state.addRequirementWithId predicate).2))
  constructor
  · rw [assumptions_eq, source_eq]
    exact tracked.classified
  · rw [assumptions_eq]
    exact tracked.unique
  · intro id member
    rw [assumptions_eq] at member
    rcases List.mem_map.mp (tracked.covered id member) with
      ⟨requirement, requirementMember, requirementId⟩
    exact List.mem_map.mpr ⟨requirement,
      Frontend.SourceInference.State.addRequirementsWithIds_requirements_subset
        state predicates requirementMember,
      requirementId⟩

/-- Template-ledger tracking supplies the containment premise that turns a
guarded stable-binder lookup into the frontend's complete batch-allocation
certificate for one generalized-local reference. -/
theorem lookupBinderRequirementAllocationCertificate
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (requirementsWellFormed : state.RequirementsWellFormed)
    (name : String) (binder : TypedBinder)
    (predicates : List ProgramPredicate)
    (found : state.lookupBinder? name = some binder) :
    Frontend.SourceInference.State.LookupBinderRequirementAllocationCertificate
      state binder predicates :=
  Frontend.SourceInference.State.addRequirementsWithIds_lookupBinder_certificate
    state name binder predicates requirementsWellFormed tracked.covered found

/-- Allocating a binder moves its qualified requirement identities into the
pending suffix.  Canonical generalization supplies the three side conditions:
new identities are distinct, fresh for the classification, and already occur
in the input requirement ledger. -/
theorem allocateBinder
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (name : String) (scheme : TypeSystem.Scheme)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false)
    (schemeRequirements : List LocalSchemeRequirement := [])
    (newUnique :
      (schemeRequirements.map (fun requirement =>
        requirement.templateRequirement)).Nodup)
    (newFresh : ∀ id, id ∈ schemeRequirements.map (fun requirement =>
        requirement.templateRequirement) →
      id ∉ state.localSchemeAssumptions)
    (newCovered : ∀ id, id ∈ schemeRequirements.map (fun requirement =>
        requirement.templateRequirement) →
      id ∈ state.requirements.map (fun requirement => requirement.id)) :
    TemplateTracking
      (state.allocateBinder name scheme span comptime schemeRequirements).2
      (pending ++ schemeRequirements.map (fun requirement =>
        requirement.templateRequirement)) := by
  let added := schemeRequirements.map (fun requirement =>
    requirement.templateRequirement)
  constructor
  · change (state.localSchemeAssumptions ++ added).Perm
      (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++
        (pending ++ added))
    simpa only [List.append_assoc] using tracked.classified.append_right added
  · change (state.localSchemeAssumptions ++ added).Nodup
    rw [List.nodup_append]
    refine ⟨tracked.unique, (by simpa [added] using newUnique), ?_⟩
    intro old oldMember new newMember same
    subst new
    exact newFresh old (by simpa [added] using newMember) oldMember
  · intro id member
    change id ∈ state.requirements.map (fun requirement => requirement.id)
    change id ∈ state.localSchemeAssumptions ++ added at member
    rcases List.mem_append.mp member with oldMember | addedMember
    · exact tracked.covered id oldMember
    · exact newCovered id (by simpa [added] using addedMember)

/-- Canonical local generalization discharges every side condition required
by template-tracking binder allocation.  The executable let paths first
replace `locals` with its substituted form and then perform exactly this
allocation. -/
theorem allocateGeneralizedValue
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (requirementsWellFormed : state.RequirementsWellFormed)
    (locals : TypeSystem.Environment) (requirementStart : Nat)
    (type : TypeSystem.Ty) (name : String)
    (span : Option Syntax.SourceSpan := none) (comptime : Bool := false) :
    let generalized := Frontend.SourceInference.Detail.generalizeValue state
      locals requirementStart type
    TemplateTracking
      (({ state with locals := locals }).allocateBinder name
        generalized.scheme span comptime generalized.requirements).2
      (pending ++ generalized.requirements.map fun requirement =>
        requirement.templateRequirement) := by
  dsimp only
  apply allocateBinder (tracked.replaceLocals locals) name
    (Frontend.SourceInference.Detail.generalizeValue state locals
      requirementStart type).scheme span comptime
    (Frontend.SourceInference.Detail.generalizeValue state locals
      requirementStart type).requirements
  · exact
      (Frontend.SourceInference.Detail.generalizeValue_templateIds_sublist
        state locals requirementStart type).nodup
        (Frontend.SourceInference.State.requirementIds_nodup state
          requirementsWellFormed)
  · intro id member
    change id ∉ state.localSchemeAssumptions
    exact Frontend.SourceInference.Detail.generalizeValue_templateIds_fresh
      state locals requirementStart type id member
  · intro id member
    change id ∈ state.requirements.map (fun requirement => requirement.id)
    exact
      (Frontend.SourceInference.Detail.generalizeValue_templateIds_sublist
        state locals requirementStart type).subset member

/-- Recording a node materializes a pending suffix matching that node's exact
template inventory; older ambient pending identities remain pending. -/
theorem recordNode
    {state : Frontend.SourceInference.State}
    {ambient : List RequirementId} {node : Node}
    (tracked : TemplateTracking state
      (ambient ++ nodeLocalSchemeTemplateIds node)) :
    TemplateTracking (state.recordNode node) ambient := by
  constructor
  · change state.localSchemeAssumptions.Perm
      (sourceLocalSchemeTemplateIds ((state.recordNode node).toTypedSource []) ++
        ambient)
    rw [recordNode_sourceLocalSchemeTemplateIds]
    have swapped :
        (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++
            (ambient ++ nodeLocalSchemeTemplateIds node)).Perm
          (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++
            (nodeLocalSchemeTemplateIds node ++ ambient)) :=
      List.Perm.append_left _ List.perm_append_comm
    simpa only [List.append_assoc] using tracked.classified.trans swapped
  · change state.localSchemeAssumptions.Nodup
    exact tracked.unique
  · change ∀ id, id ∈ state.localSchemeAssumptions →
      id ∈ state.requirements.map (fun requirement => requirement.id)
    exact tracked.covered

/-- Lexical restoration changes neither the emitted node table nor executable
template classification and therefore preserves every pending suffix. -/
theorem restoreLexicalScope
    {state : Frontend.SourceInference.State}
    {pending : List RequirementId}
    (tracked : TemplateTracking state pending)
    (scope : Frontend.SourceInference.LexicalScope) :
    TemplateTracking (state.restoreLexicalScope scope) pending := by
  constructor
  · change state.localSchemeAssumptions.Perm
      (sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ pending)
    exact tracked.classified
  · change state.localSchemeAssumptions.Nodup
    exact tracked.unique
  · change ∀ id, id ∈ state.localSchemeAssumptions →
      id ∈ state.requirements.map (fun requirement => requirement.id)
    exact tracked.covered

/-- Once no template identity remains pending, the materialized source owns
globally unique qualified-template identities. -/
theorem ownership
    {state : Frontend.SourceInference.State}
    (tracked : TemplateTracking state []) (roots : List NodeId := []) :
    LocalSchemeTemplateOwnership (state.toTypedSource roots) := by
  constructor
  have sourceUnique :
      (sourceLocalSchemeTemplateIds (state.toTypedSource [])).Nodup := by
    simpa using tracked.classified.nodup_iff.mp tracked.unique
  simpa [Frontend.SourceInference.State.toTypedSource,
    sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
    initializedLetBindings] using sourceUnique

/-- With an empty pending suffix, executable classification and materialized
source ownership classify exactly the same stable identities. -/
theorem classified_iff
    {state : Frontend.SourceInference.State}
    (tracked : TemplateTracking state []) (roots : List NodeId := [])
    (id : RequirementId) :
    id ∈ state.localSchemeAssumptions ↔
      id ∈ sourceLocalSchemeTemplateIds (state.toTypedSource roots) := by
  have aligned : id ∈ state.localSchemeAssumptions ↔
      id ∈ sourceLocalSchemeTemplateIds (state.toTypedSource []) ++ [] :=
    tracked.classified.mem_iff
  simpa [Frontend.SourceInference.State.toTypedSource,
    sourceLocalSchemeTemplateIds, localSchemeTemplateOwners,
    initializedLetBindings] using aligned

/-- Every fully materialized source template identity comes from an input
requirement row. -/
theorem source_ids_subset_requirements
    {state : Frontend.SourceInference.State}
    (tracked : TemplateTracking state []) (roots : List NodeId := []) :
    sourceLocalSchemeTemplateIds (state.toTypedSource roots) ⊆
      state.requirements.map (fun requirement => requirement.id) := by
  intro id sourceMember
  exact tracked.covered id ((tracked.classified_iff roots id).mpr sourceMember)

end TemplateTracking

/-- Every successful finalization input has a complete, unique and
ledger-covered qualified-template classification. -/
theorem finalize_templateTracking
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    TemplateTracking state [] :=
  TemplateTracking.ofValidation
    (Detail.finalize_validateSourceTemplateTracking success)

/-- Final substitution preserves the globally unique ownership of every
qualified local-scheme template retained by a finalized source. -/
theorem finalize_localSchemeTemplateOwnership
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    LocalSchemeTemplateOwnership result.typedSource := by
  rw [Detail.finalize_typedSource success]
  exact FlexibleSubstitution.LocalSchemeTemplateOwnership.applySubstitution
    result.substitution ((finalize_templateTracking success).ownership roots)

/-- Successfully checked function bodies retain globally unique qualified
local-scheme template identities. -/
theorem checkFunctionBody_success_localSchemeTemplateOwnership
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    LocalSchemeTemplateOwnership checked.typedBody := by
  obtain ⟨_, _, _, _, _, _, _, finalizeSuccess, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  exact finalize_localSchemeTemplateOwnership finalizeSuccess

/-- The source-owned qualified-local template identities materialized from a
state agree exactly with the state's executable template classification. -/
def TemplateIdsAligned (state : Frontend.SourceInference.State)
    (roots : List NodeId) : Prop :=
  ∀ id, id ∈ sourceLocalSchemeTemplateIds (state.toTypedSource roots) ↔
    id ∈ state.localSchemeAssumptions

/-- Final substitution preserves source template identities, so an alignment
established before finalization remains visible in the emitted typed source. -/
theorem finalize_templateIdsAligned
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (aligned : TemplateIdsAligned state roots)
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    ∀ id, id ∈ sourceLocalSchemeTemplateIds result.typedSource ↔
      id ∈ state.localSchemeAssumptions := by
  intro id
  rw [Detail.finalize_typedSource success]
  simp only [FlexibleSubstitution.sourceLocalSchemeTemplateIds_applySubstitution]
  exact aligned id

/-- Successful finalization supplies template classification alignment without
an external tracking premise. -/
theorem finalize_templateIdsAligned_validated
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    ∀ id, id ∈ sourceLocalSchemeTemplateIds result.typedSource ↔
      id ∈ state.localSchemeAssumptions := by
  apply finalize_templateIdsAligned
    (aligned := fun id =>
      ((finalize_templateTracking success).classified_iff roots id).symm)
    success

/-- A template row in a successfully finalized source retains canonical
assumption evidence whenever the input state's executable classification is
aligned with the source-owned template identities. -/
theorem finalize_template_evidence
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (aligned : TemplateIdsAligned state roots)
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    ∀ row, row ∈ result.solvedRequirements →
      row.id ∈ sourceLocalSchemeTemplateIds result.typedSource →
      row.evidence = .assumption row.predicate := by
  intro row member template
  have initialTemplate : row.id ∈ state.localSchemeAssumptions :=
    (finalize_templateIdsAligned aligned success row.id).mp template
  obtain ⟨patternState, finalState, requirements, _, _, _, _, patternResult,
      literalResult, _, _, _, _, requirementsResult, resultEq⟩ :=
    Detail.finalize_success_witness success
  have finalTemplate : row.id ∈ finalState.localSchemeAssumptions := by
    rw [Detail.defaultIntegerLiteralTargets_localSchemeAssumptions
      literalResult,
      Detail.defaultIntegerPatternTargets_localSchemeAssumptions
        patternResult]
    exact initialTemplate
  subst result
  exact solveRequirements_template_evidence requirementsResult row member
    finalTemplate

/-- Successful finalization alone supplies the ID alignment required to show
that every emitted qualified-template row retains assumption evidence. -/
theorem finalize_template_evidence_validated
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    ∀ row, row ∈ result.solvedRequirements →
      row.id ∈ sourceLocalSchemeTemplateIds result.typedSource →
      row.evidence = .assumption row.predicate := by
  apply finalize_template_evidence
    (aligned := fun id =>
      ((finalize_templateTracking success).classified_iff roots id).symm)
    success

/-- Proof-facing context for the requirement ledger emitted by finalization.
Both declaration assumptions and solved predicates use the final inference
substitution, while the complete solved ledger is retained for later lookup. -/
def finalizedRequirementContext
    (inferenceContext : Frontend.SourceInference.Context)
    (result : Frontend.SourceInference.Result) : SourceSemantics.Context :=
  ((SourceSemantics.Context.ofSignatures inferenceContext.signatures)
    |>.withAssumptions
      (inferenceContext.assumptions.map
        (TypedTraitResolution.applySubstitution result.substitution)))
    |>.withSolvedRequirements result.solvedRequirements

/-- Requirement-only semantic context projected from a checked function.  It
retains the final substitution on declaration predicates without yet adding
the declaration/type-variable fields used by deep body typing. -/
def checkedFinalizedRequirementContext
    (signatures : ProgramSignatures)
    (signature : ProgramFunctionSignature)
    (checked : CheckedFunction) : SourceSemantics.Context :=
  ((SourceSemantics.Context.ofSignatures signatures)
    |>.withAssumptions
      (signature.scheme.predicates.map
        (TypedTraitResolution.applySubstitution checked.substitution)))
    |>.withSolvedRequirements checked.solvedRequirements

/-- Successful finalization establishes the complete scoped requirement
ledger for its finalized source, including ordinary evidence and qualified
initializer-local assumption templates. -/
theorem finalize_scopedRequirementLedgerWellFormed
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    ScopedRequirementLedgerWellFormed
      (finalizedRequirementContext inferenceContext result)
      result.typedSource := by
  obtain ⟨patternState, finalState, solved, _, _, trackingValidation, _,
      patternDefault, literalDefault, _, _, ownershipValidation,
      scopeValidation, requirementsSolved, resultEq⟩ :=
    Detail.finalize_success_witness success
  have aligned := finalize_templateIdsAligned_validated success
  have templateOwnership := finalize_localSchemeTemplateOwnership success
  have ownershipFacts :=
    Detail.validateSourceRequirementOwnership_success ownershipValidation
  subst result
  have assumptionsEq : finalState.localSchemeAssumptions =
      state.localSchemeAssumptions := by
    rw [Detail.defaultIntegerLiteralTargets_localSchemeAssumptions
      literalDefault,
      Detail.defaultIntegerPatternTargets_localSchemeAssumptions
        patternDefault]
  have templateIff : ∀ requirement,
      requirement ∈ finalState.requirements →
      (requirement.id ∈ finalState.localSchemeAssumptions ↔
        requirement.id ∈ sourceLocalSchemeTemplateIds
          ((finalState.toTypedSource roots).applySubstitution
            finalState.inference.substitution)) := by
    intro requirement _
    rw [assumptionsEq]
    exact (aligned requirement.id).symm
  have templatesSubset :
      sourceLocalSchemeTemplateIds
          ((finalState.toTypedSource roots).applySubstitution
            finalState.inference.substitution) ⊆
        finalState.requirements.map (fun requirement => requirement.id) := by
    intro id templateMember
    have executableTemplateMember : id ∈
        ((finalState.toTypedSource roots).applySubstitution
          finalState.inference.substitution).localSchemeTemplateIds := by
      simpa using templateMember
    rw [typedSourceLocalSchemeTemplateIds_eq_sites] at executableTemplateMember
    rcases List.mem_map.mp executableTemplateMember with
      ⟨site, siteMember, siteIdEq⟩
    obtain ⟨requirement, _, requirementMember, requirementId, _, _, _, _⟩ :=
      Detail.validateSourceTemplateScopes_success scopeValidation site
        siteMember
    exact List.mem_map.mpr
      ⟨requirement, requirementMember, requirementId.trans siteIdEq⟩
  have templateScoped : ∀ requirement,
      requirement ∈ finalState.requirements →
      requirement.id ∈ finalState.localSchemeAssumptions →
      LocalSchemeTemplateRowScoped
        ((finalState.toTypedSource roots).applySubstitution
          finalState.inference.substitution) {
          id := requirement.id
          predicate := Detail.applyPredicate finalState requirement.predicate
          evidence := .assumption
            (Detail.applyPredicate finalState requirement.predicate)
        } := by
    intro requirement requirementMember classified
    exact validateSourceTemplateScopes_success_rowScoped scopeValidation
      ownershipFacts.2.1 requirementMember
      ((templateIff requirement requirementMember).mp classified)
  let baseContext : SourceSemantics.Context :=
    (SourceSemantics.Context.ofSignatures inferenceContext.signatures)
      |>.withAssumptions
        (inferenceContext.assumptions.map
          (TypedTraitResolution.applySubstitution
            finalState.inference.substitution))
  have ledgerProof := solveRequirements_scoped_ledger_sound_of_nodup
    (baseContext := baseContext)
    ownershipFacts.2.1 (by rfl) (by rfl) templateOwnership templateIff
    templatesSubset templateScoped requirementsSolved
  simpa [finalizedRequirementContext, baseContext]
    using ledgerProof

/-- Once structural closure and local-scheme freshness are available,
successful finalization supplies the remaining evidence obligation for the
final inference substitution from its target-side scoped requirement ledger. -/
theorem finalize_contextSubstitutionValid
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    {sourceContext : SourceSemantics.Context}
    {closedVariables : List TypeSystem.TypeVarId}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    (closes : FlexibleSubstitution.ContextCloses result.substitution
      closedVariables sourceContext
      (finalizedRequirementContext inferenceContext result))
    (schemesFresh : FlexibleSubstitution.LocalSchemesFreshFor sourceContext
      result.substitution) :
    FlexibleSubstitution.ContextSubstitutionValid result.substitution
      closedVariables sourceContext
      (finalizedRequirementContext inferenceContext result) := by
  exact
    FlexibleSubstitution.ContextSubstitutionValid.ofTargetScopedRequirementLedger
      closes schemesFresh
      (finalize_scopedRequirementLedgerWellFormed success)

/-- Exact executable source-to-ledger validation survives final substitution
and establishes the declarative whole-source requirement ownership judgment. -/
theorem finalize_requirementOwnership
    {semanticContext : SourceSemantics.Context}
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (solved_eq :
      semanticContext.solvedRequirements = result.solvedRequirements)
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    RequirementOwnership semanticContext result.typedSource := by
  obtain ⟨_, finalState, solved, _, _, _, _, _, _, _, _,
      ownershipValidation, _, requirementsSolved, resultEq⟩ :=
    Detail.finalize_success_witness success
  have validated :=
    Detail.validateSourceRequirementOwnership_success ownershipValidation
  have idsEq := Detail.solveRequirements_preserves_ids inferenceContext
    finalState finalState.requirements solved requirementsSolved
  subst result
  constructor
  · simpa using validated.1
  · rw [solved_eq]
    simpa [idsEq] using validated.2.2

/-- The reusable whole-body resources exposed by one successful finalization.

The hidden post-defaulting state is retained so recursive inference proofs can
target the exact state consumed by requirement solving.  Source containment,
on the other hand, remains stated against the public input and output sources:
the final source is precisely the input source under the returned
substitution. -/
structure FinalInferenceResources
    (inferenceContext : Frontend.SourceInference.Context)
    (type : TypeSystem.Ty)
    (state : Frontend.SourceInference.State)
    (roots : List NodeId)
    (result : Frontend.SourceInference.Result) where
  finalState : Frontend.SourceInference.State
  progress_of_ready :
    state.InferenceReady → state.InferenceProgress finalState
  requirements_eq : finalState.requirements = state.requirements
  substitution_eq :
    result.substitution = finalState.inference.substitution
  solve_success :
    Detail.solveRequirements inferenceContext finalState
      finalState.requirements = .ok result.solvedRequirements
  type_eq : result.type = result.substitution.apply type
  source_eq : result.typedSource =
    (state.toTypedSource roots).applySubstitution result.substitution
  solved_context_eq :
    (finalizedRequirementContext inferenceContext result).solvedRequirements =
      result.solvedRequirements
  range_formation :
    Frontend.InferenceSubstitutionRangeFormationValidated
      inferenceContext.signatures inferenceContext.scope.genericOwner
      inferenceContext.typeParameters result.substitution
  graph_closed : OccurrenceGraphClosed result.typedSource
  local_identity_ownership : LocalIdentityOwnership result.typedSource
  ledger : ScopedRequirementLedgerWellFormed
    (finalizedRequirementContext inferenceContext result) result.typedSource
  ownership : RequirementOwnership
    (finalizedRequirementContext inferenceContext result) result.typedSource
  local_no_capture : ∀ binder,
    binder ∈ (state.toTypedSource roots).initializedLetBinders →
      Detail.LocalBinderInstantiationNoCapture result.substitution binder

namespace FinalInferenceResources

/-- Package all finalization-wide resources around the exact hidden solver
state.  The progress projection remains conditional on inference readiness,
which is the invariant threaded by recursive source inference. -/
def ofFinalize
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    FinalInferenceResources inferenceContext type state roots result := by
  let witness := Detail.finalize_success_witness success
  have requirementsEq :
      witness.finalState.requirements = state.requirements := by
    rw [Detail.defaultIntegerLiteralTargets_requirements
      witness.literalDefault,
      Detail.defaultIntegerPatternTargets_requirements
        witness.patternDefault]
  have substitutionEq :
      result.substitution = witness.finalState.inference.substitution :=
    congrArg Frontend.SourceInference.Result.substitution witness.result_eq
  have solvedEq :
      result.solvedRequirements = witness.solvedRequirements :=
    congrArg Frontend.SourceInference.Result.solvedRequirements
      witness.result_eq
  refine {
    finalState := witness.finalState
    progress_of_ready := ?_
    requirements_eq := requirementsEq
    substitution_eq := substitutionEq
    solve_success := ?_
    type_eq := Detail.finalize_type success
    source_eq := Detail.finalize_typedSource success
    solved_context_eq := rfl
    range_formation :=
      Detail.finalize_substitutionRangeFormationValidated success
    graph_closed := finalize_occurrenceGraphClosed success
    local_identity_ownership := finalize_localIdentityOwnership success
    ledger := finalize_scopedRequirementLedgerWellFormed success
    ownership := finalize_requirementOwnership rfl success
    local_no_capture :=
      Detail.finalize_localBinderInstantiationNoCapture success
  }
  · intro ready
    have originsBelow := Detail.finalize_numericOriginsBelowNext success
    have patternProperties :=
      Detail.defaultIntegerPatternTargets_inferenceProperties ready
        originsBelow.1 witness.patternDefault
    have patternLiteralOrigins :=
      Detail.defaultIntegerPatternTargets_integerLiterals
        witness.patternDefault
    have literalOriginsBelow : ∀ origin ∈ witness.patternState.integerLiterals,
        origin.metavariable.index < witness.patternState.inference.next := by
      intro origin member
      have inputMember : origin ∈ state.integerLiterals := by
        rw [patternLiteralOrigins] at member
        exact member
      exact Nat.lt_of_lt_of_le (originsBelow.2 origin inputMember)
        patternProperties.1.next_le
    have literalProperties :=
      Detail.defaultIntegerLiteralTargets_inferenceProperties
        patternProperties.2 literalOriginsBelow witness.literalDefault
    exact patternProperties.1.trans literalProperties.1
  · rw [solvedEq]
    exact witness.requirementsSolved

end FinalInferenceResources

/-- Every successfully checked function body owns each solved requirement at
exactly one primary source occurrence, independently of ledger order. -/
theorem checkFunctionBody_success_requirementOwnership
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    RequirementOwnership (checkedBodyContext signatures signature checked)
      checked.typedBody := by
  obtain ⟨_, _, _, _, _, _, _, finalizeSuccess, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  exact finalize_requirementOwnership rfl finalizeSuccess

/-- Every successfully checked function body carries a complete scoped
requirement ledger in its final requirement-only semantic context. -/
theorem checkFunctionBody_success_scopedRequirementLedgerWellFormed
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    ScopedRequirementLedgerWellFormed
      (checkedFinalizedRequirementContext signatures signature checked)
      checked.typedBody := by
  obtain ⟨_, _, _, result, _, _, _, finalizeSuccess, checkedEq⟩ :=
    checkFunctionBody_success_witness success
  subst checked
  simpa [checkedFinalizedRequirementContext, finalizedRequirementContext]
    using finalize_scopedRequirementLedgerWellFormed finalizeSuccess

/-- Signature formation removes the final inference substitution from the
declaration predicates, transporting the finalized scoped ledger into the
complete declaration context used by deep body typing. -/
theorem checkFunctionBody_success_scopedRequirementLedgerWellFormed_bodyContext
    {environment : ProgramEnvironment}
    {signatures : ProgramSignatures}
    {signature : ProgramFunctionSignature}
    {fuel : Nat}
    {checked : CheckedFunction}
    (formation : ProgramSignatureFormationValidated signatures)
    (member : signature ∈ signatures.functions)
    (success : checkFunctionBody environment signatures signature fuel =
      .ok checked) :
    ScopedRequirementLedgerWellFormed
      (checkedBodyContext signatures signature checked)
      checked.typedBody := by
  apply ScopedRequirementLedgerWellFormed.transportContext
    (source := checkedFinalizedRequirementContext signatures signature checked)
    (target := checkedBodyContext signatures signature checked)
  · rfl
  · change signature.scheme.predicates =
      signature.scheme.predicates.map
        (TypedTraitResolution.applySubstitution checked.substitution)
    exact ((formation.functions signature member).2.2.apply_eq_self
      checked.substitution).symm
  · rfl
  · exact checkFunctionBody_success_scopedRequirementLedgerWellFormed
      success

/-- Executable finalization connects one retained integer-literal node to the
declarative validity judgment through its exact requirement row. -/
theorem finalize_integerLiteralValid_of_mem
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    (solvedValid :
      SolvedRequirementsValid
        (finalizedRequirementContext inferenceContext result)
        result.solvedRequirements)
    {node : ExpressionNode}
    {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (member : Node.expression node ∈ state.nodes)
    (form_eq : node.form = .integerLiteral source resolution) :
    IntegerLiteralValid
      (finalizedRequirementContext inferenceContext result)
      source
      (resolution.applySubstitution result.substitution) := by
  obtain ⟨patternState, finalState, requirements, _, _, _, ledgerValidation,
      patternResult, literalResult, _, literalValidation, _,
      _, requirementsResult, resultEq⟩ :=
    Detail.finalize_success_witness success
  have ledger :=
    Detail.validateIntegerLiteralLedger_success_correspondence
      ledgerValidation
  obtain ⟨decoded, origin, originMember, _, targetEq, _, requirementMember⟩ :=
    ledger node source resolution member form_eq
  have finalOriginMember : origin ∈ finalState.integerLiterals := by
    rw [Detail.defaultIntegerLiteralTargets_integerLiterals literalResult,
      Detail.defaultIntegerPatternTargets_integerLiterals patternResult]
    exact originMember
  have supported :=
    Detail.validateIntegerLiteralTargets_success_supported literalValidation
      origin finalOriginMember
  have finalRequirementMember :
      ({ id := resolution.requirement, predicate := resolution.predicate } :
        Requirement) ∈ finalState.requirements := by
    rw [Detail.defaultIntegerLiteralTargets_requirements literalResult,
      Detail.defaultIntegerPatternTargets_requirements patternResult]
    exact requirementMember
  subst result
  refine integerLiteralValid_of_solved decoded ?_ finalRequirementMember
    requirementsResult rfl solvedValid
  simpa [targetEq, Frontend.SourceInference.State.resolve,
    TypeSystem.InferState.resolve] using supported

/-- When finalization starts without qualified-local templates, every emitted
solved row has independently valid retained evidence in the finalized
requirement context. -/
theorem finalize_solvedRequirementsValid
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (ordinary : state.localSchemeAssumptions = [])
    (success : Detail.finalize inferenceContext type state roots = .ok result) :
    SolvedRequirementsValid
      (finalizedRequirementContext inferenceContext result)
      result.solvedRequirements := by
  obtain ⟨patternState, finalState, requirements, _, _, _, _, patternResult,
      literalResult, _, _, _, _, requirementsResult, resultEq⟩ :=
    Detail.finalize_success_witness success
  have patternOrdinary : patternState.localSchemeAssumptions = [] := by
    rw [Detail.defaultIntegerPatternTargets_localSchemeAssumptions
      patternResult, ordinary]
  have finalOrdinary : finalState.localSchemeAssumptions = [] := by
    rw [Detail.defaultIntegerLiteralTargets_localSchemeAssumptions
      literalResult, patternOrdinary]
  subst result
  apply solveRequirements_ordinary_sound
    (inferenceContext := inferenceContext)
    (state := finalState)
    (requirements := finalState.requirements)
  · intro requirement member
    rw [finalOrdinary]
    simp
  · rfl
  · rfl
  · exact requirementsResult

/-- In an ordinary (non-template) source body, successful finalization alone
supplies the retained solver evidence needed for integer-literal validity. -/
theorem finalize_integerLiteralValid_of_mem_ordinary
    {inferenceContext : Frontend.SourceInference.Context}
    {type : TypeSystem.Ty}
    {state : Frontend.SourceInference.State}
    {roots : List NodeId}
    {result : Frontend.SourceInference.Result}
    (ordinary : state.localSchemeAssumptions = [])
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    {node : ExpressionNode}
    {source : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution}
    (member : Node.expression node ∈ state.nodes)
    (form_eq : node.form = .integerLiteral source resolution) :
    IntegerLiteralValid
      (finalizedRequirementContext inferenceContext result)
      source
      (resolution.applySubstitution result.substitution) := by
  exact finalize_integerLiteralValid_of_mem success
    (finalize_solvedRequirementsValid ordinary success) member form_eq

end Solcore.SourceSemantics.SourceInferenceSoundness

namespace Solcore.SourceSemantics.FlexibleSubstitution

open Frontend SourceInference TypeSystem

/-- Once the inference pass has supplied a semantically valid closing
substitution, successful finalization transports the corresponding declarative
body derivation to the emitted typed source and result type. -/
theorem finalize_bodyHasType
    {inferenceContext : Frontend.SourceInference.Context}
    {type : Ty} {state : State} {roots : List NodeId} {result : Result}
    {sourceContext targetContext : SourceSemantics.Context}
    {closedVariables : List TypeVarId} {facts : BodyFacts}
    (success : Detail.finalize inferenceContext type state roots = .ok result)
    (catalog : SignatureCatalogWellFormed sourceContext.signatures)
    (contextValid : ContextSubstitutionValid result.substitution
      closedVariables sourceContext targetContext)
    (typing : BodyHasType (state.toTypedSource roots) sourceContext type facts) :
    BodyHasType result.typedSource targetContext result.type
      (applyBodyFacts result.substitution facts) := by
  rw [Detail.finalize_typedSource success, Detail.finalize_type success]
  exact BodyHasType.applySubstitution catalog contextValid typing

end Solcore.SourceSemantics.FlexibleSubstitution

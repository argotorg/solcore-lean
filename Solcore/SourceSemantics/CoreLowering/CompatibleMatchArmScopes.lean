import Solcore.SourceSemantics.CoreLowering.CompatiblePatternSourceBinders
import Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindingCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchCertificates

/-! Static source scope correspondence for a real match arm. Compiler
bindings are authenticated by the independently typed source pattern and its
retained declaration. The hidden scrutinee remains a separate internal slot. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatiblePatternCertificates CompatibleMatchCertificates

theorem rootBinder_filter
    {source : TypedSource} {id : Resolved.LocalId} {declared : TypedBinder}
    (accepted : SourceCoreDataPlaces.rootBinder source id = .ok declared) :
    (SourceCoreDataPlaces.declaredBinders source).filter (fun candidate => decide (candidate.id = id)) = [declared] := by
  unfold SourceCoreDataPlaces.rootBinder at accepted
  by_cases owned : id.owner ≠ source.owner
  · simp [owned, throw, bind, Except.bind] at accepted
  · simp only [owned, ↓reduceIte, bind, Except.bind] at accepted
    generalize selectedEq : (SourceCoreDataPlaces.declaredBinders source).filter
      (fun candidate => decide (candidate.id = id)) = selected at accepted
    cases selected with
    | nil => contradiction
    | cons first tail =>
      cases tail with
      | cons => contradiction
      | nil =>
        by_cases mono : first.scheme.quantified.isEmpty = true
        · by_cases empty : first.schemeRequirements.isEmpty = true
          · simp [mono, empty, pure, Except.pure] at accepted
            subst declared
            rfl
          · simp [mono, empty, throw] at accepted
        · simp [mono, throw] at accepted

theorem rootBinder_identifies
    {source : TypedSource} {binder declared : TypedBinder}
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (accepted : SourceCoreDataPlaces.rootBinder source binder.id = .ok declared) : declared = binder := by
  have filtered : binder ∈ (SourceCoreDataPlaces.declaredBinders source).filter
      (fun candidate => decide (candidate.id = binder.id)) := List.mem_filter.mpr ⟨member, by simp⟩
  rw [rootBinder_filter accepted] at filtered
  exact (List.mem_singleton.mp filtered).symm

theorem scope_internal
    {source : TypedSource} {scope : Scope} {context : SourceSemantics.Context}
    {internal : Resolved.LocalId} (payload : Ty)
    (absent : internal ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id))
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations source ((internal, payload) :: scope) context := by
  intro id declared index type selected authentic
  by_cases same : internal = id
  · subst id
    have present : declared ∈ (SourceCoreDataPlaces.declaredBinders source).filter
        (fun candidate => decide (candidate.id = internal)) := by
      rw [rootBinder_filter authentic]
      exact List.mem_singleton_self declared
    obtain ⟨member, sameId⟩ := List.mem_filter.mp present
    have sameId : declared.id = internal := of_decide_eq_true sameId
    exact False.elim (absent (List.mem_map.mpr ⟨declared, member, sameId⟩))
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at selected
    cases previous : SourceCoreLocalCell.lookup? scope id with
    | none => simp [previous] at selected
    | some entry => exact declarations _ _ _ _ previous authentic

theorem pattern_declarations
    {source : TypedSource} {site : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {arm : TypedMatchCase}
    (found : source.lookupStatement? site = some node)
    (form : node.form = .matchWith resolution) (member : arm ∈ resolution.cases)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty} {binders : List TypedBinder} {arity : Nat}
    (typed : TypedMatchPatternHasType context arm.pattern type binders arity) :
    ∀ binder ∈ binders, binder ∈ SourceCoreDataPlaces.declaredBinders source := by
  intro binder bound
  have patternMember : binder ∈ SourceCoreDataPlaces.patternBinders arm.pattern :=
    CompatiblePatternSourceBinders.pattern_binders typed ▸ bound
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨.statement node, (lookupStatement?_sound found).1, ?_⟩
  simp only [form]
  exact List.mem_flatMap.mpr ⟨arm, member, patternMember⟩

theorem scope_bind
    {source : TypedSource} {scope : Scope} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} (payload : Ty)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (extended : BinderExtends source.owner context binder nextContext) :
    CompatibleExpressionReads.ScopeDeclarations source ((binder.id, payload) :: scope) nextContext := by
  cases extended
  intro id declared index type selected authentic
  by_cases same : binder.id = id
  · subst id
    have identical := rootBinder_identifies member authentic
    subst declared
    exact .head
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at selected
    cases previous : SourceCoreLocalCell.lookup? scope id with
    | none => simp [previous] at selected
    | some entry => exact .tail same (declarations _ _ _ _ previous authentic)

theorem scope_binders
    {source : TypedSource} {scope : Scope} {context finalContext : SourceSemantics.Context}
    {bindings : List (TypedBinder × Ty)}
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (members : ∀ binder ∈ bindings.map Prod.fst, binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (extended : BindersExtend source.owner context (bindings.map Prod.fst) finalContext) :
    CompatibleExpressionReads.ScopeDeclarations source
      (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope) finalContext := by
  induction bindings generalizing scope context with
  | nil => cases extended; exact declarations
  | cons binding rest ih =>
    obtain ⟨binder, payload⟩ := binding
    cases extended with
    | cons head tail =>
      exact ih (scope_bind payload declarations (members binder List.mem_cons_self) head)
        (fun other member => members other (List.mem_cons_of_mem _ member)) tail

private theorem lookup_same_ids {first second : Scope} {binder : Resolved.LocalId} {index : Nat} {type : Ty}
    (same : first.map Prod.fst = second.map Prod.fst)
    (selected : SourceCoreLocalCell.lookup? second binder = some (index, type)) :
    ∃ payload, SourceCoreLocalCell.lookup? first binder = some (index, payload) := by
  induction first generalizing second index type with
  | nil =>
    cases second with
    | nil => cases selected
    | cons => cases same
  | cons entry rest ih =>
    obtain ⟨candidate, payload⟩ := entry
    cases second with
    | nil => cases same
    | cons entry tail =>
      obtain ⟨other, otherPayload⟩ := entry
      obtain ⟨rfl, sameTail⟩ := List.cons.inj same
      by_cases identical : candidate = binder
      · simp only [SourceCoreLocalCell.lookup?, identical, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at selected
        exact ⟨payload, selected.1.symm ▸ (by simp [SourceCoreLocalCell.lookup?, identical])⟩
      · simp only [SourceCoreLocalCell.lookup?, identical, ↓reduceIte] at selected ⊢
        cases previous : SourceCoreLocalCell.lookup? tail binder with
        | none => simp [previous] at selected
        | some entry =>
          obtain ⟨previousIndex, previousPayload⟩ := entry
          simp only [previous, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
          obtain ⟨firstPayload, found⟩ := ih sameTail previous
          exact ⟨firstPayload, by simp only [found, Option.map_some]; exact congrArg some (congrArg (fun n => (n, firstPayload)) selected.1)⟩

/-- Source declaration agreement depends on source identities in the scope.
This transports no native type or runtime environment typing. -/
theorem scope_ids {source : TypedSource} {first second : Scope} {context : SourceSemantics.Context}
    (same : first.map Prod.fst = second.map Prod.fst)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source first context) :
    CompatibleExpressionReads.ScopeDeclarations source second context := by
  intro binder declared index type selected authentic
  obtain ⟨payload, found⟩ := lookup_same_ids same selected
  exact declarations binder declared index payload found authentic

theorem Certificate.arm_scope
    {compilation : Compilation} {source : TypedSource} {scope : Scope} {site : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {arm : TypedMatchCase}
    {expected : TypeSystem.Ty} {compiled : Pattern}
    (found : source.lookupStatement? site = some node)
    (form : node.form = .matchWith resolution) (member : arm ∈ resolution.cases)
    (certificate : CompatiblePatternCertificates.Certificate compilation source scope site arm.span expected arm.pattern compiled)
    {context armContext : SourceSemantics.Context} {binders : List TypedBinder} {arity : Nat}
    (signatures : context.signatures = compilation.signatures)
    (typed : TypedMatchPatternHasType context arm.pattern expected binders arity)
    (extended : BindersExtend source.owner context binders armContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations source (armScope scope compiled) armContext := by
  have sameBinders := CompatiblePatternSourceBinders.Certificate.source_binders certificate signatures typed
  apply scope_binders declarations
  · rw [sameBinders]
    exact pattern_declarations found form member typed
  · exact sameBinders.symm ▸ extended

theorem Certificate.hidden_arm_scope
    {compilation : Compilation} {source : TypedSource} {scope : Scope} {site : StatementId}
    {node : StatementNode} {resolution : MatchResolution} {arm : TypedMatchCase}
    {expected : TypeSystem.Ty} {payload : Ty} {compiled : Pattern}
    (found : source.lookupStatement? site = some node)
    (form : node.form = .matchWith resolution) (member : arm ∈ resolution.cases)
    (certificate : CompatiblePatternCertificates.Certificate compilation source
      ((resolution.hiddenScrutinee, payload) :: scope) site arm.span expected arm.pattern compiled)
    {context armContext : SourceSemantics.Context} {binders : List TypedBinder} {arity : Nat}
    (signatures : context.signatures = compilation.signatures)
    (typed : TypedMatchPatternHasType context arm.pattern expected binders arity)
    (extended : BindersExtend source.owner context binders armContext)
    (hidden : resolution.hiddenScrutinee ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id))
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations source
      (armScope ((resolution.hiddenScrutinee, payload) :: scope) compiled) armContext :=
  Certificate.arm_scope found form member certificate signatures typed extended
    (scope_internal payload hidden declarations)

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes

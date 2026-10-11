import Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition
import Solcore.SourceSemantics.Dynamic.LocalSchemes

/-!
A successful concrete scheme matcher determines the action of every exact
semantic instantiation at that same scheme and occurrence type. The proof
retains arbitrary ordering of the semantic substitution. No ordered list
equality, source equality, Dynamic execution law, or read/capture attachment is
assumed. Attaching the two matching inputs to an actual read and live Dynamic
cell remains a separate producer obligation.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableClosedSchemeSubstitutionAgreement
open Frontend SourceInference TypeSystem
open CallableAncestryProfiles.SourceComposition

/-- The matcher only introduces domain keys appearing in its expected type.
Existing keys are retained independently of that occurrence. -/
private theorem matchBody_domain_occurs (quantified : List TypeVarId)
    (expected actual : Ty) {initial final : Substitution}
    (matched : Scheme.matchBody? quantified expected actual initial = some final) :
    ∀ metavariable, metavariable ∈ final.domain →
      metavariable ∈ initial.domain ∨ metavariable ∈ expected.freeVariables := by
  induction expected generalizing actual initial final with
  | «variable» metavariable =>
      simp only [Scheme.matchBody?] at matched
      split at matched
      · split at matched
        · split at matched <;> try contradiction
          cases matched
          exact fun _ member => Or.inl member
        · cases matched
          intro candidate member
          simp only [Substitution.domain, List.map_cons, List.mem_cons] at member
          rcases member with same | member
          · exact Or.inr (by simpa [Ty.freeVariables] using same)
          · exact Or.inl member
      · split at matched <;> try contradiction
        cases matched
        exact fun _ member => Or.inl member
  | parameter | constructor =>
      cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
      split at matched <;> try contradiction
      cases matched
      exact fun _ member => Or.inl member
  | error =>
      cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
      cases matched
      exact fun _ member => Or.inl member
  | application left right ihLeft ihRight
  | function left right ihLeft ihRight
  | product left right ihLeft ihRight
  | mapping left right ihLeft ihRight =>
      cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
      rename_i actualLeft actualRight
      obtain ⟨middle, leftMatched, rightMatched⟩ := Option.bind_eq_some_iff.mp matched
      intro metavariable member
      rcases ihRight actualRight rightMatched metavariable member with middleMember | rightMember
      · rcases ihLeft actualLeft leftMatched metavariable middleMember with initialMember | leftMember
        · exact Or.inl initialMember
        · exact Or.inr (by simp [leftMember])
      · exact Or.inr (by simp [rightMember])
  | proxy inner ih | comptime inner ih =>
      cases actual <;> simp only [Scheme.matchBody?] at matched <;> try contradiction
      rename_i actualInner
      intro metavariable member
      simpa only [Ty.freeVariables] using ih actualInner matched metavariable member

/-- Successful reordering can select every binder only if each has a genuine
assignment in the structural matcher's output. -/
private theorem reorder_domain_covers {matched : Substitution}
    {variables : List TypeVarId} {result : Substitution}
    (accepted : variables.mapM (fun metavariable => do
      pure (metavariable, ← matched.lookup? metavariable)) = some result) :
    ∀ metavariable, metavariable ∈ variables → metavariable ∈ matched.domain := by
  induction variables generalizing result with
  | nil => intro metavariable member; simp at member
  | cons head tail ih =>
      rw [List.mapM_cons] at accepted
      obtain ⟨first, found, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨rest, remainder, _accepted⟩ := Option.bind_eq_some_iff.mp accepted
      cases lookup : matched.lookup? head with
      | none => simp [lookup] at found
      | some replacement =>
          intro metavariable member
          rcases List.mem_cons.mp member with same | member
          · subst metavariable
            exact List.mem_map.mpr
              ⟨(head, replacement), Substitution.lookup?_eq_some_mem lookup, rfl⟩
          · exact ih remainder metavariable member

private theorem quantified_occurs_of_match
    {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (accepted : scheme.matchInstance? actual = some substitution) :
    ∀ metavariable, metavariable ∈ scheme.quantified →
      metavariable ∈ scheme.body.freeVariables := by
  unfold Scheme.matchInstance? at accepted
  cases certified : Scheme.matchInstanceCertificate? scheme actual with
  | none => simp [certified] at accepted
  | some certificate =>
      unfold Scheme.matchInstanceCertificate? at certified
      split at certified <;> try contradiction
      obtain ⟨matched, shape, certified⟩ := Option.bind_eq_some_iff.mp certified
      obtain ⟨reordered, ordering, _certified⟩ := Option.bind_eq_some_iff.mp certified
      intro metavariable quantified
      have inDomain := reorder_domain_covers ordering metavariable quantified
      have occurs := matchBody_domain_occurs scheme.quantified scheme.body actual
        shape metavariable inDomain
      simpa only [Substitution.domain, List.map_nil, List.mem_nil_iff, false_or] using occurs

/-- Complete accepted matching rejects phantom quantified variables. This
coverage comes from the actual matcher, rather than an extra static premise. -/
theorem quantified_occurs_of_closed_match
    {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (accepted : SourceSpecialization.matchClosedSchemeInstance? scheme actual =
      some substitution) :
    ∀ metavariable, metavariable ∈ scheme.quantified →
      metavariable ∈ scheme.body.freeVariables := by
  have concrete := (SourceSpecialization.matchClosedSchemeInstance?_sound accepted).1
  apply quantified_occurs_of_match
  simpa [SourceSpecialization.matchClosedSchemeInstance?, concrete] using accepted

/-- Equality of two substituted copies of one type identifies the variable
replacement actions at every variable which actually occurs in that type. -/
private theorem variable_actions_eq_of_apply_eq {left right : Substitution}
    (type : Ty) (same : left.apply type = right.apply type) :
    ∀ metavariable, metavariable ∈ type.freeVariables →
      left.apply (.variable metavariable) = right.apply (.variable metavariable) := by
  induction type with
  | «variable» candidate =>
      intro metavariable member
      have sameVariable : metavariable = candidate := by
        simpa [Ty.freeVariables] using member
      subst metavariable
      exact same
  | parameter | constructor | error =>
      intro metavariable member
      simp [Ty.freeVariables] at member
  | application leftType rightType ihLeft ihRight
  | function leftType rightType ihLeft ihRight
  | product leftType rightType ihLeft ihRight
  | mapping leftType rightType ihLeft ihRight =>
      injection same with leftSame rightSame
      intro metavariable member
      simp at member
      rcases member with member | member
      · exact ihLeft leftSame metavariable member
      · exact ihRight rightSame metavariable member
  | proxy inner ih | comptime inner ih =>
      injection same with innerSame
      intro metavariable member
      exact ih innerSame metavariable member

private theorem lookup_exists_of_domain {substitution : Substitution}
    {metavariable : TypeVarId} (member : metavariable ∈ substitution.domain) :
    ∃ replacement, substitution.lookup? metavariable = some replacement := by
  cases found : substitution.lookup? metavariable with
  | none =>
      exact False.elim
        (((Substitution.lookup?_eq_none_iff_not_mem_domain substitution metavariable).mp found) member)
  | some replacement => exact ⟨replacement, rfl⟩

/-- The exact semantic substitution and the actual complete matcher have the
same first-match lookup action. Their ordered lists are left independent. -/
theorem lookup_eq_of_closed_match
    {scheme : Scheme} {actual : Ty} {compiled semantic : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? scheme actual =
      some compiled)
    (exact : ExactSubstitution semantic scheme.quantified)
    (result : semantic.apply scheme.body = actual) :
    ∀ metavariable, semantic.lookup? metavariable = compiled.lookup? metavariable := by
  obtain ⟨_concrete, unique, domain, applies⟩ :=
    SourceSpecialization.matchClosedSchemeInstance?_sound matched
  have compiledExact : ExactSubstitution compiled scheme.quantified := {
    variables_nodup := unique
    domain_permutation := by rw [domain]
  }
  have actions := variable_actions_eq_of_apply_eq scheme.body (result.trans applies.symm)
  intro metavariable
  by_cases quantified : metavariable ∈ scheme.quantified
  · obtain ⟨semanticReplacement, semanticLookup⟩ :=
      lookup_exists_of_domain ((exact.mem_domain_iff metavariable).mpr quantified)
    obtain ⟨compiledReplacement, compiledLookup⟩ :=
      lookup_exists_of_domain ((compiledExact.mem_domain_iff metavariable).mpr quantified)
    have replacements : semanticReplacement = compiledReplacement := by
      simpa only [Substitution.apply, semanticLookup, compiledLookup, Option.getD_some] using
        actions metavariable (quantified_occurs_of_closed_match matched metavariable quantified)
    rw [semanticLookup, compiledLookup, replacements]
  · have semanticAbsent : metavariable ∉ semantic.domain := by
      intro member
      exact quantified ((exact.mem_domain_iff metavariable).mp member)
    have compiledAbsent : metavariable ∉ compiled.domain := by
      simpa only [domain] using quantified
    rw [(Substitution.lookup?_eq_none_iff_not_mem_domain semantic metavariable).mpr semanticAbsent,
      (Substitution.lookup?_eq_none_iff_not_mem_domain compiled metavariable).mpr compiledAbsent]

/-- Every type action agrees; source/header/context actions can therefore
transport this lookup agreement through their existing structural operators. -/
theorem apply_eq_of_closed_match
    {scheme : Scheme} {actual : Ty} {compiled semantic : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? scheme actual =
      some compiled)
    (exact : ExactSubstitution semantic scheme.quantified)
    (result : semantic.apply scheme.body = actual) (type : Ty) :
    semantic.apply type = compiled.apply type :=
  apply_lookup_congr (lookup_eq_of_closed_match matched exact result) type

/-- The actual Dynamic instantiation supplies exactness and the instance
equation internally. Only the same scheme and occurrence-type matcher input
is required at this theorem's retained binder/type indices. -/
theorem runtime_instantiation_lookup_eq
    {context : Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {binder : TypedBinder} {actual : Ty} {requirements : List RequirementId}
    {compiled semantic : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? binder.scheme actual =
      some compiled)
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence
      binder actual requirements semantic produced) :
    ∀ metavariable, semantic.lookup? metavariable = compiled.lookup? metavariable :=
  lookup_eq_of_closed_match matched instantiation.exact instantiation.result

end Solcore.SourceSemantics.CoreLowering.CallableClosedSchemeSubstitutionAgreement

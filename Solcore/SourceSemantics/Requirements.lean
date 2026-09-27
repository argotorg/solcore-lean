import Solcore.SourceSemantics.Typing

/-!
Declarative ownership and validity of source obligation identities.

The executable frontend stores solved obligations in a flat ledger and places
stable requirement IDs on expressions, patterns, assignments, and coercion
steps.  This module gives that representation a proof-facing meaning without
performing trait search.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- One solved requirement occurs in the current source ledger at the given
stable identity. -/
def ContainsRequirement (context : Context) (id : RequirementId)
    (requirement : SolvedRequirement) : Prop :=
  requirement ∈ context.solvedRequirements ∧ requirement.id = id

/-- Requirement identities are globally unique within one typed source. -/
def RequirementIdsUnique (context : Context) : Prop :=
  (context.solvedRequirements.map (fun requirement => requirement.id)).Nodup

/-- A stable requirement identity proves one exact normalized predicate. -/
def RequirementProves (context : Context) (id : RequirementId)
    (predicate : ProgramPredicate) : Prop :=
  ∃ requirement,
    ContainsRequirement context id requirement ∧
    requirement.predicate = predicate ∧
    SolvedRequirementValid context requirement

/-- A requirement identity names some independently valid predicate. -/
def RequirementValid (context : Context) (id : RequirementId) : Prop :=
  ∃ predicate, RequirementProves context id predicate

/-- Every attached identity resolves to independently valid evidence. -/
def RequirementIdsValid (context : Context)
    (ids : List RequirementId) : Prop :=
  ∀ id, id ∈ ids → RequirementValid context id

/-- Every semantically required identity is attached at the occurrence. -/
def RequirementIdsIncluded (required attached : List RequirementId) : Prop :=
  ∀ id, id ∈ required → id ∈ attached

/-- Pointwise, source-ordered correspondence between attached identities and
the predicates they prove. -/
inductive RequirementSequenceProves (context : Context) :
    List RequirementId → List ProgramPredicate → Prop where
  | nil : RequirementSequenceProves context [] []
  | cons {id predicate ids predicates}
      (head : RequirementProves context id predicate)
      (tail : RequirementSequenceProves context ids predicates) :
      RequirementSequenceProves context (id :: ids) (predicate :: predicates)

/-- The complete solved-requirement ledger is identity-unique and every entry
has independently valid retained evidence. -/
structure RequirementLedgerWellFormed (context : Context) : Prop where
  idsUnique : RequirementIdsUnique context
  entriesValid :
    ∀ requirement, requirement ∈ context.solvedRequirements →
      SolvedRequirementValid context requirement

namespace RequirementIdsValid

/-- Any sublist of a valid identity inventory is valid, independently of its
ordering or multiplicity. -/
theorem of_subset
    {context : Context} {smaller larger : List RequirementId}
    (included : smaller ⊆ larger)
    (valid : RequirementIdsValid context larger) :
    RequirementIdsValid context smaller := by
  intro id member
  exact valid id (included member)

end RequirementIdsValid

namespace RequirementSequenceProves

theorem length_eq
    {context : Context}
    {ids : List RequirementId}
    {predicates : List ProgramPredicate}
    (proves : RequirementSequenceProves context ids predicates) :
    ids.length = predicates.length := by
  induction proves with
  | nil => rfl
  | cons _ _ induction => simp [induction]

theorem ids_valid
    {context : Context}
    {ids : List RequirementId}
    {predicates : List ProgramPredicate}
    (proves : RequirementSequenceProves context ids predicates) :
    RequirementIdsValid context ids := by
  intro id member
  induction proves with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨_, head⟩
      · exact induction member

theorem head
    {context : Context}
    {id : RequirementId}
    {predicate : ProgramPredicate}
    {ids : List RequirementId}
    {predicates : List ProgramPredicate}
    (proves : RequirementSequenceProves context (id :: ids)
      (predicate :: predicates)) :
    RequirementProves context id predicate := by
  cases proves with
  | cons head _ => exact head

end RequirementSequenceProves

namespace RequirementIdsUnique

private theorem requirementId_beq_iff_eq
    (left right : RequirementId) : (left == right) = true ↔ left = right := by
  rw [show (left == right) = (left.index == right.index) by rfl]
  rw [beq_iff_eq]
  constructor
  · intro indicesEq
    cases left
    cases right
    cases indicesEq
    rfl
  · intro same
    exact congrArg RequirementId.index same

private theorem filter_id_eq_singleton_of_nodup
    {requirements : List SolvedRequirement}
    (unique : (requirements.map fun requirement => requirement.id).Nodup)
    {row : SolvedRequirement} (member : row ∈ requirements) :
    requirements.filter (fun candidate => candidate.id == row.id) = [row] := by
  induction requirements with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases unique with ⟨headFresh, tailUnique⟩
      rcases List.mem_cons.mp member with rfl | tailMember
      · have tailMisses :
            tail.filter (fun candidate => candidate.id == row.id) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro candidate candidateMember
          have idNe : candidate.id ≠ row.id := by
            intro idEq
            apply headFresh
            exact List.mem_map.mpr ⟨candidate, candidateMember, idEq⟩
          intro equal
          exact idNe ((requirementId_beq_iff_eq _ _).mp equal)
        have selfMatches : (row.id == row.id) = true :=
          (requirementId_beq_iff_eq _ _).mpr rfl
        simp [selfMatches, tailMisses]
      · have idNe : head.id ≠ row.id := by
          intro idEq
          apply headFresh
          exact List.mem_map.mpr ⟨row, tailMember, idEq.symm⟩
        have headMisses : (head.id == row.id) = false := by
          apply Bool.eq_false_iff.mpr
          intro equal
          exact idNe ((requirementId_beq_iff_eq _ _).mp equal)
        simp [headMisses, induction tailUnique tailMember]

private theorem entry_unique_of_ids_nodup
    {requirements : List SolvedRequirement}
    (unique : (requirements.map (fun requirement => requirement.id)).Nodup)
    {left right : SolvedRequirement}
    (leftMem : left ∈ requirements)
    (rightMem : right ∈ requirements)
    (id_eq : left.id = right.id) :
    left = right := by
  induction requirements generalizing left right with
  | nil => simp at leftMem
  | cons first rest induction =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases unique with ⟨firstAbsent, restUnique⟩
      simp only [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftMem
      · rcases rightMem with rfl | rightMem
        · rfl
        · exfalso
          apply firstAbsent
          exact List.mem_map.mpr ⟨right, rightMem, id_eq.symm⟩
      · rcases rightMem with rfl | rightMem
        · exfalso
          apply firstAbsent
          exact List.mem_map.mpr ⟨left, leftMem, id_eq⟩
        · exact induction restUnique leftMem rightMem id_eq

/-- Identity uniqueness alone is sufficient to show that two retained rows
selected by the same stable requirement identity are the same row.  Evidence
validity is deliberately absent: scoped local-scheme assumptions still need
this extensional fact even though they are not valid in the declaration's
outer assumption context. -/
theorem contains_unique
    {context : Context}
    (unique : RequirementIdsUnique context)
    {id : RequirementId}
    {left right : SolvedRequirement}
    (leftContains : ContainsRequirement context id left)
    (rightContains : ContainsRequirement context id right) :
    left = right := by
  rcases leftContains with ⟨leftMem, leftId⟩
  rcases rightContains with ⟨rightMem, rightId⟩
  exact entry_unique_of_ids_nodup unique leftMem rightMem
    (leftId.trans rightId.symm)

/-- Filtering an identity-unique ledger by the stable identity of one retained
row returns exactly that row.  Qualified template formation uses this stronger
list equation rather than only existential lookup. -/
theorem filter_id_eq_singleton
    {context : Context}
    (unique : RequirementIdsUnique context)
    {row : SolvedRequirement}
    (member : row ∈ context.solvedRequirements) :
    context.solvedRequirements.filter (fun candidate =>
      candidate.id == row.id) = [row] := by
  exact filter_id_eq_singleton_of_nodup unique member

/-- An identity-unique ledger cannot assign two different predicates to one
stable requirement identity. -/
theorem proves_predicate_eq
    {context : Context}
    (unique : RequirementIdsUnique context)
    {id : RequirementId} {left right : ProgramPredicate}
    (leftProves : RequirementProves context id left)
    (rightProves : RequirementProves context id right) :
    left = right := by
  rcases leftProves with
    ⟨leftRequirement, leftContains, leftPredicate, _⟩
  rcases rightProves with
    ⟨rightRequirement, rightContains, rightPredicate, _⟩
  have requirementEq := unique.contains_unique leftContains rightContains
  subst rightRequirement
  exact leftPredicate.symm.trans rightPredicate

end RequirementIdsUnique

namespace RequirementLedgerWellFormed

theorem contains_unique
    {context : Context}
    (wellFormed : RequirementLedgerWellFormed context)
    {id : RequirementId}
    {left right : SolvedRequirement}
    (leftContains : ContainsRequirement context id left)
    (rightContains : ContainsRequirement context id right) :
    left = right :=
  wellFormed.idsUnique.contains_unique leftContains rightContains

/-- An identity-unique ledger cannot assign two different predicates to the
same retained requirement identity.  This is the bridge used when static
typing and dynamic evidence production independently open the same ledger
entry. -/
theorem proves_predicate_eq
    {context : Context}
    (wellFormed : RequirementLedgerWellFormed context)
    {id : RequirementId} {left right : ProgramPredicate}
    (leftProves : RequirementProves context id left)
    (rightProves : RequirementProves context id right) :
    left = right :=
  wellFormed.idsUnique.proves_predicate_eq leftProves rightProves

/-- Ledger validity is insensitive to lexical locals and rigid-binder
bookkeeping.  It transports across contexts which retain the signature,
assumption, and solved-requirement projections used by the judgment. -/
theorem transport
    {source target : Context}
    (wellFormed : RequirementLedgerWellFormed source)
    (signatures : target.signatures = source.signatures)
    (assumptions : target.assumptions = source.assumptions)
    (requirements : target.solvedRequirements = source.solvedRequirements) :
    RequirementLedgerWellFormed target := by
  constructor
  · simpa [RequirementIdsUnique, requirements] using wellFormed.idsUnique
  · intro requirement member
    have sourceMember : requirement ∈ source.solvedRequirements := by
      simpa [requirements] using member
    cases wellFormed.entriesValid requirement sourceMember with
    | intro evidenceValid =>
        exact .intro (by simpa [signatures, assumptions] using evidenceValid)

end RequirementLedgerWellFormed

end Solcore.SourceSemantics

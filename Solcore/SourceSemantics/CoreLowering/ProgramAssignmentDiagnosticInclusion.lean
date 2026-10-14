import Solcore.Frontend.SourceCoreProgramFaultSites

/-! Actual program collection allocates disjoint assignment and boundary tokens.
Every assignment diagnostic therefore retains its exact first-match identity in
the combined program table. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.ProgramAssignmentDiagnosticInclusion
open Core Frontend SourceInference SourceCoreProgramFaultSites

private theorem word_value {number : Nat} {word : Word}
    (accepted : Word.ofNat? number = some word) : word.val = number := by
  unfold Word.ofNat? at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

private def boundaries (function : Function) : List (Word × SourceCoreFaultSites.Diagnostic) :=
  function.assignments.diagnostics ++ [
    (function.fellThroughReason, {
      error := SourceTypedRuntime.RuntimeError.functionFellThrough function.table.resultType
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none }),
    (function.table.escapedReason, {
      error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
      site := SourceCoreElaboration.ErrorSite.declaration function.table.owner
      span := none })]

private theorem own_ranges {first : Nat} {row : SourceSpecialization.SpecializedFunction} {own : Function}
    (receipt : FunctionIssuance first row own) :
    (∀ pair ∈ boundaries own, first ≤ pair.1.val ∧
      pair.1.val < first + own.table.reads.length + own.assignments.length + 2) ∧
    (∀ left ∈ boundaries own, ∀ right ∈ boundaries own, left.1 = right.1 → left = right) := by
  cases receipt with
  | intro _ _ _ _ assignments fell escaped _ _ _ =>
    obtain ⟨_, assigned, unique⟩ := SourceCoreAssignmentFaultSites.prepare_token_range assignments
    have fellNumber := word_value fell
    have escapedNumber := word_value escaped
    have assignmentUnique : ∀ left ∈ own.assignments.diagnostics,
        ∀ right ∈ own.assignments.diagnostics, left.1 = right.1 → left = right := by
      intro left leftMember right rightMember same
      obtain ⟨a, aMember, rfl⟩ := List.mem_map.mp leftMember
      obtain ⟨b, bMember, rfl⟩ := List.mem_map.mp rightMember
      have equal := unique a aMember b bMember same
      cases equal
      rfl
    constructor
    · intro pair member
      rcases List.mem_append.mp member with member | member
      · have bounds := assigned pair member; exact ⟨by omega, by omega⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> dsimp only <;> omega
    · intro left leftMember right rightMember same
      rcases List.mem_append.mp leftMember with leftMember | leftMember
      · rcases List.mem_append.mp rightMember with rightMember | rightMember
        · exact assignmentUnique left leftMember right rightMember same
        · have bound := assigned left leftMember
          simp only [List.mem_cons, List.not_mem_nil, or_false] at rightMember
          rcases rightMember with rfl | rfl <;>
            have equal := congrArg Fin.val same <;> dsimp only at equal <;> omega
      · rcases List.mem_append.mp rightMember with rightMember | rightMember
        · have bound := assigned right rightMember
          simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember
          rcases leftMember with rfl | rfl <;>
            have equal := congrArg Fin.val same <;> dsimp only at equal <;> omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember rightMember
          rcases leftMember with rfl | rfl <;> rcases rightMember with rfl | rfl
          · rfl
          · have equal := congrArg Fin.val same; dsimp only at equal; omega
          · have equal := congrArg Fin.val same; dsimp only at equal; omega
          · rfl

private theorem inventory {first : Nat} {rows : List SourceSpecialization.SpecializedFunction}
    {functions : List Function} (receipt : ProgramIssuance first rows functions) :
    (∀ pair ∈ functions.flatMap boundaries, first ≤ pair.1.val) ∧
    (∀ left ∈ functions.flatMap boundaries, ∀ right ∈ functions.flatMap boundaries,
      left.1 = right.1 → left = right) := by
  induction receipt with
  | nil => constructor <;> simp
  | @cons first row rows own functions issued remaining ih =>
    obtain ⟨bounds, unique⟩ := own_ranges issued
    constructor
    · intro pair member
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with member | member
      · exact (bounds pair member).1
      · have bound := ih.1 pair member; omega
    · intro left leftMember right rightMember same
      simp only [List.flatMap_cons, List.mem_append] at leftMember rightMember
      rcases leftMember with leftMember | leftMember
      · rcases rightMember with rightMember | rightMember
        · exact unique left leftMember right rightMember same
        · have leftBound := bounds left leftMember
          have rightBound := ih.1 right rightMember
          have equal := congrArg Fin.val same; omega
      · rcases rightMember with rightMember | rightMember
        · have rightBound := bounds right rightMember
          have leftBound := ih.1 left leftMember
          have equal := congrArg Fin.val same; omega
        · exact ih.2 left leftMember right rightMember same

private theorem find_unique {rows : List (Word × SourceCoreFaultSites.Diagnostic)}
    {pair : Word × SourceCoreFaultSites.Diagnostic} (member : pair ∈ rows)
    (unique : ∀ candidate ∈ rows, candidate.1 = pair.1 → candidate = pair) :
    rows.find? (fun candidate => decide (candidate.1 = pair.1)) = some pair := by
  induction rows with
  | nil => simp at member
  | cons head tail ih =>
    by_cases sameKey : head.1 = pair.1
    · have same := unique head List.mem_cons_self sameKey
      simp [same]
    · have tailMember : pair ∈ tail := by
        rcases List.mem_cons.mp member with same | member
        · exact (sameKey (same ▸ rfl)).elim
        · exact member
      simpa only [List.find?_cons, decide_eq_false_iff_not.mpr sameKey,
        Bool.false_eq_true, ↓reduceIte] using
        ih tailMember (fun candidate belongs => unique candidate (List.mem_cons_of_mem head belongs))

/-- The original assignment lookup produces a genuine diagnostic row. -/
theorem assignment_member {table : SourceCoreAssignmentFaultSites.Table}
    {token : Word} {diagnostic : SourceCoreFaultSites.Diagnostic}
    (decoded : table.diagnostic? token = some diagnostic) :
    (token, diagnostic) ∈ table.diagnostics := by
  unfold SourceCoreAssignmentFaultSites.Table.diagnostic? at decoded
  cases found : table.sites.find? (fun site => decide (site.reason = token)) with
  | none => simp only [found, Option.map_none] at decoded; cases decoded
  | some site =>
    simp only [found, Option.map_some, Option.some.injEq] at decoded
    have same := of_decide_eq_true (List.find?_some (p := fun site : SourceCoreAssignmentFaultSites.Site => decide (site.reason = token)) found)
    exact List.mem_map.mpr ⟨site, List.mem_of_find?_eq_some found, by simp only [same, decoded]⟩

/-- Exact program-wide inclusion, including exclusion of the two special
boundary decoder branches. No arbitrary diagnostic-table relation is assumed. -/
theorem prepare_assignment_diagnostic {plan : Plan} {root : Key} {diagnostics : SourceCoreProgramFaultSites.Program}
    (accepted : prepare plan root = .ok diagnostics)
    {own : Function} (member : own ∈ diagnostics.functions)
    {token : Word} {diagnostic : SourceCoreFaultSites.Diagnostic}
    (decoded : own.assignments.diagnostic? token = some diagnostic) :
    token ≠ Word.zero ∧ token ≠ diagnostics.rootTable.escapedReason ∧
    diagnostics.rootTable.additional.find? (fun pair => decide (pair.1 = token)) = some (token, diagnostic) ∧
    diagnostics.rootTable.diagnostic? token = some diagnostic := by
  obtain ⟨selected, collection, selectedFound, table⟩ := prepare_issuance accepted
  have additional : diagnostics.rootTable.additional = diagnostics.functions.flatMap boundaries := congrArg (·.additional) table
  have escaped : diagnostics.rootTable.escapedReason = selected.table.escapedReason := congrArg (·.escapedReason) table
  have actual := assignment_member decoded
  have belongs : (token, diagnostic) ∈ diagnostics.functions.flatMap boundaries :=
    List.mem_flatMap.mpr ⟨own, member, List.mem_append_left _ actual⟩
  have facts := inventory collection
  have positive : token ≠ Word.zero := by
    intro same
    have bound := facts.1 _ belongs
    change 1 ≤ token.val at bound
    have number := congrArg Fin.val same
    change token.val = 0 at number
    omega
  have escapedMember : (selected.table.escapedReason, {
      error := SourceTypedRuntime.RuntimeError.controlEscapedFunction
      site := SourceCoreElaboration.ErrorSite.declaration selected.table.owner
      span := none }) ∈ diagnostics.functions.flatMap boundaries :=
    List.mem_flatMap.mpr ⟨selected, List.mem_of_find?_eq_some selectedFound, by simp [boundaries]⟩
  have ordinary : token ≠ diagnostics.rootTable.escapedReason := by
    intro same
    have equal := facts.2 _ belongs _ escapedMember (same.trans escaped)
    have error := congrArg (fun pair => pair.2.error) equal
    obtain ⟨site, _, row⟩ := List.mem_map.mp actual
    have diag := congrArg Prod.snd row
    rw [← diag] at error
    cases kind : site.kind <;> simp [SourceCoreAssignmentFaultSites.Site.diagnostic, kind] at error
  have found : diagnostics.rootTable.additional.find? (fun pair => decide (pair.1 = token)) = some (token, diagnostic) := by
    rw [additional]
    exact find_unique belongs (fun candidate candidateMember same => facts.2 _ candidateMember _ belongs same)
  refine ⟨positive, ordinary, found, ?_⟩
  simp only [SourceCoreFaultSites.Table.diagnostic?, positive, ordinary, ↓reduceIte, found]

end Solcore.SourceSemantics.CoreLowering.ProgramAssignmentDiagnosticInclusion

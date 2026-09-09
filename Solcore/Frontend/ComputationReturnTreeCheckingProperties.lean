import Solcore.Frontend.ComputationReturnTree
import Solcore.Frontend.WordMatchProperties

/-! Exact optional-match checking preserves original case/default provenance.
No elaboration, typing or runtime law is assumed. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}

private def check_arm (check : Syntax.Block → Option (Core.Expr × Core.Ty))
    (arm : Syntax.MatchCase) : Option (Option Core.Word × (Core.Expr × Core.Ty)) := do
  let tag ← interpretWordMatchPattern? arm.value.pattern
  let branch ← check arm.value.body
  return (tag, branch)

private theorem check_arm_map {check : Syntax.Block → Option (Core.Expr × Core.Ty)}
    {arm : Syntax.MatchCase} :
    (check_arm check arm).map (arm, ·) = (do
      let tag ← interpretWordMatchPattern? arm.value.pattern
      let branch ← check arm.value.body
      return (arm, tag, branch)) := by
  simp [check_arm, bind, Option.map_bind, Function.comp_def]

private theorem check_arm_iff {check : Syntax.Block → Option (Core.Expr × Core.Ty)}
    {type : Core.Ty} {arm : Syntax.MatchCase} {tag : Option Core.Word} {core : Core.Expr} :
    check_arm check arm = some (tag, core, type) ↔
      WordMatchPatternClassifies arm.value.pattern tag ∧ check arm.value.body = some (core, type) := by
  simp [check_arm, bind, Option.bind_eq_some_iff, Prod.mk.injEq, interpretWordMatchPattern?_iff]

private theorem entries_check_iff {α β : Type} {check : α → Option β}
    {cases : List α} {entries : List (α × β)} :
    cases.attach.mapM (fun arm => (check arm.val).map (arm.val, ·)) = some entries ↔
      entries.map Prod.fst = cases ∧ ∀ entry ∈ entries, check entry.1 = some entry.2 := by
  change cases.attach.mapM ((fun arm => (check arm).map (arm, ·)) ∘ Subtype.val) = some entries ↔ _
  rw [← List.mapM_map, List.attach_map_subtype_val]
  induction cases generalizing entries with
  | nil => cases entries <;> simp
  | cons arm rest ih =>
      cases entries with
      | nil => simp [List.mapM_cons, bind, Option.bind_eq_some_iff]
      | cons entry entries =>
          simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.map_eq_some_iff,
            pure, Option.some.injEq, List.cons.injEq, List.map_cons,
            List.mem_cons, forall_eq_or_imp, ih]
          constructor
          · rintro ⟨_, ⟨value, accepted, rfl⟩, _, ⟨ordered, checked⟩, rfl, rfl⟩
            exact ⟨⟨rfl, ordered⟩, accepted, checked⟩
          · rintro ⟨⟨rfl, ordered⟩, accepted, checked⟩
            exact ⟨entry, ⟨entry.2, accepted, by cases entry; rfl⟩, entries,
              ⟨ordered, checked⟩, rfl, rfl⟩

private def check_default (check : Syntax.Block → Option (Core.Expr × Core.Ty)) (source : Option Syntax.Block) :=
  source.mapM (fun body => (check body).map (body, ·))

private theorem check_default_iff {check : Syntax.Block → Option (Core.Expr × Core.Ty)}
    {source : Option Syntax.Block} {checked : Option (Syntax.Block × (Core.Expr × Core.Ty))} :
    check_default check source = some checked ↔ checked.map Prod.fst = source ∧
      ∀ entry ∈ checked.toList, check entry.1 = some entry.2 := by
  cases source <;> cases checked <;> simp [check_default, Option.map_eq_some_iff]
  constructor
  · rintro ⟨_, _, found, rfl⟩; exact ⟨rfl, found⟩
  · rintro ⟨rfl, found⟩; exact ⟨_, _, found, by rfl⟩

private def anchor (defaultChecked : Option (Syntax.Block × (Core.Expr × Core.Ty)))
    (checked : List (Syntax.MatchCase × (Option Core.Word × (Core.Expr × Core.Ty)))) : Option Core.Ty :=
  match defaultChecked with | some entry => some entry.2.2 | none => checked.head?.map (fun entry => entry.2.2.2)

private def check_match (check : Syntax.Block → Option (Core.Expr × Core.Ty)) (scrutineeCore : Core.Expr)
    (scrutineeType : Core.Ty) (cases : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) : Option (Core.Expr × Core.Ty) := do
  let defaultChecked ← check_default check defaultBody
  let checked ← cases.attach.mapM (fun arm => (check_arm check arm.val).map (arm.val, ·))
  if scrutineeType = .word ∨ checked.all (fun entry => entry.2.1.isNone) = true then do
    let type ← anchor defaultChecked checked
    if checked.all (fun entry => entry.2.2.2 == type) then do
      let core ← (checked.map (fun entry => (entry.1, entry.2.1, entry.2.2.1))).foldr
        (fun entry tail => match entry.2.1 with
          | none => some (entry.2.2.weakenAt 0)
          | some word => tail.map (fun core => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) core))
        ((defaultChecked.map (fun entry => (entry.1, entry.2.1))).map (fun entry => entry.2.weakenAt 0))
      return (.letE scrutineeCore core, type)
    else none
  else none

private theorem type_beq (left right : Core.Ty) : (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Core.instBEqTy.beq, Core.instBEqDataTypeId.beq]
  rename_i left right
  cases left; cases right; simp_all

private theorem check_match_iff {check : Syntax.Block → Option (Core.Expr × Core.Ty)}
    {scrutineeCore core : Core.Expr} {scrutineeType type : Core.Ty} {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block} :
    check_match check scrutineeCore scrutineeType cases defaultBody = some (core, type) ↔
    ∃ (bodyCore : Core.Expr) (entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)))
      (defaultEntry : Option (Syntax.Block × Core.Expr)), entries.map Prod.fst = cases ∧
      (∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1) ∧
      (scrutineeType = .word ∨ ∀ entry ∈ entries, entry.2.1 = none) ∧
      (∀ entry ∈ entries, check entry.1.value.body = some (entry.2.2, type)) ∧
      defaultEntry.map Prod.fst = defaultBody ∧ (∀ entry ∈ defaultEntry.toList, check entry.1 = some (entry.2, type)) ∧
      entries.foldr (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map (fun core => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) core))
        (defaultEntry.map (fun entry => entry.2.weakenAt 0)) = some bodyCore ∧ core = .letE scrutineeCore bodyCore := by
  simp only [check_match, bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨defaults, defaultChecked, checked, entriesChecked, accepted⟩
    split at accepted
    next compatible =>
      simp only [Option.bind_eq_some_iff] at accepted
      obtain ⟨actualType, anchored, accepted⟩ := accepted
      split at accepted
      next sameTypes =>
        simp only [Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at accepted
        obtain ⟨bodyCore, lowered, rfl, rfl⟩ := accepted
        have ds := check_default_iff.mp defaultChecked
        have cs := entries_check_iff.mp entriesChecked
        refine ⟨bodyCore, checked.map (fun e => (e.1, e.2.1, e.2.2.1)),
          defaults.map (fun e => (e.1, e.2.1)), ?_, ?_, ?_, ?_, ?_, ?_, lowered, rfl⟩
        · simpa only [List.map_map, Function.comp_def] using cs.1
        · intro entry member; obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
          exact (check_arm_iff.mp (cs.2 row rowMember)).1
        · rcases compatible with word | allNone
          · exact .inl word
          · right; intro entry member
            obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
            exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp allNone row rowMember)
        · intro entry member; obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
          have same : row.2.2.2 = actualType := type_beq _ _ |>.mp (List.all_eq_true.mp sameTypes row rowMember)
          simpa only [same] using (check_arm_iff.mp (cs.2 row rowMember)).2
        · simpa only [Option.map_map, Function.comp_def] using ds.1
        · intro entry member
          rw [Option.toList_map] at member
          obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
          have source := Option.mem_toList.mp rowMember
          have same : row.2.2 = actualType := by simpa only [anchor, source, Option.some.injEq] using anchored
          have found := ds.2 row rowMember
          change check row.1 = some (row.2.1, row.2.2) at found
          simpa only [same] using found
      next different => cases accepted
    next incompatible => cases accepted
  · rintro ⟨bodyCore, entries, defaults, ordered, patterns, compatible, branches, defaultOrdered, defaultBranches, lowered, rfl⟩
    let ds := defaults.map (fun e => (e.1, e.2, type))
    let cs := entries.map (fun e => (e.1, e.2.1, e.2.2, type))
    refine ⟨ds, check_default_iff.mpr ⟨?_, ?_⟩, cs, entries_check_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa only [ds, Option.map_map, Function.comp_def] using defaultOrdered
    · intro entry member
      rw [Option.toList_map] at member
      obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
      exact defaultBranches row rowMember
    · simpa only [cs, List.map_map, Function.comp_def] using ordered
    · intro entry member; obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
      exact check_arm_iff.mpr ⟨patterns row rowMember, branches row rowMember⟩
    · have compatibleChecked : scrutineeType = .word ∨ cs.all (fun entry => entry.2.1.isNone) = true := by
        rcases compatible with word | allNone
        · exact .inl word
        · right; simpa only [cs, List.all_map, Function.comp_def, List.all_eq_true, Option.isNone_iff_eq_none] using allNone
      rw [if_pos compatibleChecked]
      simp only [Option.bind_eq_some_iff]
      refine ⟨type, ?_, ?_⟩
      · cases defaults with
        | some entry => rfl
        | none => cases entries with
          | nil => simp at lowered
          | cons entry rest => rfl
      · have same : cs.all (fun e => e.2.2.2 == type) = true := by simp [cs, type_beq]
        simp only [same, ite_true, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq]
        refine ⟨bodyCore, ?_, rfl, True.intro⟩
        simp only [cs, ds, List.map_map, Option.map_map, Function.comp_def]
        change (entries.map id).foldr _ _ = some bodyCore
        simpa only [List.map_id] using lowered

/-- Exact checker decomposition of one original optional-default terminal match. -/
theorem ComputationReturnTreeChecking.match_iff
    {blockSpan matchSpan scrutineeSpan armsSpan : Syntax.SourceSpan}
    {scrutinee : Syntax.Expr} {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
    {core : Core.Expr} {type : Core.Ty} :
    elaborateComputationReturnTree? checkChild types owner inputs
      ⟨blockSpan, [⟨matchSpan, .matchWith ⟨scrutineeSpan, ⟨scrutinee, []⟩⟩ ⟨armsSpan, ⟨cases, defaultBody⟩⟩⟩]⟩ =
        some (core, type) ↔
    ∃ scrutineeCore scrutineeType, checkChild inputs.names inputs.context scrutinee = some (scrutineeCore, scrutineeType) ∧
    ∃ (bodyCore : Core.Expr) (entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)))
      (defaultEntry : Option (Syntax.Block × Core.Expr)), entries.map Prod.fst = cases ∧
      (∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1) ∧
      (scrutineeType = .word ∨ ∀ entry ∈ entries, entry.2.1 = none) ∧
      (∀ entry ∈ entries, elaborateComputationReturnTree? checkChild types owner inputs entry.1.value.body =
        some (entry.2.2, type)) ∧ defaultEntry.map Prod.fst = defaultBody ∧
      (∀ entry ∈ defaultEntry.toList, elaborateComputationReturnTree? checkChild types owner inputs entry.1 =
        some (entry.2, type)) ∧
      entries.foldr (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map (fun core => .ifE (.binary .wordEq (.var 0) (.word word))
          (entry.2.2.weakenAt 0) core))
        (defaultEntry.map (fun entry => entry.2.weakenAt 0)) = some bodyCore ∧ core = .letE scrutineeCore bodyCore := by
  rw [elaborateComputationReturnTree?]
  constructor
  · intro accepted
    simp only [bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨⟨scrutineeCore, scrutineeType⟩, scrutineeAccepted, remaining⟩ := accepted
    refine ⟨scrutineeCore, scrutineeType, scrutineeAccepted, check_match_iff.mp ?_⟩
    simp only [check_match, check_arm_map]
    cases defaultBody <;>
      simp [check_default, anchor, bind, Option.mapM, Option.map_eq_bind, Option.bind_assoc] at remaining ⊢
    all_goals refine Eq.trans ?_ remaining
    all_goals congr 3
  · rintro ⟨scrutineeCore, scrutineeType, scrutineeAccepted, rest⟩
    simp only [scrutineeAccepted, bind, Option.bind_some]
    have checked := (check_match_iff (scrutineeCore := scrutineeCore) (scrutineeType := scrutineeType)).mpr rest
    simp only [check_match, check_arm_map] at checked
    cases defaultBody <;>
      simp [check_default, anchor, bind, Option.mapM, Option.map_eq_bind, Option.bind_assoc] at checked ⊢
    all_goals refine Eq.trans ?_ checked
    all_goals congr 3

end Solcore.Frontend

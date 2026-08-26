import Solcore.Surface.Multi.StructureJudgment
import Solcore.Surface.Multi.Structure

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

namespace Structure

/-- A selected occurrence either repeats a key from `seen` or from its prefix. -/
private def SeenLaterDuplicate {α κ : Type}
    (seen : List κ) (key : α → κ) (later : α) : List α → Prop
  | [] => False
  | head :: tail =>
      (head = later ∧ key head ∈ seen) ∨
        SeenLaterDuplicate (key head :: seen) key later tail

private theorem seenLaterDuplicate_iff {α κ : Type}
    {seen : List κ} {key : α → κ} {later : α} {values : List α} :
    SeenLaterDuplicate seen key later values ↔
      (later ∈ values ∧ key later ∈ seen) ∨
        LaterDuplicate values key later := by
  induction values generalizing seen with
  | nil => simp [SeenLaterDuplicate, LaterDuplicate]
  | cons head tail induction =>
      constructor
      · intro selected
        rcases selected with headSelected | tailSelected
        · rcases headSelected with ⟨headEq, keyMember⟩
          subst head
          exact Or.inl ⟨by simp, keyMember⟩
        · rcases (induction (seen := key head :: seen)).mp tailSelected with
            prior | duplicate
          · rcases prior with ⟨member, keyMember⟩
            rcases List.mem_cons.mp keyMember with headKey | seenKey
            · apply Or.inr
              exact LaterDuplicate.of_head member rfl headKey.symm
            · exact Or.inl ⟨List.mem_cons_of_mem head member, seenKey⟩
          · exact Or.inr (LaterDuplicate.of_tail duplicate)
      · intro selected
        rcases selected with prior | duplicate
        · rcases prior with ⟨member, keyMember⟩
          rcases List.mem_cons.mp member with headEq | tailMember
          · subst head
            exact Or.inl ⟨rfl, keyMember⟩
          · apply Or.inr
            apply (induction (seen := key head :: seen)).mpr
            exact Or.inl ⟨tailMember,
              List.mem_cons_of_mem (key head) keyMember⟩
        · rcases (laterDuplicate_cons_iff head tail key later).mp duplicate with
            tailDuplicate | headDuplicate
          · apply Or.inr
            exact (induction (seen := key head :: seen)).mpr
              (Or.inr tailDuplicate)
          · rcases headDuplicate with
              ⟨candidate, member, candidateEq, keyEq⟩
            subst candidate
            apply Or.inr
            apply (induction (seen := key head :: seen)).mpr
            exact Or.inl ⟨member, List.mem_cons.mpr (Or.inl keyEq.symm)⟩

private theorem mem_duplicateDiagnostics_go_iff {α κ : Type}
    [DecidableEq κ]
    {seen : List κ} {key : α → κ}
    {makeDiagnostic : α → StructuralDiagnostic}
    {values : List α} {diagnostic : StructuralDiagnostic} :
    diagnostic ∈
        duplicateDiagnostics.go key makeDiagnostic seen values ↔
      ∃ value,
        SeenLaterDuplicate seen key value values ∧
          makeDiagnostic value = diagnostic := by
  induction values generalizing seen with
  | nil => simp [duplicateDiagnostics.go, SeenLaterDuplicate]
  | cons head tail induction =>
      by_cases repeated : key head ∈ seen
      · rw [duplicateDiagnostics.go.eq_2, if_pos repeated]
        constructor
        · intro member
          rcases List.mem_cons.mp member with headMember | tailMember
          · exact ⟨head, Or.inl ⟨rfl, repeated⟩, headMember.symm⟩
          · rcases (induction (seen := key head :: seen)).mp tailMember with
              ⟨value, selected, equality⟩
            exact ⟨value, Or.inr selected, equality⟩
        · rintro ⟨value, selected, equality⟩
          rcases selected with headSelected | tailSelected
          · rcases headSelected with ⟨headEq, _⟩
            subst value
            exact List.mem_cons.mpr (Or.inl equality.symm)
          · apply List.mem_cons.mpr
            apply Or.inr
            exact (induction (seen := key head :: seen)).mpr
              ⟨value, tailSelected, equality⟩
      · rw [duplicateDiagnostics.go.eq_2, if_neg repeated]
        constructor
        · intro tailMember
          rcases (induction (seen := key head :: seen)).mp tailMember with
            ⟨value, selected, equality⟩
          exact ⟨value, Or.inr selected, equality⟩
        · rintro ⟨value, selected, equality⟩
          rcases selected with headSelected | tailSelected
          · exact False.elim (repeated headSelected.2)
          · exact (induction (seen := key head :: seen)).mpr
              ⟨value, tailSelected, equality⟩

/-- The duplicate collector emits exactly diagnostics for later equal keys. -/
theorem mem_duplicateDiagnostics_iff_laterDuplicate {α κ : Type}
    [DecidableEq κ]
    {key : α → κ} {makeDiagnostic : α → StructuralDiagnostic}
    {values : List α} {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ duplicateDiagnostics key makeDiagnostic values ↔
      ∃ value,
        LaterDuplicate values key value ∧
          makeDiagnostic value = diagnostic := by
  change diagnostic ∈
      duplicateDiagnostics.go key makeDiagnostic [] values ↔ _
  rw [mem_duplicateDiagnostics_go_iff]
  constructor
  · rintro ⟨value, selected, equality⟩
    have duplicate : LaterDuplicate values key value := by
      rcases (seenLaterDuplicate_iff.mp selected) with prior | duplicate
      · simp at prior
      · exact duplicate
    exact ⟨value, duplicate, equality⟩
  · rintro ⟨value, duplicate, equality⟩
    exact ⟨value, seenLaterDuplicate_iff.mpr (Or.inr duplicate), equality⟩

/-- The executable span comparison is the independent strict span order. -/
@[simp] theorem sourceSpanBefore_eq_true_iff
    (left right : SourceSpan) :
    sourceSpanBefore left right = true ↔ SpanBefore left right := by
  cases ordering : SourceId.compare left.source right.source with
  | lt => simp [sourceSpanBefore, SpanBefore, ordering]
  | eq =>
      have sourceEq : left.source = right.source :=
        SourceId.compare_eq_iff_eq.mp ordering
      have selfOrdering :
          SourceId.compare right.source right.source = .eq :=
        Std.ReflCmp.compare_self
      simp [sourceSpanBefore, SpanBefore, sourceEq, selfOrdering]
      by_cases startBefore : left.startByte < right.startByte
      · simp [startBefore]
      · have rightLeLeft : right.startByte ≤ left.startByte :=
          Nat.le_of_not_gt startBefore
        simp only [startBefore, false_or]
        constructor
        · rintro ⟨leftLeRight, endBefore⟩
          exact ⟨Nat.le_antisymm leftLeRight rightLeLeft, endBefore⟩
        · rintro ⟨startEq, endBefore⟩
          exact ⟨Nat.le_of_eq startEq, endBefore⟩
  | gt =>
      have sourceNe : left.source ≠ right.source := by
        intro sourceEq
        have equalOrdering :
            SourceId.compare left.source right.source = .eq :=
          SourceId.compare_eq_iff_eq.mpr sourceEq
        rw [ordering] at equalOrdering
        contradiction
      simp [sourceSpanBefore, SpanBefore, ordering, sourceNe]

private theorem span_eq_of_not_before_not_before
    {left right : SourceSpan}
    (notForward : ¬SpanBefore left right)
    (notBackward : ¬SpanBefore right left) :
    left = right := by
  have sourceEq : left.source = right.source := by
    cases ordering : SourceId.compare left.source right.source with
    | lt => exact False.elim (notForward (SpanBefore.of_source ordering))
    | eq => exact SourceId.compare_eq_iff_eq.mp ordering
    | gt =>
        have reverse : SourceId.compare right.source left.source = .lt :=
          Std.OrientedCmp.lt_of_gt (cmp := SourceId.compare) ordering
        exact False.elim (notBackward (SpanBefore.of_source reverse))
  have startEq : left.startByte = right.startByte := by
    rcases Nat.lt_trichotomy left.startByte right.startByte with
        forward | equal | backward
    · exact False.elim
        (notForward (SpanBefore.of_start sourceEq forward))
    · exact equal
    · exact False.elim
        (notBackward (SpanBefore.of_start sourceEq.symm backward))
  have endEq : left.endByte = right.endByte := by
    rcases Nat.lt_trichotomy left.endByte right.endByte with
        forward | equal | backward
    · exact False.elim
        (notForward (SpanBefore.of_end sourceEq startEq forward))
    · exact equal
    · exact False.elim
        (notBackward
          (SpanBefore.of_end sourceEq.symm startEq.symm backward))
  cases left
  cases right
  simp_all

private theorem leastSpanIn_unique
    {left right : SourceSpan} {spans : List SourceSpan}
    (leftLeast : LeastSpanIn left spans)
    (rightLeast : LeastSpanIn right spans) :
    left = right := by
  apply span_eq_of_not_before_not_before
  · exact rightLeast.not_before leftLeast.member
  · exact leftLeast.not_before rightLeast.member

private def leastSourceSpanStep
    (least candidate : SourceSpan) : SourceSpan :=
  if sourceSpanBefore candidate least then candidate else least

private theorem leastSpanIn_append_step
    {least : SourceSpan} {spans : List SourceSpan}
    (leastProof : LeastSpanIn least spans)
    (candidate : SourceSpan) :
    LeastSpanIn (leastSourceSpanStep least candidate)
      (spans ++ [candidate]) := by
  by_cases candidateBefore : sourceSpanBefore candidate least = true
  · have candidateBeforeProof : SpanBefore candidate least :=
      (sourceSpanBefore_eq_true_iff candidate least).mp candidateBefore
    simp only [leastSourceSpanStep, candidateBefore, if_true]
    constructor
    · simp
    · rw [noSpanBefore_iff]
      intro current member currentBefore
      rcases List.mem_append.mp member with oldMember | candidateMember
      · exact leastProof.not_before oldMember
          (SpanBefore.trans currentBefore candidateBeforeProof)
      · have currentEq : current = candidate := by
          simpa using candidateMember
        subst current
        exact spanBefore_self candidate currentBefore
  · have candidateNotBefore : ¬SpanBefore candidate least := by
      intro beforeProof
      exact candidateBefore
        ((sourceSpanBefore_eq_true_iff candidate least).mpr beforeProof)
    simp only [leastSourceSpanStep, candidateBefore]
    constructor
    · exact List.mem_append.mpr (Or.inl leastProof.member)
    · rw [noSpanBefore_iff]
      intro current member
      rcases List.mem_append.mp member with oldMember | candidateMember
      · exact leastProof.not_before oldMember
      · have currentEq : current = candidate := by
          simpa using candidateMember
        subst current
        exact candidateNotBefore

private theorem foldl_leastSourceSpanStep
    {least : SourceSpan} {spans : List SourceSpan}
    (leastProof : LeastSpanIn least spans)
    (remaining : List SourceSpan) :
    LeastSpanIn (remaining.foldl leastSourceSpanStep least)
      (spans ++ remaining) := by
  induction remaining generalizing least spans with
  | nil => simpa using leastProof
  | cons candidate rest induction =>
      simp only [List.foldl_cons]
      have nextLeast := leastSpanIn_append_step leastProof candidate
      have finalLeast := induction nextLeast
      simpa [List.append_assoc] using finalLeast

/-- The executable fold returns exactly the declaratively least listed span. -/
theorem leastSourceSpan?_eq_some_iff
    {spans : List SourceSpan} {span : SourceSpan} :
    leastSourceSpan? spans = some span ↔ LeastSpanIn span spans := by
  cases spans with
  | nil => simp [leastSourceSpan?, LeastSpanIn]
  | cons first rest =>
      have firstLeast : LeastSpanIn first [first] :=
        leastSpanIn_singleton first
      have computedLeast :
          LeastSpanIn (rest.foldl leastSourceSpanStep first)
            (first :: rest) := by
        have folded := foldl_leastSourceSpanStep firstLeast rest
        simpa using folded
      change some (rest.foldl leastSourceSpanStep first) = some span ↔ _
      constructor
      · intro selected
        have selectedEq : rest.foldl leastSourceSpanStep first = span :=
          Option.some.inj selected
        simpa [selectedEq] using computedLeast
      · intro spanLeast
        exact congrArg some (leastSpanIn_unique computedLeast spanLeast)

end Structure

end Solcore.Surface.Multi

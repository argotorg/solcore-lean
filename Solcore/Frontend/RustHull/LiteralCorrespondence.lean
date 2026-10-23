import Solcore.Frontend.RustHull.SemanticsTypeCorrespondence

/-! Literal parsing agrees with the independent Hull parser, including large
decimal and hexadecimal words reduced modulo 2^256. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Correspondence

private theorem foldlM_some_of_ok {α β : Type}
    (step : β → α → LowerM β) (sourceStep : β → α → Option β)
    (agrees : ∀ state item next, step state item = .ok next → sourceStep state item = some next)
    (items : List α) {initial result : β}
    (accepted : items.foldlM step initial = .ok result) :
    items.foldlM sourceStep initial = some result := by
  induction items generalizing initial with
  | nil => cases accepted; rfl
  | cons item items ih =>
      simp only [List.foldlM_cons] at accepted ⊢
      obtain ⟨next, first, rest⟩ := lower_bind_eq_ok.mp accepted
      rw [agrees initial item next first]
      exact ih rest

private def digitValue (base : Nat) (char : Char) : Nat :=
  if '0' ≤ char && char ≤ '9' then char.toNat - '0'.toNat
  else if 'a' ≤ char && char ≤ 'f' then char.toNat - 'a'.toNat + 10
  else if 'A' ≤ char && char ≤ 'F' then char.toNat - 'A'.toNat + 10
  else base

private theorem digits_some_of_ok {base initial result : Nat} {digits : List Char} {text : String}
    (accepted : digits.foldlM (fun accumulator char =>
      if digitValue base char < base then
        pure ((accumulator * base + digitValue base char) % Core.wordModulus)
      else fail s!"invalid word literal: {text}") initial = .ok result) :
    digits.foldlM (fun accumulator char =>
      if digitValue base char < base then
        some ((accumulator * base + digitValue base char) % Core.wordModulus)
      else none) initial = some result := by
  apply foldlM_some_of_ok _ _ _ digits accepted
  intro state char next step
  by_cases valid : digitValue base char < base
  · rw [if_pos valid] at step ⊢
    cases step
    rfl
  · simp [valid, fail] at step

theorem parseWord_some_of_ok {text : String} {value : Core.Word}
    (accepted : parseWord text = .ok value) :
    Semantics.parseWord? text = some value := by
  unfold parseWord at accepted
  unfold Semantics.parseWord?
  dsimp only at accepted ⊢
  split at accepted <;> simp_all only
  all_goals
    split at accepted
    · simp [fail] at accepted
    · rename_i nonempty
      rw [if_neg nonempty]
      obtain ⟨number, parsed, returned⟩ := lower_bind_eq_ok.mp accepted
      cases returned
      have converted := digits_some_of_ok parsed
      exact congrArg (fun parsed : Option Nat =>
        parsed.bind fun value => some (Core.Word.ofNatModulo value)) converted

end Solcore.Frontend.RustHull.Correspondence

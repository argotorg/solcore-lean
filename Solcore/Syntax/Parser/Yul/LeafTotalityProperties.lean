import Solcore.Syntax.Parser.PrimitiveTotalityProperties
import Solcore.Syntax.Parser.Yul.ExpressionProperties

/-! Totality contracts for non-recursive inline-Yul leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem yulName_ordinary : Parser.Ordinary yulName := by
  intro input
  cases result : yulName input with
  | ok name next => exact Or.inl ⟨name, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold yulName at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          rcases token with ⟨span, kind⟩
          cases kind <;> simp only [found] at result
          all_goals try { unfold rejectAt at result; contradiction }
          case identifier text =>
            exact False.elim
              ((identifier_ordinary .yulExpression).ne_invariant
                input error result)
          case yulIdentifier text => contradiction
          case keyword keyword =>
            cases keyword <;> simp only at result
            all_goals try { unfold rejectAt at result; contradiction }
            case fallbackKw => contradiction
          case symbol symbol =>
            cases symbol <;> simp only at result
            all_goals try { unfold rejectAt at result; contradiction }
            case underscore => contradiction

theorem yulLiteral_ordinary : Parser.Ordinary yulLiteral := by
  intro input
  cases result : yulLiteral input with
  | ok literal next => exact Or.inl ⟨literal, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold yulLiteral at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          rcases token with ⟨span, kind⟩
          cases kind <;> simp [found, rejectAt] at result
          case keyword keyword =>
            cases keyword <;> simp only at result
            all_goals try { unfold rejectAt at result; contradiction }
            all_goals contradiction

theorem rejectedMeta_ordinary : Parser.Ordinary rejectedMeta := by
  intro input
  cases result : rejectedMeta input with
  | ok expression next => exact Or.inl ⟨expression, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold rejectedMeta at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          rcases token with ⟨span, kind⟩
          cases kind <;> simp [found, rejectAt] at result

theorem yulName_cursor_lt_onSuccess {input next : State}
    {name : YulIdentifier} (parsed : yulName input = .ok name next) :
    input.cursor < next.cursor := by
  rw [(yulName_ok_state_shape parsed).choose_spec.2.2.2]
  omega

theorem yulLiteral_cursor_lt_onSuccess {input next : State}
    {literal : YulLiteral} (parsed : yulLiteral input = .ok literal next) :
    input.cursor < next.cursor := by
  rw [yulLiteral_ok_state_shape parsed]
  simp

theorem yulName_elementTotalityContract :
    ElementTotalityContract yulName := {
  validFor := yulName_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := yulName_preservesTokenWindow
  cursorLtOnSuccess := yulName_cursor_lt_onSuccess
  invariantFree := fun input _ error =>
    yulName_ordinary.ne_invariant input error
}

theorem yulLiteral_elementTotalityContract :
    ElementTotalityContract yulLiteral := {
  validFor := yulLiteral_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := yulLiteral_preservesTokenWindow
  cursorLtOnSuccess := yulLiteral_cursor_lt_onSuccess
  invariantFree := fun input _ error =>
    yulLiteral_ordinary.ne_invariant input error
}

theorem rejectedMeta_elementTotalityContract :
    ElementTotalityContract rejectedMeta := {
  validFor := rejectedMeta_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := rejectedMeta_preservesTokenWindow
  cursorLtOnSuccess := rejectedMeta_cursor_lt_onSuccess
  invariantFree := fun input _ error =>
    rejectedMeta_ordinary.ne_invariant input error
}

end Solcore.Syntax.Parser

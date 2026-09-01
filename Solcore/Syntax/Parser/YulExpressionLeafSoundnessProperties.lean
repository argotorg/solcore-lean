import Solcore.Syntax.DeclarativeYulExpressionLeafGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Yul.LeafProperties

/-!
Diagnostic reflection and exact declarative soundness for inline-Yul leaves.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Yul-name success never removes an earlier diagnostic. -/
theorem yulName_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulName := by
  intro input name next result diagnosticFree
  unfold yulName at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text =>
        exact identifier_reflectsDiagnosticFreeOnSuccess .yulExpression input
          name next result diagnosticFree
      case yulIdentifier text =>
        cases result
        exact diagnosticFree
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case fallbackKw =>
          cases result
          exact diagnosticFree
      case symbol symbol =>
        cases symbol <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case underscore =>
          cases result
          exact diagnosticFree

/-- Yul-literal success never removes an earlier diagnostic. -/
theorem yulLiteral_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulLiteral := by
  intro input literal next result diagnosticFree
  rw [yulLiteral_ok_state_shape result] at diagnosticFree
  exact diagnosticFree

/-- Every diagnostic-free successful Yul name follows the strict leaf grammar.

The diagnostic-free premise rules out the checked ordinary-identifier branch
whose spelling contains `-`.
-/
theorem yulName_success_sound_of_diagnosticFree {input next : State}
    {name : YulIdentifier} (diagnosticFree : next.diagnosticsRev = [])
    (result : yulName input = .ok name next) :
    DeclarativeGrammar.YulNameParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold yulName at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text =>
        have parsed := identifier_success_sound .yulExpression result
        unfold identifier at result
        cases rawResult : rawIdentifier .yulExpression input with
        | invariant error => simp [rawResult] at result
        | reject failure rejected => simp [rawResult] at result
        | ok parsedName afterName =>
            simp only [rawResult] at result
            split at result
            · cases result
              simp [State.emit] at diagnosticFree
            · have hyphenAbsent :
                  parsedName.value.toList.contains '-' = false :=
                Bool.eq_false_iff.mpr (by assumption)
              cases result
              exact .identifier hyphenAbsent parsed
      case yulIdentifier text =>
        cases result
        exact .marked (tokenAt_of_peek?_eq_some found)
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case fallbackKw =>
          cases result
          exact .fallbackKeyword (tokenAt_of_peek?_eq_some found)
      case symbol symbol =>
        cases symbol <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case underscore =>
          cases result
          exact .underscore (tokenAt_of_peek?_eq_some found)

/-- Every successful Yul literal is exactly its current literal token. -/
theorem yulLiteral_success_sound {input next : State}
    {literal : YulLiteral}
    (result : yulLiteral input = .ok literal next) :
    DeclarativeGrammar.YulLiteralParses input.declarativeRemainder literal
      next.declarativeRemainder := by
  unfold yulLiteral at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case decimalLiteral spelling =>
        cases result
        exact .decimal (tokenAt_of_peek?_eq_some found)
      case hexadecimalLiteral spelling =>
        cases result
        exact .hexadecimal (tokenAt_of_peek?_eq_some found)
      case stringLiteral spelling =>
        cases result
        exact .string (tokenAt_of_peek?_eq_some found)
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case trueKw =>
          cases result
          exact .trueKeyword (tokenAt_of_peek?_eq_some found)
        case falseKw =>
          cases result
          exact .falseKeyword (tokenAt_of_peek?_eq_some found)

/-- Strict Yul-name grammar soundness composes with source provenance. -/
theorem yulName_success_sound_and_validFor {input next : State}
    {name : YulIdentifier} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : yulName input = .ok name next) :
    DeclarativeGrammar.YulNameParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      Located.ValidFor input.file name := by
  refine ⟨yulName_success_sound_of_diagnosticFree diagnosticFree result, ?_⟩
  exact (yulName_ok_validFor inputValid result).1

/-- Yul-literal grammar soundness composes with source provenance. -/
theorem yulLiteral_success_sound_and_validFor {input next : State}
    {literal : YulLiteral} (inputValid : input.ValidFor)
    (result : yulLiteral input = .ok literal next) :
    DeclarativeGrammar.YulLiteralParses input.declarativeRemainder literal
        next.declarativeRemainder ∧
      Located.ValidFor input.file literal := by
  refine ⟨yulLiteral_success_sound result, ?_⟩
  exact (yulLiteral_ok_validFor inputValid result).1

end Solcore.Syntax.Parser

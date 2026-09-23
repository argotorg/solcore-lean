import Solcore.Syntax.DeclarativeCoreLiteralGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Diagnostic reflection and declarative soundness for Core literal leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Core-literal success never removes an earlier diagnostic. -/
theorem coreLiteral_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess coreLiteral := by
  intro input literal next result diagnosticFree
  rw [coreLiteral_ok_state_shape result] at diagnosticFree
  exact diagnosticFree

/-- Boolean-identifier success never removes an earlier diagnostic. -/
theorem booleanIdentifier_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess booleanIdentifier := by
  intro input name next result diagnosticFree
  rw [booleanIdentifier_ok_state_shape result] at diagnosticFree
  exact diagnosticFree

/-- Every successful Core literal is the exact current literal token. -/
theorem coreLiteral_success_sound {input next : State}
    {literal : CoreLiteral}
    (result : coreLiteral input = .ok literal next) :
    DeclarativeGrammar.CoreLiteralParses input.declarativeRemainder literal
      next.declarativeRemainder := by
  unfold coreLiteral at result
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

/-- Every successful Boolean builtin name is its exact keyword token. -/
theorem booleanIdentifier_success_sound {input next : State}
    {name : Identifier}
    (result : booleanIdentifier input = .ok name next) :
    DeclarativeGrammar.BooleanIdentifierParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold booleanIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        case trueKw =>
          cases result
          exact .trueKeyword (tokenAt_of_peek?_eq_some found)
        case falseKw =>
          cases result
          exact .falseKeyword (tokenAt_of_peek?_eq_some found)

namespace ExpressionAtomInternals

/-- Expression-name success reflects diagnostic freedom through its branch. -/
theorem expressionName_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess expressionName := by
  intro input name next result diagnosticFree
  unfold expressionName at result
  split at result
  · exact booleanIdentifier_reflectsDiagnosticFreeOnSuccess input name next
      result diagnosticFree
  · exact identifier_reflectsDiagnosticFreeOnSuccess .expression input name
      next result diagnosticFree

end ExpressionAtomInternals

/--
Every successful expression name follows the Boolean-first ordered grammar.
-/
theorem expressionName_success_sound {input next : State}
    {name : Identifier}
    (result : ExpressionAtomInternals.expressionName input = .ok name next) :
    DeclarativeGrammar.ExpressionNameParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold ExpressionAtomInternals.expressionName at result
  split at result
  · exact .boolean (booleanIdentifier_success_sound result)
  · have booleanAbsent : isBooleanValue input = false :=
      Bool.eq_false_iff.mpr (by assumption)
    have absences :
        isKeyword input .trueKw = false ∧
          isKeyword input .falseKw = false := by
      exact Bool.or_eq_false_iff.mp (by
        simpa only [isBooleanValue] using booleanAbsent)
    exact .identifier
      (keywordAbsentAt_of_isKeyword_eq_false .trueKw absences.1)
      (keywordAbsentAt_of_isKeyword_eq_false .falseKw absences.2)
      (identifier_success_sound .expression result)

/-- Core-literal grammar soundness composes with source provenance. -/
theorem coreLiteral_success_sound_and_validFor {input next : State}
    {literal : CoreLiteral} (inputValid : input.ValidFor)
    (result : coreLiteral input = .ok literal next) :
    DeclarativeGrammar.CoreLiteralParses input.declarativeRemainder literal
        next.declarativeRemainder ∧
      Located.ValidFor input.file literal := by
  refine ⟨coreLiteral_success_sound result, ?_⟩
  have valid := coreLiteral_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Boolean-name grammar soundness composes with source provenance. -/
theorem booleanIdentifier_success_sound_and_validFor {input next : State}
    {name : Identifier} (inputValid : input.ValidFor)
    (result : booleanIdentifier input = .ok name next) :
    DeclarativeGrammar.BooleanIdentifierParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      Located.ValidFor input.file name := by
  refine ⟨booleanIdentifier_success_sound result, ?_⟩
  have valid := booleanIdentifier_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Expression-name grammar soundness composes with source provenance. -/
theorem expressionName_success_sound_and_validFor {input next : State}
    {name : Identifier} (inputValid : input.ValidFor)
    (result : ExpressionAtomInternals.expressionName input = .ok name next) :
    DeclarativeGrammar.ExpressionNameParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      Located.ValidFor input.file name := by
  refine ⟨expressionName_success_sound result, ?_⟩
  have valid := ExpressionAtomInternals.expressionName_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser

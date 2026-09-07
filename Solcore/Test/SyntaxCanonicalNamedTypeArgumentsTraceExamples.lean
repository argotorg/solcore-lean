import Solcore.Syntax.Parser.NamedTypeArgumentsTraceProperties
import Solcore.Syntax.Parser.NamedTypeArgumentsRejectionTraceProperties
import Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples
import Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties

/-! Real typeExpr children in canonical optional argument lists. These concrete
executions do not assume or establish general recursive type trace contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalNamedTypeArgumentsTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples

private def qualified : QualifiedName := {
  span := SourceSpan.cover nameA.span nameA.span
  value := { components := { head := nameA, tail := [] } }
}
private def named : TypeExpr := makeNamedType qualified none
private def checkedState (input : State) : State := {
  input with cursor := input.cursor + 1, diagnosticsRev := hyphen nameA :: input.diagnosticsRev
}

private theorem checked_type_exec (input : State)
    (found : input.peek? = some (nameToken nameA))
    (noDot : isSymbol (checkedState input) .dot = false)
    (noArgs : isSymbol (checkedState input) .less = false) :
    typeExpr input = .ok named (checkedState input) := by
  have checked : identifier .typeExpr input = .ok nameA (checkedState input) := by
    simp only [identifier, rawIdentifier, found]
    rfl
  have path : qualifiedName .typeExpr .typeExpr input = .ok qualified (checkedState input) := by
    simp only [qualifiedName, checked, QualifiedNameInternals.qualifiedNameTail, noDot,
      Bool.false_eq_true, if_false, QualifiedNameInternals.finishQualifiedName]
    rfl
  have selected (fuel : Nat) : typeExprWithFuel (fuel + 1) input =
      parseNamedType (typeExprWithFuel fuel) input := by
    simp only [typeExprWithFuel, isKeyword, isContextual, isSymbol, isIdentifier,
      State.peekKind?, found, Option.map_some]
    rfl
  rw [typeExpr, selected]
  simp only [parseNamedType, bind, path, parseNamedTypeArguments, getState, noArgs,
    Bool.false_eq_true, if_false, pure]
  rfl

private def successText : String := "<a-b,> tail"
private def successTokens : List Token := [sym 0 1 .less, nameToken nameA, sym 4 5 .comma,
  sym 5 6 .greater, { span := span 7 11, value := .identifier "tail" }]
private def arguments : NonemptyDelimitedList TypeExpr := {
  span := span 0 6, elements := { head := named, tail := [] }
}
private def successOutput (prior : List ParseDiagnostic) : State := {
  initial successText successTokens prior with cursor := 4, diagnosticsRev := hyphen nameA :: prior.reverse
}

private theorem success_exec (prior : List ParseDiagnostic) :
    parseNamedTypeArguments typeExpr (initial successText successTokens prior) =
      .ok (some arguments) (successOutput prior) := by
  let input := initial successText successTokens prior
  let afterOpening : State := { input with cursor := 1 }
  have marker : ExactTokenParses (.symbol .less) input.declarativeRemainder
      (span 0 1) afterOpening.declarativeRemainder := ⟨⟨by change 0 < 5; decide, rfl⟩, rfl⟩
  have markerResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr marker
  change symbol .less .typeExpr input = .ok (sym 0 1 .less) afterOpening at markerResult
  have child := checked_type_exec afterOpening rfl rfl rfl
  have tail := SyntaxDelimitedTrailingSuccessTraceProperties.trailing_close_bypasses_any_child
    typeExpr (sym 0 1 .less) .greater .typeExpr .typeExpr afterOpening.remainingCount [named]
    (input := checkedState afterOpening) (afterComma := remainder successTokens 3)
    (after := remainder successTokens 4) (commaSpan := span 4 5) (closingSpan := span 5 6)
    ⟨⟨by change 2 < 5; decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩
  have raw : delimited .less .greater false typeExpr .typeExpr .typeExpr input =
      .ok { span := arguments.span, elements := arguments.elements.toList } (successOutput prior) := by
    unfold delimited delimitedWithPolicy
    rw [markerResult]
    simp only [Bool.false_and, Bool.false_eq_true, if_false]
    rw [child]
    have progress : (checkedState afterOpening).cursor > afterOpening.cursor := by change 2 > 1; decide
    simp only [progress, if_true]
    exact tail
  rw [parseNamedTypeArguments_eq_of_present typeExpr marker.1, raw]
  simp only [requireNonempty_eq_ok_of_toList]

set_option maxRecDepth 16384 in
theorem real_argument_list_lexes : Lexer.lex (file successText) = .ok (carrier successTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_real_type_argument (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      parseNamedTypeArguments typeExpr
        { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } = .ok (some arguments) output ∧
      output = successOutput prior ∧ output.diagnostics = prior ++ [hyphen nameA] ∧
      output.window = { endIndex := 5, endByte := 11 } ∧
      output.peek? = some { span := span 7 11, value := .identifier "tail" } := by
  refine ⟨carrier successTokens, successOutput prior, real_argument_list_lexes, success_exec prior,
    rfl, ?_, rfl, rfl⟩
  simp only [successOutput, State.diagnostics, List.reverse_cons, List.reverse_reverse]

private def rejectedText : String := "<a-b,+> tail"
private def rejectedTokens : List Token := [sym 0 1 .less, nameToken nameA, sym 4 5 .comma,
  sym 5 6 .plus, sym 6 7 .greater, { span := span 8 12, value := .identifier "tail" }]
private def rejectedOutput (prior : List ParseDiagnostic) : State := {
  initial rejectedText rejectedTokens prior with cursor := 3, diagnosticsRev := hyphen nameA :: prior.reverse
}
private def failure : Failure := {
  span := span 5 6, found := some (.symbol .plus)
  expected := { head := .typeExpr, tail := [] }, context := .typeExpr
}

private theorem rejection_exec (prior : List ParseDiagnostic) :
    parseNamedTypeArguments typeExpr (initial rejectedText rejectedTokens prior) =
      .reject failure (rejectedOutput prior) := by
  let input := initial rejectedText rejectedTokens prior
  let afterOpening : State := { input with cursor := 1 }
  have marker : ExactTokenParses (.symbol .less) input.declarativeRemainder
      (span 0 1) afterOpening.declarativeRemainder := ⟨⟨by change 0 < 6; decide, rfl⟩, rfl⟩
  have markerResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr marker
  change symbol .less .typeExpr input = .ok (sym 0 1 .less) afterOpening at markerResult
  have child := checked_type_exec afterOpening rfl rfl rfl
  have found : (rejectedOutput prior).peek? = some (sym 5 6 .plus) := rfl
  have selected (fuel : Nat) : typeExprWithFuel (fuel + 1) (rejectedOutput prior) =
      rejectAt (rejectedOutput prior) { head := .typeExpr, tail := [] } .typeExpr := by
    simp only [typeExprWithFuel, isKeyword, isContextual, isSymbol, isIdentifier,
      State.peekKind?, found, Option.map_some]
    rfl
  have rejected : typeExpr (rejectedOutput prior) = .reject failure (rejectedOutput prior) := by
    rw [typeExpr, selected]
    rfl
  have comma : ExactTokenParses (.symbol .comma) (checkedState afterOpening).declarativeRemainder
      (span 4 5) (rejectedOutput prior).declarativeRemainder := ⟨⟨by change 2 < 6; decide, rfl⟩, rfl⟩
  have commaResult := symbol_eq_ok_of_exactTokenParses .comma .typeExpr comma
  change symbol .comma .typeExpr (checkedState afterOpening) =
    .ok (sym 4 5 .comma) (rejectedOutput prior) at commaResult
  apply parseNamedTypeArguments_reject_iff_list.mpr
  refine ⟨rfl, ?_⟩
  change delimited .less .greater false typeExpr .typeExpr .typeExpr input =
    .reject failure (rejectedOutput prior)
  unfold delimited delimitedWithPolicy
  rw [markerResult]
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  rw [child]
  have progress : (checkedState afterOpening).cursor > afterOpening.cursor := by change 2 > 1; decide
  simp only [progress, if_true]
  change afterDelimitedElement typeExpr .greater true .typeExpr .typeExpr (sym 0 1 .less)
    (afterOpening.remainingCount + 1) [named] (checkedState afterOpening) = .reject failure (rejectedOutput prior)
  have commaPresent : isSymbol (checkedState afterOpening) .comma = true := rfl
  have noClosing : isSymbol (rejectedOutput prior) .greater = false := rfl
  simp only [afterDelimitedElement, commaPresent, if_true, commaResult, Bool.true_and,
    noClosing, Bool.false_eq_true, if_false, rejected]

set_option maxRecDepth 16384 in
theorem rejected_real_argument_lexes : Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_real_type_argument_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseNamedTypeArguments typeExpr
        { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } = .reject failure output ∧
      output = rejectedOutput prior ∧ output.diagnostics = prior ++ [hyphen nameA] ∧
      output.window = { endIndex := 6, endByte := 12 } ∧ output.peek? = some (sym 5 6 .plus) ∧
      output.tokens[5]? = some { span := span 8 12, value := .identifier "tail" } := by
  refine ⟨carrier rejectedTokens, rejectedOutput prior, rejected_real_argument_lexes, rejection_exec prior,
    rfl, ?_, rfl, rfl, rfl⟩
  simp only [rejectedOutput, State.diagnostics, List.reverse_cons, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalNamedTypeArgumentsTraceExamples

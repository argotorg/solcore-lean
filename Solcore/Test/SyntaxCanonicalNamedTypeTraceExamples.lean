import Solcore.Test.SyntaxNamedTypeTraceProperties
import Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples

/-! Bare mapping reports its complete type span only after optional arguments
succeed. A real type child failure inside selected arguments prevents that
finishing event altogether. Lexer decisions alone use kernel evaluation. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalNamedTypeTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxNamedTypeTraceProperties

private def source : SourceId := { origin := .main, path := "canonical-named-type-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def name : Identifier := { span := span 0 7, value := "mapping" }
private def nameToken : Token := { span := name.span, value := .identifier name.value }
private def qualified : QualifiedName := tracedQualifiedName name []
private def value : TypeExpr := namedTypeTraceValue qualified none
private def report : ParseDiagnostic := {
  span := value.span, kind := .constraintViolation .mappingRequiresCanonicalForm
}
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def initial (content : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with diagnosticsRev := prior.reverse
}

private theorem mapping_name_exec {input : State}
    (token : TokenAt input.tokens input.window.endIndex input.cursor nameToken)
    (noDot : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 1) (.symbol .dot)) :
    qualifiedName .typeExpr .typeExpr input = .ok qualified { input with cursor := input.cursor + 1 } := by
  have head : IdentifierTraceParses input.declarativeRemainder name
      { input.declarativeRemainder with cursor := input.cursor + 1 } [] :=
    .parsed ⟨token, rfl, rfl, rfl⟩ (.clean (by unfold IdentifierHyphenSpelling name; decide))
  exact qualifiedName_eq_ok_of_trace .typeExpr .typeExpr (.parsed head (.done noDot))

private def bareText : String := "mapping tail"
private def bareTokens : List Token := [nameToken, { span := span 8 12, value := .identifier "tail" }]
private def bareOutput (prior : List ParseDiagnostic) : State := {
  initial bareText bareTokens prior with cursor := 1, diagnosticsRev := report :: prior.reverse
}

set_option maxRecDepth 16384 in
theorem bare_mapping_lexes : Lexer.lex (file bareText) = .ok (carrier bareTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

/-- No nested parser is invoked for the bare spelling. Its one constraint
event follows every incoming report, and every other state field is exact. -/
theorem canonical_bare_mapping (nested : Parser TypeExpr) (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file bareText) = .ok lexed ∧
      parseNamedType nested { State.initial (file bareText) lexed with diagnosticsRev := prior.reverse } =
        .ok value output ∧ output = bareOutput prior ∧ output.diagnostics = prior ++ [report] ∧
      output.window = { endIndex := 2, endByte := 12 } ∧
      output.peek? = some { span := span 8 12, value := .identifier "tail" } := by
  let input := initial bareText bareTokens prior
  have nameResult := mapping_name_exec (input := input) ⟨by change 0 < 2; decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, input, initial, State.initial, carrier, bareTokens])
  have noArgs : TokenKindAbsentAt input.tokens input.window.endIndex 1 (.symbol .less) := by
    simp [TokenKindAbsentAt, TokenAt, input, initial, State.initial, carrier, bareTokens]
  have finished : NamedTypeFinishingTrace qualified none [report] := .canonicalRequired ⟨rfl, rfl⟩
  have result := no_arguments_bypass_any_child nested nameResult noArgs finished
  refine ⟨carrier bareTokens, bareOutput prior, bare_mapping_lexes, result, rfl, ?_, rfl, rfl⟩
  simp only [bareOutput, State.diagnostics, List.reverse_cons, List.reverse_reverse]

private def rejectedText : String := "mapping<+> tail"
private def rejectedTokens : List Token := [nameToken, { span := span 7 8, value := .symbol .less },
  { span := span 8 9, value := .symbol .plus }, { span := span 9 10, value := .symbol .greater },
  { span := span 11 15, value := .identifier "tail" }]
private def rejectedOutput (prior : List ParseDiagnostic) : State := {
  initial rejectedText rejectedTokens prior with cursor := 2
}
private def failure : Failure := {
  span := span 8 9, found := some (.symbol .plus)
  expected := { head := .typeExpr, tail := [] }, context := .typeExpr
}

private theorem rejected_exec (prior : List ParseDiagnostic) :
    parseNamedType typeExpr (initial rejectedText rejectedTokens prior) = .reject failure (rejectedOutput prior) := by
  let input := initial rejectedText rejectedTokens prior
  let afterName : State := { input with cursor := 1 }
  have nameResult := mapping_name_exec (input := input) ⟨by change 0 < 5; decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, input, initial, State.initial, carrier, rejectedTokens])
  have marker : ExactTokenParses (.symbol .less) afterName.declarativeRemainder
      (span 7 8) (rejectedOutput prior).declarativeRemainder := ⟨⟨by change 1 < 5; decide, rfl⟩, rfl⟩
  have markerResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr marker
  change symbol .less .typeExpr afterName =
    .ok { span := span 7 8, value := .symbol .less } (rejectedOutput prior) at markerResult
  have found : (rejectedOutput prior).peek? = some { span := span 8 9, value := .symbol .plus } := rfl
  have selected (fuel : Nat) : typeExprWithFuel (fuel + 1) (rejectedOutput prior) =
      rejectAt (rejectedOutput prior) { head := .typeExpr, tail := [] } .typeExpr := by
    simp only [typeExprWithFuel, isKeyword, isContextual, isSymbol, isIdentifier,
      State.peekKind?, found, Option.map_some]
    rfl
  have child : typeExpr (rejectedOutput prior) = .reject failure (rejectedOutput prior) := by
    rw [typeExpr, selected]
    rfl
  have raw : delimited .less .greater false typeExpr .typeExpr .typeExpr afterName =
      .reject failure (rejectedOutput prior) := by
    simp only [delimited, delimitedWithPolicy, markerResult, Bool.false_and, Bool.false_eq_true,
      if_false, child]
  exact argument_failure_bypasses_finishing typeExpr nameResult
    (parseNamedTypeArguments_reject_iff_list.mpr ⟨rfl, raw⟩)

set_option maxRecDepth 16384 in
theorem rejected_mapping_arguments_lex : Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

/-- The type rejection is still uncommitted, and the mapping constraint is
not emitted before arguments finish. Thus the entire diagnostic list is prior. -/
theorem canonical_mapping_argument_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseNamedType typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = rejectedOutput prior ∧ output.diagnostics = prior ∧
      output.window = { endIndex := 5, endByte := 15 } ∧
      output.peek? = some { span := span 8 9, value := .symbol .plus } ∧
      output.tokens[4]? = some { span := span 11 15, value := .identifier "tail" } := by
  refine ⟨carrier rejectedTokens, rejectedOutput prior, rejected_mapping_arguments_lex, rejected_exec prior,
    rfl, ?_, rfl, rfl, rfl⟩
  simp only [rejectedOutput, initial, State.diagnostics, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalNamedTypeTraceExamples

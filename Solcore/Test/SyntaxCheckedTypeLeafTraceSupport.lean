import Solcore.Syntax.Parser.QualifiedNameTraceCorrespondenceProperties
import Solcore.Syntax.Parser.NamedTypeArgumentsTracePrimitiveProperties
import Solcore.Syntax.Parser.NamedTypeFinishingTraceProperties

/-! Reusable concrete type-expression leaves: one checked identifier with no
dotted tail or arguments. Positive fuel reaches the real named-type dispatch,
without evaluating the whole parser or assuming anything about its child. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCheckedTypeLeafTraceSupport

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem checked_name_type_with_positive_fuel
    (fuel : Nat) {input : State} {name : Identifier} {trace : List ParseDiagnostic}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span := name.span, value := .identifier name.value })
    (diagnostics : IdentifierDiagnosticTrace name trace)
    (dotAbsent : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 1) (.symbol .dot))
    (argumentsAbsent : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 1) (.symbol .less))
    (notComptime : name.value ≠ ContextualKeyword.comptime.spelling)
    (notMapping : name.value ≠ ContextualKeyword.mapping.spelling) :
    typeExprWithFuel (fuel + 1) input =
      .ok (namedTypeTraceValue (tracedQualifiedName name []) none)
        { input with cursor := input.cursor + 1, diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  have nameParsed : QualifiedNameTraceParses input.file.id input.window.endByte input.declarativeRemainder
      (tracedQualifiedName name []) { input.declarativeRemainder with cursor := input.cursor + 1 } trace := by
    simpa only [List.append_nil] using QualifiedNameTraceParses.parsed
      (source := input.file.id) (endByte := input.window.endByte)
      (IdentifierTraceParses.parsed (input := input.declarativeRemainder)
        (output := { input.declarativeRemainder with cursor := input.cursor + 1 })
        ⟨token, rfl, rfl, rfl⟩ diagnostics)
      (DottedIdentifierTailTraceParses.done
        (input := { input.declarativeRemainder with cursor := input.cursor + 1 }) dotAbsent)
  have nameResult := qualifiedName_eq_ok_of_trace .typeExpr .typeExpr nameParsed
  let afterName : State := { input with
    cursor := input.cursor + 1
    diagnosticsRev := trace.reverse ++ input.diagnosticsRev }
  change qualifiedName .typeExpr .typeExpr input = .ok (tracedQualifiedName name []) afterName at nameResult
  have argumentsResult := parseNamedTypeArguments_eq_none_of_absent (typeExprWithFuel fuel)
    (input := afterName) argumentsAbsent
  have finishing : NamedTypeFinishingTrace (tracedQualifiedName name []) none [] := by
    apply NamedTypeFinishingTrace.ordinary
    intro mapping
    exact notMapping mapping.2
  have finishResult := finishNamedType_eq_ok_of_trace (tracedQualifiedName name []) none afterName finishing
  change finishNamedType (tracedQualifiedName name []) none afterName =
    .ok (namedTypeTraceValue (tracedQualifiedName name []) none) afterName at finishResult
  have namedResult : parseNamedType (typeExprWithFuel fuel) input =
      .ok (namedTypeTraceValue (tracedQualifiedName name []) none) afterName := by
    simpa only [parseNamedType, bind, nameResult, argumentsResult] using finishResult
  have current : input.peek? = some { span := name.span, value := .identifier name.value } := by
    simp only [State.peek?, token.1, if_true, token.2]
  have noComptime : isContextual input .comptime = false := by
    simp [isContextual, State.peekKind?, current, TokenKind.isContextual, notComptime]
  have noMapping : isContextual input .mapping = false := by
    simp [isContextual, State.peekKind?, current, TokenKind.isContextual, notMapping]
  have noFunction : isKeyword input .functionKw = false := by
    simp only [isKeyword, State.peekKind?, current, Option.map_some]; rfl
  have noProxy : isSymbol input .at = false := by
    simp only [isSymbol, State.peekKind?, current, Option.map_some]; rfl
  have noTuple : isSymbol input .leftParen = false := by
    simp only [isSymbol, State.peekKind?, current, Option.map_some]; rfl
  have named : isIdentifier input = true := by
    simp only [isIdentifier, State.peekKind?, current, Option.map_some]
  simpa only [typeExprWithFuel, noFunction, noComptime, noMapping, noProxy, noTuple,
    named, Bool.false_and, Bool.false_eq_true, if_false, if_true] using namedResult

theorem checked_name_type
    {input : State} {name : Identifier} {trace : List ParseDiagnostic}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span := name.span, value := .identifier name.value })
    (diagnostics : IdentifierDiagnosticTrace name trace)
    (dotAbsent : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 1) (.symbol .dot))
    (argumentsAbsent : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 1) (.symbol .less))
    (notComptime : name.value ≠ ContextualKeyword.comptime.spelling)
    (notMapping : name.value ≠ ContextualKeyword.mapping.spelling) :
    typeExpr input = .ok (namedTypeTraceValue (tracedQualifiedName name []) none)
      { input with cursor := input.cursor + 1, diagnosticsRev := trace.reverse ++ input.diagnosticsRev } :=
  checked_name_type_with_positive_fuel input.remainingCount token diagnostics dotAbsent argumentsAbsent notComptime notMapping

end Solcore.Test.SyntaxCheckedTypeLeafTraceSupport

import Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
import Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties

/-! A concrete checked-name type child inside a singleton trailing list. The
carrier, source, active window, initial cursor, and earlier diagnostics remain
arbitrary; this supplies real execution without general type-trace contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCheckedTypeListTraceSupport

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
open Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties

theorem singleton_trailing_checked_type_list
    {input : State} {name : Identifier} {trace : List ParseDiagnostic}
    {openingSpan commaSpan closingSpan : SourceSpan}
    (opening : TokenAt input.tokens input.window.endIndex input.cursor
      { span := openingSpan, value := .symbol .leftParen })
    (nameAt : TokenAt input.tokens input.window.endIndex (input.cursor + 1)
      { span := name.span, value := .identifier name.value })
    (comma : TokenAt input.tokens input.window.endIndex (input.cursor + 2)
      { span := commaSpan, value := .symbol .comma })
    (closing : TokenAt input.tokens input.window.endIndex (input.cursor + 3)
      { span := closingSpan, value := .symbol .rightParen })
    (nameTrace : IdentifierDiagnosticTrace name trace)
    (notComptime : name.value ≠ ContextualKeyword.comptime.spelling)
    (notMapping : name.value ≠ ContextualKeyword.mapping.spelling) :
    delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr input =
      .ok {
        span := SourceSpan.cover openingSpan closingSpan
        elements := [namedTypeTraceValue (tracedQualifiedName name []) none]
      } { input with cursor := input.cursor + 4, diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  have noDot : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 2) (.symbol .dot) := by
    rintro ⟨span, other⟩
    have impossible := congrArg (·.value) (comma.token_unique other)
    cases impossible
  have noArgs : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 2) (.symbol .less) := by
    rintro ⟨span, other⟩
    have impossible := congrArg (·.value) (comma.token_unique other)
    cases impossible
  have child := checked_name_type (input := { input with cursor := input.cursor + 1 })
    nameAt nameTrace noDot noArgs notComptime notMapping
  have marker := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := input) ⟨opening, rfl⟩
  have first : ({ input with cursor := input.cursor + 1 } : State).peek? =
      some { span := name.span, value := .identifier name.value } := by
    simp only [State.peek?, nameAt.1, if_true, nameAt.2]
  have noClose : isSymbol { input with cursor := input.cursor + 1 } .rightParen = false := by
    simp only [isSymbol, State.peekKind?, first, Option.map_some]
    rfl
  have progress : input.cursor + 1 + 1 > input.cursor + 1 := by omega
  have tail := trailing_close_bypasses_any_child typeExpr
    { span := openingSpan, value := .symbol .leftParen } .rightParen .typeExpr .typeExpr
    ({ input with cursor := input.cursor + 1 } : State).remainingCount
    [namedTypeTraceValue (tracedQualifiedName name []) none]
    (input := { input with cursor := input.cursor + 2, diagnosticsRev := trace.reverse ++ input.diagnosticsRev })
    (commaSpan := commaSpan) (closingSpan := closingSpan)
    ⟨comma, rfl⟩ ⟨closing, rfl⟩
  simp only [delimited, delimitedWithPolicy, marker, Bool.true_and, noClose,
    Bool.false_eq_true, if_false, child, progress, if_true]
  exact tail

theorem checked_type_list_missing_separator
    {input : State} {name : Identifier} {trace : List ParseDiagnostic}
    {openingSpan badSpan : SourceSpan}
    (opening : TokenAt input.tokens input.window.endIndex input.cursor
      { span := openingSpan, value := .symbol .leftParen })
    (nameAt : TokenAt input.tokens input.window.endIndex (input.cursor + 1)
      { span := name.span, value := .identifier name.value })
    (bad : TokenAt input.tokens input.window.endIndex (input.cursor + 2)
      { span := badSpan, value := .symbol .plus })
    (nameTrace : IdentifierDiagnosticTrace name trace)
    (notComptime : name.value ≠ ContextualKeyword.comptime.spelling)
    (notMapping : name.value ≠ ContextualKeyword.mapping.spelling) :
    delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr input =
      .reject {
        span := badSpan, found := some (.symbol .plus)
        expected := { head := .symbol .comma, tail := [.symbol .rightParen] }
        context := .typeExpr
      } { input with cursor := input.cursor + 2, diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  have noDot : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 2) (.symbol .dot) := by
    rintro ⟨span, other⟩
    have impossible := congrArg (·.value) (bad.token_unique other)
    cases impossible
  have noArgs : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 2) (.symbol .less) := by
    rintro ⟨span, other⟩
    have impossible := congrArg (·.value) (bad.token_unique other)
    cases impossible
  have child := checked_name_type (input := { input with cursor := input.cursor + 1 })
    nameAt nameTrace noDot noArgs notComptime notMapping
  have marker := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := input) ⟨opening, rfl⟩
  have first : ({ input with cursor := input.cursor + 1 } : State).peek? =
      some { span := name.span, value := .identifier name.value } := by
    simp only [State.peek?, nameAt.1, if_true, nameAt.2]
  have noClose : isSymbol { input with cursor := input.cursor + 1 } .rightParen = false := by
    simp only [isSymbol, State.peekKind?, first, Option.map_some]
    rfl
  let next : State := { input with cursor := input.cursor + 2, diagnosticsRev := trace.reverse ++ input.diagnosticsRev }
  have nextFound : next.peek? = some { span := badSpan, value := .symbol .plus } := by
    simp only [next, State.peek?, bad.1, if_true, bad.2]
  have noComma : isSymbol next .comma = false := by
    simp only [isSymbol, State.peekKind?, nextFound, Option.map_some]
    rfl
  have noFinish : isSymbol next .rightParen = false := by
    simp only [isSymbol, State.peekKind?, nextFound, Option.map_some]
    rfl
  have progress : input.cursor + 1 + 1 > input.cursor + 1 := by omega
  simp only [delimited, delimitedWithPolicy, marker, Bool.true_and, noClose,
    Bool.false_eq_true, if_false, child, progress, if_true]
  change afterDelimitedElement typeExpr .rightParen true .typeExpr .typeExpr
    { span := openingSpan, value := .symbol .leftParen }
    (({ input with cursor := input.cursor + 1 } : State).remainingCount + 1) [_] next = _
  simp only [afterDelimitedElement, noComma, noFinish, Bool.false_eq_true, if_false]
  simp only [rejectAt, State.currentSpan, State.peekKind?, nextFound, Option.map_some]
  rfl

end Solcore.Test.SyntaxCheckedTypeListTraceSupport

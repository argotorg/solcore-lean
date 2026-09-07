import Solcore.Syntax.DeclarativeExpressionAtomDispatchSelectionProperties
import Solcore.Syntax.Parser.CorePatternCoreOutcomePrimitiveProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Proof-side reflection of all ordered atom guards. The selected raw parser
has exactly the original Reply, including arbitrary recursive child behavior;
selection alone does not establish a recursive trace outcome. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

namespace ExpressionAtomDispatchTraceInternals

def selectedBranch (input : State) : ExpressionAtomDispatchBranch :=
  if isCoreLiteral input then .literal
  else if isBooleanValue input || isIdentifier input then .name
  else if isSymbol input .dot then .dotConstructor
  else if isSymbol input .at then .proxy
  else if isSymbol input .leftParen then .parenthesized
  else if isSymbol input .leftBracket then .array
  else if isKeyword input .lamKw then .lambda
  else .final

def rawParser (nested : Parser Expr) (block : Parser Block)
    (branch : ExpressionAtomDispatchBranch) : Parser Expr :=
  match branch with
  | .literal => literalExpression
  | .name => identifierExpression
  | .dotConstructor => dotConstructor nested
  | .proxy => proxyExpression
  | .parenthesized => parenthesized nested
  | .array => arrayLiteral nested
  | .lambda => lambdaExpression block
  | .final => fun input => rejectAt input { head := .expression, tail := [] } .expression

private theorem name_present_of_guard {input : State}
    (present : (isBooleanValue input || isIdentifier input) = true) :
    ExpressionNameStartsAt input.declarativeRemainder := by
  rcases Bool.or_eq_true_iff.mp present with booleanPresent | identifierPresent
  · rcases PatternInternals.booleanPatternStartsAt_of_isBooleanValue_eq_true booleanPresent with
      truePresent | falsePresent
    · exact .inl truePresent
    · exact .inr (.inl falsePresent)
  · exact .inr (.inr (identifierPresentAt_of_isIdentifier_eq_true identifierPresent))

theorem selectedBranch_selects (input : State) :
    ExpressionAtomDispatchSelects input.declarativeRemainder (selectedBranch input) := by
  unfold selectedBranch
  split
  next present => exact .literal (PatternInternals.coreLiteralStartsAt_of_isCoreLiteral_eq_true present)
  next absent =>
    have literalAbsent := not_coreLiteralStartsAt_of_isCoreLiteral_eq_false (Bool.eq_false_iff.mpr absent)
    split
    next present => exact .name literalAbsent (name_present_of_guard present)
    next absent =>
      have nameAbsent := not_expressionNameStartsAt_of_expressionNameGuard_eq_false (Bool.eq_false_iff.mpr absent)
      split
      next present =>
        exact .dotConstructor literalAbsent nameAbsent (PatternInternals.symbolTokenAt_of_isSymbol_eq_true .dot present)
      next absent =>
        have dotAbsent := symbolAbsentAt_of_isSymbol_eq_false .dot (Bool.eq_false_iff.mpr absent)
        split
        next present =>
          exact .proxy literalAbsent nameAbsent dotAbsent (PatternInternals.symbolTokenAt_of_isSymbol_eq_true .at present)
        next absent =>
          have atAbsent := symbolAbsentAt_of_isSymbol_eq_false .at (Bool.eq_false_iff.mpr absent)
          split
          next present =>
            exact .parenthesized literalAbsent nameAbsent dotAbsent atAbsent
              (PatternInternals.symbolTokenAt_of_isSymbol_eq_true .leftParen present)
          next absent =>
            have parenAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftParen (Bool.eq_false_iff.mpr absent)
            split
            next present =>
              exact .array literalAbsent nameAbsent dotAbsent atAbsent parenAbsent
                (PatternInternals.symbolTokenAt_of_isSymbol_eq_true .leftBracket present)
            next absent =>
              have bracketAbsent := symbolAbsentAt_of_isSymbol_eq_false .leftBracket (Bool.eq_false_iff.mpr absent)
              split
              next present =>
                rcases keyword_eq_ok_of_isKeyword_eq_true .lamKw .expression present with ⟨marker, parsed⟩
                exact .lambda literalAbsent nameAbsent dotAbsent atAbsent parenAbsent bracketAbsent
                  ⟨marker.span, (keyword_success_exactTokenParses .lamKw .expression parsed).1⟩
              next absent =>
                exact .final literalAbsent nameAbsent dotAbsent atAbsent parenAbsent bracketAbsent
                  (keywordAbsentAt_of_isKeyword_eq_false .lamKw (Bool.eq_false_iff.mpr absent))

theorem selectedBranch_eq_iff {input : State} {branch : ExpressionAtomDispatchBranch} :
    selectedBranch input = branch ↔ ExpressionAtomDispatchSelects input.declarativeRemainder branch := by
  constructor
  · intro same; rw [← same]; exact selectedBranch_selects input
  · exact (selectedBranch_selects input).branch_unique

theorem selectedBranch_eq_of_remainder_eq {left right : State}
    (same : left.declarativeRemainder = right.declarativeRemainder) :
    selectedBranch left = selectedBranch right := by
  apply selectedBranch_eq_iff.mpr
  rw [same]
  exact selectedBranch_selects right

theorem expressionAtomCore_eq_selected_raw (nested : Parser Expr) (block : Parser Block) (input : State) :
    expressionAtomCore nested block input = rawParser nested block (selectedBranch input) input := by
  unfold expressionAtomCore selectedBranch
  repeat' first | split | rfl

end ExpressionAtomDispatchTraceInternals

theorem ExpressionAtomInternals.expressionAtomCore_eq_raw_of_selection
    (nested : Parser Expr) (block : Parser Block) {input : State} {branch : ExpressionAtomDispatchBranch}
    (selection : ExpressionAtomDispatchSelects input.declarativeRemainder branch) :
    expressionAtomCore nested block input = ExpressionAtomDispatchTraceInternals.rawParser nested block branch input := by
  rw [ExpressionAtomDispatchTraceInternals.expressionAtomCore_eq_selected_raw,
    ExpressionAtomDispatchTraceInternals.selectedBranch_eq_iff.mpr selection]

end Solcore.Syntax.Parser

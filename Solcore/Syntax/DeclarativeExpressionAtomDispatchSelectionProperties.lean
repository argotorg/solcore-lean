import Solcore.Syntax.DeclarativeExpressionAtomDispatchSelectionGrammar

/-! Ordered guard selection is unique and exists for every token remainder,
including missing backing or a cursor outside the numeric window. These are
selection laws, not existence claims about recursive expression outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem ExpressionAtomDispatchSelects.branch_unique
    {input : Remainder} {left right : ExpressionAtomDispatchBranch}
    (leftSelected : ExpressionAtomDispatchSelects input left)
    (rightSelected : ExpressionAtomDispatchSelects input right) : left = right := by
  cases leftSelected <;> cases rightSelected <;> grind only [TokenKindAbsentAt]

theorem expressionAtomDispatchSelects_exists (input : Remainder) :
    ∃ branch, ExpressionAtomDispatchSelects input branch := by
  classical
  by_cases literal : CoreLiteralStartsAt input
  · exact ⟨.literal, .literal literal⟩
  by_cases name : ExpressionNameStartsAt input
  · exact ⟨.name, .name literal name⟩
  by_cases dot : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .dot }
  · exact ⟨.dotConstructor, .dotConstructor literal name dot⟩
  by_cases atMarker : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at }
  · exact ⟨.proxy, .proxy literal name dot atMarker⟩
  by_cases paren : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftParen }
  · exact ⟨.parenthesized, .parenthesized literal name dot atMarker paren⟩
  by_cases bracket : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftBracket }
  · exact ⟨.array, .array literal name dot atMarker paren bracket⟩
  by_cases lambda : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .keyword .lamKw }
  · exact ⟨.lambda, .lambda literal name dot atMarker paren bracket lambda⟩
  exact ⟨.final, .final literal name dot atMarker paren bracket lambda⟩

/-- A unique selected branch exists without a success/rejection premise. -/
theorem expressionAtomDispatchSelects_exists_unique (input : Remainder) :
    ∃ branch, ExpressionAtomDispatchSelects input branch ∧
      ∀ other, ExpressionAtomDispatchSelects input other → other = branch := by
  rcases expressionAtomDispatchSelects_exists input with ⟨branch, selected⟩
  exact ⟨branch, selected, fun _ other => other.branch_unique selected⟩

/-- Equal current-token observations suffice even when the backing arrays,
numeric windows, and cursor positions themselves differ. -/
theorem ExpressionAtomDispatchSelects.congr_of_tokenAt
    {left right : Remainder} {branch : ExpressionAtomDispatchBranch}
    (current : ∀ token, TokenAt left.tokens left.endIndex left.cursor token ↔
      TokenAt right.tokens right.endIndex right.cursor token) :
    ExpressionAtomDispatchSelects left branch ↔ ExpressionAtomDispatchSelects right branch := by
  have literals : CoreLiteralStartsAt left ↔ CoreLiteralStartsAt right := by
    simp only [CoreLiteralStartsAt, current]
  have names : ExpressionNameStartsAt left ↔ ExpressionNameStartsAt right := by
    simp only [ExpressionNameStartsAt, current]
  have absences : ∀ kind, TokenKindAbsentAt left.tokens left.endIndex left.cursor kind ↔
      TokenKindAbsentAt right.tokens right.endIndex right.cursor kind := by
    intro kind
    simp only [TokenKindAbsentAt, current]
  constructor <;> intro selected <;> cases selected <;> constructor <;>
    grind only

end Solcore.Syntax.DeclarativeGrammar

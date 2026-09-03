import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.File

/-! Exact execution and top-level dispatch at an independently supplied pragma
keyword. No later declaration stage is assumed to succeed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The exact independent pragma token fixes the current executable lookahead. -/
theorem peekKind_eq_pragma_of_exactTokenParses
    {input : State} {marker : SourceSpan} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after) :
    input.peekKind? = some (.keyword .pragmaKw) := by
  have current := parsed.1
  change input.cursor < input.window.endIndex ∧
    input.tokens[input.cursor]? = some { span := marker, value := .keyword .pragmaKw }
    at current
  unfold State.peekKind? State.peek?
  simp only [current.1, ↓reduceIte, current.2, Option.map_some]

/-- Consuming the independently supplied marker changes only the cursor. -/
theorem pragmaKeyword_eq_ok_of_exactTokenParses
    {input : State} {marker : SourceSpan} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after) :
    keyword .pragmaKw .pragmaDecl input =
      .ok { span := marker, value := .keyword .pragmaKw }
        { input with cursor := input.cursor + 1 } := by
  have current := parsed.1
  change input.cursor < input.window.endIndex ∧
    input.tokens[input.cursor]? = some { span := marker, value := .keyword .pragmaKw }
    at current
  have found : input.peek? = some { span := marker, value := .keyword .pragmaKw } := by
    unfold State.peek?
    simp only [current.1, ↓reduceIte, current.2]
  have accepted : ((.keyword .pragmaKw : TokenKind) == .keyword .pragmaKw) = true := rfl
  simp only [keyword, acceptToken, found, accepted, if_true]

namespace FileInternals

/-- A pragma marker is a recognized file-level stopping boundary. -/
theorem atTopItemStart_eq_true_of_pragmaToken
    {input : State} {marker : SourceSpan} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after) :
    atTopItemStart input = true := by
  unfold atTopItemStart
  rw [peekKind_eq_pragma_of_exactTokenParses parsed]
  rfl

/-- A leading pragma marker bypasses the earlier import/export guards and
selects the pragma leaf without changing its input. -/
theorem plainTopItem_eq_pragma_of_exactTokenParses
    {input : State} {marker : SourceSpan} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after) :
    plainTopItem input = mapTopItem pragmaDecl wrapPragma input := by
  have found := peekKind_eq_pragma_of_exactTokenParses parsed
  have importAbsent : isKeyword input .importKw = false := by
    unfold isKeyword; rw [found]; rfl
  have exportAbsent : isKeyword input .exportKw = false := by
    unfold isKeyword; rw [found]; rfl
  have pragmaPresent : isKeyword input .pragmaKw = true := by
    unfold isKeyword; rw [found]; rfl
  simp only [plainTopItem, importAbsent, exportAbsent, pragmaPresent,
    Bool.false_eq_true, if_false, if_true]

/-- The same marker is not a derive hash, so derive-aware dispatch is plain. -/
theorem topItem_eq_pragma_of_exactTokenParses
    {input : State} {marker : SourceSpan} {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.keyword .pragmaKw)
      input.declarativeRemainder marker after) :
    topItem input = mapTopItem pragmaDecl wrapPragma input := by
  have found := peekKind_eq_pragma_of_exactTokenParses parsed
  have noHash : isSymbol input .hash = false := by
    unfold isSymbol; rw [found]; rfl
  simp only [topItem, noHash, Bool.false_eq_true, if_false]
  exact plainTopItem_eq_pragma_of_exactTokenParses parsed

end FileInternals
end Solcore.Syntax.Parser

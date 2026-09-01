import Solcore.Syntax.DeclarativeYulStatementCorePriorityGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Yul.Statement

/-! Exact bridges for the Yul-name guard in `yulStatementCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem tokenKindStarts_of_match_true (kind : TokenKind)
    (result : (match some kind with
      | some (.identifier _)
      | some (.yulIdentifier _)
      | some (.symbol .underscore)
      | some (.keyword .fallbackKw) => true
      | _ => false) = true) :
    DeclarativeGrammar.tokenKindStartsYulName kind = true := by
  cases kind with
  | keyword value =>
      cases value <;>
        simp_all [DeclarativeGrammar.tokenKindStartsYulName]
  | symbol value =>
      cases value <;>
        simp_all [DeclarativeGrammar.tokenKindStartsYulName]
  | identifier text => rfl
  | yulIdentifier text => rfl
  | decimalLiteral spelling => contradiction
  | hexadecimalLiteral spelling => contradiction
  | stringLiteral spelling => contradiction
  | yulMetaBacktick spelling => contradiction
  | yulMetaInterpolation spelling => contradiction

private theorem tokenKindStops_of_match_false (kind : TokenKind)
    (result : (match some kind with
      | some (.identifier _)
      | some (.yulIdentifier _)
      | some (.symbol .underscore)
      | some (.keyword .fallbackKw) => true
      | _ => false) = false) :
    DeclarativeGrammar.tokenKindStartsYulName kind = false := by
  cases kind with
  | keyword value =>
      cases value <;>
        simp_all [DeclarativeGrammar.tokenKindStartsYulName]
  | symbol value =>
      cases value <;>
        simp_all [DeclarativeGrammar.tokenKindStartsYulName]
  | identifier text => contradiction
  | yulIdentifier text => contradiction
  | decimalLiteral spelling => rfl
  | hexadecimalLiteral spelling => rfl
  | stringLiteral spelling => rfl
  | yulMetaBacktick spelling => rfl
  | yulMetaInterpolation spelling => rfl

/-- Successful executable name lookahead exposes its exact current token. -/
theorem yulNameStartAt_of_startsYulName_eq_true {input : State}
    (present : startsYulName input = true) :
    DeclarativeGrammar.YulNameStartAt input.declarativeRemainder := by
  unfold startsYulName State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      refine ⟨token, tokenAt_of_peek?_eq_some found, ?_⟩
      exact tokenKindStarts_of_match_true token.value present

/-- Failed executable name lookahead excludes every admitted current kind. -/
theorem yulNameStartAbsentAt_of_startsYulName_eq_false {input : State}
    (absent : startsYulName input = false) :
    DeclarativeGrammar.YulNameStartAbsentAt input.declarativeRemainder := by
  unfold DeclarativeGrammar.YulNameStartAbsentAt
    DeclarativeGrammar.YulNameStartAt
  rintro ⟨token, ⟨inside, found⟩, tokenStarts⟩
  change input.cursor < input.window.endIndex at inside
  change input.tokens[input.cursor]? = some token at found
  unfold startsYulName State.peekKind? State.peek? at absent
  simp only [inside, ↓reduceIte, found, Option.map_some] at absent
  have tokenStops :
      DeclarativeGrammar.tokenKindStartsYulName token.value = false := by
    exact tokenKindStops_of_match_false token.value absent
  rw [tokenStarts] at tokenStops
  contradiction

end Solcore.Syntax.Parser

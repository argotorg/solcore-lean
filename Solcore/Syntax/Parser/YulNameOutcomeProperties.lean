import Solcore.Syntax.DeclarativeYulNameOutcomeProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Yul.LeafProperties

/-!
Executable success and rejection bridges for one ordinary inline-Yul name.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem ordinaryKindStops_of_executable_match_false (kind : TokenKind)
    (result : (match some kind with
      | some (.identifier _)
      | some (.yulIdentifier _)
      | some (.symbol .underscore)
      | some (.keyword .fallbackKw) => true
      | _ => false) = false) :
    DeclarativeGrammar.tokenKindStartsOrdinaryYulName kind = false := by
  cases kind with
  | keyword value =>
      cases value <;>
        simp_all [DeclarativeGrammar.tokenKindStartsOrdinaryYulName]
  | symbol value =>
      cases value <;>
        simp_all [DeclarativeGrammar.tokenKindStartsOrdinaryYulName]
  | identifier text => contradiction
  | yulIdentifier text => contradiction
  | decimalLiteral spelling => rfl
  | hexadecimalLiteral spelling => rfl
  | stringLiteral spelling => rfl
  | yulMetaBacktick spelling => rfl
  | yulMetaInterpolation spelling => rfl

private theorem noOrdinaryYulName_of_startsYulName_eq_false {input : State}
    (absent : startsYulName input = false) :
    ¬ ∃ name output,
      DeclarativeGrammar.YulNameOrdinaryParses input.declarativeRemainder name
        output := by
  rintro ⟨name, output, parsed⟩
  rcases parsed.startsAt with ⟨token, ⟨inside, found⟩, tokenStarts⟩
  change input.cursor < input.window.endIndex at inside
  change input.tokens[input.cursor]? = some token at found
  unfold startsYulName State.peekKind? State.peek? at absent
  simp only [inside, ↓reduceIte, found, Option.map_some] at absent
  have tokenStops :
      DeclarativeGrammar.tokenKindStartsOrdinaryYulName token.value = false :=
    ordinaryKindStops_of_executable_match_false token.value absent
  rw [tokenStarts] at tokenStops
  contradiction

private theorem startsYulName_eq_false_of_yulName_reject
    {input rejected : State} {failure : Failure}
    (result : yulName input = .reject failure rejected) :
    startsYulName input = false := by
  unfold yulName at result
  unfold startsYulName State.peekKind?
  cases found : input.peek? with
  | none => rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result ⊢
      all_goals try { rfl }
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text =>
        simp only [identifier, rawIdentifier, found] at result
        split at result <;> contradiction
      case yulIdentifier text => cases result
      case keyword keyword =>
        cases keyword <;> simp only at result ⊢ <;> try rfl
        all_goals try { unfold rejectAt at result; contradiction }
        case fallbackKw => cases result
      case symbol symbol =>
        cases symbol <;> simp only at result ⊢ <;> try rfl
        all_goals try { unfold rejectAt at result; contradiction }
        case underscore => cases result

/-- Every executable Yul-name success is an ordinary success, even when the
checked ordinary identifier emits a hyphen diagnostic. -/
theorem yulName_success_ordinary_sound {input next : State}
    {name : YulIdentifier} (result : yulName input = .ok name next) :
    DeclarativeGrammar.YulNameOrdinaryParses input.declarativeRemainder name
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
        exact .identifier (identifier_success_sound .yulExpression result)
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

/-- Ordinary Yul-name rejection returns the exact input parser state. -/
theorem yulName_reject_state_eq {input rejected : State} {failure : Failure}
    (result : yulName input = .reject failure rejected) : rejected = input := by
  unfold yulName at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      cases result
      rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; cases result; rfl }
      case identifier text =>
        simp only [identifier, rawIdentifier, found] at result
        split at result <;> contradiction
      case yulIdentifier text => contradiction
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; cases result; rfl }
        case fallbackKw => contradiction
      case symbol symbol =>
        cases symbol <;> simp only at result
        all_goals try { unfold rejectAt at result; cases result; rfl }
        case underscore => contradiction

/-- Every executable Yul-name rejection follows the exact binary rejection
relation. -/
theorem yulName_reject_sound {input rejected : State} {failure : Failure}
    (result : yulName input = .reject failure rejected) :
    DeclarativeGrammar.YulNameRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  have rejectedEq := yulName_reject_state_eq result
  subst rejectedEq
  exact .absent (noOrdinaryYulName_of_startsYulName_eq_false
    (startsYulName_eq_false_of_yulName_reject result))

end Solcore.Syntax.Parser

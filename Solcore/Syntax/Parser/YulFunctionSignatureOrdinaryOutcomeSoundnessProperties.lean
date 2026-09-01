import Solcore.Syntax.DeclarativeYulFunctionOutcomeProperties
import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.YulNameOutcomeProperties
import Solcore.Syntax.Parser.YulNamesOutcomeProperties
import Solcore.Syntax.Parser.Yul.Control

/-! Executable ordinary outcomes for inline-Yul function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Successful parameters retain ordinary diagnosed names and exact order. -/
theorem yulParameters_success_ordinary_sound {input output : State}
    {parameters : DelimitedList YulIdentifier}
    (result : yulParameters input = .ok parameters output) :
    DeclarativeGrammar.YulParametersOrdinaryParses
      input.declarativeRemainder parameters output.declarativeRemainder := by
  unfold yulParameters at result
  unfold DeclarativeGrammar.YulParametersOrdinaryParses
  exact delimited_allowEmpty_trailing_success_sound .leftParen .rightParen
    yulName DeclarativeGrammar.YulNameOrdinaryParses .yulStatement .yul
    yulName_success_ordinary_sound yulName_preservesTokenWindow result

/-- Rejected parameters retain the exact nested or delimiter remainder. -/
theorem yulParameters_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : yulParameters input = .reject failure rejected) :
    DeclarativeGrammar.YulParametersRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold yulParameters at result
  exact delimited_reject_sound .leftParen .rightParen true yulName
    DeclarativeGrammar.YulNameOrdinaryParses
    DeclarativeGrammar.YulNameRejects .yulStatement .yul
    yulName_success_ordinary_sound yulName_reject_sound result

namespace YulControl

/-- Successful return clauses retain arrow, names, span, order, and output. -/
theorem returnClause_success_ordinary_sound {input output : State}
    {clause : YulReturnClause}
    (result : returnClause input = .ok clause output) :
    DeclarativeGrammar.YulReturnClauseOrdinaryParses
      input.declarativeRemainder clause output.declarativeRemainder := by
  unfold returnClause at result
  cases arrowResult : symbol .arrow .yulStatement input with
  | invariant error => simp [bind, arrowResult] at result
  | reject failure rejected => simp [bind, arrowResult] at result
  | ok arrow afterArrow =>
      simp only [bind, arrowResult] at result
      cases namesResult : yulNames afterArrow with
      | invariant error => simp [namesResult] at result
      | reject failure rejected => simp [namesResult] at result
      | ok names afterNames =>
          simp only [namesResult, pure] at result
          cases result
          exact .parsed arrow.span
            (symbol_success_exactTokenParses .arrow .yulStatement arrowResult)
            (yulNames_success_ordinary_sound namesResult)

/-- Rejected return clauses record arrow absence or rejected names. -/
theorem returnClause_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : returnClause input = .reject failure rejected) :
    DeclarativeGrammar.YulReturnClauseRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold returnClause at result
  cases arrowResult : symbol .arrow .yulStatement input with
  | invariant error => simp [bind, arrowResult] at result
  | reject arrowFailure arrowRejected =>
      have rejectedEq := symbol_reject_state_eq .arrow .yulStatement
        arrowResult
      subst arrowRejected
      simp only [bind, arrowResult] at result
      cases result
      exact .arrowMissing
        (symbol_reject_tokenKindAbsentAt .arrow .yulStatement arrowResult)
  | ok arrow afterArrow =>
      simp only [bind, arrowResult] at result
      cases namesResult : yulNames afterArrow with
      | invariant error => simp [namesResult] at result
      | ok names afterNames => simp [namesResult, pure] at result
      | reject namesFailure namesRejected =>
          simp only [namesResult] at result
          cases result
          exact .namesRejected arrow.span
            (symbol_success_exactTokenParses .arrow .yulStatement arrowResult)
            (yulNames_reject_sound namesResult)

/-- Successful optional returns follow exact arrow priority. -/
theorem returns_success_ordinary_sound {input output : State}
    {returnsValue : Option YulReturnClause}
    (result : returns input = .ok returnsValue output) :
    DeclarativeGrammar.YulReturnsOrdinaryParses input.declarativeRemainder
      returnsValue output.declarativeRemainder := by
  unfold returns getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .arrow
  · simp only [present, if_true] at result
    cases clauseResult : returnClause input with
    | invariant error => simp [clauseResult] at result
    | reject failure rejected => simp [clauseResult] at result
    | ok clause afterClause =>
        simp only [clauseResult, pure] at result
        cases result
        exact .present (returnClause_success_ordinary_sound clauseResult)
  · have absent : isSymbol input .arrow = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .arrow absent)

/-- Optional returns reject only in the preferred arrow branch's names. -/
theorem returns_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : returns input = .reject failure rejected) :
    DeclarativeGrammar.YulReturnsRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold returns getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .arrow
  · simp only [present, if_true] at result
    rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .yulStatement present with
      ⟨arrow, arrowResult⟩
    unfold returnClause at result
    simp only [bind, arrowResult] at result
    cases namesResult : yulNames { input with cursor := input.cursor + 1 } with
    | invariant error => simp [namesResult] at result
    | ok names afterNames => simp [namesResult, pure] at result
    | reject namesFailure namesRejected =>
        simp only [namesResult] at result
        cases result
        exact .namesRejected arrow.span
          (symbol_success_exactTokenParses .arrow .yulStatement arrowResult)
          (yulNames_reject_sound namesResult)
  · have absent : isSymbol input .arrow = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

end YulControl

end Solcore.Syntax.Parser

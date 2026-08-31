import Solcore.Syntax.Parser.Yul.ControlProperties
import Solcore.Syntax.Parser.Yul.NamesTotalityProperties

/-! Totality for inline-Yul function parameter and return-name syntax. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem yulParameters_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ parameters next, yulParameters input = .ok parameters next) ∨
    (∃ failure next, yulParameters input = .reject failure next) :=
  delimited_ordinary .leftParen .rightParen true yulName .yulStatement .yul
    yulName_elementTotalityContract input inputValid

theorem yulParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulParameters :=
  yulParameters_ordinary

theorem yulParameters_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    yulParameters input ≠ .invariant error :=
  yulParameters_invariantFreeOnValid.ne_invariant input inputValid error

theorem yulParameters_elementTotalityContract :
    ElementTotalityContract yulParameters := {
  validFor := yulParameters_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := yulParameters_preservesTokenWindow
  cursorLtOnSuccess := yulParameters_cursor_lt_onSuccess
  invariantFree := yulParameters_invariantFreeOnValid.ne_invariant
}

theorem yulReturnClause_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ clause next, YulControl.returnClause input = .ok clause next) ∨
    (∃ failure next,
      YulControl.returnClause input = .reject failure next) := by
  rcases (symbol_ordinary .arrow .yulStatement) input with
    ⟨arrow, afterArrow, arrowResult⟩ |
    ⟨failure, rejected, arrowResult⟩
  · have arrowReply := symbol_validFor .arrow .yulStatement input inputValid
    rw [arrowResult] at arrowReply
    rcases yulNames_invariantFreeOnValid afterArrow arrowReply.2.1 with
      ⟨names, next, namesResult⟩ | ⟨failure, rejected, namesResult⟩
    · exact Or.inl ⟨{
          span := SourceSpan.cover arrow.span names.span
          value := { arrow := arrow.span, names := names.names }
        }, next, by
          simp only [YulControl.returnClause, bind, arrowResult, namesResult,
            pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [YulControl.returnClause, bind, arrowResult, namesResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [YulControl.returnClause, bind, arrowResult]⟩

theorem yulReturnClause_invariantFreeOnValid :
    Parser.InvariantFreeOnValid YulControl.returnClause :=
  yulReturnClause_ordinary

theorem yulReturnClause_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    YulControl.returnClause input ≠ .invariant error :=
  yulReturnClause_invariantFreeOnValid.ne_invariant input inputValid error

private theorem yulReturnClause_weakValidFor :
    YulControl.returnClause.ValidFor (fun _ _ => True) := by
  unfold YulControl.returnClause
  apply Parser.bind_validFor (symbol_validFor .arrow .yulStatement)
  intro arrow
  apply Parser.bind_validFor yulNames_validFor
  intro names
  exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)

private theorem yulReturnClause_preservesTokenWindow :
    Parser.PreservesTokenWindow YulControl.returnClause := by
  unfold YulControl.returnClause
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .arrow .yulStatement)
  intro arrow
  apply Parser.bind_preservesTokenWindow yulNames_preservesTokenWindow
  intro names
  exact Parser.pure_preservesTokenWindow _

theorem yulReturnClause_cursor_lt_onSuccess
    {input next : State} {clause : YulReturnClause}
    (parsed : YulControl.returnClause input = .ok clause next) :
    input.cursor < next.cursor := by
  unfold YulControl.returnClause at parsed
  simp only [bind] at parsed
  cases arrowResult : symbol .arrow .yulStatement input with
  | reject failure rejected => simp [arrowResult] at parsed
  | invariant error => simp [arrowResult] at parsed
  | ok arrow afterArrow =>
      simp only [arrowResult] at parsed
      cases namesResult : yulNames afterArrow with
      | reject failure rejected => simp [namesResult] at parsed
      | invariant error => simp [namesResult] at parsed
      | ok names afterNames =>
          simp only [namesResult, pure] at parsed
          cases parsed
          exact Nat.lt_trans
            (acceptToken_cursor_lt_onSuccess (.symbol .arrow) .yulStatement
              (· == .symbol .arrow) arrowResult)
            (yulNames_cursor_lt_onSuccess namesResult)

theorem yulReturnClause_elementTotalityContract :
    ElementTotalityContract YulControl.returnClause := {
  validFor := yulReturnClause_weakValidFor
  preservesTokenWindow := yulReturnClause_preservesTokenWindow
  cursorLtOnSuccess := yulReturnClause_cursor_lt_onSuccess
  invariantFree := yulReturnClause_invariantFreeOnValid.ne_invariant
}

theorem yulReturns_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ returns next, YulControl.returns input = .ok returns next) ∨
    (∃ failure next, YulControl.returns input = .reject failure next) := by
  by_cases present : isSymbol input .arrow
  · rcases yulReturnClause_ordinary input inputValid with
      ⟨clause, next, clauseResult⟩ | ⟨failure, rejected, clauseResult⟩
    · exact Or.inl ⟨some clause, next, by
        simp only [YulControl.returns, getState, bind, present, ↓reduceIte,
          clauseResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [YulControl.returns, getState, bind, present, ↓reduceIte,
          clauseResult]⟩
  · have absent : isSymbol input .arrow = false := by
      cases found : isSymbol input .arrow with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [YulControl.returns, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem yulReturns_invariantFreeOnValid :
    Parser.InvariantFreeOnValid YulControl.returns :=
  yulReturns_ordinary

theorem yulReturns_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    YulControl.returns input ≠ .invariant error :=
  yulReturns_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser

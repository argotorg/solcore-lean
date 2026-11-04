import Solcore.Syntax.Grammar.Yul
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.YulStatementSoundness
import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Syntax.Parser.Internal.YulExpressionSoundness
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.YulBlockSoundness

/-!
Totality of the parsers of Yul expressions and statements: on valid input they make
progress and end in an ordinary outcome.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.YulStatementCoreLookaheadProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.BlockFuelTotalityProperties
/-! Fuel-aware totality for braced inline-Yul statement sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeYulBlock_ordinary (opening : Token)
    (bodyRev : List YulStmt) :
    Parser.Ordinary (closeYulBlock opening bodyRev) := by
  intro input
  rcases (symbol_ordinary .rightBrace .yulStatement) input with
    ⟨closing, next, closingResult⟩ | ⟨failure, rejected, closingResult⟩
  · exact Or.inl ⟨{
        span := SourceSpan.cover opening.span closing.span
        body := bodyRev.reverse
      }, next, by
        unfold closeYulBlock
        simp only [closingResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      unfold closeYulBlock
      simp only [closingResult]⟩

/-- Loop and recursive-statement fuel jointly exclude every block invariant. -/
theorem yulBlockItems_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (opening : Token) :
    ∀ loopFuel bodyRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < statementFuel →
      (∃ body final,
        yulBlockItems statement opening loopFuel bodyRev input =
          .ok body final) ∨
      (∃ failure final,
        yulBlockItems statement opening loopFuel bodyRev input =
          .reject failure final) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro bodyRev input inputValid loopAdequate statementAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro bodyRev input inputValid loopAdequate statementAdequate
      unfold yulBlockItems
      split
      · exact closeYulBlock_ordinary opening bodyRev input
      · split
        · have atEnd : input.atEnd = true := by assumption
          have cursorAtEnd : input.window.endIndex ≤ input.cursor := by
            simpa [State.atEnd] using atEnd
          have peekNone : input.peek? = none := by
            unfold State.peek?
            simp [Nat.not_lt_of_ge cursorAtEnd]
          cases closingResult : symbol .rightBrace .yulStatement input with
          | ok closing next =>
              simp [symbol, acceptToken, peekNone, rejectAt] at closingResult
          | reject failure rejected =>
              exact Or.inr ⟨failure, rejected, rfl⟩
          | invariant error =>
              exact False.elim
                ((symbol_ordinary .rightBrace .yulStatement).ne_invariant
                  input error closingResult)
        · cases statementResult : statement input with
          | invariant error =>
              exact False.elim
                (contract.ne_invariant input inputValid statementAdequate
                  error statementResult)
          | reject failure rejected =>
              exact Or.inr ⟨failure, rejected, rfl⟩
          | ok value next =>
              have replyValid := contract.validFor input inputValid
              rw [statementResult] at replyValid
              have replyWindow := contract.preservesTokenWindow input
              rw [statementResult] at replyWindow
              have progress := contract.cursorLtOnSuccess statementResult
              have nextLoopAdequate : next.remainingCount < loopFuel :=
                remainingCount_lt_after_strict_progress replyValid.2.1
                  replyWindow.2 progress loopAdequate
              have nextStatementAdequate :
                  next.remainingCount < statementFuel :=
                remainingCount_lt_of_cursor_le replyWindow.2
                  (Nat.le_of_lt progress) statementAdequate
              dsimp only
              split
              · exact inductionHypothesis (value :: bodyRev) next
                  replyValid.2.1 nextLoopAdequate nextStatementAdequate
              · omega

theorem yulBlockItems_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (opening : Token) (loopFuel : Nat) (bodyRev : List YulStmt)
    (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (statementAdequate : input.remainingCount < statementFuel)
    (error : ParserInvariantError) :
    yulBlockItems statement opening loopFuel bodyRev input ≠
      .invariant error := by
  intro failed
  rcases yulBlockItems_ordinary_of_statementFuel statement statementFuel
      contract opening loopFuel bodyRev input inputValid loopAdequate
        statementAdequate with
    ⟨body, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- The opening brace supplies the one extra unit of statement fuel. -/
theorem yulBlock_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1) :
    (∃ body final, yulBlock statement input = .ok body final) ∨
    (∃ failure final,
      yulBlock statement input = .reject failure final) := by
  rcases (symbol_ordinary .leftBrace .yulStatement) input with
    ⟨opening, afterOpening, openingResult⟩ |
    ⟨failure, rejected, openingResult⟩
  · have openingReply := symbol_validFor .leftBrace .yulStatement input
      inputValid
    rw [openingResult] at openingReply
    have openingWindow :=
      symbol_preservesTokenWindow .leftBrace .yulStatement input
    rw [openingResult] at openingWindow
    have openingProgress : input.cursor < afterOpening.cursor :=
      acceptToken_cursor_lt_onSuccess (.symbol .leftBrace) .yulStatement
        (· == .symbol .leftBrace) openingResult
    have statementAdequate :
        afterOpening.remainingCount < statementFuel :=
      remainingCount_lt_after_strict_progress openingReply.2.1
        openingWindow.2 openingProgress adequate
    simpa only [yulBlock, openingResult] using
      yulBlockItems_ordinary_of_statementFuel statement statementFuel
        contract opening (afterOpening.remainingCount + 1) [] afterOpening
          openingReply.2.1 (by omega) statementAdequate
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulBlock, openingResult]⟩

theorem yulBlock_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1)
    (error : ParserInvariantError) :
    yulBlock statement input ≠ .invariant error := by
  intro failed
  rcases yulBlock_ordinary_of_statementFuel statement statementFuel contract
      input inputValid adequate with
    ⟨body, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Package a recursive-fuel Yul block for statement-layer recursion. -/
theorem yulBlock_fuelElementTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (yulBlock statement)
      (statementFuel + 1) := {
  validFor := (yulBlock_validFor (fun _ _ => True) statement
    contract.validFor
      contract.preservesTokenWindow.preservesTokensOnSuccess).mono
        (fun _ _ _ => trivial)
  preservesTokenWindow := yulBlock_preservesTokenWindow statement
    contract.preservesTokenWindow
  cursorLtOnSuccess := yulBlock_cursor_lt_onSuccess statement
    contract.preservesTokenWindow.preservesTokensOnSuccess
  ordinary := yulBlock_ordinary_of_statementFuel statement statementFuel
    contract
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.LeafTotalityProperties
/-! Totality contracts for non-recursive inline-Yul leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem yulName_ordinary : Parser.Ordinary yulName := by
  intro input
  cases result : yulName input with
  | ok name next => exact Or.inl ⟨name, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold yulName at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          rcases token with ⟨span, kind⟩
          cases kind <;> simp only [found] at result
          all_goals try { unfold rejectAt at result; contradiction }
          case identifier text =>
            exact False.elim
              ((identifier_ordinary .yulExpression).ne_invariant
                input error result)
          case yulIdentifier text => contradiction
          case keyword keyword =>
            cases keyword <;> simp only at result
            all_goals try { unfold rejectAt at result; contradiction }
            case fallbackKw => contradiction
          case symbol symbol =>
            cases symbol <;> simp only at result
            all_goals try { unfold rejectAt at result; contradiction }
            case underscore => contradiction

theorem yulLiteral_ordinary : Parser.Ordinary yulLiteral := by
  intro input
  cases result : yulLiteral input with
  | ok literal next => exact Or.inl ⟨literal, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold yulLiteral at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          rcases token with ⟨span, kind⟩
          cases kind <;> simp [found, rejectAt] at result
          case keyword keyword =>
            cases keyword <;> simp only at result
            all_goals try { unfold rejectAt at result; contradiction }
            all_goals contradiction

theorem rejectedMeta_ordinary : Parser.Ordinary rejectedMeta := by
  intro input
  cases result : rejectedMeta input with
  | ok expression next => exact Or.inl ⟨expression, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold rejectedMeta at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          rcases token with ⟨span, kind⟩
          cases kind <;> simp [found, rejectAt] at result

theorem yulName_cursor_lt_onSuccess {input next : State}
    {name : YulIdentifier} (parsed : yulName input = .ok name next) :
    input.cursor < next.cursor := by
  rw [(yulName_ok_state_shape parsed).choose_spec.2.2.2]
  omega

theorem yulLiteral_cursor_lt_onSuccess {input next : State}
    {literal : YulLiteral} (parsed : yulLiteral input = .ok literal next) :
    input.cursor < next.cursor := by
  rw [yulLiteral_ok_state_shape parsed]
  simp

theorem yulName_elementTotalityContract :
    ElementTotalityContract yulName := {
  validFor := yulName_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := yulName_preservesTokenWindow
  cursorLtOnSuccess := yulName_cursor_lt_onSuccess
  invariantFree := fun input _ error =>
    yulName_ordinary.ne_invariant input error
}

theorem yulLiteral_elementTotalityContract :
    ElementTotalityContract yulLiteral := {
  validFor := yulLiteral_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := yulLiteral_preservesTokenWindow
  cursorLtOnSuccess := yulLiteral_cursor_lt_onSuccess
  invariantFree := fun input _ error =>
    yulLiteral_ordinary.ne_invariant input error
}

theorem rejectedMeta_elementTotalityContract :
    ElementTotalityContract rejectedMeta := {
  validFor := rejectedMeta_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := rejectedMeta_preservesTokenWindow
  cursorLtOnSuccess := rejectedMeta_cursor_lt_onSuccess
  invariantFree := fun input _ error =>
    rejectedMeta_ordinary.ne_invariant input error
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.NamesTotalityProperties
/-! Totality for nonempty inline-Yul name sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem finishYulNames_ordinary (first last : YulIdentifier)
    (tailRev : List YulIdentifier) :
    Parser.Ordinary (finishYulNames first last tailRev) := by
  intro input
  exact Or.inl ⟨_, input, rfl⟩

theorem yulNamesTail_ordinary_of_remainingCount_lt
    (first : YulIdentifier) :
    ∀ fuel last tailRev input,
      input.ValidFor → input.remainingCount < fuel →
      (∃ names next,
        yulNamesTail first fuel last tailRev input = .ok names next) ∨
      (∃ failure next,
        yulNamesTail first fuel last tailRev input = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input inputValid adequate
      omega
  | succ fuel inductionHypothesis =>
      intro last tailRev input inputValid adequate
      unfold yulNamesTail
      split
      · cases commaResult : symbol .comma .yulStatement input with
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .comma .yulStatement input error
                commaResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok comma afterComma =>
            have commaReply := symbol_validFor .comma .yulStatement
              input inputValid
            rw [commaResult] at commaReply
            have commaWindow := symbol_preservesTokenWindow .comma
              .yulStatement input
            rw [commaResult] at commaWindow
            have commaProgress := acceptToken_cursor_lt_onSuccess
              (.symbol .comma) .yulStatement (· == .symbol .comma)
                commaResult
            have afterCommaAdequate : afterComma.remainingCount < fuel :=
              remainingCount_lt_after_strict_progress commaReply.2.1
                commaWindow.2 commaProgress adequate
            cases nameResult : yulName afterComma with
            | invariant error =>
                exact False.elim
                  (yulName_ordinary.ne_invariant afterComma error nameResult)
            | reject failure rejected =>
                exact Or.inr ⟨failure, rejected, by
                  simp only [nameResult]⟩
            | ok name next =>
                have nameReply := yulName_validFor afterComma commaReply.2.1
                rw [nameResult] at nameReply
                have nameWindow := yulName_preservesTokenWindow afterComma
                rw [nameResult] at nameWindow
                have nextAdequate : next.remainingCount < fuel :=
                  remainingCount_lt_of_cursor_le nameWindow.2
                    (Nat.le_of_lt (yulName_cursor_lt_onSuccess nameResult))
                      afterCommaAdequate
                rcases inductionHypothesis name (name :: tailRev) next
                    nameReply.2.1 nextAdequate with
                  ⟨names, final, recursiveResult⟩ |
                  ⟨failure, rejected, recursiveResult⟩
                · exact Or.inl ⟨names, final, by
                    simp only [nameResult]
                    exact recursiveResult⟩
                · exact Or.inr ⟨failure, rejected, by
                    simp only [nameResult]
                    exact recursiveResult⟩
      · exact finishYulNames_ordinary first last tailRev input

theorem yulNames_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulNames := by
  intro input inputValid
  rcases yulName_ordinary input with
    ⟨first, next, firstResult⟩ | ⟨failure, rejected, firstResult⟩
  · have firstReply := yulName_validFor input inputValid
    rw [firstResult] at firstReply
    rcases yulNamesTail_ordinary_of_remainingCount_lt first
        (next.remainingCount + 1) first [] next firstReply.2.1 (by omega) with
      ⟨names, final, tailResult⟩ | ⟨failure, rejected, tailResult⟩
    · exact Or.inl ⟨names, final, by
        simp only [yulNames, firstResult]
        exact tailResult⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [yulNames, firstResult]
        exact tailResult⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulNames, firstResult]⟩

theorem yulNames_cursor_lt_onSuccess {input next : State}
    {names : YulNameSequence} (parsed : yulNames input = .ok names next) :
    input.cursor < next.cursor :=
  (yulNames_ok_state_shape parsed).choose_spec.2.2.2

theorem yulNames_elementTotalityContract :
    ElementTotalityContract yulNames := {
  validFor := yulNames_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := yulNames_preservesTokenWindow
  cursorLtOnSuccess := yulNames_cursor_lt_onSuccess
  invariantFree := yulNames_invariantFreeOnValid.ne_invariant
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.SignatureTotalityProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.ExpressionFuelTotalityProperties
/-! Fuel-aware totality for one inline-Yul expression layer and recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional call arguments inherit bounded delimited totality. -/
theorem optionalYulCallArguments_ordinary_of_elementFuel
    (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ arguments next,
      optionalYulCallArguments nested input = .ok arguments next) ∨
    (∃ failure next,
      optionalYulCallArguments nested input = .reject failure next) := by
  by_cases present : isSymbol input .leftParen
  · rcases delimited_ordinary_of_elementFuel .leftParen .rightParen true
        nested .yulExpression .yul nestedFuel contract input inputValid adequate
      with ⟨arguments, next, argumentsResult⟩ |
        ⟨failure, rejected, argumentsResult⟩
    · exact Or.inl ⟨some arguments, next, by
        simp only [optionalYulCallArguments, present, ↓reduceIte, orElse,
          bind, argumentsResult, pure]⟩
    · exact Or.inl ⟨none, input, by
        simp only [optionalYulCallArguments, present, ↓reduceIte, orElse,
          bind, argumentsResult, pure]⟩
  · have absent : isSymbol input .leftParen = false := by
      cases found : isSymbol input .leftParen with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalYulCallArguments, absent, Bool.false_eq_true,
        ↓reduceIte]⟩

theorem optionalYulCallArguments_ne_invariant_of_elementFuel
    (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    optionalYulCallArguments nested input ≠ .invariant error := by
  intro failed
  rcases optionalYulCallArguments_ordinary_of_elementFuel nested nestedFuel
      contract input inputValid adequate with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- One non-recovering Yul layer is ordinary below the recursive fuel bound. -/
theorem yulExpressionCore_ordinary_of_elementFuel
    (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next,
      yulExpressionCore nested input = .ok expression next) ∨
    (∃ failure next,
      yulExpressionCore nested input = .reject failure next) := by
  unfold yulExpressionCore
  split
  · rcases yulLiteral_ordinary input with
      ⟨literal, next, literalResult⟩ | ⟨failure, rejected, literalResult⟩
    · exact Or.inl ⟨{
          span := literal.span
          value := .literal literal
        }, next, by simp only [literalResult]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [literalResult]⟩
  · split
    · rcases yulName_ordinary input with
        ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
      · have nameValid := yulName_validFor input inputValid
        rw [nameResult] at nameValid
        have nameWindow := yulName_preservesTokenWindow input
        rw [nameResult] at nameWindow
        have afterNameAdequate : afterName.remainingCount < nestedFuel :=
          remainingCount_lt_after_strict_progress nameValid.2.1 nameWindow.2
            (yulName_cursor_lt_onSuccess nameResult) adequate
        rcases optionalYulCallArguments_ordinary_of_elementFuel nested
            nestedFuel contract afterName nameValid.2.1 (by omega) with
          ⟨arguments, next, argumentsResult⟩ |
          ⟨failure, rejected, argumentsResult⟩
        · cases arguments with
          | none => exact Or.inl ⟨{
              span := name.span
              value := .identifier name
            }, next, by
              simp only [nameResult, argumentsResult]⟩
          | some arguments => exact Or.inl ⟨{
              span := SourceSpan.cover name.span arguments.span
              value := .call name arguments
            }, next, by
              simp only [nameResult, argumentsResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [nameResult, argumentsResult]⟩
      · exact Or.inr ⟨failure, rejected, by simp only [nameResult]⟩
    · split <;> try { exact rejectedMeta_ordinary input }
      exact Or.inr ⟨_, input, rfl⟩

theorem yulExpressionCore_ne_invariant_of_elementFuel
    (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    yulExpressionCore nested input ≠ .invariant error := by
  intro failed
  rcases yulExpressionCore_ordinary_of_elementFuel nested nestedFuel contract
      input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

namespace YulExpressionInternals

/-- More fuel than remaining tokens makes recovery terminate successfully. -/
theorem recoverAux_exists_ok_of_remainingCount_lt
    (first last : SourceSpan) :
    ∀ fuel input, input.remainingCount < fuel →
      ∃ expression final,
        recoverAux first last fuel input = .ok expression final := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      intro input adequate
      omega
  | succ fuel inductionHypothesis =>
      intro input adequate
      unfold recoverAux
      split
      · exact ⟨_, _, rfl⟩
      · cases advanced : input.advance? with
        | none => exact ⟨_, _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            change ∃ expression final,
              recoverAux first token.span fuel next = .ok expression final
            apply inductionHypothesis token.span next
            unfold State.advance? at advanced
            cases found : input.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                have cursorBeforeEnd :=
                  State.cursor_lt_endIndex_of_peek?_eq_some found
                simp only [State.remainingCount] at adequate ⊢
                omega

/-- The recovery fuel selected by `layer` is always sufficient. -/
theorem recoverAux_production_exists_ok
    (first last : SourceSpan) (input : State) :
    ∃ expression final,
      recoverAux first last (input.remainingCount + 1) input =
        .ok expression final :=
  recoverAux_exists_ok_of_remainingCount_lt first last
    (input.remainingCount + 1) input (by omega)

theorem recoverAux_ne_invariant_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (input : State)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    recoverAux first last fuel input ≠ .invariant error := by
  intro failed
  rcases recoverAux_exists_ok_of_remainingCount_lt first last fuel input
      adequate with ⟨expression, final, result⟩
  rw [result] at failed
  contradiction

/-- Recovery does not reintroduce invariants after an ordinary core rejection. -/
theorem layer_ordinary_of_elementFuel
    (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next, layer nested input = .ok expression next) ∨
    (∃ failure next, layer nested input = .reject failure next) := by
  rcases yulExpressionCore_ordinary_of_elementFuel nested nestedFuel contract
      input inputValid adequate with
    ⟨expression, next, coreResult⟩ |
    ⟨failure, failedState, coreResult⟩
  · exact Or.inl ⟨expression, next, by simp only [layer, coreResult]⟩
  · let rewound := { failedState with cursor := input.cursor }
    by_cases boundary : isBoundary rewound
    · exact Or.inr ⟨failure, rewound, by
        simp only [layer, coreResult, rewound, boundary, ↓reduceIte]⟩
    · cases advanced : rewound.advance? with
      | none => exact Or.inr ⟨failure, rewound, by
          simp only [layer, coreResult, rewound, boundary,
            Bool.false_eq_true, ↓reduceIte, advanced]⟩
      | some pair =>
          rcases pair with ⟨token, afterToken⟩
          rcases recoverAux_production_exists_ok token.span token.span
              (afterToken.emit failure.toDiagnostic) with
            ⟨recovered, final, recoveredResult⟩
          have recoveredAtProductionFuel :
              recoverAux token.span token.span
                (afterToken.remainingCount + 1)
                (afterToken.emit failure.toDiagnostic) =
                  .ok recovered final := by
            have emitRemaining :
                (afterToken.emit failure.toDiagnostic).remainingCount =
                  afterToken.remainingCount := rfl
            rw [emitRemaining] at recoveredResult
            exact recoveredResult
          exact Or.inl ⟨recovered, final, by
            simp only [layer, coreResult, rewound, boundary,
              Bool.false_eq_true, ↓reduceIte, advanced,
              recoveredAtProductionFuel]⟩

theorem layer_ne_invariant_of_elementFuel
    (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    layer nested input ≠ .invariant error := by
  intro failed
  rcases layer_ordinary_of_elementFuel nested nestedFuel contract input
      inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end YulExpressionInternals

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.ExpressionRecursiveTotalityProperties
/-! Recursive-family and public totality for inline-Yul expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulAdvance_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

namespace YulExpressionInternals

/-- Every successful recovering layer consumes at least one input token. -/
theorem layer_cursor_lt_onSuccess
    (nested : Parser YulExpr) {input final : State} {value : YulExpr}
    (parsed : layer nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold layer at parsed
  cases coreResult : yulExpressionCore nested input with
  | invariant error => simp [coreResult] at parsed
  | ok expression next =>
      simp only [coreResult] at parsed
      cases parsed
      exact yulExpressionCore_cursor_lt_onSuccess nested coreResult
  | reject failure failedState =>
      simp only [coreResult] at parsed
      let rewound := { failedState with cursor := input.cursor }
      split at parsed
      · contradiction
      · cases advanced : rewound.advance? with
        | none =>
            rw [advanced] at parsed
            contradiction
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            rw [advanced] at parsed
            have recoveryMonotone := recoverAux_cursorMonotoneOnSuccess
              token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic) value final parsed
            have shape := yulAdvance_state_shape advanced
            have afterCursor : afterToken.cursor = input.cursor + 1 := by
              simp [shape, rewound]
            have emittedCursor :
                (afterToken.emit failure.toDiagnostic).cursor =
                  afterToken.cursor := rfl
            rw [emittedCursor, afterCursor] at recoveryMonotone
            omega

/-- Strict progress also holds uniformly across the recursive fuel family. -/
theorem withFuel_cursor_lt_onSuccess
    (fuel : Nat) {input final : State} {value : YulExpr}
    (parsed : withFuel fuel input = .ok value final) :
    input.cursor < final.cursor := by
  cases fuel with
  | zero =>
      unfold withFuel at parsed
      contradiction
  | succ fuel =>
      exact layer_cursor_lt_onSuccess (withFuel fuel) parsed

/-- Each recursive parser is total exactly below its own fuel index. -/
theorem withFuel_fuelElementTotalityContract : ∀ fuel,
    FuelElementTotalityContract (withFuel fuel) fuel := by
  intro fuel
  induction fuel with
  | zero =>
      exact {
        validFor := (withFuel_validFor 0).mono (fun _ _ _ => trivial)
        preservesTokenWindow := withFuel_preservesTokenWindow 0
        cursorLtOnSuccess := withFuel_cursor_lt_onSuccess 0
        ordinary := by
          intro input inputValid adequate
          omega
      }
  | succ fuel inductionHypothesis =>
      exact {
        validFor := (withFuel_validFor (fuel + 1)).mono
          (fun _ _ _ => trivial)
        preservesTokenWindow := withFuel_preservesTokenWindow (fuel + 1)
        cursorLtOnSuccess := withFuel_cursor_lt_onSuccess (fuel + 1)
        ordinary := by
          intro input inputValid adequate
          simpa only [withFuel] using
            layer_ordinary_of_elementFuel (withFuel fuel) fuel
              inductionHypothesis input inputValid
                (by simpa [Nat.succ_eq_add_one] using adequate)
      }

theorem withFuel_ordinary_of_remainingCount_lt
    (fuel : Nat) (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel) :
    (∃ expression next, withFuel fuel input = .ok expression next) ∨
    (∃ failure next, withFuel fuel input = .reject failure next) :=
  (withFuel_fuelElementTotalityContract fuel).ordinary input inputValid
    adequate

theorem withFuel_ne_invariant_of_remainingCount_lt
    (fuel : Nat) (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    withFuel fuel input ≠ .invariant error :=
  (withFuel_fuelElementTotalityContract fuel).ne_invariant input inputValid
    adequate error

end YulExpressionInternals

/-- Production fuel makes the public recursive Yul parser ordinary. -/
theorem yulExpression_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulExpression := by
  intro input inputValid
  unfold yulExpression
  exact YulExpressionInternals.withFuel_ordinary_of_remainingCount_lt
    (input.remainingCount + 1) input inputValid (by omega)

theorem yulExpression_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    yulExpression input ≠ .invariant error :=
  yulExpression_invariantFreeOnValid.ne_invariant input inputValid error

/-- Every successful public Yul expression consumes its leading token. -/
theorem yulExpression_cursor_lt_onSuccess
    {input final : State} {value : YulExpr}
    (parsed : yulExpression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulExpression at parsed
  exact YulExpressionInternals.withFuel_cursor_lt_onSuccess
    (input.remainingCount + 1) parsed

/-- Public inline-Yul expressions satisfy the complete element contract. -/
theorem yulExpression_elementTotalityContract :
    ElementTotalityContract yulExpression := {
  validFor := yulExpression_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := yulExpression_preservesTokenWindow
  cursorLtOnSuccess := yulExpression_cursor_lt_onSuccess
  invariantFree := fun input inputValid error =>
    yulExpression_ne_invariant input inputValid error
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.StatementLeafTotalityProperties
/-! Valid-input totality for the non-recursive inline-Yul statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional `let` initialization is ordinary on every valid input. -/
theorem yulLetInitializer_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulLetInitializer := by
  unfold yulLetInitializer
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases present : isSymbol observed .colonEqual
  · simp only [present, if_true]
    apply Parser.bind_invariantFreeOnValid
      (symbol_validFor .colonEqual .yulStatement)
      (symbol_ordinary .colonEqual .yulStatement).invariantFreeOnValid
    intro marker
    apply Parser.bind_invariantFreeOnValid yulExpression_validFor
      yulExpression_invariantFreeOnValid
    intro expression
    exact Parser.pure_invariantFreeOnValid (some expression)
  · simp only [present]
    exact Parser.pure_invariantFreeOnValid none

theorem yulLetInitializer_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ initializer next,
      yulLetInitializer input = .ok initializer next) ∨
    (∃ failure next, yulLetInitializer input = .reject failure next) :=
  yulLetInitializer_invariantFreeOnValid input inputValid

theorem yulLetInitializer_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    yulLetInitializer input ≠ .invariant error :=
  yulLetInitializer_invariantFreeOnValid.ne_invariant input inputValid error

/-- A non-recursive Yul `let` statement is ordinary on valid input. -/
theorem yulLetStatement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulLetStatement := by
  unfold yulLetStatement
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .letKw .yulStatement)
    (keyword_ordinary .letKw .yulStatement).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid yulNames_validFor
    yulNames_invariantFreeOnValid
  intro names
  apply Parser.bind_invariantFreeOnValid yulLetInitializer_validFor
    yulLetInitializer_invariantFreeOnValid
  intro initializer
  exact Parser.pure_invariantFreeOnValid _

theorem yulLetStatement_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ statement next, yulLetStatement input = .ok statement next) ∨
    (∃ failure next, yulLetStatement input = .reject failure next) :=
  yulLetStatement_invariantFreeOnValid input inputValid

theorem yulLetStatement_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    yulLetStatement input ≠ .invariant error :=
  yulLetStatement_invariantFreeOnValid.ne_invariant input inputValid error

/-- A nonempty Yul assignment is ordinary on valid input. -/
theorem yulAssignment_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulAssignment := by
  unfold yulAssignment
  apply Parser.bind_invariantFreeOnValid yulNames_validFor
    yulNames_invariantFreeOnValid
  intro names
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .colonEqual .yulStatement)
    (symbol_ordinary .colonEqual .yulStatement).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid yulExpression_validFor
    yulExpression_invariantFreeOnValid
  intro value
  exact Parser.pure_invariantFreeOnValid _

theorem yulAssignment_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ statement next, yulAssignment input = .ok statement next) ∨
    (∃ failure next, yulAssignment input = .reject failure next) :=
  yulAssignment_invariantFreeOnValid input inputValid

theorem yulAssignment_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    yulAssignment input ≠ .invariant error :=
  yulAssignment_invariantFreeOnValid.ne_invariant input inputValid error

/-- Lifting a Yul expression into statement position preserves totality. -/
theorem yulExpressionStatement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulExpressionStatement := by
  unfold yulExpressionStatement
  apply Parser.bind_invariantFreeOnValid yulExpression_validFor
    yulExpression_invariantFreeOnValid
  intro expression
  exact Parser.pure_invariantFreeOnValid _

theorem yulExpressionStatement_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ statement next,
      yulExpressionStatement input = .ok statement next) ∨
    (∃ failure next,
      yulExpressionStatement input = .reject failure next) :=
  yulExpressionStatement_invariantFreeOnValid input inputValid

theorem yulExpressionStatement_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    yulExpressionStatement input ≠ .invariant error :=
  yulExpressionStatement_invariantFreeOnValid.ne_invariant input inputValid
    error

private theorem yulReturnArguments_invariantFreeOnValid :
    Parser.InvariantFreeOnValid
      (delimited .leftParen .rightParen true yulExpression
        .yulExpression .yul) :=
  delimited_ordinary .leftParen .rightParen true yulExpression
    .yulExpression .yul yulExpression_elementTotalityContract

/-- Source-level `return(...)` is ordinary on valid input. -/
theorem yulReturnBuiltin_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulReturnBuiltin := by
  unfold yulReturnBuiltin
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .returnKw .yulStatement)
    (keyword_ordinary .returnKw .yulStatement).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    (delimited_validFor YulExpr.ValidFor .leftParen .rightParen true
      yulExpression .yulExpression .yul yulExpression_validFor
        yulExpression_preservesTokensOnSuccess)
    yulReturnArguments_invariantFreeOnValid
  intro arguments
  exact Parser.pure_invariantFreeOnValid _

theorem yulReturnBuiltin_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ statement next, yulReturnBuiltin input = .ok statement next) ∨
    (∃ failure next, yulReturnBuiltin input = .reject failure next) :=
  yulReturnBuiltin_invariantFreeOnValid input inputValid

theorem yulReturnBuiltin_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    yulReturnBuiltin input ≠ .invariant error :=
  yulReturnBuiltin_invariantFreeOnValid.ne_invariant input inputValid error

/-- Keyword-only control statements are ordinary on valid input. -/
theorem yulControlToken_invariantFreeOnValid (value : HardKeyword)
    (result : YulStmtValue) :
    Parser.InvariantFreeOnValid (yulControlToken value result) := by
  unfold yulControlToken
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor value .yulStatement)
    (keyword_ordinary value .yulStatement).invariantFreeOnValid
  intro marker
  exact Parser.pure_invariantFreeOnValid _

theorem yulControlToken_ordinary (value : HardKeyword)
    (result : YulStmtValue) (input : State) (inputValid : input.ValidFor) :
    (∃ statement next,
      yulControlToken value result input = .ok statement next) ∨
    (∃ failure next,
      yulControlToken value result input = .reject failure next) :=
  yulControlToken_invariantFreeOnValid value result input inputValid

theorem yulControlToken_ne_invariant (value : HardKeyword)
    (result : YulStmtValue) (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    yulControlToken value result input ≠ .invariant error :=
  (yulControlToken_invariantFreeOnValid value result).ne_invariant input
    inputValid error

/-- Syntax/state contracts paired with valid-input totality for Yul leaves. -/
structure YulStatementTotalityContract (parser : Parser YulStmt) : Prop
    extends YulStatementParserContracts parser where
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  invariantFree : Parser.InvariantFreeOnValid parser

namespace YulStatementTotalityContract

theorem ne_invariant {parser : Parser YulStmt}
    (contract : YulStatementTotalityContract parser)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error :=
  contract.invariantFree.ne_invariant input inputValid error

end YulStatementTotalityContract

theorem yulLetStatement_totalityContract :
    YulStatementTotalityContract yulLetStatement := {
  toYulStatementParserContracts := {
    validFor := yulLetStatement_validFor
    preservesTokens := yulLetStatement_preservesTokensOnSuccess
    cursorMonotone := yulLetStatement_cursorMonotoneOnSuccess
    startsAtToken := yulLetStatement_startsAtCurrentTokenOnSuccess
  }
  preservesTokenWindow := yulLetStatement_preservesTokenWindow
  invariantFree := yulLetStatement_invariantFreeOnValid
}

theorem yulAssignment_totalityContract :
    YulStatementTotalityContract yulAssignment := {
  toYulStatementParserContracts := {
    validFor := yulAssignment_validFor
    preservesTokens := yulAssignment_preservesTokensOnSuccess
    cursorMonotone := yulAssignment_cursorMonotoneOnSuccess
    startsAtToken := yulAssignment_startsAtCurrentTokenOnSuccess
  }
  preservesTokenWindow := yulAssignment_preservesTokenWindow
  invariantFree := yulAssignment_invariantFreeOnValid
}

theorem yulExpressionStatement_totalityContract :
    YulStatementTotalityContract yulExpressionStatement := {
  toYulStatementParserContracts := {
    validFor := yulExpressionStatement_validFor
    preservesTokens := yulExpressionStatement_preservesTokensOnSuccess
    cursorMonotone := yulExpressionStatement_cursorMonotoneOnSuccess
    startsAtToken := yulExpressionStatement_startsAtCurrentTokenOnSuccess
  }
  preservesTokenWindow := yulExpressionStatement_preservesTokenWindow
  invariantFree := yulExpressionStatement_invariantFreeOnValid
}

theorem yulReturnBuiltin_totalityContract :
    YulStatementTotalityContract yulReturnBuiltin := {
  toYulStatementParserContracts := {
    validFor := yulReturnBuiltin_validFor
    preservesTokens := yulReturnBuiltin_preservesTokensOnSuccess
    cursorMonotone := yulReturnBuiltin_cursorMonotoneOnSuccess
    startsAtToken := yulReturnBuiltin_startsAtCurrentTokenOnSuccess
  }
  preservesTokenWindow := yulReturnBuiltin_preservesTokenWindow
  invariantFree := yulReturnBuiltin_invariantFreeOnValid
}

theorem yulControlToken_totalityContract (value : HardKeyword)
    (result : YulStmtValue)
    (resultValid : ∀ file span, span.ValidFor file →
      YulStmt.ValidFor file { span, value := result }) :
    YulStatementTotalityContract (yulControlToken value result) := {
  toYulStatementParserContracts := {
    validFor := yulControlToken_validFor value result resultValid
    preservesTokens := yulControlToken_preservesTokensOnSuccess value result
    cursorMonotone := yulControlToken_cursorMonotoneOnSuccess value result
    startsAtToken := yulControlToken_startsAtCurrentTokenOnSuccess value result
  }
  preservesTokenWindow := yulControlToken_preservesTokenWindow value result
  invariantFree := yulControlToken_invariantFreeOnValid value result
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.StatementLeafStrictTotalityProperties
/-! Strict progress and complete contracts for inline-Yul statement leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_cursor_lt_onSuccess_of_first {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstStrict : ∀ {input middle : State} {value : alpha},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value,
      Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  change (match first input with
    | .ok firstValue middle => next firstValue middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue middle =>
      simp only [firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue middle value final parsed)
  | reject failure rejected => simp [firstResult] at parsed
  | invariant error => simp [firstResult] at parsed

/-- A successful `let` statement consumes its leading keyword. -/
theorem yulLetStatement_cursor_lt_onSuccess
    {input final : State} {value : YulStmt}
    (parsed : yulLetStatement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulLetStatement at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .letKw)
      .yulStatement (· == .keyword .letKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess yulNames_cursorMonotoneOnSuccess
  intro names
  apply Parser.bind_cursorMonotoneOnSuccess
    yulLetInitializer_cursorMonotoneOnSuccess
  intro initializer
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful assignment consumes its first target name. -/
theorem yulAssignment_cursor_lt_onSuccess
    {input final : State} {value : YulStmt}
    (parsed : yulAssignment input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulAssignment at parsed
  apply bind_cursor_lt_onSuccess_of_first yulNames_cursor_lt_onSuccess ?_
    parsed
  intro names
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .colonEqual .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro expression
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful expression statement consumes its expression's first token. -/
theorem yulExpressionStatement_cursor_lt_onSuccess
    {input final : State} {value : YulStmt}
    (parsed : yulExpressionStatement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulExpressionStatement at parsed
  apply bind_cursor_lt_onSuccess_of_first
    yulExpression_cursor_lt_onSuccess ?_ parsed
  intro expression
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful source-level `return(...)` consumes its keyword. -/
theorem yulReturnBuiltin_cursor_lt_onSuccess
    {input final : State} {value : YulStmt}
    (parsed : yulReturnBuiltin input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulReturnBuiltin at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .returnKw)
      .yulStatement (· == .keyword .returnKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
      yulExpression .yulExpression .yul)
  intro arguments
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Every successful keyword-only control statement consumes its keyword. -/
theorem yulControlToken_cursor_lt_onSuccess
    (keywordValue : HardKeyword) (result : YulStmtValue)
    {input final : State} {value : YulStmt}
    (parsed : yulControlToken keywordValue result input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulControlToken at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun parsedKeyword => acceptToken_cursor_lt_onSuccess
      (.keyword keywordValue) .yulStatement
        (· == .keyword keywordValue) parsedKeyword) ?_ parsed
  intro marker
  exact Parser.pure_cursorMonotoneOnSuccess _

namespace YulStatementTotalityContract

/-- Adding strict progress turns a Yul syntax contract into a loop contract. -/
theorem elementTotalityContract {parser : Parser YulStmt}
    (contract : YulStatementTotalityContract parser)
    (strict : ∀ {input final : State} {value : YulStmt},
      parser input = .ok value final → input.cursor < final.cursor) :
    ElementTotalityContract parser := {
  validFor := contract.validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := contract.preservesTokenWindow
  cursorLtOnSuccess := strict
  invariantFree := contract.invariantFree.ne_invariant
}

end YulStatementTotalityContract

theorem yulLetStatement_elementTotalityContract :
    ElementTotalityContract yulLetStatement :=
  YulStatementTotalityContract.elementTotalityContract
    yulLetStatement_totalityContract yulLetStatement_cursor_lt_onSuccess

theorem yulAssignment_elementTotalityContract :
    ElementTotalityContract yulAssignment :=
  YulStatementTotalityContract.elementTotalityContract
    yulAssignment_totalityContract yulAssignment_cursor_lt_onSuccess

theorem yulExpressionStatement_elementTotalityContract :
    ElementTotalityContract yulExpressionStatement :=
  YulStatementTotalityContract.elementTotalityContract
    yulExpressionStatement_totalityContract
      yulExpressionStatement_cursor_lt_onSuccess

theorem yulReturnBuiltin_elementTotalityContract :
    ElementTotalityContract yulReturnBuiltin :=
  YulStatementTotalityContract.elementTotalityContract
    yulReturnBuiltin_totalityContract yulReturnBuiltin_cursor_lt_onSuccess

theorem yulControlToken_elementTotalityContract
    (keywordValue : HardKeyword) (result : YulStmtValue)
    (resultValid : ∀ file span, span.ValidFor file →
      YulStmt.ValidFor file { span, value := result }) :
    ElementTotalityContract (yulControlToken keywordValue result) :=
  YulStatementTotalityContract.elementTotalityContract
    (yulControlToken_totalityContract keywordValue result resultValid)
      (yulControlToken_cursor_lt_onSuccess keywordValue result)

theorem yulLeaveControl_elementTotalityContract :
    ElementTotalityContract (yulControlToken .leaveKw .leave) :=
  yulControlToken_elementTotalityContract .leaveKw .leave
    (fun _ _ => YulStmt.ValidFor.leave)

theorem yulBreakControl_elementTotalityContract :
    ElementTotalityContract (yulControlToken .breakKw .break) :=
  yulControlToken_elementTotalityContract .breakKw .break
    (fun _ _ => YulStmt.ValidFor.break)

theorem yulContinueControl_elementTotalityContract :
    ElementTotalityContract (yulControlToken .continueKw .continue) :=
  yulControlToken_elementTotalityContract .continueKw .continue
    (fun _ _ => YulStmt.ValidFor.continue)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.StatementFallbackFuelTotalityProperties
/-! Fuel-aware totality across Yul statement fallback and termination. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Syntax/state laws paired with a bounded ordinary Yul statement parser. -/
structure FuelYulStatementTotalityContract
    (parser : Parser YulStmt) (fuel : Nat) : Prop
    extends YulStatementParserContracts parser where
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  ordinary : ∀ input, input.ValidFor → input.remainingCount < fuel →
    (∃ value next, parser input = .ok value next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace FuelYulStatementTotalityContract

/-- A Yul statement contract at a larger fuel bound proves every smaller bound. -/
theorem weaken {parser : Parser YulStmt} {smallFuel largeFuel : Nat}
    (contract : FuelYulStatementTotalityContract parser largeFuel)
    (bound : smallFuel ≤ largeFuel) :
    FuelYulStatementTotalityContract parser smallFuel := {
  toYulStatementParserContracts := contract.toYulStatementParserContracts
  preservesTokenWindow := contract.preservesTokenWindow
  ordinary := fun input inputValid adequate =>
    contract.ordinary input inputValid
      (Nat.lt_of_lt_of_le adequate bound)
}

theorem ne_invariant {parser : Parser YulStmt} {fuel : Nat}
    (contract : FuelYulStatementTotalityContract parser fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- An unconditionally total leaf is fuel-total for every chosen bound. -/
theorem ofTotality {parser : Parser YulStmt}
    (contract : YulStatementTotalityContract parser) (fuel : Nat) :
    FuelYulStatementTotalityContract parser fuel := {
  toYulStatementParserContracts := contract.toYulStatementParserContracts
  preservesTokenWindow := contract.preservesTokenWindow
  ordinary := fun input inputValid _ => contract.invariantFree input inputValid
}

end FuelYulStatementTotalityContract

/-- Recognized fallback is ordinary below both branch fuel bounds. -/
theorem recognizedYulStatementOrFallback_ordinary_of_fuels
    (primary fallback : Parser YulStmt) (primaryFuel fallbackFuel : Nat)
    (primaryContract :
      FuelYulStatementTotalityContract primary primaryFuel)
    (fallbackContract :
      FuelYulStatementTotalityContract fallback fallbackFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < Nat.min primaryFuel fallbackFuel) :
    (∃ value next,
      recognizedYulStatementOrFallback primary fallback input =
        .ok value next) ∨
    (∃ failure next,
      recognizedYulStatementOrFallback primary fallback input =
        .reject failure next) := by
  have primaryAdequate : input.remainingCount < primaryFuel :=
    Nat.lt_of_lt_of_le adequate (Nat.min_le_left primaryFuel fallbackFuel)
  have fallbackAdequate : input.remainingCount < fallbackFuel :=
    Nat.lt_of_lt_of_le adequate (Nat.min_le_right primaryFuel fallbackFuel)
  rcases primaryContract.ordinary input inputValid primaryAdequate with
    ⟨value, next, primaryResult⟩ |
    ⟨failure, rejected, primaryResult⟩
  · exact Or.inl ⟨value, next, by
      simp only [recognizedYulStatementOrFallback, primaryResult]⟩
  · rcases fallbackContract.ordinary input inputValid fallbackAdequate with
      ⟨value, next, fallbackResult⟩ |
      ⟨fallbackFailure, fallbackRejected, fallbackResult⟩
    · let reset : State := {
        next with diagnosticsRev := input.diagnosticsRev
      }
      exact Or.inl ⟨value, reset.emit failure.toDiagnostic, by
        simp only [recognizedYulStatementOrFallback, primaryResult,
          fallbackResult, reset]⟩
    · exact Or.inr ⟨failure, input, by
        simp only [recognizedYulStatementOrFallback, primaryResult,
          fallbackResult]⟩

/-- Complete branch contracts compose through recognized fallback. -/
theorem recognizedYulStatementOrFallback_fuelTotalityContract
    (primary fallback : Parser YulStmt) (primaryFuel fallbackFuel : Nat)
    (primaryContract :
      FuelYulStatementTotalityContract primary primaryFuel)
    (fallbackContract :
      FuelYulStatementTotalityContract fallback fallbackFuel) :
    FuelYulStatementTotalityContract
      (recognizedYulStatementOrFallback primary fallback)
      (Nat.min primaryFuel fallbackFuel) := {
  toYulStatementParserContracts := {
    validFor := recognizedYulStatementOrFallback_validFor primary fallback
      primaryContract.validFor fallbackContract.validFor
    preservesTokens :=
      recognizedYulStatementOrFallback_preservesTokensOnSuccess_of_success
        primary fallback primaryContract.preservesTokens
          fallbackContract.preservesTokens
    cursorMonotone :=
      recognizedYulStatementOrFallback_cursorMonotoneOnSuccess primary
        fallback primaryContract.cursorMonotone fallbackContract.cursorMonotone
    startsAtToken :=
      recognizedYulStatementOrFallback_startsAtCurrentTokenOnSuccess primary
        fallback primaryContract.startsAtToken fallbackContract.startsAtToken
  }
  preservesTokenWindow :=
    recognizedYulStatementOrFallback_preservesTokenWindow primary fallback
      primaryContract.preservesTokenWindow
        fallbackContract.preservesTokenWindow
  ordinary := recognizedYulStatementOrFallback_ordinary_of_fuels primary
    fallback primaryFuel fallbackFuel primaryContract fallbackContract
}

/-- Optional semicolon consumption has only ordinary outcomes. -/
theorem optionalYulSemicolon_ordinary (value : YulStmt) :
    Parser.Ordinary (optionalYulSemicolon value) := by
  intro input
  unfold optionalYulSemicolon
  simp only [getState, bind]
  split
  · rcases (symbol_ordinary .semicolon .yulStatement) input with
      ⟨marker, next, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · exact Or.inl ⟨value, next, by simp only [markerResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [markerResult]⟩
  · exact Or.inl ⟨value, input, rfl⟩

/-- Optional termination retains strict progress made by the core statement. -/
theorem yulStatementTerminated_cursor_lt_onSuccess_of_core
    (nested : Parser YulStmt)
    (coreStrict : ∀ {input final : State} {value : YulStmt},
      yulStatementCore nested input = .ok value final →
        input.cursor < final.cursor)
    {input final : State} {value : YulStmt}
    (parsed : yulStatementTerminated nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulStatementTerminated at parsed
  cases coreResult : yulStatementCore nested input with
  | invariant error => simp [bind, coreResult] at parsed
  | reject failure rejected => simp [bind, coreResult] at parsed
  | ok coreValue afterCore =>
      simp only [bind, coreResult] at parsed
      exact Nat.lt_of_lt_of_le (coreStrict coreResult)
        (optionalYulSemicolon_cursorMonotoneOnSuccess coreValue
          afterCore value final parsed)

/-- Optional termination preserves the core statement's fuel bound. -/
theorem yulStatementTerminated_ordinary_of_coreFuel
    (nested : Parser YulStmt) (fuel : Nat)
    (coreContract : FuelYulStatementTotalityContract
      (yulStatementCore nested) fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel) :
    (∃ value next,
      yulStatementTerminated nested input = .ok value next) ∨
    (∃ failure next,
      yulStatementTerminated nested input = .reject failure next) := by
  rcases coreContract.ordinary input inputValid adequate with
    ⟨value, afterCore, coreResult⟩ |
    ⟨failure, rejected, coreResult⟩
  · rcases optionalYulSemicolon_ordinary value afterCore with
      ⟨terminated, next, terminatedResult⟩ |
      ⟨failure, rejected, terminatedResult⟩
    · exact Or.inl ⟨terminated, next, by
        simp only [yulStatementTerminated, bind, coreResult,
          terminatedResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [yulStatementTerminated, bind, coreResult,
          terminatedResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulStatementTerminated, bind, coreResult]⟩

theorem yulStatementTerminated_fuelTotalityContract
    (nested : Parser YulStmt) (fuel : Nat)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (coreContract : FuelYulStatementTotalityContract
      (yulStatementCore nested) fuel) :
    FuelYulStatementTotalityContract
      (yulStatementTerminated nested) fuel := {
  toYulStatementParserContracts := {
    validFor := yulStatementTerminated_validFor nested nestedValid
      nestedPreserves
    preservesTokens := yulStatementTerminated_preservesTokensOnSuccess nested
      nestedValid nestedPreserves
    cursorMonotone := yulStatementTerminated_cursorMonotoneOnSuccess nested
      nestedValid nestedPreserves
    startsAtToken := yulStatementTerminated_startsAtCurrentTokenOnSuccess
      nested nestedValid nestedPreserves
  }
  preservesTokenWindow := yulStatementTerminated_preservesTokenWindow nested
    coreContract.preservesTokenWindow
  ordinary := yulStatementTerminated_ordinary_of_coreFuel nested fuel
    coreContract
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.StatementChoiceFuelTotalityProperties
/-! Fuel-total transactional and state-selected Yul statement choices. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem adequate_left {left right count : Nat}
    (adequate : count < Nat.min left right) : count < left :=
  Nat.lt_of_lt_of_le adequate (Nat.min_le_left left right)

private theorem adequate_right {left right count : Nat}
    (adequate : count < Nat.min left right) : count < right :=
  Nat.lt_of_lt_of_le adequate (Nat.min_le_right left right)

/-- Strict branch progress survives diagnostic-replacing fallback. -/
theorem recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
    (primary fallback : Parser YulStmt)
    (primaryStrict : ∀ {input next : State} {value : YulStmt},
      primary input = .ok value next → input.cursor < next.cursor)
    (fallbackStrict : ∀ {input next : State} {value : YulStmt},
      fallback input = .ok value next → input.cursor < next.cursor)
    {input final : State} {value : YulStmt}
    (parsed : recognizedYulStatementOrFallback primary fallback input =
      .ok value final) :
    input.cursor < final.cursor := by
  unfold recognizedYulStatementOrFallback at parsed
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at parsed
  | ok primaryValue next =>
      simp only [primaryResult] at parsed
      cases parsed
      exact primaryStrict primaryResult
  | reject failure rejected =>
      simp only [primaryResult] at parsed
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at parsed
      | reject fallbackFailure fallbackRejected =>
          simp [fallbackResult] at parsed
      | ok fallbackValue next =>
          simp only [fallbackResult] at parsed
          cases parsed
          have progress : input.cursor < next.cursor :=
            fallbackStrict fallbackResult
          change input.cursor < next.cursor
          exact progress

/-- Selecting a parser from the initial state preserves bounded totality. -/
theorem stateChoice_fuelTotalityContract
    (condition : State → Bool) (first second : Parser YulStmt)
    (firstFuel secondFuel : Nat)
    (firstContract : FuelYulStatementTotalityContract first firstFuel)
    (secondContract : FuelYulStatementTotalityContract second secondFuel) :
    FuelYulStatementTotalityContract
      (fun input => if condition input then first input else second input)
      (Nat.min firstFuel secondFuel) := {
  toYulStatementParserContracts := {
    validFor := by
      intro input inputValid
      by_cases selected : condition input = true
      · simpa [selected] using firstContract.validFor input inputValid
      · simpa [selected] using secondContract.validFor input inputValid
    preservesTokens := by
      intro input value next result
      by_cases selected : condition input = true
      · exact firstContract.preservesTokens input value next
          (by simpa [selected] using result)
      · exact secondContract.preservesTokens input value next
          (by simpa [selected] using result)
    cursorMonotone := by
      intro input value next result
      by_cases selected : condition input = true
      · exact firstContract.cursorMonotone input value next
          (by simpa [selected] using result)
      · exact secondContract.cursorMonotone input value next
          (by simpa [selected] using result)
    startsAtToken := by
      intro input value next result
      by_cases selected : condition input = true
      · exact firstContract.startsAtToken input value next
          (by simpa [selected] using result)
      · exact secondContract.startsAtToken input value next
          (by simpa [selected] using result)
  }
  preservesTokenWindow := by
    intro input
    by_cases selected : condition input = true
    · simpa [selected] using firstContract.preservesTokenWindow input
    · simpa [selected] using secondContract.preservesTokenWindow input
  ordinary := by
    intro input inputValid adequate
    by_cases selected : condition input = true
    · simpa [selected] using firstContract.ordinary input inputValid
        (adequate_left adequate)
    · simpa [selected] using secondContract.ordinary input inputValid
        (adequate_right adequate)
}

theorem stateChoice_cursor_lt_onSuccess_of_strict
    (condition : State → Bool) (first second : Parser YulStmt)
    (firstStrict : ∀ {input next : State} {value : YulStmt},
      first input = .ok value next → input.cursor < next.cursor)
    (secondStrict : ∀ {input next : State} {value : YulStmt},
      second input = .ok value next → input.cursor < next.cursor)
    {input final : State} {value : YulStmt}
    (parsed : (fun state => if condition state then first state
      else second state) input = .ok value final) :
    input.cursor < final.cursor := by
  by_cases selected : condition input = true
  · exact firstStrict (by simpa [selected] using parsed)
  · exact secondStrict (by simpa [selected] using parsed)

/-- Transactional choice is ordinary below both alternative fuel bounds. -/
theorem orElse_fuelTotalityContract
    (first second : Parser YulStmt) (firstFuel secondFuel : Nat)
    (firstContract : FuelYulStatementTotalityContract first firstFuel)
    (secondContract : FuelYulStatementTotalityContract second secondFuel) :
    FuelYulStatementTotalityContract (orElse first second)
      (Nat.min firstFuel secondFuel) := {
  toYulStatementParserContracts := {
    validFor := Parser.orElse_validFor firstContract.validFor
      secondContract.validFor
    preservesTokens := Parser.orElse_preservesTokensOnSuccess
      firstContract.preservesTokens secondContract.preservesTokens
    cursorMonotone := Parser.orElse_cursorMonotoneOnSuccess
      firstContract.cursorMonotone secondContract.cursorMonotone
    startsAtToken := Parser.orElse_startsAtCurrentTokenOnSuccess
      firstContract.startsAtToken secondContract.startsAtToken
  }
  preservesTokenWindow := Parser.orElse_preservesTokenWindow
    firstContract.preservesTokenWindow secondContract.preservesTokenWindow
  ordinary := by
    intro input inputValid adequate
    rcases firstContract.ordinary input inputValid (adequate_left adequate) with
      ⟨value, next, firstResult⟩ | ⟨failure, rejected, firstResult⟩
    · exact Or.inl ⟨value, next, by
        simp only [orElse, firstResult]⟩
    · rcases secondContract.ordinary input inputValid
          (adequate_right adequate) with
        ⟨value, next, secondResult⟩ |
        ⟨failure, rejected, secondResult⟩
      · exact Or.inl ⟨value, next, by
          simp only [orElse, firstResult, secondResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [orElse, firstResult, secondResult]⟩
}

theorem orElse_cursor_lt_onSuccess_of_strict
    (first second : Parser YulStmt)
    (firstStrict : ∀ {input next : State} {value : YulStmt},
      first input = .ok value next → input.cursor < next.cursor)
    (secondStrict : ∀ {input next : State} {value : YulStmt},
      second input = .ok value next → input.cursor < next.cursor)
    {input final : State} {value : YulStmt}
    (parsed : orElse first second input = .ok value final) :
    input.cursor < final.cursor := by
  unfold orElse at parsed
  cases firstResult : first input with
  | invariant error => simp [firstResult] at parsed
  | ok firstValue next =>
      simp only [firstResult] at parsed
      cases parsed
      exact firstStrict firstResult
  | reject failure rejected =>
      simp only [firstResult] at parsed
      exact secondStrict parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.StatementRecoveryFuelTotalityProperties
/-! Fuel-aware totality for Yul statement recovery and its outer layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulRecoveryAdvance_state_shape {input next : State}
    {token : Token} (advanced : input.advance? = some (token, next)) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

/-- More fuel than remaining tokens makes statement recovery succeed. -/
theorem recoverYulStatementAux_exists_ok_of_remainingCount_lt
    (first last : SourceSpan) :
    ∀ fuel input, input.remainingCount < fuel →
      ∃ statement final,
        recoverYulStatementAux first last fuel input = .ok statement final := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      intro input adequate
      omega
  | succ fuel inductionHypothesis =>
      intro input adequate
      unfold recoverYulStatementAux
      split
      · exact ⟨_, _, rfl⟩
      · cases advanced : input.advance? with
        | none => exact ⟨_, _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            change ∃ statement final,
              recoverYulStatementAux first token.span fuel next =
                .ok statement final
            apply inductionHypothesis token.span next
            unfold State.advance? at advanced
            cases found : input.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                have cursorBeforeEnd :=
                  State.cursor_lt_endIndex_of_peek?_eq_some found
                simp only [State.remainingCount] at adequate ⊢
                omega

/-- Adequately fueled statement recovery has an ordinary success result. -/
theorem recoverYulStatementAux_ordinary_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (input : State)
    (adequate : input.remainingCount < fuel) :
    (∃ statement final,
      recoverYulStatementAux first last fuel input = .ok statement final) ∨
    (∃ failure final,
      recoverYulStatementAux first last fuel input = .reject failure final) :=
  Or.inl (recoverYulStatementAux_exists_ok_of_remainingCount_lt first last
    fuel input adequate)

/-- The production-selected statement recovery fuel is always sufficient. -/
theorem recoverYulStatementAux_production_exists_ok
    (first last : SourceSpan) (input : State) :
    ∃ statement final,
      recoverYulStatementAux first last (input.remainingCount + 1) input =
        .ok statement final :=
  recoverYulStatementAux_exists_ok_of_remainingCount_lt first last
    (input.remainingCount + 1) input (by omega)

theorem recoverYulStatementAux_production_ordinary
    (first last : SourceSpan) :
    Parser.Ordinary (fun input =>
      recoverYulStatementAux first last (input.remainingCount + 1) input) := by
  intro input
  exact Or.inl (recoverYulStatementAux_production_exists_ok first last input)

theorem recoverYulStatementAux_production_invariantFreeOnValid
    (first last : SourceSpan) :
    Parser.InvariantFreeOnValid (fun input =>
      recoverYulStatementAux first last (input.remainingCount + 1) input) :=
  (recoverYulStatementAux_production_ordinary first last).invariantFreeOnValid

theorem recoverYulStatementAux_production_ne_invariant
    (first last : SourceSpan) (input : State) (error : ParserInvariantError) :
    recoverYulStatementAux first last (input.remainingCount + 1) input ≠
      .invariant error :=
  (recoverYulStatementAux_production_ordinary first last).ne_invariant input
    error

theorem recoverYulStatementAux_ne_invariant_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (input : State)
    (adequate : input.remainingCount < fuel) (error : ParserInvariantError) :
    recoverYulStatementAux first last fuel input ≠ .invariant error := by
  intro failed
  rcases recoverYulStatementAux_exists_ok_of_remainingCount_lt first last
      fuel input adequate with ⟨statement, final, result⟩
  rw [result] at failed
  contradiction

/-- Recovery adds no invariant after an ordinary terminated rejection. -/
theorem yulStatementLayer_ordinary_of_terminatedFuel
    (nested : Parser YulStmt) (fuel : Nat)
    (contract : FuelYulStatementTotalityContract
      (yulStatementTerminated nested) fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel) :
    (∃ statement next, yulStatementLayer nested input = .ok statement next) ∨
    (∃ failure next,
      yulStatementLayer nested input = .reject failure next) := by
  rcases contract.ordinary input inputValid adequate with
    ⟨statement, next, terminatedResult⟩ |
    ⟨failure, failedState, terminatedResult⟩
  · exact Or.inl ⟨statement, next, by
      simp only [yulStatementLayer, terminatedResult]⟩
  · let rewound := { failedState with cursor := input.cursor }
    by_cases boundary : rewound.atEnd || isSymbol rewound .rightBrace
    · exact Or.inr ⟨failure, rewound, by
        simp only [yulStatementLayer, terminatedResult, rewound, boundary,
          ↓reduceIte]⟩
    · cases advanced : rewound.advance? with
      | none => exact Or.inr ⟨failure, rewound, by
          simp only [yulStatementLayer, terminatedResult, rewound, boundary,
            Bool.false_eq_true, ↓reduceIte, advanced]⟩
      | some pair =>
          rcases pair with ⟨token, afterToken⟩
          rcases recoverYulStatementAux_production_exists_ok token.span
              token.span (afterToken.emit failure.toDiagnostic) with
            ⟨recovered, final, recoveredResult⟩
          have recoveredAtProductionFuel :
              recoverYulStatementAux token.span token.span
                (afterToken.remainingCount + 1)
                (afterToken.emit failure.toDiagnostic) =
                  .ok recovered final := by
            have emitRemaining :
                (afterToken.emit failure.toDiagnostic).remainingCount =
                  afterToken.remainingCount := rfl
            rw [emitRemaining] at recoveredResult
            exact recoveredResult
          exact Or.inl ⟨recovered, final, by
            simp only [yulStatementLayer, terminatedResult, rewound, boundary,
              Bool.false_eq_true, ↓reduceIte, advanced,
              recoveredAtProductionFuel]⟩

theorem yulStatementLayer_ne_invariant_of_terminatedFuel
    (nested : Parser YulStmt) (fuel : Nat)
    (contract : FuelYulStatementTotalityContract
      (yulStatementTerminated nested) fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel) (error : ParserInvariantError) :
    yulStatementLayer nested input ≠ .invariant error := by
  intro failed
  rcases yulStatementLayer_ordinary_of_terminatedFuel nested fuel contract
      input inputValid adequate with
    ⟨statement, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Layer success is strict when ordinary terminated success is strict. -/
theorem yulStatementLayer_cursor_lt_onSuccess_of_terminated
    (nested : Parser YulStmt)
    (terminatedStrict : ∀ {input final : State} {value : YulStmt},
      yulStatementTerminated nested input = .ok value final →
        input.cursor < final.cursor)
    {input final : State} {value : YulStmt}
    (parsed : yulStatementLayer nested input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulStatementLayer at parsed
  cases terminatedResult : yulStatementTerminated nested input with
  | invariant error => simp [terminatedResult] at parsed
  | ok statement next =>
      simp only [terminatedResult] at parsed
      cases parsed
      exact terminatedStrict terminatedResult
  | reject failure failedState =>
      simp only [terminatedResult] at parsed
      let rewound := { failedState with cursor := input.cursor }
      split at parsed
      · contradiction
      · cases advanced : rewound.advance? with
        | none =>
            rw [advanced] at parsed
            contradiction
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            rw [advanced] at parsed
            have recovered :=
              recoverYulStatementAux_cursorMonotoneOnSuccess token.span
                token.span (afterToken.remainingCount + 1)
                (afterToken.emit failure.toDiagnostic) value final parsed
            have shape := yulRecoveryAdvance_state_shape advanced
            exact Nat.lt_of_lt_of_le (by
              simp [shape, State.emit, rewound]) recovered

/-- Package one recovering layer with its complete bounded contract. -/
theorem yulStatementLayer_fuelTotalityContract
    (nested : Parser YulStmt) (fuel : Nat)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (coreShape : Parser.PreservesTokenWindow (yulStatementCore nested))
    (terminatedContract : FuelYulStatementTotalityContract
      (yulStatementTerminated nested) fuel) :
    FuelYulStatementTotalityContract (yulStatementLayer nested) fuel := {
  toYulStatementParserContracts := {
    validFor := yulStatementLayer_validFor nested nestedValid nestedPreserves
      coreShape
    preservesTokens := yulStatementLayer_preservesTokensOnSuccess nested
      coreShape
    cursorMonotone := yulStatementLayer_cursorMonotoneOnSuccess nested
      nestedValid nestedPreserves
    startsAtToken := yulStatementLayer_startsAtCurrentTokenOnSuccess nested
      nestedValid nestedPreserves coreShape
  }
  preservesTokenWindow := yulStatementLayer_preservesTokenWindow nested
    coreShape
  ordinary := yulStatementLayer_ordinary_of_terminatedFuel nested fuel
    terminatedContract
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.ControlIfFuelTotalityProperties
/-! Fuel-aware totality for inline-Yul `if` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulIfStatement_weakValidFor
    (statement : Parser YulStmt)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement) :
    (yulIfStatement statement).ValidFor (fun _ _ => True) := by
  unfold yulIfStatement
  apply Parser.bind_validFor (keyword_validFor .ifKw .yulStatement)
  intro marker
  apply Parser.bind_validFor yulExpression_elementTotalityContract.validFor
  intro condition
  apply Parser.bind_validFor
    (yulBlock_validFor (fun _ _ => True) statement statementValid
      statementWindow.preservesTokensOnSuccess)
  intro body
  exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)

/--
The keyword and condition spend two units before the block needs its one-unit
wrapper around recursive statement fuel.
-/
theorem yulIfStatement_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 3) :
    (∃ value next, yulIfStatement statement input = .ok value next) ∨
    (∃ failure next,
      yulIfStatement statement input = .reject failure next) := by
  rcases (keyword_ordinary .ifKw .yulStatement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .ifKw .yulStatement input
      inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .ifKw .yulStatement
      input
    rw [markerResult] at markerWindow
    have markerProgress : input.cursor < afterMarker.cursor :=
      acceptToken_cursor_lt_onSuccess (.keyword .ifKw) .yulStatement
        (· == .keyword .ifKw) markerResult
    have conditionBudget :
        afterMarker.remainingCount < statementFuel + 2 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress (by omega)
    have expressionFree : Parser.InvariantFreeOnValid yulExpression :=
      Parser.invariantFreeOnValid_of_ne_invariant
        yulExpression_elementTotalityContract.invariantFree
    rcases expressionFree afterMarker markerReply.2.1 with
      ⟨condition, afterCondition, conditionResult⟩ |
      ⟨failure, rejected, conditionResult⟩
    · have conditionReply := yulExpression_validFor afterMarker
        markerReply.2.1
      rw [conditionResult] at conditionReply
      have conditionWindow :=
        yulExpression_elementTotalityContract.preservesTokenWindow afterMarker
      rw [conditionResult] at conditionWindow
      have conditionProgress :=
        yulExpression_elementTotalityContract.cursorLtOnSuccess
          conditionResult
      have bodyBudget :
          afterCondition.remainingCount < statementFuel + 1 :=
        remainingCount_lt_after_strict_progress conditionReply.2.1
          conditionWindow.2 conditionProgress (by omega)
      let blockContract := yulBlock_fuelElementTotalityContract statement
        statementFuel statementContract
      rcases blockContract.ordinary afterCondition conditionReply.2.1
          bodyBudget with
        ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
      · exact Or.inl ⟨{
            span := SourceSpan.cover marker.span body.span
            value := .ifThen condition body.body
          }, final, by
            simp only [yulIfStatement, bind, markerResult, conditionResult,
              bodyResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [yulIfStatement, bind, markerResult, conditionResult,
            bodyResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [yulIfStatement, bind, markerResult, conditionResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulIfStatement, bind, markerResult]⟩

theorem yulIfStatement_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 3)
    (error : ParserInvariantError) :
    yulIfStatement statement input ≠ .invariant error := by
  intro failed
  rcases yulIfStatement_ordinary_of_statementFuel statement statementFuel
      statementContract input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Every successful Yul `if` consumes its leading keyword. -/
theorem yulIfStatement_cursor_lt_onSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input final : State} {value : YulStmt}
    (parsed : yulIfStatement statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulIfStatement at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .ifKw)
      .yulStatement (· == .keyword .ifKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- The strict loop contract for one fuel-bounded Yul `if` branch. -/
theorem yulIfStatement_fuelElementTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (yulIfStatement statement)
      (statementFuel + 3) := {
  validFor := yulIfStatement_weakValidFor statement
    statementContract.validFor statementContract.preservesTokenWindow
  preservesTokenWindow := yulIfStatement_preservesTokenWindow statement
    yulExpression_elementTotalityContract.preservesTokenWindow
      statementContract.preservesTokenWindow
  cursorLtOnSuccess := yulIfStatement_cursor_lt_onSuccess statement
    statementContract.preservesTokenWindow.preservesTokensOnSuccess
  ordinary := yulIfStatement_ordinary_of_statementFuel statement
    statementFuel statementContract
}

/-- Package full Yul statement laws together with the same fuel proof. -/
theorem yulIfStatement_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelYulStatementTotalityContract (yulIfStatement statement)
      (statementFuel + 3) := by
  let statementElement : FuelElementTotalityContract statement
      statementFuel := {
    validFor := statementContract.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := statementContract.preservesTokenWindow
    cursorLtOnSuccess := statementStrict
    ordinary := statementContract.ordinary
  }
  exact {
    toYulStatementParserContracts := {
      validFor := yulIfStatement_validFor statement yulExpression_validFor
        yulExpression_startsAtCurrentTokenOnSuccess
        yulExpression_preservesTokensOnSuccess
        yulExpression_cursorMonotoneOnSuccess statementContract.validFor
          statementContract.preservesTokens
      preservesTokens := yulIfStatement_preservesTokensOnSuccess statement
        yulExpression_preservesTokensOnSuccess
          statementContract.preservesTokens
      cursorMonotone := yulIfStatement_cursorMonotoneOnSuccess statement
        yulExpression_cursorMonotoneOnSuccess
          statementContract.preservesTokens
      startsAtToken := yulIfStatement_startsAtCurrentTokenOnSuccess statement
    }
    preservesTokenWindow := yulIfStatement_preservesTokenWindow statement
      yulExpression_preservesTokenWindow
        statementContract.preservesTokenWindow
    ordinary := yulIfStatement_ordinary_of_statementFuel statement
      statementFuel statementElement
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.ControlForFuelTotalityProperties
/-! Fuel-aware totality for inline-Yul `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulForStatement_weakValidFor
    (statement : Parser YulStmt)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement) :
    (yulForStatement statement).ValidFor (fun _ _ => True) := by
  let blockValid := yulBlock_validFor (fun _ _ => True) statement
    statementValid statementWindow.preservesTokensOnSuccess
  unfold yulForStatement
  apply Parser.bind_validFor (keyword_validFor .forKw .yulStatement)
  intro marker
  apply Parser.bind_validFor blockValid
  intro initializer
  apply Parser.bind_validFor yulExpression_elementTotalityContract.validFor
  intro condition
  apply Parser.bind_validFor blockValid
  intro post
  apply Parser.bind_validFor blockValid
  intro body
  exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)

/--
The leading keyword spends the one unit needed to enter the first block;
subsequent strict block progress preserves enough fuel for every later block.
-/
theorem yulForStatement_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 2) :
    (∃ value next, yulForStatement statement input = .ok value next) ∨
    (∃ failure next,
      yulForStatement statement input = .reject failure next) := by
  let blockContract := yulBlock_fuelElementTotalityContract statement
    statementFuel statementContract
  have expressionFree : Parser.InvariantFreeOnValid yulExpression :=
    Parser.invariantFreeOnValid_of_ne_invariant
      yulExpression_elementTotalityContract.invariantFree
  rcases (keyword_ordinary .forKw .yulStatement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .forKw .yulStatement input
      inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .forKw .yulStatement
      input
    rw [markerResult] at markerWindow
    have initializerBudget :
        afterMarker.remainingCount < statementFuel + 1 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .forKw) .yulStatement
          (· == .keyword .forKw) markerResult) adequate
    rcases blockContract.ordinary afterMarker markerReply.2.1
        initializerBudget with
      ⟨initializer, afterInitializer, initializerResult⟩ |
      ⟨failure, rejected, initializerResult⟩
    · have initializerReply := blockContract.validFor afterMarker
        markerReply.2.1
      rw [initializerResult] at initializerReply
      have initializerWindow := blockContract.preservesTokenWindow afterMarker
      rw [initializerResult] at initializerWindow
      have conditionBudget :
          afterInitializer.remainingCount < statementFuel :=
        remainingCount_lt_after_strict_progress initializerReply.2.1
          initializerWindow.2
          (blockContract.cursorLtOnSuccess initializerResult)
          initializerBudget
      rcases expressionFree afterInitializer initializerReply.2.1 with
        ⟨condition, afterCondition, conditionResult⟩ |
        ⟨failure, rejected, conditionResult⟩
      · have conditionReply := yulExpression_validFor afterInitializer
          initializerReply.2.1
        rw [conditionResult] at conditionReply
        have conditionWindow :=
          yulExpression_elementTotalityContract.preservesTokenWindow
            afterInitializer
        rw [conditionResult] at conditionWindow
        have conditionProgress :=
          yulExpression_elementTotalityContract.cursorLtOnSuccess
            conditionResult
        have postBudget :
            afterCondition.remainingCount < statementFuel + 1 := by
          have preserved :
              afterCondition.remainingCount < statementFuel :=
            remainingCount_lt_of_cursor_le conditionWindow.2
              (Nat.le_of_lt conditionProgress) conditionBudget
          omega
        rcases blockContract.ordinary afterCondition conditionReply.2.1
            postBudget with
          ⟨post, afterPost, postResult⟩ |
          ⟨failure, rejected, postResult⟩
        · have postReply := blockContract.validFor afterCondition
            conditionReply.2.1
          rw [postResult] at postReply
          have postWindow := blockContract.preservesTokenWindow afterCondition
          rw [postResult] at postWindow
          have bodyBudget :
              afterPost.remainingCount < statementFuel + 1 := by
            have spent : afterPost.remainingCount < statementFuel :=
              remainingCount_lt_after_strict_progress postReply.2.1
                postWindow.2 (blockContract.cursorLtOnSuccess postResult)
                  postBudget
            omega
          rcases blockContract.ordinary afterPost postReply.2.1 bodyBudget with
            ⟨body, final, bodyResult⟩ |
            ⟨failure, rejected, bodyResult⟩
          · exact Or.inl ⟨{
                span := SourceSpan.cover marker.span body.span
                value := .forLoop initializer.body condition post.body
                  body.body
              }, final, by
                simp only [yulForStatement, bind, markerResult,
                  initializerResult, conditionResult, postResult, bodyResult,
                  pure]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [yulForStatement, bind, markerResult,
                initializerResult, conditionResult, postResult, bodyResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [yulForStatement, bind, markerResult,
              initializerResult, conditionResult, postResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [yulForStatement, bind, markerResult, initializerResult,
            conditionResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [yulForStatement, bind, markerResult, initializerResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulForStatement, bind, markerResult]⟩

theorem yulForStatement_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 2)
    (error : ParserInvariantError) :
    yulForStatement statement input ≠ .invariant error := by
  intro failed
  rcases yulForStatement_ordinary_of_statementFuel statement statementFuel
      statementContract input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Every successful Yul `for` consumes its leading keyword. -/
theorem yulForStatement_cursor_lt_onSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input final : State} {value : YulStmt}
    (parsed : yulForStatement statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulForStatement at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .forKw)
      .yulStatement (· == .keyword .forKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro initializer
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro post
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- The strict loop contract for one fuel-bounded Yul `for` branch. -/
theorem yulForStatement_fuelElementTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (yulForStatement statement)
      (statementFuel + 2) := {
  validFor := yulForStatement_weakValidFor statement
    statementContract.validFor statementContract.preservesTokenWindow
  preservesTokenWindow := yulForStatement_preservesTokenWindow statement
    yulExpression_elementTotalityContract.preservesTokenWindow
      statementContract.preservesTokenWindow
  cursorLtOnSuccess := yulForStatement_cursor_lt_onSuccess statement
    statementContract.preservesTokenWindow.preservesTokensOnSuccess
  ordinary := yulForStatement_ordinary_of_statementFuel statement
    statementFuel statementContract
}

/-- Package full Yul statement laws together with the same fuel proof. -/
theorem yulForStatement_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelYulStatementTotalityContract (yulForStatement statement)
      (statementFuel + 2) := by
  let statementElement : FuelElementTotalityContract statement
      statementFuel := {
    validFor := statementContract.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := statementContract.preservesTokenWindow
    cursorLtOnSuccess := statementStrict
    ordinary := statementContract.ordinary
  }
  exact {
    toYulStatementParserContracts := {
      validFor := yulForStatement_validFor statement yulExpression_validFor
        yulExpression_preservesTokensOnSuccess
        yulExpression_cursorMonotoneOnSuccess statementContract.validFor
          statementContract.preservesTokens
      preservesTokens := yulForStatement_preservesTokensOnSuccess statement
        yulExpression_preservesTokensOnSuccess
          statementContract.preservesTokens
      cursorMonotone := yulForStatement_cursorMonotoneOnSuccess statement
        yulExpression_cursorMonotoneOnSuccess
          statementContract.preservesTokens
      startsAtToken := yulForStatement_startsAtCurrentTokenOnSuccess statement
    }
    preservesTokenWindow := yulForStatement_preservesTokenWindow statement
      yulExpression_preservesTokenWindow
        statementContract.preservesTokenWindow
    ordinary := yulForStatement_ordinary_of_statementFuel statement
      statementFuel statementElement
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.ControlFunctionFuelTotalityProperties
/-! Fuel-aware totality for Yul block wrappers and function definitions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FuelYulStatementTotalityContract

/-- Add strict progress to view a Yul statement contract as a block element. -/
theorem fuelElementTotalityContract {parser : Parser YulStmt} {fuel : Nat}
    (contract : FuelYulStatementTotalityContract parser fuel)
    (strict : ∀ {input final : State} {value : YulStmt},
      parser input = .ok value final → input.cursor < final.cursor) :
    FuelElementTotalityContract parser fuel := {
  validFor := contract.validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := contract.preservesTokenWindow
  cursorLtOnSuccess := strict
  ordinary := contract.ordinary
}

end FuelYulStatementTotalityContract

/-- A block wrapper has exactly the ordinary outcomes of its parsed block. -/
theorem yulBlockStatement_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1) :
    (∃ value final, yulBlockStatement statement input = .ok value final) ∨
    (∃ failure final,
      yulBlockStatement statement input = .reject failure final) := by
  rcases (yulBlock_fuelElementTotalityContract statement statementFuel
      contract).ordinary input inputValid adequate with
    ⟨block, final, result⟩ | ⟨failure, final, result⟩
  · exact Or.inl ⟨{ span := block.span, value := .block block.body }, final,
      by simp only [yulBlockStatement, bind, result, pure]⟩
  · exact Or.inr ⟨failure, final, by
      simp only [yulBlockStatement, bind, result]⟩

theorem yulBlockStatement_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1)
    (error : ParserInvariantError) :
    yulBlockStatement statement input ≠ .invariant error := by
  intro failed
  rcases yulBlockStatement_ordinary_of_statementFuel statement statementFuel
      contract input inputValid adequate with
    ⟨value, final, result⟩ | ⟨failure, final, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Every successful block wrapper consumes its opening brace. -/
theorem yulBlockStatement_cursor_lt_onSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input final : State} {value : YulStmt}
    (parsed : yulBlockStatement statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulBlockStatement at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (yulBlock_cursor_lt_onSuccess statement statementPreserves) ?_ parsed
  intro block
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Package a recursive block wrapper with full Yul statement laws. -/
theorem yulBlockStatement_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelYulStatementTotalityContract (yulBlockStatement statement)
      (statementFuel + 1) := by
  let element := contract.fuelElementTotalityContract statementStrict
  exact {
    toYulStatementParserContracts := {
      validFor := yulBlockStatement_validFor statement contract.validFor
        contract.preservesTokens
      preservesTokens := yulBlockStatement_preservesTokensOnSuccess statement
        contract.preservesTokens
      cursorMonotone := yulBlockStatement_cursorMonotoneOnSuccess statement
        contract.preservesTokens
      startsAtToken := yulBlockStatement_startsAtCurrentTokenOnSuccess statement
        contract.preservesTokens
    }
    preservesTokenWindow := yulBlockStatement_preservesTokenWindow statement
      contract.preservesTokenWindow
    ordinary := yulBlockStatement_ordinary_of_statementFuel statement
      statementFuel element
  }

/--
The function keyword, name, and parameter list spend three units before the
body block needs its one-unit wrapper around recursive statement fuel.
-/
theorem yulFunctionStatement_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 4) :
    (∃ value final, yulFunctionStatement statement input = .ok value final) ∨
    (∃ failure final,
      yulFunctionStatement statement input = .reject failure final) := by
  rcases (keyword_ordinary .functionKw .yulStatement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .functionKw .yulStatement input
      inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .functionKw
      .yulStatement input
    rw [markerResult] at markerWindow
    have afterMarkerBudget :
        afterMarker.remainingCount < statementFuel + 3 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .functionKw)
          .yulStatement (· == .keyword .functionKw) markerResult) (by omega)
    rcases yulName_ordinary afterMarker with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · have nameReply := yulName_validFor afterMarker markerReply.2.1
      rw [nameResult] at nameReply
      have nameWindow := yulName_preservesTokenWindow afterMarker
      rw [nameResult] at nameWindow
      have afterNameBudget : afterName.remainingCount < statementFuel + 2 :=
        remainingCount_lt_after_strict_progress nameReply.2.1 nameWindow.2
          (yulName_cursor_lt_onSuccess nameResult) (by omega)
      rcases yulParameters_ordinary afterName nameReply.2.1 with
        ⟨parameters, afterParameters, parametersResult⟩ |
        ⟨failure, rejected, parametersResult⟩
      · have parametersReply := yulParameters_validFor afterName
          nameReply.2.1
        rw [parametersResult] at parametersReply
        have parametersWindow := yulParameters_preservesTokenWindow afterName
        rw [parametersResult] at parametersWindow
        have afterParametersBudget :
            afterParameters.remainingCount < statementFuel + 1 :=
          remainingCount_lt_after_strict_progress parametersReply.2.1
            parametersWindow.2
              (yulParameters_cursor_lt_onSuccess parametersResult) (by omega)
        rcases yulReturns_ordinary afterParameters parametersReply.2.1 with
          ⟨returns, afterReturns, returnsResult⟩ |
          ⟨failure, rejected, returnsResult⟩
        · have returnsReply := yulReturns_validFor afterParameters
            parametersReply.2.1
          rw [returnsResult] at returnsReply
          have returnsWindow := yulReturns_preservesTokenWindow afterParameters
          rw [returnsResult] at returnsWindow
          have bodyBudget : afterReturns.remainingCount < statementFuel + 1 :=
            remainingCount_lt_of_cursor_le returnsWindow.2
              (yulReturns_cursorMonotoneOnSuccess afterParameters returns
                afterReturns returnsResult) afterParametersBudget
          rcases (yulBlock_fuelElementTotalityContract statement statementFuel
              contract).ordinary afterReturns returnsReply.2.1 bodyBudget with
            ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
          · exact Or.inl ⟨{
                span := SourceSpan.cover marker.span body.span
                value := .functionDef name parameters returns body.body
              }, final, by
                simp only [yulFunctionStatement, bind, markerResult,
                  nameResult, parametersResult, returnsResult, bodyResult,
                  pure]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [yulFunctionStatement, bind, markerResult, nameResult,
                parametersResult, returnsResult, bodyResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [yulFunctionStatement, bind, markerResult, nameResult,
              parametersResult, returnsResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [yulFunctionStatement, bind, markerResult, nameResult,
            parametersResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [yulFunctionStatement, bind, markerResult, nameResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulFunctionStatement, bind, markerResult]⟩

theorem yulFunctionStatement_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 4)
    (error : ParserInvariantError) :
    yulFunctionStatement statement input ≠ .invariant error := by
  intro failed
  rcases yulFunctionStatement_ordinary_of_statementFuel statement
      statementFuel contract input inputValid adequate with
    ⟨value, final, result⟩ | ⟨failure, final, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Every successful function definition consumes its leading keyword. -/
theorem yulFunctionStatement_cursor_lt_onSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input final : State} {value : YulStmt}
    (parsed : yulFunctionStatement statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulFunctionStatement at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .functionKw)
      .yulStatement (· == .keyword .functionKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess yulName_cursorMonotoneOnSuccess
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    yulParameters_cursorMonotoneOnSuccess
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess yulReturns_cursorMonotoneOnSuccess
  intro returns
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Package a recursive function definition with full Yul statement laws. -/
theorem yulFunctionStatement_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelYulStatementTotalityContract (yulFunctionStatement statement)
      (statementFuel + 4) := by
  let element := contract.fuelElementTotalityContract statementStrict
  exact {
    toYulStatementParserContracts := {
      validFor := yulFunctionStatement_validFor statement contract.validFor
        contract.preservesTokens
      preservesTokens := yulFunctionStatement_preservesTokensOnSuccess statement
        contract.preservesTokens
      cursorMonotone := yulFunctionStatement_cursorMonotoneOnSuccess statement
        contract.preservesTokens
      startsAtToken := yulFunctionStatement_startsAtCurrentTokenOnSuccess
        statement
    }
    preservesTokenWindow := yulFunctionStatement_preservesTokenWindow statement
      contract.preservesTokenWindow
    ordinary := yulFunctionStatement_ordinary_of_statementFuel statement
      statementFuel element
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.ControlSwitchFuelTotalityProperties
/-! Fuel-aware totality for the internal arms of inline-Yul switches. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace YulControl

/-- Fuel-bounded totality for helpers which may succeed without consuming. -/
structure FuelParserTotalityContract {alpha : Type}
    (parser : Parser alpha) (fuel : Nat) : Prop where
  validFor : parser.ValidFor (fun _ _ => True)
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  ordinary : ∀ input, input.ValidFor → input.remainingCount < fuel →
    (∃ value next, parser input = .ok value next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace FuelParserTotalityContract

theorem ne_invariant {alpha : Type} {parser : Parser alpha} {fuel : Nat}
    (contract : FuelParserTotalityContract parser fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end FuelParserTotalityContract

end YulControl

private theorem yulCase_weakValidFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement) :
    (YulControl.caseArm statement).ValidFor (fun _ _ => True) := by
  unfold YulControl.caseArm
  apply Parser.bind_validFor (keyword_validFor .caseKw .yulStatement)
  intro marker
  apply Parser.bind_validFor yulLiteral_elementTotalityContract.validFor
  intro literal
  apply Parser.bind_validFor
    (yulBlock_validFor (fun _ _ => True) statement statementValid
      statementWindow.preservesTokensOnSuccess)
  intro body
  exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)

/-- A `case`, its literal, and its block spend three wrapper fuel units. -/
theorem yulCase_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 3) :
    (∃ value next, YulControl.caseArm statement input = .ok value next) ∨
      (∃ failure next,
        YulControl.caseArm statement input = .reject failure next) := by
  rcases (keyword_ordinary .caseKw .yulStatement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .caseKw .yulStatement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .caseKw .yulStatement input
    rw [markerResult] at markerWindow
    have literalBudget : afterMarker.remainingCount < statementFuel + 2 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .caseKw) .yulStatement
          (· == .keyword .caseKw) markerResult) adequate
    rcases yulLiteral_ordinary afterMarker with
      ⟨literal, afterLiteral, literalResult⟩ |
      ⟨failure, rejected, literalResult⟩
    · have literalReply := yulLiteral_elementTotalityContract.validFor
        afterMarker markerReply.2.1
      rw [literalResult] at literalReply
      have literalWindow := yulLiteral_preservesTokenWindow afterMarker
      rw [literalResult] at literalWindow
      have bodyBudget : afterLiteral.remainingCount < statementFuel + 1 :=
        remainingCount_lt_after_strict_progress literalReply.2.1
          literalWindow.2 (yulLiteral_cursor_lt_onSuccess literalResult)
            literalBudget
      rcases (yulBlock_fuelElementTotalityContract statement statementFuel
          statementContract).ordinary afterLiteral literalReply.2.1 bodyBudget with
        ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
      · exact Or.inl ⟨{
            span := SourceSpan.cover marker.span body.span
            value := .arm literal body.body
          }, final, by
            simp only [YulControl.caseArm, bind, markerResult, literalResult,
              bodyResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [YulControl.caseArm, bind, markerResult, literalResult,
            bodyResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [YulControl.caseArm, bind, markerResult, literalResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [YulControl.caseArm, bind, markerResult]⟩

theorem yulCase_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 3)
    (error : ParserInvariantError) :
    YulControl.caseArm statement input ≠ .invariant error := by
  intro failed
  rcases yulCase_ordinary_of_statementFuel statement statementFuel
      statementContract input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

theorem yulCase_fuelElementTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (YulControl.caseArm statement)
      (statementFuel + 3) := {
  validFor := yulCase_weakValidFor statement statementContract.validFor
    statementContract.preservesTokenWindow
  preservesTokenWindow := yulCase_preservesTokenWindow statement
    statementContract.preservesTokenWindow
  cursorLtOnSuccess := yulCase_cursor_lt_onSuccess statement
    statementContract.preservesTokenWindow.preservesTokensOnSuccess
  ordinary := yulCase_ordinary_of_statementFuel statement statementFuel
    statementContract
}

/-- Loop fuel and recursive-statement fuel are independent in a case list. -/
theorem yulCases_ordinary_of_fuels
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel) :
    ∀ loopFuel casesRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < statementFuel + 3 →
      (∃ cases next,
        YulControl.caseList statement loopFuel casesRev input = .ok cases next) ∨
      (∃ failure next,
        YulControl.caseList statement loopFuel casesRev input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero => intros; omega
  | succ loopFuel inductionHypothesis =>
      intro casesRev input inputValid loopAdequate statementAdequate
      unfold YulControl.caseList
      split
      · let armContract := yulCase_fuelElementTotalityContract statement
          statementFuel statementContract
        cases armResult : YulControl.caseArm statement input with
        | invariant error =>
            exact False.elim (armContract.ne_invariant input inputValid
              statementAdequate error armResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok arm next =>
            have armReply := armContract.validFor input inputValid
            rw [armResult] at armReply
            have armWindow := armContract.preservesTokenWindow input
            rw [armResult] at armWindow
            have progress := armContract.cursorLtOnSuccess armResult
            have nextLoop : next.remainingCount < loopFuel :=
              remainingCount_lt_after_strict_progress armReply.2.1 armWindow.2
                progress loopAdequate
            have nextStatement : next.remainingCount < statementFuel + 3 :=
              remainingCount_lt_of_cursor_le armWindow.2
                (Nat.le_of_lt progress) statementAdequate
            change
              (∃ cases final,
                (if next.cursor > input.cursor then
                  YulControl.caseList statement loopFuel
                    (arm :: casesRev) next
                else
                  .invariant (.noProgress .yul next.currentSpan)) =
                    .ok cases final) ∨
              (∃ failure final,
                (if next.cursor > input.cursor then
                  YulControl.caseList statement loopFuel
                    (arm :: casesRev) next
                else
                  .invariant (.noProgress .yul next.currentSpan)) =
                    .reject failure final)
            rw [if_pos progress]
            exact inductionHypothesis (arm :: casesRev) next armReply.2.1
              nextLoop nextStatement
      · exact Or.inl ⟨casesRev.reverse, input, rfl⟩

theorem yulCases_ne_invariant_of_fuels
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel)
    (loopFuel : Nat) (casesRev : List YulCase)
    (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (statementAdequate : input.remainingCount < statementFuel + 3)
    (error : ParserInvariantError) :
    YulControl.caseList statement loopFuel casesRev input ≠
      .invariant error := by
  intro failed
  rcases yulCases_ordinary_of_fuels statement statementFuel statementContract
      loopFuel casesRev input inputValid loopAdequate statementAdequate with
    ⟨cases, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Package the dynamically bounded case-list parser used by `switch`. -/
theorem yulCases_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    YulControl.FuelParserTotalityContract
      (fun input => YulControl.caseList statement
        (input.remainingCount + 1) [] input)
      (statementFuel + 3) := by
  let statementElement := statementContract.fuelElementTotalityContract
    statementStrict
  exact {
    validFor := fun input inputValid =>
      (yulCases_validFor statement statementContract.validFor
        statementContract.preservesTokens (input.remainingCount + 1)
          input inputValid).mono (fun _ _ _ => trivial)
    preservesTokenWindow := fun input =>
      yulCases_preservesTokenWindow statement
        statementContract.preservesTokenWindow
          (input.remainingCount + 1) [] input
    cursorMonotoneOnSuccess := fun input value next result =>
      yulCases_cursorMonotoneOnSuccess statement
        (input.remainingCount + 1) [] input value next result
    ordinary := fun input inputValid adequate =>
      yulCases_ordinary_of_fuels statement statementFuel statementElement
        (input.remainingCount + 1) [] input inputValid (by omega) adequate
  }

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.ControlSwitchDefaultFuelTotalityProperties
/-! Fuel-aware totality for the optional default arm of a Yul switch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem optionalYulDefault_weakValidFor
    (statement : Parser YulStmt)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement) :
    (YulControl.optionalDefault statement).ValidFor (fun _ _ => True) := by
  unfold YulControl.optionalDefault
  apply Parser.bind_validFor getState_validFor
  intro observed
  split
  · apply Parser.bind_validFor (keyword_validFor .defaultKw .yulStatement)
    intro marker
    apply Parser.bind_validFor
      (yulBlock_validFor (fun _ _ => True) statement statementValid
        statementWindow.preservesTokensOnSuccess)
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  · exact Parser.pure_validFor none _ (fun _ => trivial)

/-- A present `default` spends one keyword unit before its block wrapper. -/
theorem optionalYulDefault_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 2) :
    (∃ value next,
      YulControl.optionalDefault statement input = .ok value next) ∨
    (∃ failure next,
      YulControl.optionalDefault statement input = .reject failure next) := by
  unfold YulControl.optionalDefault
  simp only [getState, bind]
  split
  · rcases (keyword_ordinary .defaultKw .yulStatement) input with
      ⟨marker, afterMarker, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · have markerReply := keyword_validFor .defaultKw .yulStatement input
        inputValid
      rw [markerResult] at markerReply
      have markerWindow := keyword_preservesTokenWindow .defaultKw
        .yulStatement input
      rw [markerResult] at markerWindow
      have bodyBudget : afterMarker.remainingCount < statementFuel + 1 :=
        remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
          (acceptToken_cursor_lt_onSuccess (.keyword .defaultKw)
            .yulStatement (· == .keyword .defaultKw) markerResult) adequate
      rcases (yulBlock_fuelElementTotalityContract statement statementFuel
          statementContract).ordinary afterMarker markerReply.2.1 bodyBudget with
        ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
      · exact Or.inl ⟨some body, final, by
          simp only [markerResult, bodyResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [markerResult, bodyResult]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [markerResult]⟩
  · exact Or.inl ⟨none, input, rfl⟩

theorem optionalYulDefault_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 2)
    (error : ParserInvariantError) :
    YulControl.optionalDefault statement input ≠ .invariant error := by
  intro failed
  rcases optionalYulDefault_ordinary_of_statementFuel statement statementFuel
      statementContract input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Package the optional, potentially non-consuming default helper. -/
theorem optionalYulDefault_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel) :
    YulControl.FuelParserTotalityContract
      (YulControl.optionalDefault statement) (statementFuel + 2) := {
  validFor := optionalYulDefault_weakValidFor statement
    statementContract.validFor statementContract.preservesTokenWindow
  preservesTokenWindow := optionalYulDefault_preservesTokenWindow statement
    statementContract.preservesTokenWindow
  cursorMonotoneOnSuccess := optionalYulDefault_cursorMonotoneOnSuccess
    statement statementContract.preservesTokenWindow.preservesTokensOnSuccess
  ordinary := optionalYulDefault_ordinary_of_statementFuel statement
    statementFuel statementContract
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.ControlSwitchStatementFuelTotalityProperties
/-! Fuel-aware totality for complete inline-Yul `switch` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem switch_bind_cursor_lt_of_first {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstStrict : ∀ {input middle : State} {value : alpha},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value,
      Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  change (match first input with
    | .ok firstValue middle => next firstValue middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue middle =>
      simp only [firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue middle value final parsed)
  | reject failure rejected => simp [firstResult] at parsed
  | invariant error => simp [firstResult] at parsed

/--
The default-only path spends four strict tokens before recursive statements;
case arms spend at least one more. This common bound covers both paths.
-/
theorem yulSwitchStatement_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 4) :
    (∃ value next, yulSwitchStatement statement input = .ok value next) ∨
      (∃ failure next,
        yulSwitchStatement statement input = .reject failure next) := by
  let statementElement := statementContract.fuelElementTotalityContract
    statementStrict
  let casesContract := yulCases_fuelTotalityContract statement statementFuel
    statementContract statementStrict
  let defaultContract := optionalYulDefault_fuelTotalityContract statement
    statementFuel statementElement
  rcases (keyword_ordinary .switchKw .yulStatement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .switchKw .yulStatement input
      inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .switchKw
      .yulStatement input
    rw [markerResult] at markerWindow
    have expressionBudget :
        afterMarker.remainingCount < statementFuel + 3 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .switchKw) .yulStatement
          (· == .keyword .switchKw) markerResult) adequate
    have expressionFree : Parser.InvariantFreeOnValid yulExpression :=
      Parser.invariantFreeOnValid_of_ne_invariant
        yulExpression_elementTotalityContract.invariantFree
    rcases expressionFree afterMarker markerReply.2.1 with
      ⟨scrutinee, afterExpression, expressionResult⟩ |
      ⟨failure, rejected, expressionResult⟩
    · have expressionReply := yulExpression_elementTotalityContract.validFor
        afterMarker markerReply.2.1
      rw [expressionResult] at expressionReply
      have expressionWindow :=
        yulExpression_elementTotalityContract.preservesTokenWindow afterMarker
      rw [expressionResult] at expressionWindow
      have casesBudget :
          afterExpression.remainingCount < statementFuel + 2 :=
        remainingCount_lt_after_strict_progress expressionReply.2.1
          expressionWindow.2
            (yulExpression_elementTotalityContract.cursorLtOnSuccess
              expressionResult) expressionBudget
      rcases casesContract.ordinary afterExpression expressionReply.2.1
          (by omega) with
        ⟨cases, afterCases, casesResult⟩ |
        ⟨failure, rejected, casesResult⟩
      · have casesReply := casesContract.validFor afterExpression
          expressionReply.2.1
        rw [casesResult] at casesReply
        have casesWindow := casesContract.preservesTokenWindow afterExpression
        rw [casesResult] at casesWindow
        have defaultBudget :
            afterCases.remainingCount < statementFuel + 2 :=
          remainingCount_lt_of_cursor_le casesWindow.2
            (casesContract.cursorMonotoneOnSuccess afterExpression cases
              afterCases casesResult) casesBudget
        rcases defaultContract.ordinary afterCases casesReply.2.1
            defaultBudget with
          ⟨defaultBody, afterDefault, defaultResult⟩ |
          ⟨failure, rejected, defaultResult⟩
        · cases cases with
          | cons head tail =>
              cases defaultBody with
              | none =>
                  let endSpan := match (head :: tail).reverse with
                    | last :: _ => last.span
                    | [] => scrutinee.span
                  exact Or.inl ⟨{
                      span := SourceSpan.cover marker.span endSpan
                      value := .switch scrutinee { head, tail } none
                    }, afterDefault, by
                    simp only [yulSwitchStatement, bind, markerResult,
                      expressionResult, casesResult, defaultResult, pure,
                      Option.map_none, endSpan]
                    rfl⟩
              | some body =>
                  exact Or.inl ⟨{
                      span := SourceSpan.cover marker.span body.span
                      value := .switch scrutinee { head, tail }
                        (some body.body)
                    }, afterDefault, by
                    simp only [yulSwitchStatement, bind, markerResult,
                      expressionResult, casesResult, defaultResult, pure,
                      Option.map_some]⟩
          | nil =>
              cases defaultBody with
              | none =>
                  let span := SourceSpan.cover marker.span scrutinee.span
                  let diagnostic : ParseDiagnostic := {
                    span
                    kind := .constraintViolation .yulSwitchRequiresCase
                  }
                  exact Or.inl ⟨{ span, value := .error },
                    afterDefault.emit diagnostic, by
                    simp only [yulSwitchStatement, bind, markerResult,
                      expressionResult, casesResult, defaultResult,
                      List.reverse_nil, emitDiagnostic, modifyState, pure,
                      span, diagnostic]⟩
              | some body =>
                  let span := SourceSpan.cover marker.span body.span
                  let diagnostic : ParseDiagnostic := {
                    span
                    kind := .constraintViolation .yulSwitchRequiresCase
                  }
                  exact Or.inl ⟨{ span, value := .error },
                    afterDefault.emit diagnostic, by
                    simp only [yulSwitchStatement, bind, markerResult,
                      expressionResult, casesResult, defaultResult,
                      emitDiagnostic, modifyState, pure, span, diagnostic]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [yulSwitchStatement, bind, markerResult,
              expressionResult, casesResult, defaultResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [yulSwitchStatement, bind, markerResult,
            expressionResult, casesResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [yulSwitchStatement, bind, markerResult, expressionResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulSwitchStatement, bind, markerResult]⟩

theorem yulSwitchStatement_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 4)
    (error : ParserInvariantError) :
    yulSwitchStatement statement input ≠ .invariant error := by
  intro failed
  rcases yulSwitchStatement_ordinary_of_statementFuel statement statementFuel
      statementContract statementStrict input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Every successful Yul switch consumes its leading keyword. -/
theorem yulSwitchStatement_cursor_lt_onSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input final : State} {value : YulStmt}
    (parsed : yulSwitchStatement statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulSwitchStatement at parsed
  apply switch_bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .switchKw)
      .yulStatement (· == .keyword .switchKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro scrutinee
  apply Parser.bind_cursorMonotoneOnSuccess
  · intro input cases next result
    exact yulCases_cursorMonotoneOnSuccess statement
      (input.remainingCount + 1) [] input cases next result
  intro cases
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalYulDefault_cursorMonotoneOnSuccess statement statementPreserves)
  intro defaultBody
  cases cases with
  | cons head tail => exact Parser.pure_cursorMonotoneOnSuccess _
  | nil =>
      apply Parser.bind_cursorMonotoneOnSuccess
        (emitDiagnostic_cursorMonotoneOnSuccess _)
      intro emitted
      exact Parser.pure_cursorMonotoneOnSuccess _

theorem yulSwitchStatement_fuelElementTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelElementTotalityContract (yulSwitchStatement statement)
      (statementFuel + 4) := {
  validFor := (yulSwitchStatement_validFor statement
    statementContract.validFor statementContract.preservesTokens).mono
      (fun _ _ _ => trivial)
  preservesTokenWindow := yulSwitchStatement_preservesTokenWindow statement
    statementContract.preservesTokenWindow
  cursorLtOnSuccess := yulSwitchStatement_cursor_lt_onSuccess statement
    statementContract.preservesTokens
  ordinary := yulSwitchStatement_ordinary_of_statementFuel statement
    statementFuel statementContract statementStrict
}

theorem yulSwitchStatement_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelYulStatementTotalityContract (yulSwitchStatement statement)
      (statementFuel + 4) := {
  toYulStatementParserContracts := {
    validFor := yulSwitchStatement_validFor statement
      statementContract.validFor statementContract.preservesTokens
    preservesTokens := yulSwitchStatement_preservesTokensOnSuccess statement
      statementContract.preservesTokens
    cursorMonotone := yulSwitchStatement_cursorMonotoneOnSuccess statement
      statementContract.preservesTokens
    startsAtToken := yulSwitchStatement_startsAtCurrentTokenOnSuccess statement
  }
  preservesTokenWindow := yulSwitchStatement_preservesTokenWindow statement
    statementContract.preservesTokenWindow
  ordinary := yulSwitchStatement_ordinary_of_statementFuel statement
    statementFuel statementContract statementStrict
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.StatementCoreFuelTotalityProperties
/-! Fuel-aware totality for the complete ordered Yul statement dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem recognized_sameFuel_contract
    (primary fallback : Parser YulStmt) (fuel : Nat)
    (primaryContract : FuelYulStatementTotalityContract primary fuel)
    (fallbackContract : FuelYulStatementTotalityContract fallback fuel) :
    FuelYulStatementTotalityContract
      (recognizedYulStatementOrFallback primary fallback) fuel := by
  simpa using recognizedYulStatementOrFallback_fuelTotalityContract
    primary fallback fuel fuel primaryContract fallbackContract

private theorem stateChoice_sameFuel_contract
    (condition : State → Bool) (first second : Parser YulStmt) (fuel : Nat)
    (firstContract : FuelYulStatementTotalityContract first fuel)
    (secondContract : FuelYulStatementTotalityContract second fuel) :
    FuelYulStatementTotalityContract
      (fun input => if condition input then first input else second input)
      fuel := by
  simpa using stateChoice_fuelTotalityContract condition first second fuel fuel
    firstContract secondContract

private theorem orElse_sameFuel_contract
    (first second : Parser YulStmt) (fuel : Nat)
    (firstContract : FuelYulStatementTotalityContract first fuel)
    (secondContract : FuelYulStatementTotalityContract second fuel) :
    FuelYulStatementTotalityContract (orElse first second) fuel := by
  simpa using orElse_fuelTotalityContract first second fuel fuel firstContract
    secondContract

/-- Every ordered Yul statement branch is ordinary at one common outer fuel. -/
theorem yulStatementCore_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelYulStatementTotalityContract (yulStatementCore statement)
      (statementFuel + 1) := by
  let commonFuel := statementFuel + 1
  have fallbackContract : FuelYulStatementTotalityContract
      yulExpressionStatement commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      yulExpressionStatement_totalityContract commonFuel
  have blockContract : FuelYulStatementTotalityContract
      (yulBlockStatement statement) commonFuel := by
    simpa [commonFuel] using yulBlockStatement_fuelTotalityContract statement
      statementFuel statementContract statementStrict
  have letContract : FuelYulStatementTotalityContract yulLetStatement
      commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      yulLetStatement_totalityContract commonFuel
  have ifContract : FuelYulStatementTotalityContract
      (yulIfStatement statement) commonFuel :=
    (yulIfStatement_fuelTotalityContract statement statementFuel
      statementContract statementStrict).weaken (by
        simp only [commonFuel]
        omega)
  have forContract : FuelYulStatementTotalityContract
      (yulForStatement statement) commonFuel :=
    (yulForStatement_fuelTotalityContract statement statementFuel
      statementContract statementStrict).weaken (by
        simp only [commonFuel]
        omega)
  have switchContract : FuelYulStatementTotalityContract
      (yulSwitchStatement statement) commonFuel :=
    (yulSwitchStatement_fuelTotalityContract statement statementFuel
      statementContract statementStrict).weaken (by
        simp only [commonFuel]
        omega)
  have functionContract : FuelYulStatementTotalityContract
      (yulFunctionStatement statement) commonFuel :=
    (yulFunctionStatement_fuelTotalityContract statement statementFuel
      statementContract statementStrict).weaken (by
        simp only [commonFuel]
        omega)
  have returnContract : FuelYulStatementTotalityContract yulReturnBuiltin
      commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      yulReturnBuiltin_totalityContract commonFuel
  have leaveContract : FuelYulStatementTotalityContract
      (yulControlToken .leaveKw .leave) commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      (yulControlToken_totalityContract .leaveKw .leave
        (fun _ _ => YulStmt.ValidFor.leave)) commonFuel
  have breakContract : FuelYulStatementTotalityContract
      (yulControlToken .breakKw .break) commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      (yulControlToken_totalityContract .breakKw .break
        (fun _ _ => YulStmt.ValidFor.break)) commonFuel
  have continueContract : FuelYulStatementTotalityContract
      (yulControlToken .continueKw .continue) commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      (yulControlToken_totalityContract .continueKw .continue
        (fun _ _ => YulStmt.ValidFor.continue)) commonFuel
  have assignmentContract : FuelYulStatementTotalityContract yulAssignment
      commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      yulAssignment_totalityContract commonFuel
  change FuelYulStatementTotalityContract (yulStatementCore statement)
    commonFuel
  unfold yulStatementCore
  apply stateChoice_sameFuel_contract
  · exact recognized_sameFuel_contract _ _ commonFuel blockContract
      fallbackContract
  · apply stateChoice_sameFuel_contract
    · exact recognized_sameFuel_contract _ _ commonFuel letContract
        fallbackContract
    · apply stateChoice_sameFuel_contract
      · exact recognized_sameFuel_contract _ _ commonFuel ifContract
          fallbackContract
      · apply stateChoice_sameFuel_contract
        · exact recognized_sameFuel_contract _ _ commonFuel forContract
            fallbackContract
        · apply stateChoice_sameFuel_contract
          · exact recognized_sameFuel_contract _ _ commonFuel switchContract
              fallbackContract
          · apply stateChoice_sameFuel_contract
            · exact recognized_sameFuel_contract _ _ commonFuel
                functionContract fallbackContract
            · apply stateChoice_sameFuel_contract
              · exact recognized_sameFuel_contract _ _ commonFuel
                  returnContract fallbackContract
              · apply stateChoice_sameFuel_contract
                · exact recognized_sameFuel_contract _ _ commonFuel
                    leaveContract fallbackContract
                · apply stateChoice_sameFuel_contract
                  · exact recognized_sameFuel_contract _ _ commonFuel
                      breakContract fallbackContract
                  · apply stateChoice_sameFuel_contract
                    · exact recognized_sameFuel_contract _ _ commonFuel
                        continueContract fallbackContract
                    · apply stateChoice_sameFuel_contract
                      · exact orElse_sameFuel_contract _ _ commonFuel
                          assignmentContract fallbackContract
                      · exact fallbackContract

/-- Every successful ordered Yul statement branch consumes at least one token. -/
theorem yulStatementCore_cursor_lt_onSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input final : State} {value : YulStmt}
    (parsed : yulStatementCore statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulStatementCore at parsed
  dsimp only at parsed
  split at parsed
  · exact recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
      _ _ (yulBlockStatement_cursor_lt_onSuccess statement
        statementPreserves) yulExpressionStatement_cursor_lt_onSuccess parsed
  · split at parsed
    · exact recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
        _ _ yulLetStatement_cursor_lt_onSuccess
          yulExpressionStatement_cursor_lt_onSuccess parsed
    · split at parsed
      · exact recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
          _ _ (yulIfStatement_cursor_lt_onSuccess statement
            statementPreserves) yulExpressionStatement_cursor_lt_onSuccess
              parsed
      · split at parsed
        · exact recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
            _ _ (yulForStatement_cursor_lt_onSuccess statement
              statementPreserves) yulExpressionStatement_cursor_lt_onSuccess
                parsed
        · split at parsed
          · exact recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
              _ _ (yulSwitchStatement_cursor_lt_onSuccess statement
                statementPreserves) yulExpressionStatement_cursor_lt_onSuccess
                  parsed
          · split at parsed
            · exact
                recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
                  _ _ (yulFunctionStatement_cursor_lt_onSuccess statement
                    statementPreserves)
                      yulExpressionStatement_cursor_lt_onSuccess parsed
            · split at parsed
              · exact
                  recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
                    _ _ yulReturnBuiltin_cursor_lt_onSuccess
                      yulExpressionStatement_cursor_lt_onSuccess parsed
              · split at parsed
                · exact
                    recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
                      _ _ (yulControlToken_cursor_lt_onSuccess .leaveKw .leave)
                        yulExpressionStatement_cursor_lt_onSuccess parsed
                · split at parsed
                  · exact
                      recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
                        _ _ (yulControlToken_cursor_lt_onSuccess .breakKw .break)
                          yulExpressionStatement_cursor_lt_onSuccess parsed
                  · split at parsed
                    · exact
                        recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
                          _ _ (yulControlToken_cursor_lt_onSuccess .continueKw
                            .continue) yulExpressionStatement_cursor_lt_onSuccess
                              parsed
                    · split at parsed
                      · exact orElse_cursor_lt_onSuccess_of_strict _ _
                          yulAssignment_cursor_lt_onSuccess
                            yulExpressionStatement_cursor_lt_onSuccess parsed
                      · exact yulExpressionStatement_cursor_lt_onSuccess parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.StatementRecursiveFuelTotalityProperties
/-! Totality for the recursive and public inline-Yul statement parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful fuel-indexed statement consumes at least one token. -/
theorem yulStatementWithFuel_cursor_lt_onSuccess :
    ∀ fuel, ∀ {input final : State} {value : YulStmt},
      yulStatementWithFuel fuel input = .ok value final →
        input.cursor < final.cursor := by
  intro fuel
  cases fuel with
  | zero =>
      intro input final value parsed
      simp [yulStatementWithFuel] at parsed
  | succ fuel =>
      intro input final value parsed
      apply yulStatementLayer_cursor_lt_onSuccess_of_terminated
        (yulStatementWithFuel fuel) ?_ parsed
      intro terminatedInput terminatedFinal terminatedValue terminatedParsed
      exact yulStatementTerminated_cursor_lt_onSuccess_of_core
        (yulStatementWithFuel fuel)
        (yulStatementCore_cursor_lt_onSuccess (yulStatementWithFuel fuel)
          (yulStatementWithFuel_preservesTokensOnSuccess fuel))
        terminatedParsed

/--
The syntax recursion index is also the exact valid-input totality bound.
The zero parser is vacuously total below zero; each layer adds one unit.
-/
theorem yulStatementWithFuel_fuelTotalityContract :
    ∀ fuel, FuelYulStatementTotalityContract
      (yulStatementWithFuel fuel) fuel := by
  intro fuel
  induction fuel with
  | zero =>
      exact {
        toYulStatementParserContracts := {
          validFor := yulStatementWithFuel_validFor 0
          preservesTokens := yulStatementWithFuel_preservesTokensOnSuccess 0
          cursorMonotone := yulStatementWithFuel_cursorMonotoneOnSuccess 0
          startsAtToken :=
            yulStatementWithFuel_startsAtCurrentTokenOnSuccess 0
        }
        preservesTokenWindow := yulStatementWithFuel_preservesTokenWindow 0
        ordinary := by
          intro input inputValid adequate
          omega
      }
  | succ fuel inductionHypothesis =>
      let nested := yulStatementWithFuel fuel
      let coreContract := yulStatementCore_fuelTotalityContract nested fuel
        inductionHypothesis
        (yulStatementWithFuel_cursor_lt_onSuccess fuel)
      let terminatedContract := yulStatementTerminated_fuelTotalityContract
        nested (fuel + 1) (yulStatementWithFuel_validFor fuel)
          (yulStatementWithFuel_preservesTokensOnSuccess fuel) coreContract
      have layerContract := yulStatementLayer_fuelTotalityContract nested
        (fuel + 1) (yulStatementWithFuel_validFor fuel)
          (yulStatementWithFuel_preservesTokensOnSuccess fuel)
            coreContract.preservesTokenWindow terminatedContract
      simpa only [yulStatementWithFuel, nested] using layerContract

/-- The production-selected recursive fuel always yields an ordinary reply. -/
theorem yulStatement_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ value next, yulStatement input = .ok value next) ∨
      (∃ failure next, yulStatement input = .reject failure next) := by
  unfold yulStatement
  exact (yulStatementWithFuel_fuelTotalityContract
    (input.remainingCount + 1)).ordinary input inputValid (by omega)

theorem yulStatement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulStatement :=
  yulStatement_ordinary

theorem yulStatement_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    yulStatement input ≠ .invariant error :=
  yulStatement_invariantFreeOnValid.ne_invariant input inputValid error

/-- Public statement success inherits strict progress from its chosen index. -/
theorem yulStatement_cursor_lt_onSuccess
    {input final : State} {value : YulStmt}
    (parsed : yulStatement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulStatement at parsed
  exact yulStatementWithFuel_cursor_lt_onSuccess
    (input.remainingCount + 1) parsed

/-- Complete syntax, state, and valid-input totality for public Yul statements. -/
theorem yulStatement_totalityContract :
    YulStatementTotalityContract yulStatement := {
  toYulStatementParserContracts := {
    validFor := yulStatement_validFor
    preservesTokens := yulStatement_preservesTokensOnSuccess
    cursorMonotone := yulStatement_cursorMonotoneOnSuccess
    startsAtToken := yulStatement_startsAtCurrentTokenOnSuccess
  }
  preservesTokenWindow := yulStatement_preservesTokenWindow
  invariantFree := yulStatement_invariantFreeOnValid
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Yul.BodyTotalityProperties
/-! Valid-input totality for the public braced inline-Yul body parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public recursive Yul statements satisfy the strict loop-element contract. -/
theorem yulStatement_elementTotalityContract :
    ElementTotalityContract yulStatement := {
  validFor := yulStatement_totalityContract.validFor.mono
    (fun _ _ _ => trivial)
  preservesTokenWindow :=
    yulStatement_totalityContract.preservesTokenWindow
  cursorLtOnSuccess := yulStatement_cursor_lt_onSuccess
  invariantFree := yulStatement_ne_invariant
}

/-- The production-sized block loop always has an ordinary valid-input reply. -/
theorem yulBody_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ body final, yulBody input = .ok body final) ∨
      (∃ failure final, yulBody input = .reject failure final) := by
  let statementFuel := input.remainingCount + 1
  let statementContract : FuelElementTotalityContract yulStatement
      statementFuel := {
    validFor := yulStatement_elementTotalityContract.validFor
    preservesTokenWindow :=
      yulStatement_elementTotalityContract.preservesTokenWindow
    cursorLtOnSuccess :=
      yulStatement_elementTotalityContract.cursorLtOnSuccess
    ordinary := fun state stateValid _ => yulStatement_ordinary state stateValid
  }
  simpa only [yulBody] using
    yulBlock_ordinary_of_statementFuel yulStatement statementFuel
      statementContract input inputValid (by
        simp only [statementFuel]
        omega)

theorem yulBody_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulBody :=
  yulBody_ordinary

theorem yulBody_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    yulBody input ≠ .invariant error :=
  yulBody_invariantFreeOnValid.ne_invariant input inputValid error

/-- A successful public body consumes its opening brace. -/
theorem yulBody_cursor_lt_onSuccess
    {input final : State} {body : YulParsedBlock}
    (parsed : yulBody input = .ok body final) :
    input.cursor < final.cursor := by
  unfold yulBody at parsed
  exact yulBlock_cursor_lt_onSuccess yulStatement
    yulStatement_preservesTokensOnSuccess parsed

/-- Complete loop, state-window, progress, and totality laws for `yulBody`. -/
theorem yulBody_elementTotalityContract :
    ElementTotalityContract yulBody := {
  validFor := yulBody_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := yulBody_preservesTokenWindow
  cursorLtOnSuccess := yulBody_cursor_lt_onSuccess
  invariantFree := yulBody_ne_invariant
}

end Solcore.Syntax.Parser
end

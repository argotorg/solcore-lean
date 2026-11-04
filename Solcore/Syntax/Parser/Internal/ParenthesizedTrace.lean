import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.Internal.ExpressionAtomProofs
import Solcore.Syntax.Parser.Internal.DelimitedTrace
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Parser.Internal.PatternProofs
import Solcore.Syntax.Internal.ExpressionTrace
import Solcore.Syntax.Parser.Internal.TypeTrace
import Solcore.Syntax.Parser.Internal.DelimitedSoundness

/-!
Parser side of the traces of parenthesized forms, array literals and atom recovery: the
parsers produce exactly the events of the trace grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomTupleUnrestrictedFuelTotalityProperties
/-! Parenthesized atoms and their actual tuple loop are ordinary on arbitrary
States. A real opening/comma token pays one fuel unit; successful children
preserve only endIndex and strict cursor progress. No other child frame is used. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem closeTuple_ordinary_unrestricted (opening : Token) (elementsRev : List Expr) :
    Parser.Ordinary (closeTuple opening elementsRev) := by
  intro input
  rcases symbol_ordinary .rightParen .expression input with
    ⟨closing, next, result⟩ | ⟨failure, rejected, result⟩
  · simp only [closeTuple, bind, result]
    split <;> exact .inl ⟨_, next, rfl⟩
  · exact .inr ⟨failure, rejected, by simp only [closeTuple, bind, result]⟩

theorem closeTuple_ne_invariant_unrestricted (opening : Token) (elementsRev : List Expr)
    (input : State) (error : ParserInvariantError) : closeTuple opening elementsRev input ≠ .invariant error :=
  (closeTuple_ordinary_unrestricted opening elementsRev).ne_invariant input error

theorem tupleTail_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel) (opening : Token) :
    ∀ loopFuel elementsRev input,
      input.remainingCount < loopFuel → input.remainingCount < nestedFuel + 1 →
      (∃ value next, tupleTail nested opening loopFuel elementsRev input = .ok value next) ∨
      (∃ failure next, tupleTail nested opening loopFuel elementsRev input = .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero => intro elementsRev input loopAdequate nestedAdequate; omega
  | succ loopFuel ih =>
      intro elementsRev input loopAdequate nestedAdequate
      unfold tupleTail
      cases commaResult : symbol .comma .expression input with
      | invariant error => exact False.elim (symbol_ne_invariant .comma .expression input error commaResult)
      | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
      | ok comma afterComma =>
          have commaLoopAdequate := symbol_remainingCount_lt_of_success .comma .expression commaResult loopAdequate
          have commaNestedAdequate := symbol_remainingCount_lt_of_success .comma .expression commaResult nestedAdequate
          simp only
          split
          · exact closeTuple_ordinary_unrestricted opening elementsRev afterComma
          · cases childResult : nested afterComma with
            | invariant error => exact False.elim (contract.ne_invariant afterComma commaNestedAdequate error childResult)
            | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
            | ok value next =>
                have progress := contract.cursorLtOnSuccess childResult
                have nextNestedAdequate := contract.remainingCount_lt_of_success childResult commaNestedAdequate
                dsimp only
                split
                · split
                  · exact ih (value :: elementsRev) next
                      (contract.remainingCount_lt_of_success childResult commaLoopAdequate) (by omega)
                  · exact closeTuple_ordinary_unrestricted opening (value :: elementsRev) next
                · omega

theorem tupleTail_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (opening : Token) (loopFuel : Nat) (elementsRev : List Expr) (input : State)
    (loopAdequate : input.remainingCount < loopFuel) (nestedAdequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    tupleTail nested opening loopFuel elementsRev input ≠ .invariant error := by
  intro failed
  rcases tupleTail_ordinary_of_unrestrictedElementFuel nested nestedFuel contract opening
    loopFuel elementsRev input loopAdequate nestedAdequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

theorem tupleTail_production_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (opening : Token) (elementsRev : List Expr) (input : State)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, tupleTail nested opening (input.remainingCount + 1) elementsRev input = .ok value next) ∨
    (∃ failure next, tupleTail nested opening (input.remainingCount + 1) elementsRev input = .reject failure next) :=
  tupleTail_ordinary_of_unrestrictedElementFuel nested nestedFuel contract opening
    (input.remainingCount + 1) elementsRev input (Nat.lt_succ_self _) adequate

theorem tupleTail_production_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (opening : Token) (elementsRev : List Expr) (input : State)
    (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    tupleTail nested opening (input.remainingCount + 1) elementsRev input ≠ .invariant error :=
  tupleTail_ne_invariant_of_unrestrictedElementFuel nested nestedFuel contract opening
    (input.remainingCount + 1) elementsRev input (Nat.lt_succ_self _) adequate error

theorem parenthesized_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, parenthesized nested input = .ok value next) ∨
    (∃ failure next, parenthesized nested input = .reject failure next) := by
  unfold parenthesized
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => exact False.elim (symbol_ne_invariant .leftParen .expression input error openingResult)
  | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
  | ok opening afterOpening =>
      have afterOpeningAdequate := symbol_remainingCount_lt_of_success .leftParen .expression openingResult adequate
      simp only
      split
      · exact closeTuple_ordinary_unrestricted opening [] afterOpening
      · cases childResult : nested afterOpening with
        | invariant error => exact False.elim (contract.ne_invariant afterOpening afterOpeningAdequate error childResult)
        | reject failure rejected => exact .inr ⟨failure, rejected, rfl⟩
        | ok first next =>
            have progress := contract.cursorLtOnSuccess childResult
            have nextAdequate := contract.remainingCount_lt_of_success childResult afterOpeningAdequate
            dsimp only
            split
            · omega
            · split
              · exact tupleTail_production_ordinary_of_unrestrictedElementFuel nested nestedFuel contract
                  opening [first] next (by omega)
              · exact closeTuple_ordinary_unrestricted opening [first] next

theorem parenthesized_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    parenthesized nested input ≠ .invariant error := by
  intro failed
  rcases parenthesized_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomCollectionUnrestrictedFuelTotalityProperties
/-! Dot constructors and arrays use the actual no-trailing list policy under
the three-field unrestricted child contract. Only successful endIndex and
strict progress are assumed; child source, tokens, diagnostics, and rejection
States remain unconstrained. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem optionalDotConstructorArguments_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ arguments next, optionalDotConstructorArguments nested input = .ok arguments next) ∨
    (∃ failure next, optionalDotConstructorArguments nested input = .reject failure next) := by
  cases present : isSymbol input .leftParen with
  | false => exact .inl ⟨none, input, by
      simp only [optionalDotConstructorArguments, getState, bind, present, Bool.false_eq_true, if_false, pure]⟩
  | true =>
      rcases delimitedWithPolicy_ordinary_of_unrestrictedElementFuel .leftParen .rightParen true false
        nested .expression .expression nestedFuel contract input adequate with
        ⟨values, next, result⟩ | ⟨failure, rejected, result⟩
      · exact .inl ⟨some values, next, by
          simp only [optionalDotConstructorArguments, getState, bind, present, if_true,
            delimitedNoTrailing, result, pure]⟩
      · exact .inr ⟨failure, rejected, by
          simp only [optionalDotConstructorArguments, getState, bind, present, if_true,
            delimitedNoTrailing, result]⟩

theorem optionalDotConstructorArguments_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    optionalDotConstructorArguments nested input ≠ .invariant error := by
  intro failed
  rcases optionalDotConstructorArguments_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

theorem dotConstructor_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, dotConstructor nested input = .ok value next) ∨
    (∃ failure next, dotConstructor nested input = .reject failure next) := by
  rcases symbol_ordinary .dot .expression input with
    ⟨dot, afterDot, dotResult⟩ | ⟨failure, rejected, dotResult⟩
  · have afterDotAdequate := symbol_remainingCount_lt_of_success .dot .expression dotResult adequate
    rcases expressionName_ordinary afterDot with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · have nameWindow := expressionName_preservesTokenWindow afterDot
      rw [nameResult] at nameWindow
      have afterNameAdequate : afterName.remainingCount < nestedFuel :=
        remainingCount_lt_of_endIndex_eq (congrArg TokenWindow.endIndex nameWindow.2)
          (Nat.le_of_lt (expressionName_cursor_lt_onSuccess nameResult)) afterDotAdequate
      rcases optionalDotConstructorArguments_ordinary_of_unrestrictedElementFuel nested nestedFuel contract
        afterName (by omega) with ⟨arguments, final, argumentResult⟩ | ⟨failure, rejected, argumentResult⟩
      · let endSpan := arguments.map (fun values => values.span) |>.getD name.span
        exact .inl ⟨{
            span := SourceSpan.cover dot.span endSpan
            value := .dotConstructor dot.span name arguments
          }, final, by simp only [dotConstructor, bind, dotResult, nameResult, argumentResult, pure]; rfl⟩
      · exact .inr ⟨failure, rejected, by simp only [dotConstructor, bind, dotResult, nameResult, argumentResult]⟩
    · exact .inr ⟨failure, rejected, by simp only [dotConstructor, bind, dotResult, nameResult]⟩
  · exact .inr ⟨failure, rejected, by simp only [dotConstructor, bind, dotResult]⟩

theorem dotConstructor_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    dotConstructor nested input ≠ .invariant error := by
  intro failed
  rcases dotConstructor_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

theorem arrayLiteral_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, arrayLiteral nested input = .ok value next) ∨
    (∃ failure next, arrayLiteral nested input = .reject failure next) := by
  rcases delimitedWithPolicy_ordinary_of_unrestrictedElementFuel .leftBracket .rightBracket true false
    nested .expression .expression nestedFuel contract input adequate with
    ⟨values, next, result⟩ | ⟨failure, rejected, result⟩
  · exact .inl ⟨{ span := values.span, value := .array values }, next, by
      simp only [arrayLiteral, bind, delimitedNoTrailing, result, pure]⟩
  · exact .inr ⟨failure, rejected, by simp only [arrayLiteral, bind, delimitedNoTrailing, result]⟩

theorem arrayLiteral_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    arrayLiteral nested input ≠ .invariant error := by
  intro failed
  rcases arrayLiteral_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomDispatchSelectionTraceProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomRecoveryTraceStateProperties
/-! Standalone recovery appends exactly one event on success, retains the
complete source/window, and rejects without committing its terminal report.
The scan never replays diagnostics from the tokens that it skips. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

private theorem advance_state {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

theorem recoverAtomAux_success_frame (first : SourceSpan) :
    ∀ fuel last {input output : State} {value : Expr},
      recoverAtomAux first last fuel input = .ok value output →
      output.file = input.file ∧
        output.diagnostics = input.diagnostics ++ [expressionAtomRecoveryTraceEvent value.span] := by
  intro fuel
  induction fuel with
  | zero => intro last input output value result; simp [recoverAtomAux] at result
  | succ fuel ih =>
      intro last input output value result
      unfold recoverAtomAux at result
      split at result
      · unfold finishRecoveredAtom at result
        cases result
        exact ⟨rfl, by simp [State.emit, State.diagnostics, expressionAtomRecoveryTraceEvent]⟩
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredAtom at result
            cases result
            exact ⟨rfl, by simp [State.emit, State.diagnostics, expressionAtomRecoveryTraceEvent]⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            have shape := advance_state advanced
            subst next
            exact ih token.span (input := { input with cursor := input.cursor + 1 }) result

theorem recoverAtom_success_frame {input output : State} {value : Expr}
    (result : recoverAtom input = .ok value output) :
    output.file = input.file ∧ output.diagnostics = input.diagnostics ++ [expressionAtomRecoveryTraceEvent value.span] := by
  unfold recoverAtom at result
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at result
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      have frame := recoverAtomAux_success_frame token.span (next.remainingCount + 1) token.span result
      rw [advance_state advanced] at frame
      exact frame

theorem recoverAtom_reject_shape {input rejected : State} {failure : Failure}
    (result : recoverAtom input = .reject failure rejected) :
    rejected = input ∧ (rejectAt input { head := .expression, tail := [] } .expression : Reply Expr) =
      .reject failure input := by
  unfold recoverAtom at result
  cases advanced : input.advance? with
  | none =>
      simp only [advanced] at result
      unfold rejectAt at result
      cases result
      exact ⟨rfl, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoverAtomAux_production_exists_ok token.span token.span next with ⟨value, output, success⟩
      rw [success] at result
      contradiction

theorem recoverAtom_preservesFile : Parser.PreservesFile recoverAtom := by
  intro input
  cases result : recoverAtom input with
  | invariant error => trivial
  | ok value output => exact (recoverAtom_success_frame result).1
  | reject failure rejected => rw [(recoverAtom_reject_shape result).1]; rfl

theorem recoverAtom_success_context : ParserSuccessContext recoverAtom := by
  intro input output value result
  have window := recoverAtom_preservesTokenWindow input
  rw [result] at window
  exact ⟨(recoverAtom_success_frame result).1, window.2⟩

theorem recoverAtom_reject_context {input rejected : State} {failure : Failure}
    (result : recoverAtom input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  rw [(recoverAtom_reject_shape result).1]
  exact ⟨rfl, rfl⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomRecoveryTraceProperties
/-! Standalone recovery has unrestricted exact trace contracts. Completeness
uses ordinary execution, not existence from the independent joint specification.
The caller's earlier failure report is neither reconstructed nor re-emitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

theorem recoverAtom_trace_success_sound :
    ParserTraceSuccessSound recoverAtom ExpressionAtomRecoveryTraceParses := by
  intro input output value result
  exact ⟨[expressionAtomRecoveryTraceEvent value.span],
    ⟨recoverAtom_success_ordinary_sound result, rfl⟩, (recoverAtom_success_frame result).2⟩

theorem recoverAtom_reject_trace_sound :
    ParserTraceRejectSound recoverAtom ExpressionAtomRecoveryTraceRejects := by
  intro input rejected failure result
  have ordinary := recoverAtom_reject_ordinary_sound result
  rcases recoverAtom_reject_shape result with ⟨rfl, reported⟩
  exact ⟨[], ⟨ordinary, (rejectAt_reject_reports _ .expression reported).1, rfl⟩, by simp⟩

theorem recoverAtom_trace_success_complete :
    ParserTraceSuccessComplete recoverAtom ExpressionAtomRecoveryTraceParses :=
  trace_success_complete_of_sound recoverAtom_trace_success_sound recoverAtom_reject_trace_sound
    (fun _ _ => expressionAtomRecoveryTraceExactOutcomeSpec) recoverAtom_ne_invariant

theorem recoverAtom_trace_reject_complete :
    ParserTraceRejectComplete recoverAtom ExpressionAtomRecoveryTraceRejects :=
  trace_reject_complete_of_sound recoverAtom_trace_success_sound recoverAtom_reject_trace_sound
    (fun _ _ => expressionAtomRecoveryTraceExactOutcomeSpec) recoverAtom_ne_invariant

theorem recoverAtom_trace_success_iff
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionAtomRecoveryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, recoverAtom input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact recoverAtom_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases recoverAtom_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem recoverAtom_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionAtomRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, recoverAtom input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact recoverAtom_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases recoverAtom_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem recoverAtom_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionAtomRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, recoverAtom input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [recoverAtom_trace_reject_iff]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem recoverAtom_trace_success_state_iff
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionAtomRecoveryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      recoverAtom input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases recoverAtom_trace_success_complete parsed with ⟨output, result, afterEq, events⟩
    have frame := recoverAtom_success_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact recoverAtom_trace_success_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem recoverAtom_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionAtomRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      recoverAtom input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases recoverAtom_trace_reject_failure_iff.mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := recoverAtom_reject_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact recoverAtom_trace_reject_failure_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem recoverAtom_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionAtomRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, recoverAtom input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases recoverAtom_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, recoverAtom_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ recoverAtom_trace_reject_failure_state_iff.mpr result

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomTraceContextProperties
/-! Public atom guards and frames over the actual supplied core. Source/end-byte
frames deliberately allow changed token carriers and end indices. Full-window
context and ordinary execution are separate, explicit conditional contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}

theorem isAtomBoundary_true_iff (input : State) :
    isAtomBoundary input = true ↔ ExpressionAtomBoundaryStops input.declarativeRemainder := by
  constructor
  · exact expressionAtomBoundaryStops_of_isAtomBoundary input
  · intro stops
    cases guard : isAtomBoundary input with
    | true => rfl
    | false => exact False.elim (no_expressionAtomBoundaryStops_of_isAtomBoundary_eq_false input guard stops)

theorem isAtomBoundary_false_iff (input : State) :
    isAtomBoundary input = false ↔ ¬ ExpressionAtomBoundaryStops input.declarativeRemainder := by
  constructor
  · exact no_expressionAtomBoundaryStops_of_isAtomBoundary_eq_false input
  · intro continues
    cases guard : isAtomBoundary input with
    | false => rfl
    | true => exact False.elim (continues ((isAtomBoundary_true_iff input).mp guard))

theorem expressionAtom_preservesFile
    (coreFile : Parser.PreservesFile (expressionAtomCore nested block)) :
    Parser.PreservesFile (expressionAtom nested block) := by
  intro input
  cases coreResult : expressionAtomCore nested block input with
  | ok value next =>
      simp only [expressionAtom, coreResult]
      exact coreFile.file_eq_of_ok coreResult
  | reject failure failed =>
      have frame := coreFile.file_eq_of_reject coreResult
      simp only [expressionAtom, coreResult]
      split
      · exact frame
      · exact (recoverAtom_preservesFile _).trans frame
  | invariant error => simp only [expressionAtom, coreResult]; trivial

theorem expressionAtom_success_source_end
    (coreSuccessFrame : ∀ {input output value}, expressionAtomCore nested block input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input output : State} {value : Expr}
    (result : expressionAtom nested block input = .ok value output) :
    output.file = input.file ∧ output.window.endByte = input.window.endByte := by
  cases coreResult : expressionAtomCore nested block input with
  | ok actual next =>
      simp only [expressionAtom, coreResult] at result
      cases result
      exact coreSuccessFrame coreResult
  | reject failure failed =>
      have frame := coreRejectFrame coreResult
      simp only [expressionAtom, coreResult] at result
      split at result
      · contradiction
      · have recovery := recoverAtom_success_context result
        exact ⟨recovery.1.trans frame.1, (congrArg TokenWindow.endByte recovery.2).trans frame.2⟩
  | invariant error => simp only [expressionAtom, coreResult] at result; contradiction

theorem expressionAtom_reject_source_end
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input rejected : State} {failure : Failure}
    (result : expressionAtom nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte := by
  cases coreResult : expressionAtomCore nested block input with
  | ok value next => simp only [expressionAtom, coreResult] at result; contradiction
  | reject original failed =>
      have frame := coreRejectFrame coreResult
      simp only [expressionAtom, coreResult] at result
      split at result
      · rcases Reply.reject.inj result with ⟨rfl, stateEq⟩
        rw [← stateEq]
        exact frame
      · have recovery := recoverAtom_reject_context result
        exact ⟨recovery.1.trans frame.1, (congrArg TokenWindow.endByte recovery.2).trans frame.2⟩
  | invariant error => simp only [expressionAtom, coreResult] at result; contradiction

theorem expressionAtom_success_context
    (coreSuccessFrame : ParserSuccessContext (expressionAtomCore nested block))
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window) :
    ParserSuccessContext (expressionAtom nested block) := by
  intro input output value result
  cases coreResult : expressionAtomCore nested block input with
  | ok actual next =>
      simp only [expressionAtom, coreResult] at result
      cases result
      exact coreSuccessFrame coreResult
  | reject failure failed =>
      have frame := coreRejectFrame coreResult
      simp only [expressionAtom, coreResult] at result
      split at result
      · contradiction
      · have recovery := recoverAtom_success_context result
        exact ⟨recovery.1.trans frame.1, recovery.2.trans frame.2⟩
  | invariant error => simp only [expressionAtom, coreResult] at result; contradiction

theorem expressionAtom_reject_context
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input rejected : State} {failure : Failure}
    (result : expressionAtom nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  cases coreResult : expressionAtomCore nested block input with
  | ok value next => simp only [expressionAtom, coreResult] at result; contradiction
  | reject original failed =>
      have frame := coreRejectFrame coreResult
      simp only [expressionAtom, coreResult] at result
      split at result
      · rcases Reply.reject.inj result with ⟨rfl, stateEq⟩
        rw [← stateEq]
        exact frame
      · have recovery := recoverAtom_reject_context result
        exact ⟨recovery.1.trans frame.1, recovery.2.trans frame.2⟩
  | invariant error => simp only [expressionAtom, coreResult] at result; contradiction

theorem expressionAtom_ordinary_of_core
    (coreOrdinary : Parser.Ordinary (expressionAtomCore nested block)) :
    Parser.Ordinary (expressionAtom nested block) := by
  intro input
  rcases coreOrdinary input with ⟨value, next, parsed⟩ | ⟨failure, failed, rejected⟩
  · exact .inl ⟨value, next, by simp only [expressionAtom, parsed]⟩
  · simp only [expressionAtom, rejected]
    split
    · exact .inr ⟨_, _, rfl⟩
    · exact recoverAtom_ordinary _

theorem expressionAtom_ne_invariant_of_core
    (coreOrdinary : Parser.Ordinary (expressionAtomCore nested block))
    (input : State) (error : ParserInvariantError) : expressionAtom nested block input ≠ .invariant error :=
  (expressionAtom_ordinary_of_core coreOrdinary).ne_invariant input error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomTraceProperties
/-! Public atom trace contracts over the actual core. The rejected source and
end byte are explicit; tokens and end index may change and survive rewind.
Completeness composes only matching core completeness contracts and standalone
recovery, without ordinary-execution, progress, or validity assumptions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {coreTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {coreRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionAtom_trace_success_sound
    (coreSuccessSound : ParserTraceSuccessSound (expressionAtomCore nested block) coreTrace)
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceSuccessSound (expressionAtom nested block) (ExpressionAtomTraceParses coreTrace coreRejects) := by
  intro input output value result
  cases coreResult : expressionAtomCore nested block input with
  | ok parameter next =>
      simp only [expressionAtom, coreResult] at result
      cases result
      rcases coreSuccessSound coreResult with ⟨trace, parsed, events⟩
      exact ⟨trace, .core parsed, events⟩
  | reject original failed =>
      let rewound := { failed with cursor := input.cursor }
      rcases coreRejectSound coreResult with ⟨coreTrace, coreRejected, coreEvents⟩
      have frame := coreRejectFrame coreResult
      simp only [expressionAtom, coreResult] at result
      change (if isAtomBoundary rewound then
        .reject original rewound else recoverAtom (rewound.emit original.toDiagnostic)) = .ok value output at result
      split at result
      · contradiction
      · rename_i continues
        rcases recoverAtom_trace_success_sound result with ⟨trace, parsed, events⟩
        have recovery : ExpressionAtomRecoveryTraceParses input.file.id input.window.endByte
            (expressionAtomTraceRewind input.declarativeRemainder failed.declarativeRemainder)
            value output.declarativeRemainder trace := by
          simpa only [State.emit, rewound, State.declarativeRemainder, expressionAtomTraceRewind,
            frame.1, frame.2] using parsed
        refine ⟨(coreTrace ++ [original.toDiagnostic]) ++ trace,
          .recovered coreRejected
            (no_expressionAtomBoundaryStops_of_isAtomBoundary_eq_false rewound (Bool.eq_false_iff.mpr continues)) recovery, ?_⟩
        calc
          output.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ trace := by
            simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
          _ = input.diagnostics ++ ((coreTrace ++ [original.toDiagnostic]) ++ trace) := by
            rw [coreEvents]
            simp only [List.append_assoc]
  | invariant error => simp only [expressionAtom, coreResult] at result; contradiction

theorem expressionAtom_reject_trace_sound
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceRejectSound (expressionAtom nested block) (ExpressionAtomTraceRejects coreRejects) := by
  intro input rejected failure result
  cases coreResult : expressionAtomCore nested block input with
  | ok value next => simp only [expressionAtom, coreResult] at result; contradiction
  | reject original failed =>
      let rewound := { failed with cursor := input.cursor }
      rcases coreRejectSound coreResult with ⟨coreTrace, coreRejected, coreEvents⟩
      have frame := coreRejectFrame coreResult
      simp only [expressionAtom, coreResult] at result
      change (if isAtomBoundary rewound then
        .reject original rewound else recoverAtom (rewound.emit original.toDiagnostic)) =
          .reject failure rejected at result
      split at result
      · rename_i stops
        rcases Reply.reject.inj result with ⟨rfl, stateEq⟩
        rw [← stateEq]
        exact ⟨coreTrace, .boundary coreRejected
          (expressionAtomBoundaryStops_of_isAtomBoundary rewound stops), coreEvents⟩
      · rename_i continues
        rcases recoverAtom_reject_trace_sound result with ⟨trace, rejection, events⟩
        have recovery : ExpressionAtomRecoveryTraceRejects input.file.id input.window.endByte
            (expressionAtomTraceRewind input.declarativeRemainder failed.declarativeRemainder)
            rejected.declarativeRemainder failure.toDiagnostic trace := by
          simpa only [State.emit, rewound, State.declarativeRemainder, expressionAtomTraceRewind,
            frame.1, frame.2] using rejection
        refine ⟨(coreTrace ++ [original.toDiagnostic]) ++ trace,
          .recovery coreRejected
            (no_expressionAtomBoundaryStops_of_isAtomBoundary_eq_false rewound (Bool.eq_false_iff.mpr continues)) recovery, ?_⟩
        calc
          rejected.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ trace := by
            simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
          _ = input.diagnostics ++ ((coreTrace ++ [original.toDiagnostic]) ++ trace) := by
            rw [coreEvents]
            simp only [List.append_assoc]
  | invariant error => simp only [expressionAtom, coreResult] at result; contradiction

theorem expressionAtom_trace_success_complete
    (coreSuccessComplete : ParserTraceSuccessComplete (expressionAtomCore nested block) coreTrace)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceSuccessComplete (expressionAtom nested block) (ExpressionAtomTraceParses coreTrace coreRejects) := by
  intro input value after trace parsed
  cases parsed with
  | core parsed =>
      rcases coreSuccessComplete parsed with ⟨output, result, afterEq, events⟩
      exact ⟨output, by simp only [expressionAtom, result], afterEq, events⟩
  | recovered coreRejected continues recovered =>
      rename_i failedR coreReport coreTraceEvents recoveryTrace
      rcases coreRejectComplete coreRejected with ⟨original, failed, coreResult, failedEq, reportEq, coreEvents⟩
      have frame := coreRejectFrame coreResult
      let rewound : State := { failed with cursor := input.cursor }
      have rewindEq : rewound.declarativeRemainder = _ :=
        congrArg (expressionAtomTraceRewind input.declarativeRemainder) failedEq
      rw [← rewindEq] at continues
      have guard := (isAtomBoundary_false_iff rewound).mpr continues
      dsimp only [rewound] at guard
      have ownerEq : (rewound.emit original.toDiagnostic).file.id = input.file.id := congrArg (·.id) frame.1
      have endEq : (rewound.emit original.toDiagnostic).window.endByte = input.window.endByte := frame.2
      rw [← rewindEq, ← ownerEq, ← endEq] at recovered
      rcases recoverAtom_trace_success_complete (input := rewound.emit original.toDiagnostic) recovered with
        ⟨output, result, afterEq, events⟩
      refine ⟨output, by simpa only [expressionAtom, coreResult, guard, Bool.false_eq_true, if_false] using result,
        afterEq, ?_⟩
      have events' : output.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ recoveryTrace := by
        simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
      rw [events', coreEvents, reportEq]
      simp only [List.append_assoc]

theorem expressionAtom_trace_reject_complete
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte) :
    ParserTraceRejectComplete (expressionAtom nested block) (ExpressionAtomTraceRejects coreRejects) := by
  intro input after report trace rejection
  cases rejection with
  | boundary coreRejected stops =>
      rcases coreRejectComplete coreRejected with ⟨original, failed, coreResult, failedEq, reportEq, coreEvents⟩
      let rewound : State := { failed with cursor := input.cursor }
      have rewindEq : rewound.declarativeRemainder = _ :=
        congrArg (expressionAtomTraceRewind input.declarativeRemainder) failedEq
      rw [← rewindEq] at stops
      have guard := (isAtomBoundary_true_iff rewound).mpr stops
      dsimp only [rewound] at guard
      exact ⟨original, rewound, by simp only [expressionAtom, coreResult, guard, if_true]; rfl,
        rewindEq, reportEq, coreEvents⟩
  | recovery coreRejected continues recoveryRejected =>
      rename_i failedR coreReport coreTraceEvents recoveryTrace
      rcases coreRejectComplete coreRejected with ⟨original, failed, coreResult, failedEq, reportEq, coreEvents⟩
      have frame := coreRejectFrame coreResult
      let rewound : State := { failed with cursor := input.cursor }
      have rewindEq : rewound.declarativeRemainder = _ :=
        congrArg (expressionAtomTraceRewind input.declarativeRemainder) failedEq
      rw [← rewindEq] at continues
      have guard := (isAtomBoundary_false_iff rewound).mpr continues
      dsimp only [rewound] at guard
      have ownerEq : (rewound.emit original.toDiagnostic).file.id = input.file.id := congrArg (·.id) frame.1
      have endEq : (rewound.emit original.toDiagnostic).window.endByte = input.window.endByte := frame.2
      rw [← rewindEq, ← ownerEq, ← endEq] at recoveryRejected
      rcases recoverAtom_trace_reject_complete (input := rewound.emit original.toDiagnostic) recoveryRejected with
        ⟨failure, rejected, result, afterEq, finalReportEq, events⟩
      refine ⟨failure, rejected,
        by simpa only [expressionAtom, coreResult, guard, Bool.false_eq_true, if_false] using result,
        afterEq, finalReportEq, ?_⟩
      have events' : rejected.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ recoveryTrace := by
        simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
      rw [events', coreEvents, reportEq]
      simp only [List.append_assoc]

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExpressionAtomTraceStateProperties
/-! The public rewind/recovery trace reconstructs every field of both outcomes,
including the exact terminal Failure separately from committed reports. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}
  {coreTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {coreRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem expressionAtom_trace_success_iff
    (coreSuccessSound : ParserTraceSuccessSound (expressionAtomCore nested block) coreTrace)
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreSuccessComplete : ParserTraceSuccessComplete (expressionAtomCore nested block) coreTrace)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionAtomTraceParses coreTrace coreRejects input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, expressionAtom nested block input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionAtom_trace_success_complete coreSuccessComplete coreRejectComplete coreRejectFrame
  · rintro ⟨output, result, afterEq, events⟩
    rcases expressionAtom_trace_success_sound coreSuccessSound coreRejectSound coreRejectFrame result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem expressionAtom_trace_reject_iff
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionAtomTraceRejects coreRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, expressionAtom nested block input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionAtom_trace_reject_complete coreRejectComplete coreRejectFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases expressionAtom_reject_trace_sound coreRejectSound coreRejectFrame result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem expressionAtom_trace_reject_failure_iff
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionAtomTraceRejects coreRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, expressionAtom nested block input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [expressionAtom_trace_reject_iff coreRejectSound coreRejectComplete coreRejectFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem expressionAtom_trace_success_state_iff
    (coreSuccessSound : ParserTraceSuccessSound (expressionAtomCore nested block) coreTrace)
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreSuccessComplete : ParserTraceSuccessComplete (expressionAtomCore nested block) coreTrace)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreSuccessFrame : ∀ {input output value}, expressionAtomCore nested block input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionAtomTraceParses coreTrace coreRejects input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      expressionAtom nested block input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases expressionAtom_trace_success_complete coreSuccessComplete coreRejectComplete coreRejectFrame parsed with ⟨output, result, afterEq, events⟩
    have frame := expressionAtom_success_source_end coreSuccessFrame coreRejectFrame result
    have same := State.eq_traceResult_of_fields frame.1
      frame.2 afterEq events
    exact same ▸ result
  · intro result
    exact (expressionAtom_trace_success_iff coreSuccessSound coreRejectSound coreSuccessComplete coreRejectComplete coreRejectFrame).mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionAtom_trace_reject_failure_state_iff
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionAtomTraceRejects coreRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      expressionAtom nested block input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (expressionAtom_trace_reject_failure_iff coreRejectSound coreRejectComplete coreRejectFrame).mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := expressionAtom_reject_source_end coreRejectFrame result
    have same := State.eq_traceResult_of_fields frame.1
      frame.2 afterEq events
    exact same ▸ result
  · intro result
    exact (expressionAtom_trace_reject_failure_iff coreRejectSound coreRejectComplete coreRejectFrame).mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionAtom_trace_reject_state_iff
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectComplete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionAtomTraceRejects coreRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, expressionAtom nested block input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases expressionAtom_trace_reject_complete coreRejectComplete coreRejectFrame rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (expressionAtom_trace_reject_failure_state_iff coreRejectSound coreRejectComplete coreRejectFrame).mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (expressionAtom_trace_reject_failure_state_iff coreRejectSound coreRejectComplete coreRejectFrame).mpr result

/-! Non-vacuous existence follows from the explicit core ordinary contract and
soundness, not from the independent joint uniqueness/disjointness laws. -/

theorem expressionAtom_exists_trace_outcome
    (coreOrdinary : Parser.Ordinary (expressionAtomCore nested block))
    (coreSuccessSound : ParserTraceSuccessSound (expressionAtomCore nested block) coreTrace)
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (input : State) :
    (∃ value output trace,
      expressionAtom nested block input = .ok value output ∧
      ExpressionAtomTraceParses coreTrace coreRejects input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      expressionAtom nested block input = .reject failure rejected ∧
      ExpressionAtomTraceRejects coreRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases expressionAtom_ordinary_of_core coreOrdinary input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases expressionAtom_trace_success_sound coreSuccessSound coreRejectSound coreRejectFrame result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases expressionAtom_reject_trace_sound coreRejectSound coreRejectFrame result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem expressionAtomTrace_outcome_exists
    (coreOrdinary : Parser.Ordinary (expressionAtomCore nested block))
    (coreSuccessSound : ParserTraceSuccessSound (expressionAtomCore nested block) coreTrace)
    (coreRejectSound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, ExpressionAtomTraceParses coreTrace coreRejects source endByte input value output trace) ∨
    (∃ rejected report trace, ExpressionAtomTraceRejects coreRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }
    tokens := input.tokens
    cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }
    diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases expressionAtom_exists_trace_outcome coreOrdinary coreSuccessSound coreRejectSound coreRejectFrame state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TupleClosingTraceProperties
/-! Exact silent tuple closing. Forward elements determine group versus tuple;
the closing span is supplied by the token, never recovered by inverting cover. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem closing_forward_reverse (opening closing : SourceSpan) (elementsRev : List Expr) :
    (match elementsRev with
      | [only] => ({ span := SourceSpan.cover opening closing, value := .group only } : Expr)
      | _ => {
          span := SourceSpan.cover opening closing
          value := .tuple { span := SourceSpan.cover opening closing, elements := elementsRev.reverse } }) =
      DeclarativeGrammar.closeParenthesizedExpression opening closing elementsRev.reverse := by
  cases elementsRev with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          dsimp only
          unfold DeclarativeGrammar.closeParenthesizedExpression
          split
          · rename_i only same
            have length := congrArg List.length same
            simp at length
          · rfl

theorem closeTuple_eq_of_symbol (opening : Token) (elementsRev : List Expr) (input : State) :
    closeTuple opening elementsRev input = match symbol .rightParen .expression input with
      | .ok closing output => .ok (DeclarativeGrammar.closeParenthesizedExpression
          opening.span closing.span elementsRev.reverse) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  unfold closeTuple
  cases result : symbol .rightParen .expression input <;> simp only [bind, result, pure]
  case ok closing output =>
    have shape := closing_forward_reverse opening.span closing.span elementsRev
    cases elementsRev with
    | nil => rfl
    | cons first rest => cases rest <;> simpa only using congrArg (fun value => Reply.ok value output) shape

theorem closeTuple_success_trace_sound (opening : Token) (elementsRev : List Expr)
    {input output : State} {value : Expr}
    (result : closeTuple opening elementsRev input = .ok value output) :
    ∃ closingSpan, DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
      input.declarativeRemainder closingSpan output.declarativeRemainder ∧
      value = DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan elementsRev.reverse ∧
      output = { input with cursor := input.cursor + 1 } := by
  rw [closeTuple_eq_of_symbol] at result
  cases closingResult : symbol .rightParen .expression input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok closing next =>
      simp only [closingResult] at result
      cases result
      exact ⟨closing.span, symbol_success_exactTokenParses .rightParen .expression closingResult,
        rfl, (symbol_ok_tokenAt .rightParen .expression closingResult).2⟩

theorem closeTuple_trace_success_iff (opening : Token) (elementsRev : List Expr)
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    ((∃ closingSpan, DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
      input.declarativeRemainder closingSpan after ∧
      value = DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan elementsRev.reverse) ∧ trace = []) ↔
    ∃ output, closeTuple opening elementsRev input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨⟨closingSpan, parsed, rfl⟩, rfl⟩
    have result := symbol_eq_ok_of_exactTokenParses .rightParen .expression parsed
    exact ⟨{ input with cursor := input.cursor + 1 }, by rw [closeTuple_eq_of_symbol, result],
      parsed.2.symm, by simp only [State.diagnostics, List.append_nil]⟩
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases closeTuple_success_trace_sound opening elementsRev result with ⟨closingSpan, parsed, valueEq, stateEq⟩
    refine ⟨⟨closingSpan, afterEq ▸ parsed, valueEq⟩, ?_⟩
    have : input.diagnostics ++ [] = input.diagnostics ++ trace := by
      simpa only [stateEq, State.diagnostics, List.append_nil] using diagnostics
    exact (List.append_cancel_left this).symm

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ParenthesizedTraceSoundnessProperties
/-! Successful actual parentheses reflect complete appended diagnostic traces.
Tail suffixes exclude the existing reverse prefix, which is used only for AST
assembly at the final closing token. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem tupleTail_success_trace_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) :
    ∀ fuel elementsRev input value output,
      tupleTail nested opening fuel elementsRev input = .ok value output →
      ∃ suffix closingSpan trace,
        value = DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan (elementsRev.reverse ++ suffix) ∧
        DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace input.file.id input.window.endByte
          input.declarativeRemainder suffix closingSpan output.declarativeRemainder trace ∧
        output.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input value output result; simp [tupleTail] at result
  | succ fuel ih =>
      intro elementsRev input value output result
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          have commaParsed := symbol_success_exactTokenParses .comma .expression commaResult
          have commaState := (symbol_ok_tokenAt .comma .expression commaResult).2
          subst afterComma
          simp only [commaResult] at result
          split at result
          · rcases closeTuple_success_trace_sound opening elementsRev result with
              ⟨closingSpan, closingParsed, valueEq, stateEq⟩
            refine ⟨[], closingSpan, [], by simpa only [List.append_nil] using valueEq,
              .trailing comma.span closingSpan commaParsed closingParsed, ?_⟩
            rw [stateEq]; simp only [State.diagnostics, List.append_nil]
          · rename_i noClose
            have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false .rightParen (Bool.eq_false_iff.mpr noClose)
            cases childResult : nested { input with cursor := input.cursor + 1 } with
            | invariant error => simp [childResult] at result
            | reject failure rejected => simp [childResult] at result
            | ok child next =>
                simp only [childResult] at result
                split at result
                · rename_i progress
                  rcases successSound childResult with ⟨headEvents, childParsed, childEq⟩
                  split at result
                  · have frame := contextFrame childResult
                    rcases ih (child :: elementsRev) next value output result with
                      ⟨suffix, closingSpan, tailEvents, valueEq, tailParsed, tailEq⟩
                    refine ⟨child :: suffix, closingSpan, headEvents ++ tailEvents, ?_,
                      .next comma.span closingSpan commaParsed closingAbsent childParsed progress ?_, ?_⟩
                    · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valueEq
                    · simpa only [frame.1, frame.2] using tailParsed
                    · rw [tailEq, childEq]; exact List.append_assoc _ _ _
                  · rename_i noComma
                    have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false .comma (Bool.eq_false_iff.mpr noComma)
                    rcases closeTuple_success_trace_sound opening (child :: elementsRev) result with
                      ⟨closingSpan, closingParsed, valueEq, stateEq⟩
                    refine ⟨[child], closingSpan, headEvents, ?_,
                      .final comma.span closingSpan commaParsed closingAbsent childParsed progress commaAbsent closingParsed, ?_⟩
                    · simpa only [List.reverse_cons] using valueEq
                    · rw [stateEq]; exact childEq
                · contradiction

theorem parenthesized_trace_success_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceSuccessSound (parenthesized nested)
      (DeclarativeGrammar.ParenthesizedExpressionTraceParses elementTrace) := by
  intro input output value result
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      have openingParsed := symbol_success_exactTokenParses .leftParen .expression openingResult
      have openingState := (symbol_ok_tokenAt .leftParen .expression openingResult).2
      subst afterOpening
      simp only [openingResult] at result
      split at result
      · rcases closeTuple_success_trace_sound opening [] result with ⟨closingSpan, closingParsed, valueEq, stateEq⟩
        refine ⟨[], ?_, ?_⟩
        · rw [valueEq]; exact .empty opening.span closingSpan openingParsed closingParsed
        · rw [stateEq]; simp only [State.diagnostics, List.append_nil]
      · rename_i noClose
        have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false .rightParen (Bool.eq_false_iff.mpr noClose)
        cases childResult : nested { input with cursor := input.cursor + 1 } with
        | invariant error => simp [childResult] at result
        | reject failure rejected => simp [childResult] at result
        | ok first next =>
            simp only [childResult] at result
            split at result
            · contradiction
            · rename_i noStall
              have progress : input.cursor + 1 < next.cursor := Nat.lt_of_not_ge noStall
              rcases successSound childResult with ⟨headEvents, childParsed, childEq⟩
              split at result
              · have frame := contextFrame childResult
                rcases tupleTail_success_trace_sound successSound contextFrame opening
                    (next.remainingCount + 1) [first] next value output result with
                  ⟨suffix, closingSpan, tailEvents, valueEq, tailParsed, tailEq⟩
                have valueShape : value = DeclarativeGrammar.closeParenthesizedExpression
                    opening.span closingSpan (first :: suffix) := by simpa using valueEq
                refine ⟨headEvents ++ tailEvents, ?_, ?_⟩
                · rw [valueShape]
                  exact .tuple opening.span closingSpan openingParsed closingAbsent childParsed progress
                    (by simpa only [frame.1, frame.2] using tailParsed)
                · rw [tailEq, childEq]; exact List.append_assoc _ _ _
              · rename_i noComma
                have commaAbsent := symbolAbsentAt_of_isSymbol_eq_false .comma (Bool.eq_false_iff.mpr noComma)
                rcases closeTuple_success_trace_sound opening [first] result with
                  ⟨closingSpan, closingParsed, valueEq, stateEq⟩
                refine ⟨headEvents, ?_, ?_⟩
                · rw [valueEq]
                  exact .group opening.span closingSpan openingParsed closingAbsent childParsed progress commaAbsent closingParsed
                · rw [stateEq]; exact childEq

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TupleTailTraceCompletenessProperties
/-! Successful tuple suffixes execute with sufficient remaining-token fuel.
Only successful source/full-window preservation and strict grammar progress
bound recursion; neither source validity nor a token-carrier law is needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DelimitedTraceInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem tupleTailTrace_comma_present {input : State} {values : List Expr} {closingSpan : SourceSpan}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder values closingSpan after trace) : isSymbol input .comma = true := by
  rcases parsed.comma_present with ⟨span, token⟩
  exact symbol_present .comma (after := { input.declarativeRemainder with cursor := input.cursor + 1 }) ⟨token, rfl⟩

theorem tupleTail_trace_success_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (fuel : Nat) (elementsRev : List Expr)
    {input : State} {suffix : List Expr} {closingSpan : SourceSpan}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder suffix closingSpan after trace)
    (adequate : input.remainingCount < fuel) :
    ∃ output, tupleTail nested opening fuel elementsRev input = .ok
        (DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan (elementsRev.reverse ++ suffix)) output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing elementsRev input suffix closingSpan after trace with
  | zero => omega
  | succ fuel ih =>
      cases parsed with
      | trailing commaSpan closingSpan comma finish =>
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
          rcases comma with ⟨_, rfl⟩
          have closingPresent := symbol_present .rightParen
            (input := { input with cursor := input.cursor + 1 }) finish
          rcases (closeTuple_trace_success_iff opening elementsRev
              (input := { input with cursor := input.cursor + 1 })).mp ⟨⟨closingSpan, finish, rfl⟩, rfl⟩ with
            ⟨output, result, afterEq, diagnostics⟩
          exact ⟨output, by simpa only [tupleTail, commaResult, closingPresent, if_true, List.append_nil] using result,
            afterEq, diagnostics⟩
      | final commaSpan closingSpan comma absent child progress noComma finish =>
          rename_i afterComma afterElement value
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
          rcases comma with ⟨_, rfl⟩
          rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
            ⟨next, childResult, afterEq, childEq⟩
          have nextProgress : input.cursor + 1 < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have noCommaNext : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex
              next.cursor (.symbol .comma) := by simpa only [← afterEq, State.declarativeRemainder] using noComma
          have finishNext : DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
              next.declarativeRemainder closingSpan after := by simpa only [afterEq] using finish
          rcases (closeTuple_trace_success_iff opening (value :: elementsRev)).mp
              ⟨⟨closingSpan, finishNext, rfl⟩, rfl⟩ with ⟨output, result, finalEq, diagnostics⟩
          refine ⟨output, ?_, finalEq, ?_⟩
          · simp only [tupleTail, commaResult, symbol_absent .rightParen
              (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true,
              if_false, childResult, nextProgress, if_true, symbol_absent .comma noCommaNext]
            simpa only [List.reverse_cons] using result
          · rw [diagnostics, List.append_nil]
            exact childEq
      | next commaSpan closingSpan comma absent child progress tail =>
          rename_i afterComma afterElement value rest headEvents tailEvents
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
          rcases comma with ⟨commaToken, rfl⟩
          rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
            ⟨next, childResult, afterEq, childEq⟩
          have frame := contextFrame childResult
          have nextProgress : input.cursor + 1 < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have tailAtNext : DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace
              next.file.id next.window.endByte next.declarativeRemainder rest closingSpan after tailEvents := by
            simpa only [frame.1, frame.2, afterEq] using tail
          have nextAdequate : next.remainingCount < fuel := by
            have inside : input.cursor < input.window.endIndex := commaToken.1
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          rcases ih (value :: elementsRev) tailAtNext nextAdequate with ⟨output, result, finalEq, diagnostics⟩
          refine ⟨output, ?_, finalEq, ?_⟩
          · simp only [tupleTail, commaResult, symbol_absent .rightParen
              (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true,
              if_false, childResult, nextProgress, if_true, tupleTailTrace_comma_present tailAtNext]
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using result
          · rw [diagnostics, childEq]; exact List.append_assoc _ _ _

theorem tupleTail_production_trace_success_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (elementsRev : List Expr)
    {input : State} {suffix : List Expr} {closingSpan : SourceSpan}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder suffix closingSpan after trace) :
    ∃ output, tupleTail nested opening (input.remainingCount + 1) elementsRev input = .ok
        (DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan (elementsRev.reverse ++ suffix)) output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  tupleTail_trace_success_complete successComplete contextFrame opening (input.remainingCount + 1) elementsRev parsed (by omega)

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ParenthesizedTraceCompletenessProperties
/-! Complete actual parenthesized success. In the tuple branch production
fuel is afterFirst.remainingCount + 1, exactly as in the implementation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DelimitedTraceInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem parenthesized_trace_success_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceSuccessComplete (parenthesized nested)
      (DeclarativeGrammar.ParenthesizedExpressionTraceParses elementTrace) := by
  intro input value after trace parsed
  cases parsed with
  | empty openingSpan closingSpan opening finish =>
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
      rcases opening with ⟨_, rfl⟩
      have closingPresent := symbol_present .rightParen
        (input := { input with cursor := input.cursor + 1 }) finish
      rcases (closeTuple_trace_success_iff { span := openingSpan, value := .symbol .leftParen } []
          (input := { input with cursor := input.cursor + 1 })).mp ⟨⟨closingSpan, finish, rfl⟩, rfl⟩ with
        ⟨output, result, afterEq, diagnostics⟩
      exact ⟨output, by simpa only [parenthesized, openingResult, closingPresent, if_true, List.reverse_nil] using result,
        afterEq, diagnostics⟩
  | group openingSpan closingSpan opening absent child progress noComma finish =>
      rename_i afterOpening afterElement element
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨next, childResult, afterEq, childEq⟩
      have nextProgress : input.cursor + 1 < next.cursor := by
        simpa only [← afterEq, State.declarativeRemainder] using progress
      have noCommaNext : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex
          next.cursor (.symbol .comma) := by simpa only [← afterEq, State.declarativeRemainder] using noComma
      have finishNext : DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
          next.declarativeRemainder closingSpan after := by simpa only [afterEq] using finish
      rcases (closeTuple_trace_success_iff { span := openingSpan, value := .symbol .leftParen } [element]).mp
          ⟨⟨closingSpan, finishNext, rfl⟩, rfl⟩ with ⟨output, result, finalEq, diagnostics⟩
      refine ⟨output, ?_, finalEq, ?_⟩
      · simpa only [parenthesized, openingResult, symbol_absent .rightParen
          (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false,
          childResult, Nat.not_le_of_gt nextProgress, symbol_absent .comma noCommaNext,
          List.reverse_cons, List.reverse_nil, List.nil_append] using result
      · rw [diagnostics, List.append_nil]; exact childEq
  | tuple openingSpan closingSpan opening absent child progress tail =>
      rename_i afterOpening afterFirst first rest headEvents tailEvents
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨next, childResult, afterEq, childEq⟩
      have frame := contextFrame childResult
      have nextProgress : input.cursor + 1 < next.cursor := by
        simpa only [← afterEq, State.declarativeRemainder] using progress
      have tailAtNext : DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace
          next.file.id next.window.endByte next.declarativeRemainder rest closingSpan after tailEvents := by
        simpa only [frame.1, frame.2, afterEq] using tail
      rcases tupleTail_production_trace_success_complete successComplete contextFrame
          { span := openingSpan, value := .symbol .leftParen } [first] tailAtNext with
        ⟨output, result, finalEq, diagnostics⟩
      refine ⟨output, ?_, finalEq, ?_⟩
      · simp only [parenthesized, openingResult, symbol_absent .rightParen
          (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false,
          childResult, Nat.not_le_of_gt nextProgress, tupleTailTrace_comma_present tailAtNext, if_true]
        simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] using result
      · rw [diagnostics, childEq]; exact List.append_assoc _ _ _

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ParenthesizedTraceContextProperties
/-! Source/full-window context follows successful children independently of
diagnostic traces and token-carrier preservation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}

theorem tupleTail_success_context (contextFrame : ExpressionSuccessContext nested) (opening : Token) :
    ∀ fuel elementsRev input value output, tupleTail nested opening fuel elementsRev input = .ok value output →
      output.file = input.file ∧ output.window = input.window := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input value output result; simp [tupleTail] at result
  | succ fuel ih =>
      intro elementsRev input value output result
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject failure rejected => simp [commaResult] at result
      | ok comma afterComma =>
          have commaState := (symbol_ok_tokenAt .comma .expression commaResult).2
          subst afterComma
          simp only [commaResult] at result
          split at result
          · rcases closeTuple_success_trace_sound opening elementsRev result with ⟨_, _, _, stateEq⟩
            rw [stateEq]; exact ⟨rfl, rfl⟩
          · cases childResult : nested { input with cursor := input.cursor + 1 } with
            | invariant error => simp [childResult] at result
            | reject failure rejected => simp [childResult] at result
            | ok child next =>
                simp only [childResult] at result
                split at result
                · have frame := contextFrame childResult
                  split at result
                  · have tail := ih (child :: elementsRev) next value output result
                    exact ⟨tail.1.trans frame.1, tail.2.trans frame.2⟩
                  · rcases closeTuple_success_trace_sound opening (child :: elementsRev) result with ⟨_, _, _, stateEq⟩
                    rw [stateEq]; exact frame
                · contradiction

theorem parenthesized_success_context (contextFrame : ExpressionSuccessContext nested) :
    ExpressionSuccessContext (parenthesized nested) := by
  intro input output value result
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      have openingState := (symbol_ok_tokenAt .leftParen .expression openingResult).2
      subst afterOpening
      simp only [openingResult] at result
      split at result
      · rcases closeTuple_success_trace_sound opening [] result with ⟨_, _, _, stateEq⟩
        rw [stateEq]; exact ⟨rfl, rfl⟩
      · cases childResult : nested { input with cursor := input.cursor + 1 } with
        | invariant error => simp [childResult] at result
        | reject failure rejected => simp [childResult] at result
        | ok first next =>
            simp only [childResult] at result
            split at result
            · contradiction
            · have frame := contextFrame childResult
              split at result
              · have tail := tupleTail_success_context contextFrame opening (next.remainingCount + 1)
                  [first] next value output result
                exact ⟨tail.1.trans frame.1, tail.2.trans frame.2⟩
              · rcases closeTuple_success_trace_sound opening [first] result with ⟨_, _, _, stateEq⟩
                rw [stateEq]; exact frame

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ParenthesizedTraceCorrespondenceProperties
/-! Exact successful parenthesized outcomes and arbitrary-prefix tuple tails.
The final AST is assembled from forward values; closing spans stay explicit. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem tupleTail_trace_success_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (fuel : Nat) (elementsRev : List Expr)
    {input : State} (adequate : input.remainingCount < fuel) {value : Expr}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    (∃ suffix closingSpan,
      value = DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan (elementsRev.reverse ++ suffix) ∧
      DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace input.file.id input.window.endByte
        input.declarativeRemainder suffix closingSpan after trace) ↔
    ∃ output, tupleTail nested opening fuel elementsRev input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨suffix, closingSpan, rfl, parsed⟩
    exact tupleTail_trace_success_complete successComplete contextFrame opening fuel elementsRev parsed adequate
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases tupleTail_success_trace_sound successSound contextFrame opening fuel elementsRev input value output result with
      ⟨suffix, closingSpan, actualTrace, valueEq, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    exact ⟨suffix, closingSpan, valueEq, by simpa only [afterEq, events] using parsed⟩

theorem tupleTail_production_trace_success_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (elementsRev : List Expr)
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    (∃ suffix closingSpan,
      value = DeclarativeGrammar.closeParenthesizedExpression opening.span closingSpan (elementsRev.reverse ++ suffix) ∧
      DeclarativeGrammar.ParenthesizedTupleTailTraceParses elementTrace input.file.id input.window.endByte
        input.declarativeRemainder suffix closingSpan after trace) ↔
    ∃ output, tupleTail nested opening (input.remainingCount + 1) elementsRev input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  tupleTail_trace_success_iff successSound successComplete contextFrame opening
    (input.remainingCount + 1) elementsRev (by omega)

theorem parenthesized_trace_success_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedExpressionTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, parenthesized nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parenthesized_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parenthesized_trace_success_sound successSound contextFrame result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TupleClosingRejectionTraceProperties
/-! Closing failure preserves the entire state and asks only for a right
parenthesis, regardless of the accumulated reverse element prefix. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem closeTuple_reject_iff_symbol (opening : Token) (elementsRev : List Expr)
    {input rejected : State} {failure : Failure} :
    closeTuple opening elementsRev input = .reject failure rejected ↔
      symbol .rightParen .expression input = .reject failure rejected := by
  rw [closeTuple_eq_of_symbol]
  cases symbol .rightParen .expression input <;> simp

theorem closeTuple_reject_state_eq (opening : Token) (elementsRev : List Expr)
    {input rejected : State} {failure : Failure}
    (result : closeTuple opening elementsRev input = .reject failure rejected) : rejected = input :=
  symbol_reject_state_eq .rightParen .expression ((closeTuple_reject_iff_symbol opening elementsRev).mp result)

theorem closeTuple_reject_reports_iff (opening : Token) (elementsRev : List Expr)
    {input : State} {report : ParseDiagnostic} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .rightParen) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .symbol .rightParen, tail := [] } .expression input.declarativeRemainder report) ↔
      ∃ failure, closeTuple opening elementsRev input = .reject failure input ∧ failure.toDiagnostic = report := by
  rw [symbol_reject_reports_iff .rightParen .expression]
  simp only [closeTuple_reject_iff_symbol]

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TupleTailRejectionTraceSoundnessProperties
/-! Every raw fixed-fuel tuple-tail rejection reflects the exact uncommitted
report and ordered event suffix. No selection or token-carrier premise. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DelimitedTraceInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem tupleTail_reject_trace_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) :
    ∀ fuel elementsRev input failure rejected,
      tupleTail nested opening fuel elementsRev input = .reject failure rejected →
      ∃ trace, DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
        input.file.id input.window.endByte input.declarativeRemainder rejected.declarativeRemainder
        failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input failure rejected result; simp [tupleTail] at result
  | succ fuel ih =>
      intro elementsRev input failure rejected result
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject commaFailure commaRejected =>
          have shape := symbol_reject_state_eq .comma .expression commaResult
          subst commaRejected
          simp only [commaResult] at result
          cases result
          have reported := (symbol_reject_reports_iff .comma .expression).mpr ⟨failure, commaResult, rfl⟩
          exact ⟨[], .commaMissing reported.1 reported.2, by simp⟩
      | ok comma afterComma =>
          have commaParsed := symbol_success_exactTokenParses .comma .expression commaResult
          have shape := (symbol_ok_tokenAt .comma .expression commaResult).2
          simp only [commaResult] at result
          by_cases closingPresent : isSymbol afterComma .rightParen = true
          · rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .expression closingPresent with ⟨closing, closingResult⟩
            simp [closingPresent, closeTuple_eq_of_symbol, closingResult] at result
          · have closingFalse := Bool.eq_false_iff.mpr closingPresent
            have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false .rightParen closingFalse
            simp only [closingFalse, Bool.false_eq_true, if_false] at result
            cases childResult : nested afterComma with
            | invariant error => simp [childResult] at result
            | reject childFailure childRejected =>
                simp only [childResult] at result
                cases result
                rcases rejectSound childResult with ⟨trace, childRejected, diagnostics⟩
                refine ⟨trace, .elementRejected comma.span commaParsed closingAbsent ?_, ?_⟩
                · simpa only [shape] using childRejected
                · simpa only [shape, State.diagnostics] using diagnostics
            | ok value next =>
                simp only [childResult] at result
                by_cases progress : next.cursor > afterComma.cursor
                · simp only [progress, if_true] at result
                  rcases successSound childResult with ⟨childEvents, childParsed, childEq⟩
                  have frame := contextFrame childResult
                  have childAtInput : elementTrace input.file.id input.window.endByte afterComma.declarativeRemainder
                      value next.declarativeRemainder childEvents := by simpa only [shape] using childParsed
                  by_cases commaPresent : isSymbol next .comma = true
                  · simp only [commaPresent, if_true] at result
                    rcases symbol_eq_ok_of_isSymbol_eq_true .comma .expression commaPresent with ⟨nextComma, nextResult⟩
                    rcases ih (value :: elementsRev) next failure rejected result with ⟨tailEvents, tailRejected, tailEq⟩
                    have tailAtInput : DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
                        input.file.id input.window.endByte next.declarativeRemainder rejected.declarativeRemainder
                        failure.toDiagnostic tailEvents := by simpa only [frame.1, frame.2, shape] using tailRejected
                    refine ⟨childEvents ++ tailEvents, .laterRejected comma.span nextComma.span commaParsed closingAbsent
                      childAtInput progress (symbol_ok_tokenAt .comma .expression nextResult).1 tailAtInput, ?_⟩
                    rw [tailEq, childEq, List.append_assoc]
                    simp only [shape, State.diagnostics]
                  · have commaFalse := Bool.eq_false_iff.mpr commaPresent
                    simp only [commaFalse, Bool.false_eq_true, if_false] at result
                    have rejectedEq := closeTuple_reject_state_eq opening (value :: elementsRev) result
                    subst rejected
                    have reported := (closeTuple_reject_reports_iff opening (value :: elementsRev)).mpr ⟨failure, result, rfl⟩
                    refine ⟨childEvents, .closingMissing comma.span commaParsed closingAbsent childAtInput progress
                      (symbolAbsentAt_of_isSymbol_eq_false .comma commaFalse) reported.1 ?_, ?_⟩
                    · simpa only [frame.1, frame.2, shape] using reported.2
                    · simpa only [shape, State.diagnostics] using childEq
                · simp only [progress, if_false] at result
                  contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.TupleTailRejectionTraceCompletenessProperties
/-! Independent raw tuple rejection derivations execute with adequate fuel.
Only strict cursor progress and the successful full-window frame bound the
recursive calls; neither token preservation nor input validity is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DelimitedTraceInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem tupleTail_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (fuel : Nat) (elementsRev : List Expr)
    {input : State} {after : DeclarativeGrammar.Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace)
    (adequate : input.remainingCount < fuel) :
    ∃ failure rejected, tupleTail nested opening fuel elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing elementsRev input after report trace with
  | zero => omega
  | succ fuel ih =>
      cases rejection with
      | commaMissing absent reported =>
          rcases (symbol_reject_reports_iff .comma .expression).mp ⟨absent, reported⟩ with ⟨failure, result, reportEq⟩
          exact ⟨failure, input, by simp only [tupleTail, result], rfl, reportEq, by simp⟩
      | elementRejected commaSpan comma absent child =>
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
          rcases comma with ⟨_, rfl⟩
          rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) child with
            ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
          exact ⟨failure, rejected, by
            simp only [tupleTail, commaResult, symbol_absent .rightParen
              (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false, result],
            afterEq, reportEq, diagnostics⟩
      | closingMissing commaSpan comma absent child progress noComma noClosing reported =>
          rename_i afterComma value
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
          rcases comma with ⟨_, rfl⟩
          rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
            ⟨next, childResult, afterEq, childEq⟩
          have frame := contextFrame childResult
          have nextProgress : input.cursor + 1 < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have noCommaNext : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex
              next.cursor (.symbol .comma) := by simpa only [← afterEq, State.declarativeRemainder] using noComma
          have noClosingNext : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex
              next.cursor (.symbol .rightParen) := by simpa only [← afterEq, State.declarativeRemainder] using noClosing
          have reportNext : DeclarativeGrammar.RejectAtReports next.file.id next.window.endByte
              { head := .symbol .rightParen, tail := [] } .expression next.declarativeRemainder report := by
            simpa only [frame.1, frame.2, afterEq] using reported
          rcases (closeTuple_reject_reports_iff opening (value :: elementsRev)).mp ⟨noClosingNext, reportNext⟩ with
            ⟨failure, result, reportEq⟩
          exact ⟨failure, next, by
            simp only [tupleTail, commaResult, symbol_absent .rightParen
              (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false,
              childResult, nextProgress, if_true, symbol_absent .comma noCommaNext, result],
            afterEq, reportEq, childEq⟩
      | laterRejected commaSpan nextSpan comma absent child progress nextComma tail =>
          rename_i afterComma afterElement value childEvents tailEvents
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
          rcases comma with ⟨commaToken, rfl⟩
          rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
            ⟨next, childResult, afterEq, childEq⟩
          have frame := contextFrame childResult
          have nextProgress : input.cursor + 1 < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have nextCommaToken : DeclarativeGrammar.TokenAt next.tokens next.window.endIndex next.cursor
              { span := nextSpan, value := .symbol .comma } := by
            simpa only [← afterEq, State.declarativeRemainder] using nextComma
          have nextCommaPresent := symbol_present .comma
            (after := { next.declarativeRemainder with cursor := next.cursor + 1 }) ⟨nextCommaToken, rfl⟩
          have tailAtNext : DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
              next.file.id next.window.endByte next.declarativeRemainder after report tailEvents := by
            simpa only [frame.1, frame.2, afterEq] using tail
          have nextAdequate : next.remainingCount < fuel := by
            have inside : input.cursor < input.window.endIndex := commaToken.1
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          rcases ih (value :: elementsRev) tailAtNext nextAdequate with
            ⟨failure, rejected, result, finalEq, reportEq, diagnostics⟩
          refine ⟨failure, rejected, ?_, finalEq, reportEq, ?_⟩
          · simp only [tupleTail, commaResult, symbol_absent .rightParen
              (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false,
              childResult, nextProgress, if_true, nextCommaPresent]
            exact result
          · rw [diagnostics, childEq, List.append_assoc]
            rfl

theorem tupleTail_production_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (elementsRev : List Expr)
    {input : State} {after : DeclarativeGrammar.Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace) :
    ∃ failure rejected, tupleTail nested opening (input.remainingCount + 1) elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  tupleTail_trace_reject_complete successComplete rejectComplete contextFrame opening
    (input.remainingCount + 1) elementsRev rejection (by omega)

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ParenthesizedRejectionTraceSoundnessProperties
/-! Raw parenthesized rejection reflection, including a missing opening token.
The tail route explicitly records the comma selected after the first child. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parenthesized_reject_trace_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceRejectSound (parenthesized nested)
      (DeclarativeGrammar.ParenthesizedExpressionTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      have shape := symbol_reject_state_eq .leftParen .expression openingResult
      subst openingRejected
      simp only [openingResult] at result
      cases result
      have reported := (symbol_reject_reports_iff .leftParen .expression).mpr ⟨failure, openingResult, rfl⟩
      exact ⟨[], .openingMissing reported.1 reported.2, by simp⟩
  | ok opening afterOpening =>
      have openingParsed := symbol_success_exactTokenParses .leftParen .expression openingResult
      have shape := (symbol_ok_tokenAt .leftParen .expression openingResult).2
      simp only [openingResult] at result
      by_cases closingPresent : isSymbol afterOpening .rightParen = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .expression closingPresent with ⟨closing, closingResult⟩
        simp [closingPresent, closeTuple_eq_of_symbol, closingResult] at result
      · have closingFalse := Bool.eq_false_iff.mpr closingPresent
        have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false .rightParen closingFalse
        simp only [closingFalse, Bool.false_eq_true, if_false] at result
        cases childResult : nested afterOpening with
        | invariant error => simp [childResult] at result
        | reject childFailure childRejected =>
            simp only [childResult] at result
            cases result
            rcases rejectSound childResult with ⟨trace, childRejected, diagnostics⟩
            refine ⟨trace, .firstRejected opening.span openingParsed closingAbsent ?_, ?_⟩
            · simpa only [shape] using childRejected
            · simpa only [shape, State.diagnostics] using diagnostics
        | ok first next =>
            simp only [childResult] at result
            by_cases noProgress : next.cursor ≤ afterOpening.cursor
            · simp only [noProgress, if_true] at result
              contradiction
            · simp only [noProgress, if_false] at result
              have progress : afterOpening.cursor < next.cursor := Nat.lt_of_not_ge noProgress
              rcases successSound childResult with ⟨childEvents, childParsed, childEq⟩
              have frame := contextFrame childResult
              have childAtInput : elementTrace input.file.id input.window.endByte afterOpening.declarativeRemainder
                  first next.declarativeRemainder childEvents := by simpa only [shape] using childParsed
              by_cases commaPresent : isSymbol next .comma = true
              · simp only [commaPresent, if_true] at result
                rcases symbol_eq_ok_of_isSymbol_eq_true .comma .expression commaPresent with ⟨comma, commaResult⟩
                rcases tupleTail_reject_trace_sound successSound rejectSound contextFrame opening
                  (next.remainingCount + 1) [first] next failure rejected result with ⟨tailEvents, tailRejected, tailEq⟩
                have tailAtInput : DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
                    input.file.id input.window.endByte next.declarativeRemainder rejected.declarativeRemainder
                    failure.toDiagnostic tailEvents := by simpa only [frame.1, frame.2, shape] using tailRejected
                refine ⟨childEvents ++ tailEvents, .tailRejected opening.span comma.span openingParsed closingAbsent
                  childAtInput progress (symbol_ok_tokenAt .comma .expression commaResult).1 tailAtInput, ?_⟩
                rw [tailEq, childEq, List.append_assoc]
                simp only [shape, State.diagnostics]
              · have commaFalse := Bool.eq_false_iff.mpr commaPresent
                simp only [commaFalse, Bool.false_eq_true, if_false] at result
                have rejectedEq := closeTuple_reject_state_eq opening [first] result
                subst rejected
                have reported := (closeTuple_reject_reports_iff opening [first]).mpr ⟨failure, result, rfl⟩
                refine ⟨childEvents, .closingMissing opening.span openingParsed closingAbsent childAtInput progress
                  (symbolAbsentAt_of_isSymbol_eq_false .comma commaFalse) reported.1 ?_, ?_⟩
                · simpa only [frame.1, frame.2, shape] using reported.2
                · simpa only [shape, State.diagnostics] using childEq

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ParenthesizedRejectionTraceCompletenessProperties
/-! Raw parenthesized rejection execution. The production tail fuel is exactly
the remaining count after the first successful child, plus one. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DelimitedTraceInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parenthesized_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceRejectComplete (parenthesized nested)
      (DeclarativeGrammar.ParenthesizedExpressionTraceRejects elementTrace elementRejects) := by
  intro input after report trace rejection
  cases rejection with
  | openingMissing absent reported =>
      rcases (symbol_reject_reports_iff .leftParen .expression).mp ⟨absent, reported⟩ with ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [parenthesized, result], rfl, reportEq, by simp⟩
  | firstRejected openingSpan opening absent child =>
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
      rcases opening with ⟨_, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
      exact ⟨failure, rejected, by
        simp only [parenthesized, openingResult, symbol_absent .rightParen
          (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false, result],
        afterEq, reportEq, diagnostics⟩
  | closingMissing openingSpan opening absent child progress noComma noClosing reported =>
      rename_i afterOpening value
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨next, childResult, afterEq, childEq⟩
      have frame := contextFrame childResult
      have nextProgress : ¬ next.cursor ≤ input.cursor + 1 := by
        have : input.cursor + 1 < next.cursor := by
          simpa only [← afterEq, State.declarativeRemainder] using progress
        omega
      have noCommaNext : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex
          next.cursor (.symbol .comma) := by simpa only [← afterEq, State.declarativeRemainder] using noComma
      have noClosingNext : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex
          next.cursor (.symbol .rightParen) := by simpa only [← afterEq, State.declarativeRemainder] using noClosing
      have reportNext : DeclarativeGrammar.RejectAtReports next.file.id next.window.endByte
          { head := .symbol .rightParen, tail := [] } .expression next.declarativeRemainder report := by
        simpa only [frame.1, frame.2, afterEq] using reported
      rcases (closeTuple_reject_reports_iff { span := openingSpan, value := .symbol .leftParen } [value]).mp
          ⟨noClosingNext, reportNext⟩ with ⟨failure, result, reportEq⟩
      exact ⟨failure, next, by
        simp only [parenthesized, openingResult, symbol_absent .rightParen
          (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false,
          childResult, nextProgress, symbol_absent .comma noCommaNext, result],
        afterEq, reportEq, childEq⟩
  | tailRejected openingSpan commaSpan opening absent child progress comma tail =>
      rename_i afterOpening afterFirst first childEvents tailEvents
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) child with
        ⟨next, childResult, afterEq, childEq⟩
      have frame := contextFrame childResult
      have nextProgress : ¬ next.cursor ≤ input.cursor + 1 := by
        have : input.cursor + 1 < next.cursor := by
          simpa only [← afterEq, State.declarativeRemainder] using progress
        omega
      have commaToken : DeclarativeGrammar.TokenAt next.tokens next.window.endIndex next.cursor
          { span := commaSpan, value := .symbol .comma } := by
        simpa only [← afterEq, State.declarativeRemainder] using comma
      have commaPresent := symbol_present .comma
        (after := { next.declarativeRemainder with cursor := next.cursor + 1 }) ⟨commaToken, rfl⟩
      have tailAtNext : DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
          next.file.id next.window.endByte next.declarativeRemainder after report tailEvents := by
        simpa only [frame.1, frame.2, afterEq] using tail
      rcases tupleTail_production_trace_reject_complete successComplete rejectComplete contextFrame
          { span := openingSpan, value := .symbol .leftParen } [first] tailAtNext with
        ⟨failure, rejected, result, finalEq, reportEq, diagnostics⟩
      refine ⟨failure, rejected, ?_, finalEq, reportEq, ?_⟩
      · simp only [parenthesized, openingResult, symbol_absent .rightParen
          (input := { input with cursor := input.cursor + 1 }) absent, Bool.false_eq_true, if_false,
          childResult, nextProgress, commaPresent, if_true]
        exact result
      · rw [diagnostics, childEq, List.append_assoc]
        rfl

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ParenthesizedRejectionTraceCorrespondenceProperties
/-! Adequate raw-tail and production parenthesized correspondences preserve
the entire Failure, arbitrary incoming events, and reverse element prefixes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem tupleTail_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (fuel : Nat) (elementsRev : List Expr)
    {input : State} (adequate : input.remainingCount < fuel)
    {after : DeclarativeGrammar.Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, tupleTail nested opening fuel elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro rejection
    exact tupleTail_trace_reject_complete successComplete rejectComplete contextFrame
      opening fuel elementsRev rejection adequate
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases tupleTail_reject_trace_sound successSound rejectSound contextFrame opening fuel elementsRev input failure rejected result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem tupleTail_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (fuel : Nat) (elementsRev : List Expr)
    {input : State} (adequate : input.remainingCount < fuel)
    {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, tupleTail nested opening fuel elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [tupleTail_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame opening fuel elementsRev adequate]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem parenthesized_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State}
    {after : DeclarativeGrammar.Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedExpressionTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parenthesized nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parenthesized_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parenthesized_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parenthesized_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State}
    {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedExpressionTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parenthesized nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parenthesized_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem tupleTail_production_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (elementsRev : List Expr)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, tupleTail nested opening (input.remainingCount + 1) elementsRev input =
        .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      failure.toDiagnostic = report ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  tupleTail_trace_reject_iff successSound rejectSound successComplete rejectComplete
    contextFrame opening (input.remainingCount + 1) elementsRev (by omega)

theorem tupleTail_production_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (elementsRev : List Expr)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, tupleTail nested opening (input.remainingCount + 1) elementsRev input =
        .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  tupleTail_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete
    contextFrame opening (input.remainingCount + 1) elementsRev (by omega)

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.ArrayLiteralTraceProperties
/-! Exact traces for the actual array wrapper, conditional only on the five
child-expression contracts. Successful mapping changes the AST alone; ordinary
failure and its complete state escape unchanged without committing a report. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {element : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem arrayLiteral_success_iff_raw {input output : State} {value : Expr} :
    arrayLiteral element input = .ok value output ↔
      ∃ values, delimitedNoTrailing .leftBracket .rightBracket true element .expression .expression input =
        .ok values output ∧ value = { span := values.span, value := .array values } := by
  cases result : delimitedNoTrailing .leftBracket .rightBracket true element .expression .expression input <;>
    simp only [arrayLiteral, bind, result, pure, reduceCtorEq, Reply.ok.injEq]
  case ok values next =>
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨values, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨other, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
  case reject => simp
  case invariant => simp

theorem arrayLiteral_reject_iff_raw {input rejected : State} {failure : Failure} :
    arrayLiteral element input = .reject failure rejected ↔
      delimitedNoTrailing .leftBracket .rightBracket true element .expression .expression input =
        .reject failure rejected := by
  cases result : delimitedNoTrailing .leftBracket .rightBracket true element .expression .expression input <;>
    simp only [arrayLiteral, bind, result, pure, reduceCtorEq, Reply.reject.injEq, iff_self]

theorem arrayLiteral_trace_success_sound
    (successSound : ExpressionTraceSuccessSound element elementTrace)
    (contextFrame : ExpressionSuccessContext element) :
    ExpressionTraceSuccessSound (arrayLiteral element)
      (DeclarativeGrammar.ArrayLiteralTraceParses elementTrace) := by
  intro input output value result
  rcases arrayLiteral_success_iff_raw.mp result with ⟨values, raw, rfl⟩
  rcases delimitedNoTrailing_success_trace_sound successSound contextFrame
      .leftBracket .rightBracket true .expression .expression raw with ⟨trace, parsed, events⟩
  exact ⟨trace, .parsed parsed, events⟩

theorem arrayLiteral_trace_success_complete
    (successComplete : ExpressionTraceSuccessComplete element elementTrace)
    (contextFrame : ExpressionSuccessContext element) :
    ExpressionTraceSuccessComplete (arrayLiteral element)
      (DeclarativeGrammar.ArrayLiteralTraceParses elementTrace) := by
  intro input value after trace parsed
  cases parsed with
  | parsed values =>
      rcases delimitedNoTrailing_trace_success_complete successComplete contextFrame
          .leftBracket .rightBracket true .expression .expression values with ⟨output, result, afterEq, events⟩
      exact ⟨output, arrayLiteral_success_iff_raw.mpr ⟨_, result, rfl⟩, afterEq, events⟩

theorem arrayLiteral_trace_reject_sound
    (successSound : ExpressionTraceSuccessSound element elementTrace)
    (rejectSound : ExpressionTraceRejectSound element elementRejects)
    (contextFrame : ExpressionSuccessContext element) :
    ExpressionTraceRejectSound (arrayLiteral element)
      (DeclarativeGrammar.ArrayLiteralTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  exact delimitedNoTrailing_reject_trace_sound successSound rejectSound contextFrame
    .leftBracket .rightBracket true .expression .expression (arrayLiteral_reject_iff_raw.mp result)

theorem arrayLiteral_trace_reject_complete
    (successComplete : ExpressionTraceSuccessComplete element elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete element elementRejects)
    (contextFrame : ExpressionSuccessContext element) :
    ExpressionTraceRejectComplete (arrayLiteral element)
      (DeclarativeGrammar.ArrayLiteralTraceRejects elementTrace elementRejects) := by
  intro input after diagnostic trace rejected
  rcases delimitedNoTrailing_trace_reject_complete successComplete rejectComplete contextFrame
      .leftBracket .rightBracket true .expression .expression rejected with
    ⟨failure, output, result, afterEq, reportEq, events⟩
  exact ⟨failure, output, arrayLiteral_reject_iff_raw.mpr result, afterEq, reportEq, events⟩

theorem arrayLiteral_success_context
    (contextFrame : ExpressionSuccessContext element) :
    ExpressionSuccessContext (arrayLiteral element) := by
  intro input output value result
  rcases arrayLiteral_success_iff_raw.mp result with ⟨values, raw, _⟩
  exact delimitedNoTrailing_success_context contextFrame .leftBracket .rightBracket true
    .expression .expression raw

theorem arrayLiteral_trace_success_iff
    (successSound : ExpressionTraceSuccessSound element elementTrace)
    (successComplete : ExpressionTraceSuccessComplete element elementTrace)
    (contextFrame : ExpressionSuccessContext element)
    {input : State} {value : Expr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ArrayLiteralTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, arrayLiteral element input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact arrayLiteral_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, events⟩
    rcases arrayLiteral_trace_success_sound successSound contextFrame result with
      ⟨actual, parsed, actualEvents⟩
    have traceEq : actual = trace := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem arrayLiteral_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound element elementTrace)
    (rejectSound : ExpressionTraceRejectSound element elementRejects)
    (successComplete : ExpressionTraceSuccessComplete element elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete element elementRejects)
    (contextFrame : ExpressionSuccessContext element)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ArrayLiteralTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
      ∃ failure rejected, arrayLiteral element input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact arrayLiteral_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases arrayLiteral_trace_reject_sound successSound rejectSound contextFrame result with
      ⟨actual, rejection, actualEvents⟩
    have traceEq : actual = trace := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem arrayLiteral_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound element elementTrace)
    (rejectSound : ExpressionTraceRejectSound element elementRejects)
    (successComplete : ExpressionTraceSuccessComplete element elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete element elementRejects)
    (contextFrame : ExpressionSuccessContext element)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ArrayLiteralTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, arrayLiteral element input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [arrayLiteral_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

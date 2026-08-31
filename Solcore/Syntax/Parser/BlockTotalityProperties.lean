import Solcore.Syntax.Parser.Block
import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.InvariantFreeProperties

/-! Valid-input totality for Core block loops and captured blocks. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Closing a block can only succeed or reject at its closing brace. -/
theorem closeCoreBlock_ne_invariant (opening : Token)
    (policy : TailExpressionPolicy) (bodyRev : List Statement)
    (input : State) (error : ParserInvariantError) :
    closeCoreBlock opening policy bodyRev input ≠ .invariant error := by
  intro invariantResult
  unfold closeCoreBlock at invariantResult
  simp only [bind] at invariantResult
  cases closingResult : symbol .rightBrace .statement input with
  | ok closing afterClosing =>
      simp [closingResult, modifyState, pure] at invariantResult
  | reject failure rejected =>
      simp [closingResult] at invariantResult
  | invariant closingError =>
      exact (symbol_ne_invariant .rightBrace .statement input closingError)
        closingResult

private theorem symbol_ne_ok_of_atEnd (value : Symbol)
    (context : ParseContext) {input next : State} {token : Token}
    (atEnd : input.atEnd = true)
    (result : symbol value context input = .ok token next) : False := by
  have found := (symbol_ok_state_shape value context result).1
  have beforeEnd := State.cursor_lt_endIndex_of_peek?_eq_some found
  have ended : input.window.endIndex <= input.cursor := by
    simpa [State.atEnd] using atEnd
  omega

/--
Adequate token fuel excludes all defensive block-loop invariants. Each
successful statement must preserve the active window and consume a token.
-/
theorem coreBlockItems_ne_invariant_of_remainingCount_lt
    (statement : Parser Statement)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement)
    (statementStrict : forall {input next : State} {value : Statement},
      statement input = .ok value next -> input.cursor < next.cursor)
    (statementFree : Parser.InvariantFreeOnValid statement)
    (opening : Token) (policy : TailExpressionPolicy) :
    forall fuel bodyRev input,
      input.ValidFor -> input.remainingCount < fuel ->
      forall error,
        coreBlockItems statement opening policy fuel bodyRev input ≠
          .invariant error := by
  intro fuel
  induction fuel with
  | zero =>
      intro bodyRev input inputValid adequate error
      omega
  | succ fuel inductionHypothesis =>
      intro bodyRev input inputValid adequate error invariantResult
      unfold coreBlockItems at invariantResult
      split at invariantResult
      · exact closeCoreBlock_ne_invariant opening policy bodyRev input error
          invariantResult
      · split at invariantResult
        · have atEnd : input.atEnd = true := by assumption
          cases closingResult : symbol .rightBrace .statement input with
          | ok closing afterClosing =>
              exact symbol_ne_ok_of_atEnd .rightBrace .statement atEnd
                closingResult
          | reject failure rejected =>
              simp [closingResult] at invariantResult
          | invariant closingError =>
              exact (symbol_ne_invariant .rightBrace .statement input
                closingError) closingResult
        · cases statementResult : statement input with
          | reject failure rejected =>
              simp [statementResult] at invariantResult
          | invariant statementError =>
              exact statementFree.ne_invariant input inputValid
                statementError statementResult
          | ok value afterStatement =>
              have replyValid := statementValid input inputValid
              rw [statementResult] at replyValid
              have replyWindow := statementWindow input
              rw [statementResult] at replyWindow
              have progress := statementStrict statementResult
              simp only [statementResult] at invariantResult
              split at invariantResult
              · have nextAdequate : afterStatement.remainingCount < fuel :=
                  remainingCount_lt_after_strict_progress replyValid.2.1
                    replyWindow.2 progress adequate
                exact inductionHypothesis (value :: bodyRev) afterStatement
                  replyValid.2.1 nextAdequate error invariantResult
              · omega

/-- A Core block cannot expose loop invariants on valid parser states. -/
theorem coreBlock_ne_invariant (statement : Parser Statement)
    (policy : TailExpressionPolicy)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement)
    (statementStrict : forall {input next : State} {value : Statement},
      statement input = .ok value next -> input.cursor < next.cursor)
    (statementFree : Parser.InvariantFreeOnValid statement)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    coreBlock statement policy input ≠ .invariant error := by
  intro invariantResult
  unfold coreBlock at invariantResult
  cases openingResult : symbol .leftBrace .statement input with
  | reject failure rejected =>
      simp [openingResult] at invariantResult
  | invariant openingError =>
      exact (symbol_ne_invariant .leftBrace .statement input openingError)
        openingResult
  | ok opening afterOpening =>
      have openingReply :=
        symbol_validFor .leftBrace .statement input inputValid
      rw [openingResult] at openingReply
      exact coreBlockItems_ne_invariant_of_remainingCount_lt statement
        statementValid statementWindow statementStrict statementFree opening
          policy (afterOpening.remainingCount + 1) [] afterOpening
          openingReply.2.1 (by omega) error (by
            simpa only [openingResult] using invariantResult)

/-- Valid inputs always receive an ordinary Core-block reply. -/
theorem coreBlock_invariantFreeOnValid (statement : Parser Statement)
    (policy : TailExpressionPolicy)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement)
    (statementStrict : forall {input next : State} {value : Statement},
      statement input = .ok value next -> input.cursor < next.cursor)
    (statementFree : Parser.InvariantFreeOnValid statement) :
    Parser.InvariantFreeOnValid (coreBlock statement policy) :=
  Parser.invariantFreeOnValid_of_ne_invariant
    (coreBlock_ne_invariant statement policy statementValid statementWindow
      statementStrict statementFree)

/-- Isolation preserves invariant freedom, including its recovery path. -/
theorem BlockInternals.isolateBlock_invariantFreeOnValid
    (parser : Parser Block)
    (parserFree : Parser.InvariantFreeOnValid parser) :
    Parser.InvariantFreeOnValid (isolateBlock parser) := by
  apply Parser.invariantFreeOnValid_of_ne_invariant
  intro input inputValid error invariantResult
  unfold isolateBlock at invariantResult
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      exact parserFree.ne_invariant input inputValid error (by
        simpa only [captureResult] using invariantResult)
  | some captured =>
      have childValid :=
        (BlockInternals.captureBlock?_validFor inputValid captureResult).entered
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | ok body childAfter =>
          simp [captureResult, childResult] at invariantResult
      | reject failure childAfter =>
          simp [captureResult, childResult] at invariantResult
      | invariant childError =>
          exact parserFree.ne_invariant _ childValid childError childResult

/-- Isolation is strict when its uncaptured parser is strict. -/
theorem BlockInternals.isolateBlock_cursor_lt_onSuccess
    (parser : Parser Block)
    (parserStrict : forall {input next : State} {body : Block},
      parser input = .ok body next -> input.cursor < next.cursor)
    {input next : State} {body : Block}
    (result : isolateBlock parser input = .ok body next) :
    input.cursor < next.cursor := by
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      have parserResult : parser input = .ok body next := by
        simpa only [isolateBlock, captureResult] using result
      exact parserStrict parserResult
  | some captured =>
      apply isolateBlock_cursor_lt_onSuccess_of_balancedCapture parser
        (input := input) (next := next) (body := body)
      · simp [hasBalancedBlockCapture, captureResult]
      · exact result

/-- Package the complete Core-block boundary for recursive expression use. -/
theorem isolatedCoreBlock_elementTotalityContract
    (statementValueValid : SourceFile -> Statement -> Prop)
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementValid : statement.ValidFor statementValueValid)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (statementStrict : forall {input next : State} {value : Statement},
      statement input = .ok value next -> input.cursor < next.cursor)
    (statementFree : Parser.InvariantFreeOnValid statement)
    (statementSpan : forall file value,
      statementValueValid file value -> value.span.ValidFor file) :
    ElementTotalityContract
      (isolateBlock (coreBlock statement policy)) := {
  validFor := (isolatedCoreBlock_validFor statementValueValid statement policy
    statementValid statementWindow.preservesTokensOnSuccess statementSpan).mono
      (fun _ _ _ => trivial)
  preservesTokenWindow := isolatedCoreBlock_preservesTokenWindow statement
    policy statementWindow
  cursorLtOnSuccess := BlockInternals.isolateBlock_cursor_lt_onSuccess _
    (coreBlock_cursor_lt_onSuccess statement policy)
  invariantFree :=
    (BlockInternals.isolateBlock_invariantFreeOnValid _
      (coreBlock_invariantFreeOnValid statement policy
        (statementValid.mono (fun _ _ _ => trivial)) statementWindow
          statementStrict statementFree)).ne_invariant
}

end Solcore.Syntax.Parser

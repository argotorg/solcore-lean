import Solcore.Syntax.DeclarativeCoreBlockIsolationOutcomeGrammar
import Solcore.Syntax.Parser.BalancedBlockCaptureCompletenessProperties
import Solcore.Syntax.Parser.BalancedBlockCaptureSoundnessProperties

/-! Generic diagnostic-inclusive executable outcomes for block isolation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem captured_child_remainder_eq
    (input : State) (captured : BlockInternals.CapturedBlock)
    (capture : DeclarativeGrammar.BalancedBlockCapture)
    (endIndexEq : captured.window.endIndex = capture.endIndex) :
    (input.enterWindow input.cursor captured.window).declarativeRemainder =
      capture.childRemainder input.declarativeRemainder := by
  simp [State.declarativeRemainder, State.enterWindow,
    DeclarativeGrammar.BalancedBlockCapture.childRemainder, endIndexEq]

private theorem captured_parent_remainder_eq
    (input child : State) (captured : BlockInternals.CapturedBlock)
    (capture : DeclarativeGrammar.BalancedBlockCapture)
    (endIndexEq : captured.window.endIndex = capture.endIndex) :
    (State.mergeDiagnostics
        ({ input with cursor := captured.window.endIndex } : State)
        child).declarativeRemainder =
      capture.parentRemainder input.declarativeRemainder := by
  simp [State.declarativeRemainder, State.mergeDiagnostics,
    DeclarativeGrammar.BalancedBlockCapture.parentRemainder, endIndexEq]

private theorem captured_recovered_remainder_eq
    (input child : State) (captured : BlockInternals.CapturedBlock)
    (capture : DeclarativeGrammar.BalancedBlockCapture)
    (failure : Failure)
    (endIndexEq : captured.window.endIndex = capture.endIndex) :
    ((State.mergeDiagnostics
        ({ input with cursor := captured.window.endIndex } : State)
        child).emit failure.toDiagnostic).declarativeRemainder =
      capture.parentRemainder input.declarativeRemainder := by
  simp [State.declarativeRemainder, State.mergeDiagnostics, State.emit,
    DeclarativeGrammar.BalancedBlockCapture.parentRemainder, endIndexEq]

/-- Every executable isolation success is an uncaptured raw success, a
captured child success, or recovery of a captured child rejection. -/
theorem isolateBlock_success_ordinary_sound
    (parser : Parser Block)
    (blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (blockSuccessSound : ∀ {input output : State} {body : Block},
      parser input = .ok body output → blockOrdinary
        input.declarativeRemainder body output.declarativeRemainder)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      parser input = .reject failure rejected → blockRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input output : State} {body : Block}
    (result : isolateBlock parser input = .ok body output) :
    DeclarativeGrammar.IsolatedCoreBlockOrdinaryParses blockOrdinary
      blockRejects input.declarativeRemainder body
        output.declarativeRemainder := by
  unfold isolateBlock at result
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      simp only [captureResult] at result
      exact .direct
        (BlockInternals.captureBlock?_none_absent captureResult)
        (blockSuccessSound result)
  | some captured =>
      simp only [captureResult] at result
      rcases BlockInternals.captureBlock?_success_sound captureResult with
        ⟨capture, captureParsed, spanEq, endIndexEq, endByteEq⟩
      have childInputEq := captured_child_remainder_eq input captured capture
        endIndexEq
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | invariant error => simp [childResult] at result
      | ok childBody childAfter =>
          simp only [childResult] at result
          cases result
          have parentOutputEq := captured_parent_remainder_eq input childAfter
            captured capture endIndexEq
          rw [parentOutputEq]
          exact .captured captureParsed (by
            rw [← childInputEq]
            exact blockSuccessSound childResult)
      | reject childFailure childRejected =>
          simp only [childResult] at result
          cases result
          have parentOutputEq := captured_recovered_remainder_eq input
            childRejected captured capture childFailure endIndexEq
          rw [parentOutputEq, spanEq]
          exact .recovered captureParsed (by
            rw [← childInputEq]
            exact blockRejectSound childResult)

/-- An executable isolation rejection is only an uncaptured raw rejection. -/
theorem isolateBlock_reject_ordinary_sound
    (parser : Parser Block)
    (blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      parser input = .reject failure rejected → blockRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : isolateBlock parser input = .reject failure rejected) :
    DeclarativeGrammar.IsolatedCoreBlockRejects blockRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold isolateBlock at result
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      simp only [captureResult] at result
      exact .direct
        (BlockInternals.captureBlock?_none_absent captureResult)
        (blockRejectSound result)
  | some captured =>
      simp only [captureResult] at result
      cases childResult : parser
          (input.enterWindow input.cursor captured.window) with
      | invariant error => simp [childResult] at result
      | ok childBody childAfter => simp [childResult] at result
      | reject childFailure childRejected => simp [childResult] at result

/-- Package generic executable isolation success and rejection. -/
theorem isolateBlock_ordinaryOutcome_sound
    (parser : Parser Block)
    (blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (blockSuccessSound : ∀ {input output : State} {body : Block},
      parser input = .ok body output → blockOrdinary
        input.declarativeRemainder body output.declarativeRemainder)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      parser input = .reject failure rejected → blockRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {body : Block},
      isolateBlock parser input = .ok body output →
        DeclarativeGrammar.IsolatedCoreBlockOrdinaryParses blockOrdinary
          blockRejects input.declarativeRemainder body
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isolateBlock parser input = .reject failure rejected →
        DeclarativeGrammar.IsolatedCoreBlockRejects blockRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨isolateBlock_success_ordinary_sound parser blockOrdinary blockRejects
      blockSuccessSound blockRejectSound,
    isolateBlock_reject_ordinary_sound parser blockRejects blockRejectSound⟩

end Solcore.Syntax.Parser

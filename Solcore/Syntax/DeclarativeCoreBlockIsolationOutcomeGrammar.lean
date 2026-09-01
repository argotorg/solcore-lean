import Solcore.Syntax.DeclarativeBalancedBlockGrammar

/-!
Parser-independent ordinary outcomes for balanced Core block isolation.

When no balanced capture exists, the underlying block outcome is exposed in
the parent window.  A balanced capture runs the block outcome in its child
window and always resumes the parent after the matching closing brace;
ordinary child rejection is recovered as an empty block.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive success of a balanced isolated block. -/
inductive IsolatedCoreBlockOrdinaryParses
    (blockOrdinary : Remainder → Syntax.Block → Remainder → Prop)
    (blockRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Block → Remainder → Prop where
  | direct {input output : Remainder} {body : Syntax.Block}
      (captureAbsent : BalancedBlockCaptureAbsentAt input)
      (bodyParsed : blockOrdinary input body output) :
      IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects input body
        output
  | captured {input childOutput : Remainder} {body : Syntax.Block}
      {capture : BalancedBlockCapture}
      (captureParsed : BalancedBlockCaptures input capture)
      (bodyParsed : blockOrdinary (capture.childRemainder input) body
        childOutput) :
      IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects input body
        (capture.parentRemainder input)
  | recovered {input childRejected : Remainder}
      {capture : BalancedBlockCapture}
      (captureParsed : BalancedBlockCaptures input capture)
      (bodyRejected : blockRejects (capture.childRemainder input)
        childRejected) :
      IsolatedCoreBlockOrdinaryParses blockOrdinary blockRejects input {
        span := capture.span
        value := []
      } (capture.parentRemainder input)

/-- Exact external rejection of isolation: only an uncaptured underlying
block rejection escapes the wrapper. -/
inductive IsolatedCoreBlockRejects
    (blockRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | direct {input rejected : Remainder}
      (captureAbsent : BalancedBlockCaptureAbsentAt input)
      (bodyRejected : blockRejects input rejected) :
      IsolatedCoreBlockRejects blockRejects input rejected

end Solcore.Syntax.DeclarativeGrammar

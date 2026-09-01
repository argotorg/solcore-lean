import Solcore.Syntax.DeclarativeBalancedBlockGrammar
import Solcore.Syntax.Parser.Block

/-!
Executable balanced-brace capture agrees exactly with the parser-independent
token scan.  The public theorem hides the scanner's termination fuel.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace BlockInternals

private theorem tokenKind_eq_leftBrace_of_beq {kind : TokenKind}
    (accepted : (kind == .symbol .leftBrace) = true) :
    kind = .symbol .leftBrace := by
  change instBEqTokenKind.beq kind (.symbol .leftBrace) = true at accepted
  cases kind <;> simp only [instBEqTokenKind.beq] at accepted
  all_goals try { contradiction }
  case symbol symbol =>
    change instBEqSymbol.beq symbol .leftBrace = true at accepted
    unfold instBEqSymbol.beq at accepted
    cases symbol <;> first | rfl | cases accepted

private theorem tokenAt_of_peekOffset?_eq_some {state : State}
    {offset : Nat} {token : Token}
    (found : state.peekOffset? offset = some token) :
    DeclarativeGrammar.TokenAt state.tokens state.window.endIndex
      (state.cursor + offset) token := by
  unfold State.peekOffset? at found
  dsimp only at found
  split at found
  · exact ⟨by assumption, found⟩
  · contradiction

private theorem captureBlockTail_success_sound (state : State)
    (opening : Token) :
    ∀ fuel depth offset captured,
      0 < depth →
      captureBlockTail state opening fuel depth offset = some captured →
      ∃ closingSpan capturedEnd,
        DeclarativeGrammar.BalancedBlockTailScans
          state.declarativeRemainder depth offset closingSpan capturedEnd ∧
        captured = {
          span := SourceSpan.cover opening.span closingSpan
          window := {
            endIndex := capturedEnd
            endByte := closingSpan.endByte
          }
        } := by
  intro fuel
  induction fuel with
  | zero =>
      intro depth offset captured depthPositive result
      contradiction
  | succ fuel inductionHypothesis =>
      intro depth offset captured depthPositive result
      unfold captureBlockTail at result
      cases found : state.peekOffset? offset with
      | none => simp [found] at result
      | some token =>
          simp only [found] at result
          have tokenAt := tokenAt_of_peekOffset?_eq_some found
          rcases token with ⟨tokenSpan, kind⟩
          have otherCase
              (notOpening : kind ≠ .symbol .leftBrace)
              (notClosing : kind ≠ .symbol .rightBrace)
              (recursive : captureBlockTail state opening fuel depth
                (offset + 1) = some captured) :
              ∃ closingSpan capturedEnd,
                DeclarativeGrammar.BalancedBlockTailScans
                  state.declarativeRemainder depth offset closingSpan
                    capturedEnd ∧
                captured = {
                  span := SourceSpan.cover opening.span closingSpan
                  window := {
                    endIndex := capturedEnd
                    endByte := closingSpan.endByte
                  }
                } := by
            rcases inductionHypothesis depth (offset + 1) captured
                depthPositive recursive with
              ⟨closingSpan, capturedEnd, tail, capturedEq⟩
            exact ⟨closingSpan, capturedEnd,
              .other tokenAt notOpening notClosing tail, capturedEq⟩
          cases kind with
          | symbol symbol =>
              cases symbol <;> try
                exact otherCase (by simp) (by simp) result
              case leftBrace =>
                rcases inductionHypothesis (depth + 1) (offset + 1)
                    captured (by omega) result with
                  ⟨closingSpan, capturedEnd, tail, capturedEq⟩
                exact ⟨closingSpan, capturedEnd,
                  .opening tokenAt tail, capturedEq⟩
              case rightBrace =>
                by_cases atRoot : depth = 1
                · subst depth
                  have capturedEq : captured = {
                      span := SourceSpan.cover opening.span tokenSpan
                      window := {
                        endIndex := state.cursor + offset + 1
                        endByte := tokenSpan.endByte
                      }
                    } := (Option.some.inj (by simpa using result)).symm
                  exact ⟨tokenSpan, state.cursor + offset + 1,
                    .close tokenAt, capturedEq⟩
                · have reducedPositive : 0 < depth - 1 := by omega
                  have recursive : captureBlockTail state opening fuel
                      (depth - 1) (offset + 1) = some captured := by
                    simpa [atRoot] using result
                  rcases inductionHypothesis (depth - 1) (offset + 1)
                      captured reducedPositive recursive with
                    ⟨closingSpan, capturedEnd, tail, capturedEq⟩
                  have tailAtConstructorDepth :
                      DeclarativeGrammar.BalancedBlockTailScans
                        state.declarativeRemainder (depth - 2 + 1)
                          (offset + 1) closingSpan capturedEnd := by
                    simpa only [show depth - 2 + 1 = depth - 1 by omega]
                      using tail
                  have nested :=
                    DeclarativeGrammar.BalancedBlockTailScans.nestedClosing
                      (depth := depth - 2) tokenAt tailAtConstructorDepth
                  have scan :
                      DeclarativeGrammar.BalancedBlockTailScans
                        state.declarativeRemainder depth offset closingSpan
                          capturedEnd := by
                    simpa only [show depth - 2 + 2 = depth by omega]
                      using nested
                  exact ⟨closingSpan, capturedEnd, scan, capturedEq⟩
          | keyword keyword =>
              exact otherCase (by simp) (by simp) result
          | identifier text =>
              exact otherCase (by simp) (by simp) result
          | yulIdentifier text =>
              exact otherCase (by simp) (by simp) result
          | decimalLiteral text =>
              exact otherCase (by simp) (by simp) result
          | hexadecimalLiteral text =>
              exact otherCase (by simp) (by simp) result
          | stringLiteral text =>
              exact otherCase (by simp) (by simp) result
          | yulMetaBacktick text =>
              exact otherCase (by simp) (by simp) result
          | yulMetaInterpolation text =>
              exact otherCase (by simp) (by simp) result

/--
Every executable balanced capture is the exact declarative first matching
brace capture, including its source span and child token/byte window.
-/
theorem captureBlock?_success_sound {input : State}
    {captured : CapturedBlock}
    (result : captureBlock? input = some captured) :
    ∃ declarativeCapture : DeclarativeGrammar.BalancedBlockCapture,
      DeclarativeGrammar.BalancedBlockCaptures input.declarativeRemainder
        declarativeCapture ∧
      captured.span = declarativeCapture.span ∧
      captured.window.endIndex = declarativeCapture.endIndex ∧
      captured.window.endByte = declarativeCapture.endByte := by
  unfold captureBlock? at result
  cases found : input.peek? with
  | none => simp [found] at result
  | some opening =>
      simp only [found] at result
      split at result
      next openingIsBrace =>
        rcases opening with ⟨openingSpan, openingKind⟩
        have openingKindEq : openingKind = .symbol .leftBrace :=
          tokenKind_eq_leftBrace_of_beq openingIsBrace
        subst openingKind
        have openingToken := tokenAt_of_peek?_eq_some found
        rcases captureBlockTail_success_sound input
            { span := openingSpan, value := .symbol .leftBrace }
            input.remainingCount 1 1 captured (by omega) result with
          ⟨closingSpan, capturedEnd, tail, capturedEq⟩
        subst captured
        let declarativeCapture :
            DeclarativeGrammar.BalancedBlockCapture := {
          span := SourceSpan.cover openingSpan closingSpan
          endIndex := capturedEnd
          endByte := closingSpan.endByte
        }
        refine ⟨declarativeCapture, ?_, rfl, rfl, rfl⟩
        exact .captured openingToken tail
      next openingIsNotBrace => contradiction

end BlockInternals

end Solcore.Syntax.Parser

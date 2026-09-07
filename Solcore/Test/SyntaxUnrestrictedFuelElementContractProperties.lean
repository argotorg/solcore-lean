import Solcore.Syntax.Parser.DelimitedUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties

/-! The unrestricted contract permits a child to replace source, tokens,
endByte, and diagnostics, and even to advance past endIndex. Actual delimiter
execution still reaches an ordinary outcome. These are intentionally synthetic
children, not diagnostic-trace or state-validity contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxUnrestrictedFuelElementContractProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

private def originalFile : SourceFile := {
  id := { origin := .main, path := "unrestricted-original.sol" }, content := "("
}
private def replacementFile : SourceFile := {
  id := { origin := .external "child", path := "unrestricted-replacement.sol" }, content := ""
}
private def childEvent : ParseDiagnostic := {
  span := { source := replacementFile.id, startByte := 0, endByte := 0 }
  kind := .invalidIdentifierHyphen "synthetic-child"
}
private def openingToken : Token := {
  span := { source := originalFile.id, startByte := 0, endByte := 1 }, value := .symbol .leftParen
}
private def fixture (prior : List ParseDiagnostic) : State := {
  file := originalFile, tokens := #[openingToken], cursor := 0
  window := { endIndex := 1, endByte := 1 }, diagnosticsRev := prior.reverse
}
private def rewritten (input : State) : State := {
  file := replacementFile, tokens := #[], cursor := input.cursor + 10
  window := { endIndex := input.window.endIndex, endByte := 19 }, diagnosticsRev := [childEvent]
}
private def rewritingChild : Parser Nat := fun input => .ok 7 (rewritten input)
private def finalState : State := {
  file := replacementFile, tokens := #[], cursor := 11
  window := { endIndex := 1, endByte := 19 }, diagnosticsRev := [childEvent]
}
private def missingDelimiter : Failure := {
  span := { source := replacementFile.id, startByte := 19, endByte := 19 }, found := none
  expected := { head := .symbol .comma, tail := [.symbol .rightParen] }, context := .typeExpr
}

theorem rewriting_child_contract (fuel : Nat) : UnrestrictedFuelElementContract rewritingChild fuel where
  endIndexOnSuccess result := by
    simp only [rewritingChild] at result
    cases result
    rfl
  cursorLtOnSuccess result := by
    simp only [rewritingChild] at result
    cases result
    simp only [rewritten]
    omega
  ordinary input _ := Or.inl ⟨7, rewritten input, rfl⟩

/-- Every delimiter policy accepts this minimal contract on arbitrary states. -/
theorem arbitrary_policy_ordinary (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (fuel : Nat) (input : State)
    (adequate : input.remainingCount < fuel + 1) :
    (∃ values next, delimitedWithPolicy opening closing allowEmpty allowTrailing rewritingChild
      context phase input = .ok values next) ∨
    (∃ failure next, delimitedWithPolicy opening closing allowEmpty allowTrailing rewritingChild
      context phase input = .reject failure next) :=
  delimitedWithPolicy_ordinary_of_unrestrictedElementFuel opening closing allowEmpty allowTrailing
    rewritingChild context phase fuel (rewriting_child_contract fuel) input adequate

/-- The child changes all non-contract fields and overshoots the retained end index. -/
theorem child_changes_frames_and_overshoots (prior : List ParseDiagnostic) :
    rewritingChild { fixture prior with cursor := 1 } = .ok 7 finalState ∧
    finalState.file.id ≠ (fixture prior).file.id ∧
    finalState.tokens ≠ (fixture prior).tokens ∧
    finalState.window.endByte ≠ (fixture prior).window.endByte ∧
    finalState.diagnosticsRev = [childEvent] ∧
    finalState.window.endIndex = (fixture prior).window.endIndex ∧
    finalState.window.endIndex < finalState.cursor := by
  exact ⟨rfl, by change replacementFile.id ≠ originalFile.id; decide,
    by change (#[] : Array Token) ≠ #[openingToken]; decide,
    by change 19 ≠ 1; decide, rfl, rfl, by decide⟩

private theorem tail_rejected :
    afterDelimitedElement rewritingChild .rightParen true .typeExpr .typeExpr openingToken 1 [7] finalState =
      .reject missingDelimiter finalState := by
  have commaAbsent : isSymbol finalState .comma = false := rfl
  have closingAbsent : isSymbol finalState .rightParen = false := rfl
  simp only [afterDelimitedElement, commaAbsent, closingAbsent, Bool.false_eq_true, if_false]
  rfl

/-- At EOF the synthetic child advances by ten, replaces all prior events,
and leaves an ordinary ordered delimiter report at its new source/endByte. -/
theorem exact_rejection_after_rewriting (prior : List ParseDiagnostic) :
    delimited .leftParen .rightParen false rewritingChild .typeExpr .typeExpr (fixture prior) =
      .reject missingDelimiter finalState ∧
    finalState.remainingCount = 0 ∧
    finalState.diagnostics = [childEvent] := by
  have token : ExactTokenParses (.symbol .leftParen) (fixture prior).declarativeRemainder
      openingToken.span ({ fixture prior with cursor := 1 } : State).declarativeRemainder :=
    ⟨by change TokenAt #[openingToken] 1 0 openingToken; exact ⟨by decide, rfl⟩, rfl⟩
  have opening : symbol .leftParen .typeExpr (fixture prior) =
      .ok openingToken { fixture prior with cursor := 1 } :=
    symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr token
  have child := (child_changes_frames_and_overshoots prior).1
  refine ⟨?_, rfl, rfl⟩
  unfold delimited delimitedWithPolicy
  rw [opening]
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  rw [child]
  change afterDelimitedElement rewritingChild .rightParen true .typeExpr .typeExpr openingToken 1 [7] finalState = _
  exact tail_rejected

/-- This endpoint violates the usual cursor and token-window bounds. -/
theorem final_state_is_not_valid : ¬ finalState.ValidFor := by
  intro valid
  have bound := valid.cursor_le_endIndex
  simp only [finalState] at bound
  omega

end Solcore.Test.SyntaxUnrestrictedFuelElementContractProperties

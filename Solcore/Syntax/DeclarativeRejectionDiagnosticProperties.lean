import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Totality and exactness of independent current-input rejection reports. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every carrier has an exact current-token or empty-window observation. -/
theorem currentInputAt_total (source : SourceId) (endByte : Nat)
    (input : Remainder) :
    ∃ span found, CurrentInputAt source endByte input span found := by
  by_cases inside : input.cursor < input.endIndex
  · cases current : input.tokens[input.cursor]? with
    | none => exact ⟨_, _, .missingToken inside current⟩
    | some token => exact ⟨_, _, .token ⟨inside, current⟩⟩
  · exact ⟨_, _, .windowEnd (Nat.le_of_not_gt inside)⟩

/-- Fixed source, byte boundary, and remainder determine both observed fields. -/
theorem CurrentInputAt.result_unique
    {source : SourceId} {endByte : Nat} {input : Remainder}
    {leftSpan rightSpan : SourceSpan} {leftFound rightFound : Option TokenKind}
    (left : CurrentInputAt source endByte input leftSpan leftFound)
    (right : CurrentInputAt source endByte input rightSpan rightFound) :
    leftSpan = rightSpan ∧ leftFound = rightFound := by
  cases left with
  | token leftPresent =>
      cases right with
      | token rightPresent =>
          have same := Option.some.inj (leftPresent.2.symm.trans rightPresent.2)
          cases same
          exact ⟨rfl, rfl⟩
      | windowEnd atEnd => exact False.elim (Nat.not_lt_of_ge atEnd leftPresent.1)
      | missingToken inside missing => simp [leftPresent.2] at missing
  | windowEnd atEnd =>
      cases right with
      | token rightPresent => exact False.elim (Nat.not_lt_of_ge atEnd rightPresent.1)
      | windowEnd => exact ⟨rfl, rfl⟩
      | missingToken inside missing => exact False.elim (Nat.not_lt_of_ge atEnd inside)
  | missingToken inside missing =>
      cases right with
      | token rightPresent => simp [rightPresent.2] at missing
      | windowEnd atEnd => exact False.elim (Nat.not_lt_of_ge atEnd inside)
      | missingToken => exact ⟨rfl, rfl⟩

/-- Every expected-token catalog and context select a report. -/
theorem rejectAtReports_total (source : SourceId) (endByte : Nat)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (input : Remainder) :
    ∃ diagnostic, RejectAtReports source endByte expected context input diagnostic := by
  rcases currentInputAt_total source endByte input with ⟨span, found, current⟩
  exact ⟨_, .reported current⟩

/-- Reports fix the full source span, found token, expectations, and context. -/
theorem RejectAtReports.diagnostic_unique
    {source : SourceId} {endByte : Nat}
    {expected : NonemptyList ParseExpectation} {context : ParseContext}
    {input : Remainder} {left right : ParseDiagnostic}
    (leftReported : RejectAtReports source endByte expected context input left)
    (rightReported : RejectAtReports source endByte expected context input right) :
    left = right := by
  cases leftReported with
  | reported leftCurrent =>
      cases rightReported with
      | reported rightCurrent =>
          rcases leftCurrent.result_unique rightCurrent with ⟨rfl, rfl⟩
          rfl

end Solcore.Syntax.DeclarativeGrammar

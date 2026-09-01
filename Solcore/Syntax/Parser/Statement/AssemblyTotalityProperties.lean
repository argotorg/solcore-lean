import Solcore.Syntax.Parser.TermStatementFallbackFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.BodyTotalityProperties

/-! Valid-input totality for Core inline-assembly statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Inline assembly has only ordinary outcomes on every valid parser state. -/
theorem assemblyStatement_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ statement final, assemblyStatement input = .ok statement final) ∨
      (∃ failure final,
        assemblyStatement input = .reject failure final) := by
  rcases (keyword_ordinary .assemblyKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .assemblyKw .statement input
      inputValid
    rw [markerResult] at markerReply
    have bodyFree : Parser.InvariantFreeOnValid yulBody :=
      Parser.invariantFreeOnValid_of_ne_invariant
        yulBody_elementTotalityContract.invariantFree
    rcases bodyFree afterMarker markerReply.2.1 with
      ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
    · exact Or.inl ⟨{
          span := SourceSpan.cover marker.span body.span
          value := .assembly body.body
        }, final, by
          simp only [assemblyStatement, bind, markerResult, bodyResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [assemblyStatement, bind, markerResult, bodyResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [assemblyStatement, bind, markerResult]⟩

theorem assemblyStatement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid assemblyStatement :=
  assemblyStatement_ordinary

theorem assemblyStatement_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    assemblyStatement input ≠ .invariant error :=
  assemblyStatement_invariantFreeOnValid.ne_invariant input inputValid error

/-- The public assembly parser is also a strict reusable parser element. -/
theorem assemblyStatement_elementTotalityContract :
    ElementTotalityContract assemblyStatement := {
  validFor := (assemblyStatement_validFor
    (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ _ => trivial)).mono (fun _ _ _ => trivial)
  preservesTokenWindow := assemblyStatement_preservesTokenWindow
  cursorLtOnSuccess := assemblyStatement_cursor_lt_onSuccess
  invariantFree := assemblyStatement_ne_invariant
}

/-- Strict assembly element totality is fuel-valid at every chosen bound. -/
theorem assemblyStatement_fuelElementTotalityContract (fuel : Nat) :
    FuelElementTotalityContract assemblyStatement fuel := {
  validFor := assemblyStatement_elementTotalityContract.validFor
  preservesTokenWindow :=
    assemblyStatement_elementTotalityContract.preservesTokenWindow
  cursorLtOnSuccess :=
    assemblyStatement_elementTotalityContract.cursorLtOnSuccess
  ordinary := fun input inputValid _ =>
    assemblyStatement_ordinary input inputValid
}

/-- Complete semantic-value, state-window, and totality laws for assembly. -/
theorem assemblyStatement_totalityContract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (yulValid : ∀ file statement,
      YulStmt.ValidFor file statement → yulValueValid file statement) :
    TermInternals.StatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      assemblyStatement := {
  toStatementParserContract := {
    validFor := assemblyStatement_validFor expressionValueValid
      patternValueValid yulValueValid yulValid
    preservesTokenWindow := assemblyStatement_preservesTokenWindow
    cursorMonotoneOnSuccess := assemblyStatement_cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      assemblyStatement_startsAtCurrentTokenOnSuccess
  }
  invariantFree := assemblyStatement_invariantFreeOnValid
}

/-- The unconditional assembly proof is fuel-total at every chosen bound. -/
theorem assemblyStatement_fuelTotalityContract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (yulValid : ∀ file statement,
      YulStmt.ValidFor file statement → yulValueValid file statement)
    (fuel : Nat) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      assemblyStatement fuel := {
  toStatementParserContract :=
    (assemblyStatement_totalityContract expressionValueValid
      patternValueValid yulValueValid yulValid).toStatementParserContract
  ordinary := fun input inputValid _ =>
    assemblyStatement_ordinary input inputValid
}

end Solcore.Syntax.Parser

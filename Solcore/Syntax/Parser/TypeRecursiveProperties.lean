import Solcore.Syntax.Parser.TypeNamedProperties

/-! Fuel-inductive contracts for the complete recursive type parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem typeExprWithFuel_contracts : ∀ fuel,
    (typeExprWithFuel fuel).ValidFor TypeExpr.ValidFor ∧
    Parser.PreservesTokensOnSuccess (typeExprWithFuel fuel) ∧
    Parser.CursorMonotoneOnSuccess (typeExprWithFuel fuel) ∧
    Parser.StartsAtCurrentTokenOnSuccess
      (typeExprWithFuel fuel) (·.span) := by
  intro fuel
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro input inputValid
        simp [typeExprWithFuel, Reply.ValidFor]
      · intro input value next result
        simp [typeExprWithFuel] at result
      · intro input value next result
        simp [typeExprWithFuel] at result
      · intro input value next result
        simp [typeExprWithFuel] at result
  | succ fuel inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨nestedValid, nestedTokens, nestedCursor, nestedStarts⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro input inputValid
        simp only [typeExprWithFuel]
        split
        · exact parseFunctionType_validFor (typeExprWithFuel fuel)
            nestedValid nestedTokens input inputValid
        · split
          · exact parseComptimeType_validFor (typeExprWithFuel fuel)
              nestedValid nestedStarts nestedTokens nestedCursor input inputValid
          · split
            · exact parseMappingType_validFor (typeExprWithFuel fuel)
                nestedValid nestedStarts nestedTokens nestedCursor input inputValid
            · split
              · exact parseProxyType_validFor (typeExprWithFuel fuel)
                  nestedValid nestedStarts input inputValid
              · split
                · exact parseTupleType_validFor (typeExprWithFuel fuel)
                    nestedValid nestedTokens input inputValid
                · split
                  · exact parseNamedType_validFor (typeExprWithFuel fuel)
                      nestedValid nestedTokens input inputValid
                  · unfold rejectAt Reply.ValidFor
                    exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
      · intro input value next result
        simp only [typeExprWithFuel] at result
        split at result
        · exact parseFunctionType_preservesTokensOnSuccess
            (typeExprWithFuel fuel) nestedTokens input value next result
        · split at result
          · exact parseComptimeType_preservesTokensOnSuccess
              (typeExprWithFuel fuel) nestedTokens input value next result
          · split at result
            · exact parseMappingType_preservesTokensOnSuccess
                (typeExprWithFuel fuel) nestedTokens input value next result
            · split at result
              · exact parseProxyType_preservesTokensOnSuccess
                  (typeExprWithFuel fuel) nestedTokens input value next result
              · split at result
                · exact parseTupleType_preservesTokensOnSuccess
                    (typeExprWithFuel fuel) nestedTokens input value next result
                · split at result
                  · exact parseNamedType_preservesTokensOnSuccess
                      (typeExprWithFuel fuel) nestedTokens input value next result
                  · unfold rejectAt at result
                    contradiction
      · intro input value next result
        simp only [typeExprWithFuel] at result
        split at result
        · exact parseFunctionType_cursorMonotoneOnSuccess
            (typeExprWithFuel fuel) input value next result
        · split at result
          · exact parseComptimeType_cursorMonotoneOnSuccess
              (typeExprWithFuel fuel) nestedCursor input value next result
          · split at result
            · exact parseMappingType_cursorMonotoneOnSuccess
                (typeExprWithFuel fuel) nestedCursor input value next result
            · split at result
              · exact parseProxyType_cursorMonotoneOnSuccess
                  (typeExprWithFuel fuel) nestedCursor input value next result
              · split at result
                · exact parseTupleType_cursorMonotoneOnSuccess
                    (typeExprWithFuel fuel) input value next result
                · split at result
                  · exact parseNamedType_cursorMonotoneOnSuccess
                      (typeExprWithFuel fuel) input value next result
                  · unfold rejectAt at result
                    contradiction
      · intro input value next result
        simp only [typeExprWithFuel] at result
        split at result
        · exact parseFunctionType_startsAtCurrentTokenOnSuccess
            (typeExprWithFuel fuel) input value next result
        · split at result
          · exact parseComptimeType_startsAtCurrentTokenOnSuccess
              (typeExprWithFuel fuel) input value next result
          · split at result
            · exact parseMappingType_startsAtCurrentTokenOnSuccess
                (typeExprWithFuel fuel) input value next result
            · split at result
              · exact parseProxyType_startsAtCurrentTokenOnSuccess
                  (typeExprWithFuel fuel) input value next result
              · split at result
                · exact parseTupleType_startsAtCurrentTokenOnSuccess
                    (typeExprWithFuel fuel) input value next result
                · split at result
                  · exact parseNamedType_startsAtCurrentTokenOnSuccess
                      (typeExprWithFuel fuel) input value next result
                  · unfold rejectAt at result
                    contradiction

/-- Every fuel-bounded recursive type parse retains source provenance. -/
theorem typeExprWithFuel_validFor (fuel : Nat) :
    (typeExprWithFuel fuel).ValidFor TypeExpr.ValidFor :=
  (typeExprWithFuel_contracts fuel).1

/-- Every successful fuel-bounded type parse retains the token carrier. -/
theorem typeExprWithFuel_preservesTokensOnSuccess (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (typeExprWithFuel fuel) :=
  (typeExprWithFuel_contracts fuel).2.1

/-- Every successful fuel-bounded type parse is cursor-monotone. -/
theorem typeExprWithFuel_cursorMonotoneOnSuccess (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess (typeExprWithFuel fuel) :=
  (typeExprWithFuel_contracts fuel).2.2.1

/-- Every successful fuel-bounded type starts at its current token. -/
theorem typeExprWithFuel_startsAtCurrentTokenOnSuccess (fuel : Nat) :
    Parser.StartsAtCurrentTokenOnSuccess
      (typeExprWithFuel fuel) (·.span) :=
  (typeExprWithFuel_contracts fuel).2.2.2

/-- Public recursive type parsing retains source provenance at computed fuel. -/
theorem typeExpr_validFor : typeExpr.ValidFor TypeExpr.ValidFor := by
  intro input inputValid
  unfold typeExpr
  exact typeExprWithFuel_validFor (input.remainingCount + 1)
    input inputValid

/-- Public recursive type success retains the immutable token carrier. -/
theorem typeExpr_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess typeExpr := by
  intro input value next result
  unfold typeExpr at result
  exact typeExprWithFuel_preservesTokensOnSuccess
    (input.remainingCount + 1) input value next result

/-- Public recursive type success never rewinds the parser cursor. -/
theorem typeExpr_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess typeExpr := by
  intro input value next result
  unfold typeExpr at result
  exact typeExprWithFuel_cursorMonotoneOnSuccess
    (input.remainingCount + 1) input value next result

/-- Public recursive type success starts at the current input token. -/
theorem typeExpr_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess typeExpr (·.span) := by
  intro input value next result
  unfold typeExpr at result
  exact typeExprWithFuel_startsAtCurrentTokenOnSuccess
    (input.remainingCount + 1) input value next result

end Solcore.Syntax.Parser

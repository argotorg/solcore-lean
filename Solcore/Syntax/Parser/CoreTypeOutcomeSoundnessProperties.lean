import Solcore.Syntax.Parser.CoreFunctionTypeRejectionSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeNamedRejectionSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeSimpleRejectionSoundnessProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-! Aggregate ordinary-success and exact-rejection soundness for Core types. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Fuel zero is the invariant boundary and cannot report ordinary rejection. -/
theorem typeExprWithFuel_zero_ne_reject {input rejected : State}
    {failure : Failure} :
    typeExprWithFuel 0 input ≠ .reject failure rejected := by
  simp [typeExprWithFuel]

/-- Every fuel-bounded executable rejection follows the exact prioritized
parser-independent relation at the same fuel. -/
theorem typeExprWithFuel_reject_sound :
    ∀ fuel {input rejected : State} {failure : Failure},
      typeExprWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.TypeExprRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro input rejected failure result
      simp [typeExprWithFuel] at result
  | succ fuel inductionHypothesis =>
      intro input rejected failure result
      simp only [typeExprWithFuel] at result
      split at result
      next functionPresent =>
        exact .function (parseFunctionType_reject_type_sound
          (typeExprWithFuel fuel)
          (DeclarativeGrammar.TypeExprRejectsWithFuel fuel)
          (typeExprWithFuel_success_sound fuel) inductionHypothesis
          (typeExprWithFuel_preservesTokenWindow fuel) functionPresent result)
      next functionAbsent =>
        have functionAbsentAt := keywordAbsentAt_of_isKeyword_eq_false
          .functionKw (Bool.eq_false_iff.mpr functionAbsent)
        split at result
        next comptimePresent =>
          have composite : (isContextual input .comptime &&
              (input.peekOffsetKind? 1 == some (.symbol .less))) = true := by
            change (isContextual input .comptime &&
              (input.peekOffsetKind? 1 == some (.symbol .less))) = true at comptimePresent
            exact comptimePresent
          have parts := Bool.and_eq_true_iff.mp composite
          exact .comptime functionAbsentAt
            (parseComptimeType_reject_type_sound (typeExprWithFuel fuel)
              (DeclarativeGrammar.TypeExprRejectsWithFuel fuel)
              (typeExprWithFuel_success_sound fuel) inductionHypothesis parts.1
              parts.2 result)
        next comptimeAbsent =>
          have comptimeFalse : (isContextual input .comptime &&
              (input.peekOffsetKind? 1 == some (.symbol .less))) = false := by
            apply Bool.eq_false_iff.mpr
            change ¬ (isContextual input .comptime &&
              (input.peekOffsetKind? 1 == some (.symbol .less))) = true at comptimeAbsent
            exact comptimeAbsent
          have comptimeAbsentAt :=
            contextualSymbolPairAbsentAt_of_guard_eq_false .comptime .less
              comptimeFalse
          split at result
          next mappingPresent =>
            have composite : (isContextual input .mapping &&
                (input.peekOffsetKind? 1 ==
                  some (.symbol .leftParen))) = true := by
              change (isContextual input .mapping &&
                (input.peekOffsetKind? 1 ==
                  some (.symbol .leftParen))) = true at mappingPresent
              exact mappingPresent
            have parts := Bool.and_eq_true_iff.mp composite
            exact .mapping functionAbsentAt comptimeAbsentAt
              (parseMappingType_reject_type_sound (typeExprWithFuel fuel)
                (DeclarativeGrammar.TypeExprRejectsWithFuel fuel)
                (typeExprWithFuel_success_sound fuel) inductionHypothesis parts.1
                parts.2 result)
          next mappingAbsent =>
            have mappingFalse : (isContextual input .mapping &&
                (input.peekOffsetKind? 1 ==
                  some (.symbol .leftParen))) = false := by
              apply Bool.eq_false_iff.mpr
              change ¬ (isContextual input .mapping &&
                (input.peekOffsetKind? 1 ==
                  some (.symbol .leftParen))) = true at mappingAbsent
              exact mappingAbsent
            have mappingAbsentAt :=
              contextualSymbolPairAbsentAt_of_guard_eq_false .mapping
                .leftParen mappingFalse
            split at result
            next proxyPresent =>
              exact .proxy functionAbsentAt comptimeAbsentAt mappingAbsentAt
                (parseProxyType_reject_type_sound (typeExprWithFuel fuel)
                  (DeclarativeGrammar.TypeExprRejectsWithFuel fuel)
                  inductionHypothesis proxyPresent result)
            next proxyAbsent =>
              have atAbsent := symbolAbsentAt_of_isSymbol_eq_false .at
                (Bool.eq_false_iff.mpr proxyAbsent)
              split at result
              next tuplePresent =>
                exact .tuple functionAbsentAt comptimeAbsentAt mappingAbsentAt
                  atAbsent
                  (parseTupleType_reject_type_sound (typeExprWithFuel fuel)
                    (DeclarativeGrammar.TypeExprRejectsWithFuel fuel)
                    (typeExprWithFuel_success_sound fuel) inductionHypothesis
                    tuplePresent result)
              next tupleAbsent =>
                have leftParenAbsent :=
                  symbolAbsentAt_of_isSymbol_eq_false .leftParen
                    (Bool.eq_false_iff.mpr tupleAbsent)
                split at result
                next namedPresent =>
                  have identifierPresent :=
                    identifierPresentAt_of_isIdentifier_eq_true namedPresent
                  exact .named functionAbsentAt comptimeAbsentAt
                    mappingAbsentAt atAbsent leftParenAbsent identifierPresent
                    (parseNamedType_reject_type_sound (typeExprWithFuel fuel)
                      (DeclarativeGrammar.TypeExprRejectsWithFuel fuel)
                      (typeExprWithFuel_success_sound fuel)
                      inductionHypothesis result)
                next namedAbsent =>
                  have identifierAbsent :=
                    identifierAbsentAt_of_isIdentifier_eq_false
                      (Bool.eq_false_iff.mpr namedAbsent)
                  unfold rejectAt at result
                  cases result
                  exact .final functionAbsentAt comptimeAbsentAt
                    mappingAbsentAt atAbsent leftParenAbsent identifierAbsent

/-- Fuel-bounded executable ordinary replies jointly reflect established
recursive successes and exact same-fuel rejections. -/
theorem typeExprWithFuel_ordinaryOutcome_sound (fuel : Nat) :
    (∀ {input next : State} {value : TypeExpr},
      typeExprWithFuel fuel input = .ok value next →
        DeclarativeGrammar.TypeExprOrdinaryParses
          input.declarativeRemainder value next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      typeExprWithFuel fuel input = .reject failure rejected →
        DeclarativeGrammar.TypeExprRejectsWithFuel fuel
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨typeExprWithFuel_success_sound fuel, typeExprWithFuel_reject_sound fuel⟩

/-- Every public executable rejection uses the same remainder-derived fuel as
the public parser-independent rejection relation. -/
theorem typeExpr_reject_sound {input rejected : State} {failure : Failure}
    (result : typeExpr input = .reject failure rejected) :
    DeclarativeGrammar.TypeExprRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold typeExpr at result
  have reflected := typeExprWithFuel_reject_sound
    (input.remainingCount + 1) result
  simpa [DeclarativeGrammar.TypeExprRejects,
    DeclarativeGrammar.typeExprPublicFuel, State.remainingCount,
    State.declarativeRemainder] using reflected

/-- Public executable ordinary replies jointly reflect the established
recursive success grammar and exact public rejection relation. -/
theorem typeExpr_ordinaryOutcome_sound :
    (∀ {input next : State} {value : TypeExpr},
      typeExpr input = .ok value next →
        DeclarativeGrammar.TypeExprOrdinaryParses
          input.declarativeRemainder value next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected →
        DeclarativeGrammar.TypeExprRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨typeExpr_success_sound, typeExpr_reject_sound⟩

end Solcore.Syntax.Parser

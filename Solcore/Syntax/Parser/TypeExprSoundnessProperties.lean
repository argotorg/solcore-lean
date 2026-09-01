import Solcore.Syntax.Parser.TypeFunctionSoundnessProperties
import Solcore.Syntax.Parser.TypeMappingSoundnessProperties
import Solcore.Syntax.Parser.TypeNamedSoundnessProperties
import Solcore.Syntax.Parser.TypeRecursiveProperties
import Solcore.Syntax.Parser.TypeSimpleSoundnessProperties

/-! Aggregate success soundness for recursive type-expression parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextualSymbolPairAbsentAt_of_composite_eq_false
    (keyword : ContextualKeyword) (following : Symbol) {input : State}
    (absent : (isContextual input keyword &&
      (input.peekOffsetKind? 1 == some (.symbol following))) = false) :
    DeclarativeGrammar.ContextualSymbolPairAbsentAt
      input.declarativeRemainder keyword following := by
  rintro ⟨keywordSpan, followingSpan, keywordToken, followingToken⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor {
      span := keywordSpan
      value := .identifier keyword.spelling
    } at keywordToken
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    (input.cursor + 1) {
      span := followingSpan
      value := .symbol following
    } at followingToken
  have keywordPresent : isContextual input keyword = true := by
    unfold isContextual State.peekKind? State.peek?
    simp only [keywordToken.1, ↓reduceIte, keywordToken.2, Option.map_some,
      TokenKind.isContextual]
    exact beq_iff_eq.mpr rfl
  have followingPresent :
      (input.peekOffsetKind? 1 == some (.symbol following)) = true := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [followingToken.1, ↓reduceIte, followingToken.2,
      Option.map_some]
    change instBEqTokenKind.beq (.symbol following)
      (.symbol following) = true
    simp only [instBEqTokenKind.beq]
    change instBEqSymbol.beq following following = true
    unfold instBEqSymbol.beq
    cases following <;> rfl
  rw [keywordPresent, followingPresent] at absent
  contradiction

/-- Every successful fuel-bounded type parse follows the recursive grammar. -/
theorem typeExprWithFuel_success_sound :
    ∀ fuel {input next : State} {value : TypeExpr},
      typeExprWithFuel fuel input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro input next value result
      simp [typeExprWithFuel] at result
  | succ fuel inductionHypothesis =>
      intro input next value result
      simp only [typeExprWithFuel] at result
      split at result
      next functionPresent =>
        exact parseFunctionType_success_sound (typeExprWithFuel fuel)
          inductionHypothesis (typeExprWithFuel_preservesTokenWindow fuel)
          result
      next functionAbsent =>
        split at result
        next comptimePresent =>
          exact parseComptimeType_success_sound (typeExprWithFuel fuel)
            inductionHypothesis result
        next comptimeAbsent =>
          split at result
          next mappingPresent =>
            exact parseMappingType_success_sound (typeExprWithFuel fuel)
              inductionHypothesis result
          next mappingAbsent =>
            split at result
            next proxyPresent =>
              exact parseProxyType_success_sound (typeExprWithFuel fuel)
                inductionHypothesis result
            next proxyAbsent =>
              split at result
              next tuplePresent =>
                exact parseTupleType_success_sound (typeExprWithFuel fuel)
                  inductionHypothesis
                  (typeExprWithFuel_preservesTokenWindow fuel) result
              next tupleAbsent =>
                split at result
                next namedPresent =>
                  have comptimeFalse :
                      (isContextual input .comptime &&
                        (input.peekOffsetKind? 1 ==
                          some (.symbol .less))) = false := by
                    apply Bool.eq_false_iff.mpr
                    change ¬ (isContextual input .comptime &&
                      (input.peekOffsetKind? 1 ==
                        some (.symbol .less))) = true at comptimeAbsent
                    exact comptimeAbsent
                  have mappingFalse :
                      (isContextual input .mapping &&
                        (input.peekOffsetKind? 1 ==
                          some (.symbol .leftParen))) = false := by
                    apply Bool.eq_false_iff.mpr
                    change ¬ (isContextual input .mapping &&
                      (input.peekOffsetKind? 1 ==
                        some (.symbol .leftParen))) = true at mappingAbsent
                    exact mappingAbsent
                  exact parseNamedType_success_sound (typeExprWithFuel fuel)
                    inductionHypothesis
                    (typeExprWithFuel_preservesTokenWindow fuel)
                    (contextualSymbolPairAbsentAt_of_composite_eq_false
                      .comptime .less comptimeFalse)
                    (contextualSymbolPairAbsentAt_of_composite_eq_false
                      .mapping .leftParen mappingFalse)
                    result
                next namedAbsent =>
                  unfold rejectAt at result
                  contradiction

/-- Every successful public type parse follows the recursive grammar. -/
theorem typeExpr_success_sound {input next : State} {value : TypeExpr}
    (result : typeExpr input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold typeExpr at result
  exact typeExprWithFuel_success_sound (input.remainingCount + 1) result

/-- Public type grammar soundness composes with source validity. -/
theorem typeExpr_success_sound_and_validFor {input next : State}
    {value : TypeExpr} (inputValid : input.ValidFor)
    (result : typeExpr input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      TypeExpr.ValidFor input.file value := by
  refine ⟨typeExpr_success_sound result, ?_⟩
  have valid := typeExpr_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser

import Solcore.Syntax.DeclarativeNestingOutcomeGrammar

/-! Functionality and outcome exclusion for bounded nesting scans. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A bounded nesting scan has exactly one ordinary result. -/
theorem NestingScans.result_unique
    {limit : Nat} {context : NestingContext} {tokens : List Token}
    {left right : Option NestingOverflow}
    (leftScan : NestingScans limit context tokens left)
    (rightScan : NestingScans limit context tokens right) :
    left = right := by
  induction leftScan generalizing right with
  | done =>
      cases rightScan
      rfl
  | conditionalExceeded leftAction leftExceeds =>
      cases rightScan <;> simp_all <;> omega
  | conditionalContinues leftAction leftWithin leftTail
        inductionHypothesis =>
      cases rightScan <;> simp_all <;> try omega
      exact inductionHypothesis (by assumption)
  | groupExceeded leftAction leftExceeds =>
      cases rightScan <;> simp_all <;> omega
  | groupContinues leftAction leftWithin leftTail inductionHypothesis =>
      cases rightScan <;> simp_all <;> try omega
      exact inductionHypothesis (by assumption)
  | blockExceeded leftAction leftExceeds =>
      cases rightScan <;> simp_all <;> omega
  | blockContinues leftAction leftWithin leftTail inductionHypothesis =>
      cases rightScan <;> simp_all <;> try omega
      exact inductionHypothesis (by assumption)
  | close leftAction leftTail inductionHypothesis =>
      cases rightScan <;> simp_all
      exact inductionHypothesis (by assumption)
  | reset leftAction leftTail inductionHypothesis =>
      cases rightScan <;> simp_all
      exact inductionHypothesis (by assumption)
  | preserve leftAction leftTail inductionHypothesis =>
      cases rightScan <;> simp_all
      exact inductionHypothesis (by assumption)

/-- Every finite token sequence has a declarative bounded-nesting result. -/
theorem NestingScans.exists_result (limit : Nat) :
    ∀ (context : NestingContext) (tokens : List Token),
      ∃ result, NestingScans limit context tokens result := by
  intro context tokens
  induction tokens generalizing context with
  | nil => exact ⟨none, .done⟩
  | cons token rest inductionHypothesis =>
      cases action : nestingAction token.value with
      | conditional =>
          by_cases exceeds : limit < context.conditionalDepth + 1
          · exact ⟨_, .conditionalExceeded action exceeds⟩
          · have within : context.conditionalDepth + 1 ≤ limit := by omega
            rcases inductionHypothesis
                { context with
                  conditionalDepth := context.conditionalDepth + 1 } with
              ⟨result, tail⟩
            exact ⟨result, .conditionalContinues action within tail⟩
      | groupOpen =>
          by_cases exceeds : limit < context.delimiterDepth + 1
          · exact ⟨_, .groupExceeded action exceeds⟩
          · have within : context.delimiterDepth + 1 ≤ limit := by omega
            rcases inductionHypothesis {
              delimiterDepth := context.delimiterDepth + 1
              conditionalDepth := context.conditionalDepth
              conditionalBases := context.conditionalDepth ::
                context.conditionalBases
            } with ⟨result, tail⟩
            exact ⟨result, .groupContinues action within tail⟩
      | blockOpen =>
          by_cases exceeds : limit < context.delimiterDepth + 1
          · exact ⟨_, .blockExceeded action exceeds⟩
          · have within : context.delimiterDepth + 1 ≤ limit := by omega
            rcases inductionHypothesis {
              delimiterDepth := context.delimiterDepth + 1
              conditionalDepth := 0
              conditionalBases := 0 :: context.conditionalBases
            } with ⟨result, tail⟩
            exact ⟨result, .blockContinues action within tail⟩
      | close =>
          rcases inductionHypothesis context.closeDelimiter with
            ⟨result, tail⟩
          exact ⟨result, .close action tail⟩
      | reset =>
          rcases inductionHypothesis context.resetConditional with
            ⟨result, tail⟩
          exact ⟨result, .reset action tail⟩
      | preserve =>
          rcases inductionHypothesis context with ⟨result, tail⟩
          exact ⟨result, .preserve action tail⟩

/-- A canonical overflow diagnostic excludes a clear nesting scan. -/
theorem NestingExceeds.disjointClears
    {tokens : List Token} {overflow : NestingOverflow}
    (exceeds : NestingExceeds tokens overflow) :
    ¬ NestingClears tokens := by
  intro clears
  have unique := exceeds.result_unique clears
  contradiction

/-- The first canonical overflow is unique. -/
theorem NestingExceeds.overflow_unique
    {tokens : List Token} {left right : NestingOverflow}
    (leftExceeds : NestingExceeds tokens left)
    (rightExceeds : NestingExceeds tokens right) :
    left = right := by
  have unique := leftExceeds.result_unique rightExceeds
  exact Option.some.inj unique

/-- Canonical nesting either clears or reports one exact first overflow. -/
theorem nestingOutcome_total (tokens : List Token) :
    NestingClears tokens ∨
      ∃ overflow, NestingExceeds tokens overflow := by
  rcases NestingScans.exists_result canonicalNestingLimit
      ({} : NestingContext) tokens with ⟨result, scan⟩
  cases result with
  | none => exact Or.inl scan
  | some overflow => exact Or.inr ⟨overflow, scan⟩

end Solcore.Syntax.DeclarativeGrammar

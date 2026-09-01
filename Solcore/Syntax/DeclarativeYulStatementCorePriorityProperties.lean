import Solcore.Syntax.DeclarativeYulStatementCoreOutcomeGrammar
import Solcore.Syntax.DeclarativeYulStatementOrdinaryRecoveryGrammar

/-! Exclusivity laws for exact statement-core guard priority. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Numeric order of the executable statement-core decisions. -/
def YulStatementCoreStage.rank : YulStatementCoreStage → Nat
  | .blockGuard => 0
  | .letGuard => 1
  | .ifGuard => 2
  | .forGuard => 3
  | .switchGuard => 4
  | .functionGuard => 5
  | .returnGuard => 6
  | .leaveGuard => 7
  | .breakGuard => 8
  | .continueGuard => 9
  | .nameGuard => 10
  | .fallback => 11

/-- Exact negative evidence corresponding to one positive guard. -/
def YulStatementCoreGuardAbsentAt (input : Remainder) :
    YulStatementCoreStage → Prop
  | .blockGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftBrace)
  | .letGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .letKw)
  | .ifGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .ifKw)
  | .forGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .forKw)
  | .switchGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .switchKw)
  | .functionGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .functionKw)
  | .returnGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .returnKw)
  | .leaveGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .leaveKw)
  | .breakGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .breakKw)
  | .continueGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .continueKw)
  | .nameGuard => YulNameStartAbsentAt input
  | .fallback => False

/-- A positive guard conflicts with its exact negative evidence. -/
theorem YulStatementCoreGuardAbsentAt.not_guard
    {input : Remainder} {stage : YulStatementCoreStage}
    (absent : YulStatementCoreGuardAbsentAt input stage) :
    ¬ YulStatementCoreGuardAt input stage := by
  cases stage <;>
    simp only [YulStatementCoreGuardAbsentAt, YulStatementCoreGuardAt,
      YulStatementCoreTokenAt, YulNameStartAbsentAt] at absent ⊢
  all_goals exact absent

/-- A priority prefix contains negative evidence for every earlier guard. -/
theorem YulStatementCorePrefixAbsent.guardAbsent_of_rank_lt
    {input : Remainder} {stage previous : YulStatementCoreStage}
    (priority : YulStatementCorePrefixAbsent input stage)
    (before : previous.rank < stage.rank) :
    YulStatementCoreGuardAbsentAt input previous := by
  induction priority with
  | start =>
      cases previous <;> simp [YulStatementCoreStage.rank] at before
  | afterBlock prior absent ih =>
      cases previous <;>
        simp_all [YulStatementCoreStage.rank,
          YulStatementCoreGuardAbsentAt]
  | afterLet prior absent ih =>
      cases previous <;>
        simp_all [YulStatementCoreStage.rank,
          YulStatementCoreGuardAbsentAt]
  | afterIf prior absent ih =>
      cases previous <;>
        simp_all [YulStatementCoreStage.rank,
          YulStatementCoreGuardAbsentAt]
  | afterFor prior absent ih =>
      cases previous <;>
        simp_all [YulStatementCoreStage.rank,
          YulStatementCoreGuardAbsentAt]
  | afterSwitch prior absent ih =>
      cases previous <;>
        simp_all [YulStatementCoreStage.rank,
          YulStatementCoreGuardAbsentAt]
  | afterFunction prior absent ih =>
      cases previous <;>
        simp_all [YulStatementCoreStage.rank,
          YulStatementCoreGuardAbsentAt]
  | afterReturn prior absent ih =>
      cases previous <;>
        simp_all [YulStatementCoreStage.rank,
          YulStatementCoreGuardAbsentAt]
  | afterLeave prior absent ih =>
      cases previous <;>
        simp_all [YulStatementCoreStage.rank,
          YulStatementCoreGuardAbsentAt]
  | afterBreak prior absent ih =>
      cases previous <;>
        simp_all [YulStatementCoreStage.rank,
          YulStatementCoreGuardAbsentAt]
  | afterContinue prior absent ih =>
      cases previous <;>
        simp_all [YulStatementCoreStage.rank,
          YulStatementCoreGuardAbsentAt]
  | afterName prior absent ih =>
      cases previous <;>
        simp_all [YulStatementCoreStage.rank,
          YulStatementCoreGuardAbsentAt]

/-- Stage rank exactly reflects the finite dispatcher order. -/
theorem YulStatementCoreStage.rank_injective :
    Function.Injective YulStatementCoreStage.rank := by
  intro left right equal
  cases left <;> cases right <;>
    simp_all [YulStatementCoreStage.rank]

/-- Exact priority and positive guards select at most one stage. -/
theorem yulStatementCore_selectedStage_unique
    {input : Remainder} {left right : YulStatementCoreStage}
    (leftPriority : YulStatementCorePrefixAbsent input left)
    (leftGuard : YulStatementCoreGuardAt input left)
    (rightPriority : YulStatementCorePrefixAbsent input right)
    (rightGuard : YulStatementCoreGuardAt input right) :
    left = right := by
  apply YulStatementCoreStage.rank_injective
  by_cases equal : left.rank = right.rank
  · exact equal
  · rcases Nat.lt_or_gt_of_ne equal with before | after
    · exact False.elim
        ((rightPriority.guardAbsent_of_rank_lt before).not_guard leftGuard)
    · exact False.elim
        ((leftPriority.guardAbsent_of_rank_lt after).not_guard rightGuard)

private theorem tokenAt_value_unique {tokens : Array Token}
    {endIndex index : Nat} {left right : Token}
    (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left.value = right.value := by
  have tokenEq : left = right := Option.some.inj (leftAt.2.symm.trans rightAt.2)
  cases tokenEq
  rfl

private theorem YulStatementCoreGuardAt.has_token
    {input : Remainder} {stage : YulStatementCoreStage}
    (guard : YulStatementCoreGuardAt input stage)
    (notFallback : stage ≠ .fallback) :
    ∃ token, TokenAt input.tokens input.endIndex input.cursor token := by
  cases stage <;>
    simp only [YulStatementCoreGuardAt, YulStatementCoreTokenAt,
      YulNameStartAt] at guard
  case nameGuard =>
    rcases guard with ⟨token, tokenAt, starts⟩
    exact ⟨token, tokenAt⟩
  case fallback => contradiction
  all_goals
    rcases guard with ⟨span, tokenAt⟩
    exact ⟨_, tokenAt⟩

/-- Every outer statement recovery boundary excludes every guarded core
decision.  The final unguarded expression fallback is handled separately. -/
theorem YulStatementRejects.not_coreGuard
    {input rejected : Remainder}
    (rejection : YulStatementRejects input rejected)
    {stage : YulStatementCoreStage} (notFallback : stage ≠ .fallback) :
    ¬ YulStatementCoreGuardAt input stage := by
  intro guard
  cases rejection with
  | windowEnd atEnd =>
      rcases guard.has_token notFallback with ⟨token, tokenAt⟩
      exact (Nat.not_lt_of_ge atEnd) tokenAt.1
  | rightBrace rightBraceAt =>
      cases stage <;>
        simp only [YulStatementCoreGuardAt, YulStatementCoreTokenAt,
          YulNameStartAt] at guard
      case nameGuard =>
        rcases guard with ⟨token, tokenAt, starts⟩
        have kindEq := tokenAt_value_unique tokenAt rightBraceAt
        rw [kindEq] at starts
        simp [tokenKindStartsYulName] at starts
      case fallback => contradiction
      all_goals
        rcases guard with ⟨span, tokenAt⟩
        have kindEq := tokenAt_value_unique tokenAt rightBraceAt
        simp at kindEq
  | missingToken inside missing =>
      rcases guard.has_token notFallback with ⟨token, tokenAt⟩
      unfold TokenAt at tokenAt
      rw [missing] at tokenAt
      cases tokenAt.2

end Solcore.Syntax.DeclarativeGrammar

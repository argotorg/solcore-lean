import Solcore.Syntax.DeclarativeCoreStatementLayerGrammar

/-! Exact guard selection for the ordered Core statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An exact current token-kind selected by a Core statement guard. -/
def StatementLayerTokenAt (input : Remainder) (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := kind }

/-- Positive evidence for the executable guard at one dispatcher stage. -/
def StatementLayerGuardAt (input : Remainder) : StatementLayerStage → Prop
  | .letGuard => StatementLayerTokenAt input (.keyword .letKw)
  | .returnGuard => StatementLayerTokenAt input (.keyword .returnKw)
  | .matchGuard => StatementLayerTokenAt input (.keyword .matchKw)
  | .forGuard => StatementLayerTokenAt input (.keyword .forKw)
  | .whileGuard => StatementLayerTokenAt input
      (.identifier ContextualKeyword.while.spelling)
  | .ifGuard => StatementLayerTokenAt input (.keyword .ifKw)
  | .assemblyGuard => StatementLayerTokenAt input (.keyword .assemblyKw)
  | .blockGuard => StatementLayerTokenAt input (.symbol .leftBrace)
  | .breakGuard => StatementLayerTokenAt input (.keyword .breakKw)
  | .continueGuard => StatementLayerTokenAt input (.keyword .continueKw)
  | .fallback => True

/-- Numeric order of the executable Core statement decisions. -/
def StatementLayerStage.rank : StatementLayerStage → Nat
  | .letGuard => 0
  | .returnGuard => 1
  | .matchGuard => 2
  | .forGuard => 3
  | .whileGuard => 4
  | .ifGuard => 5
  | .assemblyGuard => 6
  | .blockGuard => 7
  | .breakGuard => 8
  | .continueGuard => 9
  | .fallback => 10

/-- Exact negative evidence corresponding to one positive guard. -/
def StatementLayerGuardAbsentAt (input : Remainder) :
    StatementLayerStage → Prop
  | .letGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .letKw)
  | .returnGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .returnKw)
  | .matchGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .matchKw)
  | .forGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .forKw)
  | .whileGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.identifier ContextualKeyword.while.spelling)
  | .ifGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .ifKw)
  | .assemblyGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .assemblyKw)
  | .blockGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftBrace)
  | .breakGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .breakKw)
  | .continueGuard => TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .continueKw)
  | .fallback => False

/-- A positive guard conflicts with its exact negative evidence. -/
theorem StatementLayerGuardAbsentAt.not_guard
    {input : Remainder} {stage : StatementLayerStage}
    (absent : StatementLayerGuardAbsentAt input stage) :
    ¬ StatementLayerGuardAt input stage := by
  cases stage <;>
    simp only [StatementLayerGuardAbsentAt, StatementLayerGuardAt,
      StatementLayerTokenAt] at absent ⊢
  all_goals exact absent

/-- A priority prefix contains negative evidence for every earlier guard. -/
theorem StatementLayerPrefixAbsent.guardAbsent_of_rank_lt
    {input : Remainder} {stage previous : StatementLayerStage}
    (priority : StatementLayerPrefixAbsent input stage)
    (before : previous.rank < stage.rank) :
    StatementLayerGuardAbsentAt input previous := by
  induction priority with
  | start =>
      cases previous <;> simp [StatementLayerStage.rank] at before
  | afterLet prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterReturn prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterMatch prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterFor prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterWhile prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterIf prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterAssembly prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterBlock prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterBreak prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]
  | afterContinue prior absent ih =>
      cases previous <;>
        simp_all [StatementLayerStage.rank, StatementLayerGuardAbsentAt]

/-- Stage rank exactly reflects the finite dispatcher order. -/
theorem StatementLayerStage.rank_injective :
    Function.Injective StatementLayerStage.rank := by
  intro left right equal
  cases left <;> cases right <;> simp_all [StatementLayerStage.rank]

/-- Exact priority and positive guards select at most one Core stage. -/
theorem statementLayer_selectedStage_unique
    {input : Remainder} {left right : StatementLayerStage}
    (leftPriority : StatementLayerPrefixAbsent input left)
    (leftGuard : StatementLayerGuardAt input left)
    (rightPriority : StatementLayerPrefixAbsent input right)
    (rightGuard : StatementLayerGuardAt input right) :
    left = right := by
  apply StatementLayerStage.rank_injective
  by_cases equal : left.rank = right.rank
  · exact equal
  · rcases Nat.lt_or_gt_of_ne equal with before | after
    · exact False.elim
        ((rightPriority.guardAbsent_of_rank_lt before).not_guard leftGuard)
    · exact False.elim
        ((leftPriority.guardAbsent_of_rank_lt after).not_guard rightGuard)

end Solcore.Syntax.DeclarativeGrammar

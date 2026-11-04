import Solcore.Syntax.DeclarativeTransactionalFallbackOutcomeProperties
import Solcore.Syntax.DeclarativeYulBlockStatementOutcomeProperties
import Solcore.Syntax.DeclarativeYulFunctionOutcomeProperties
import Solcore.Syntax.DeclarativeYulLetOrdinaryOutcomeProperties
import Solcore.Syntax.DeclarativeYulNameStatementOutcomeProperties
import Solcore.Syntax.DeclarativeYulStatementControlOutcomeProperties
import Solcore.Syntax.DeclarativeYulSwitchOutcomeProperties
import Solcore.Syntax.Grammar.Yul
import Solcore.Syntax.Grammar.YulOrdinary
import Solcore.Syntax.DeclarativeYulBlockOutcomeProperties
import Solcore.Syntax.DeclarativeTransactionalFallbackExactnessProperties
import Solcore.Syntax.DeclarativeYulFunctionExactnessProperties
import Solcore.Syntax.DeclarativeYulStatementBasicExactnessProperties
import Solcore.Syntax.DeclarativeYulStatementControlExactnessProperties
import Solcore.Syntax.DeclarativeYulSwitchExactnessProperties

/-!
Yul statements at fuel, and the public body grammar.

The definitions rest on outcome lemmas, so those lemmas stay in this file. Main
declarations: `YulStatementCoreOrdinaryParses`, `YulStatementOrdinaryParsesWithFuel`,
`YulStatementOrdinaryParses`, `YulBodyOrdinaryParses`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementCoreOutcomeGrammar
/-!
Parser-independent ordinary successes and exact rejections for the prioritized
inline-Yul statement-core dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An exact current token-kind selected by a statement-core guard. -/
def YulStatementCoreTokenAt (input : Remainder) (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := kind }

/-- Positive evidence for the executable guard at one dispatcher stage. -/
def YulStatementCoreGuardAt (input : Remainder) :
    YulStatementCoreStage → Prop
  | .blockGuard => YulStatementCoreTokenAt input (.symbol .leftBrace)
  | .letGuard => YulStatementCoreTokenAt input (.keyword .letKw)
  | .ifGuard => YulStatementCoreTokenAt input (.keyword .ifKw)
  | .forGuard => YulStatementCoreTokenAt input (.keyword .forKw)
  | .switchGuard => YulStatementCoreTokenAt input (.keyword .switchKw)
  | .functionGuard => YulStatementCoreTokenAt input (.keyword .functionKw)
  | .returnGuard => YulStatementCoreTokenAt input (.keyword .returnKw)
  | .leaveGuard => YulStatementCoreTokenAt input (.keyword .leaveKw)
  | .breakGuard => YulStatementCoreTokenAt input (.keyword .breakKw)
  | .continueGuard => YulStatementCoreTokenAt input (.keyword .continueKw)
  | .nameGuard => YulNameStartAt input
  | .fallback => True

/-- Ordinary outcome of a recognized primary and expression-statement
fallback, both run transactionally from the original remainder. -/
abbrev YulRecognizedStatementOrdinaryParses
    (primaryParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (primaryRejects : Remainder → Remainder → Prop) :=
  TransactionalFallbackOrdinaryParses primaryParses primaryRejects
    YulExpressionStatementOrdinaryParses

/-- Exact nonconsuming rejection of a recognized primary and its expression
fallback. -/
abbrev YulRecognizedStatementRejects
    (primaryRejects : Remainder → Remainder → Prop) :=
  TransactionalFallbackRejects primaryRejects
    YulExpressionStatementRejects

/-- Ordinary success of the complete prioritized statement-core dispatcher. -/
inductive YulStatementCoreOrdinaryParsesAt
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    YulStatementCoreStage → Remainder → Syntax.YulStmt → Remainder → Prop where
  | block {input output statement}
      (priority : YulStatementCorePrefixAbsent input .blockGuard)
      (guard : YulStatementCoreGuardAt input .blockGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulBlockStatementOrdinaryParses statementOrdinary)
        (YulBlockStatementRejects statementOrdinary statementRejects)
        input statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .blockGuard input statement output
  | letDecl {input output statement}
      (priority : YulStatementCorePrefixAbsent input .letGuard)
      (guard : YulStatementCoreGuardAt input .letGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        YulLetStatementOrdinaryParses YulLetStatementRejects input statement
        output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .letGuard input statement output
  | ifThen {input output statement}
      (priority : YulStatementCorePrefixAbsent input .ifGuard)
      (guard : YulStatementCoreGuardAt input .ifGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulIfStatementOrdinaryParses statementOrdinary)
        (YulIfStatementRejects statementOrdinary statementRejects) input
        statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .ifGuard input statement output
  | forLoop {input output statement}
      (priority : YulStatementCorePrefixAbsent input .forGuard)
      (guard : YulStatementCoreGuardAt input .forGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulForStatementOrdinaryParses statementOrdinary)
        (YulForStatementRejects statementOrdinary statementRejects) input
        statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .forGuard input statement output
  | switch {input output statement}
      (priority : YulStatementCorePrefixAbsent input .switchGuard)
      (guard : YulStatementCoreGuardAt input .switchGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulSwitchStatementOrdinaryParses statementOrdinary)
        (YulSwitchStatementRejects statementOrdinary statementRejects) input
        statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .switchGuard input statement output
  | functionDef {input output statement}
      (priority : YulStatementCorePrefixAbsent input .functionGuard)
      (guard : YulStatementCoreGuardAt input .functionGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulFunctionStatementOrdinaryParses statementOrdinary)
        (YulFunctionStatementRejects statementOrdinary statementRejects) input
        statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .functionGuard input statement output
  | returnBuiltin {input output statement}
      (priority : YulStatementCorePrefixAbsent input .returnGuard)
      (guard : YulStatementCoreGuardAt input .returnGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        YulReturnBuiltinOrdinaryParses YulReturnBuiltinRejects input statement
        output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .returnGuard input statement output
  | leave {input output statement}
      (priority : YulStatementCorePrefixAbsent input .leaveGuard)
      (guard : YulStatementCoreGuardAt input .leaveGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulControlTokenOrdinaryParses .leaveKw .leave)
        (YulControlTokenRejects .leaveKw) input statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .leaveGuard input statement output
  | break {input output statement}
      (priority : YulStatementCorePrefixAbsent input .breakGuard)
      (guard : YulStatementCoreGuardAt input .breakGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulControlTokenOrdinaryParses .breakKw .break)
        (YulControlTokenRejects .breakKw) input statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .breakGuard input statement output
  | continue {input output statement}
      (priority : YulStatementCorePrefixAbsent input .continueGuard)
      (guard : YulStatementCoreGuardAt input .continueGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulControlTokenOrdinaryParses .continueKw .continue)
        (YulControlTokenRejects .continueKw) input statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .continueGuard input statement output
  | nameChoice {input output statement}
      (priority : YulStatementCorePrefixAbsent input .nameGuard)
      (guard : YulStatementCoreGuardAt input .nameGuard)
      (parsed : YulNameStatementOrdinaryParses input statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .nameGuard input statement output
  | expressionFallback {input output statement}
      (priority : YulStatementCorePrefixAbsent input .fallback)
      (parsed : YulExpressionStatementOrdinaryParses input statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .fallback input statement output

/-- Ordinary success at the uniquely selected statement-core stage. -/
def YulStatementCoreOrdinaryParses
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (input : Remainder) (statement : Syntax.YulStmt) (output : Remainder) :
    Prop :=
  ∃ stage, YulStatementCoreOrdinaryParsesAt statementOrdinary
    statementRejects stage input statement output

/-- Exact rejection of the uniquely selected statement-core branch. -/
inductive YulStatementCoreRejectsAt
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    YulStatementCoreStage → Remainder → Remainder → Prop where
  | block {input rejected}
      (priority : YulStatementCorePrefixAbsent input .blockGuard)
      (guard : YulStatementCoreGuardAt input .blockGuard)
      (rejection : YulRecognizedStatementRejects
        (YulBlockStatementRejects statementOrdinary statementRejects) input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .blockGuard
        input rejected
  | letDecl {input rejected}
      (priority : YulStatementCorePrefixAbsent input .letGuard)
      (guard : YulStatementCoreGuardAt input .letGuard)
      (rejection : YulRecognizedStatementRejects YulLetStatementRejects input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .letGuard
        input rejected
  | ifThen {input rejected}
      (priority : YulStatementCorePrefixAbsent input .ifGuard)
      (guard : YulStatementCoreGuardAt input .ifGuard)
      (rejection : YulRecognizedStatementRejects
        (YulIfStatementRejects statementOrdinary statementRejects) input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .ifGuard
        input rejected
  | forLoop {input rejected}
      (priority : YulStatementCorePrefixAbsent input .forGuard)
      (guard : YulStatementCoreGuardAt input .forGuard)
      (rejection : YulRecognizedStatementRejects
        (YulForStatementRejects statementOrdinary statementRejects) input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .forGuard
        input rejected
  | switch {input rejected}
      (priority : YulStatementCorePrefixAbsent input .switchGuard)
      (guard : YulStatementCoreGuardAt input .switchGuard)
      (rejection : YulRecognizedStatementRejects
        (YulSwitchStatementRejects statementOrdinary statementRejects) input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .switchGuard
        input rejected
  | functionDef {input rejected}
      (priority : YulStatementCorePrefixAbsent input .functionGuard)
      (guard : YulStatementCoreGuardAt input .functionGuard)
      (rejection : YulRecognizedStatementRejects
        (YulFunctionStatementRejects statementOrdinary statementRejects) input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects
        .functionGuard input rejected
  | returnBuiltin {input rejected}
      (priority : YulStatementCorePrefixAbsent input .returnGuard)
      (guard : YulStatementCoreGuardAt input .returnGuard)
      (rejection : YulRecognizedStatementRejects YulReturnBuiltinRejects input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .returnGuard
        input rejected
  | leave {input rejected}
      (priority : YulStatementCorePrefixAbsent input .leaveGuard)
      (guard : YulStatementCoreGuardAt input .leaveGuard)
      (rejection : YulRecognizedStatementRejects
        (YulControlTokenRejects .leaveKw) input rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .leaveGuard
        input rejected
  | break {input rejected}
      (priority : YulStatementCorePrefixAbsent input .breakGuard)
      (guard : YulStatementCoreGuardAt input .breakGuard)
      (rejection : YulRecognizedStatementRejects
        (YulControlTokenRejects .breakKw) input rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .breakGuard
        input rejected
  | continue {input rejected}
      (priority : YulStatementCorePrefixAbsent input .continueGuard)
      (guard : YulStatementCoreGuardAt input .continueGuard)
      (rejection : YulRecognizedStatementRejects
        (YulControlTokenRejects .continueKw) input rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects
        .continueGuard input rejected
  | nameChoice {input rejected}
      (priority : YulStatementCorePrefixAbsent input .nameGuard)
      (guard : YulStatementCoreGuardAt input .nameGuard)
      (rejection : YulNameStatementRejects input rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .nameGuard
        input rejected
  | expressionFallback {input rejected}
      (priority : YulStatementCorePrefixAbsent input .fallback)
      (rejection : YulExpressionStatementRejects input rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .fallback
        input rejected

/-- Exact rejection at the uniquely selected statement-core stage. -/
def YulStatementCoreRejects
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (input rejected : Remainder) : Prop :=
  ∃ stage, YulStatementCoreRejectsAt statementOrdinary statementRejects
    stage input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementCorePriorityProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementCoreOutcomeProperties
/-! Deterministic outcome laws for the prioritized Yul statement core. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An ordinary core success retains its exact negative prefix. -/
theorem YulStatementCoreOrdinaryParsesAt.priority
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {stage input statement output}
    (parsed : YulStatementCoreOrdinaryParsesAt statementOrdinary
      statementRejects stage input statement output) :
    YulStatementCorePrefixAbsent input stage := by
  cases parsed <;> assumption

/-- An ordinary core success retains positive evidence for its selected
guard; the final fallback guard is trivially true. -/
theorem YulStatementCoreOrdinaryParsesAt.guard
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {stage input statement output}
    (parsed : YulStatementCoreOrdinaryParsesAt statementOrdinary
      statementRejects stage input statement output) :
    YulStatementCoreGuardAt input stage := by
  cases parsed <;> simp_all [YulStatementCoreGuardAt]

/-- An exact core rejection retains its exact negative prefix. -/
theorem YulStatementCoreRejectsAt.priority
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {stage input rejected}
    (rejection : YulStatementCoreRejectsAt statementOrdinary statementRejects
      stage input rejected) :
    YulStatementCorePrefixAbsent input stage := by
  cases rejection <;> assumption

/-- An exact core rejection retains positive evidence for its selected
guard; the final fallback guard is trivially true. -/
theorem YulStatementCoreRejectsAt.guard
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {stage input rejected}
    (rejection : YulStatementCoreRejectsAt statementOrdinary statementRejects
      stage input rejected) :
    YulStatementCoreGuardAt input stage := by
  cases rejection <;> simp_all [YulStatementCoreGuardAt]

/-- Ordinary core success has a unique output remainder. -/
theorem YulStatementCoreOrdinaryParses.output_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementCoreOrdinaryParses statementOrdinary
      statementRejects input left afterLeft)
    (rightParsed : YulStatementCoreOrdinaryParses statementOrdinary
      statementRejects input right afterRight) : afterLeft = afterRight := by
  rcases leftParsed with ⟨leftStage, leftParsed⟩
  rcases rightParsed with ⟨rightStage, rightParsed⟩
  have selected := yulStatementCore_selectedStage_unique leftParsed.priority
    leftParsed.guard rightParsed.priority rightParsed.guard
  subst rightStage
  cases leftParsed <;> cases rightParsed
  all_goals first
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulBlockStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        yulLetStatementDeterministicOutcomeSpec
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulIfStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulForStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulSwitchStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulFunctionStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        yulReturnBuiltinDeterministicOutcomeSpec
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulControlTokenDeterministicOutcomeSpec .leaveKw .leave)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulControlTokenDeterministicOutcomeSpec .breakKw .break)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact TransactionalFallbackOrdinaryParses.output_unique
        (yulControlTokenDeterministicOutcomeSpec .continueKw .continue)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          (by assumption)
    | exact yulNameStatementDeterministicOutcomeSpec.successOutputUnique
        (by assumption) (by assumption)
    | exact yulExpressionStatementDeterministicOutcomeSpec.successOutputUnique
        (by assumption) (by assumption)

/-- Exact core rejection excludes every ordinary core success. -/
theorem YulStatementCoreRejects.disjointOrdinary
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulStatementCoreRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ statement output,
      YulStatementCoreOrdinaryParses statementOrdinary statementRejects input
        statement output := by
  rintro ⟨statement, output, successful⟩
  rcases rejection with ⟨rejectedStage, rejection⟩
  rcases successful with ⟨successfulStage, successful⟩
  have selected := yulStatementCore_selectedStage_unique rejection.priority
    rejection.guard successful.priority successful.guard
  subst successfulStage
  cases rejection <;> cases successful
  all_goals first
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulBlockStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        yulLetStatementDeterministicOutcomeSpec
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulIfStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulForStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulSwitchStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulFunctionStatementDeterministicOutcomeSpec statementOutcomes)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        yulReturnBuiltinDeterministicOutcomeSpec
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulControlTokenDeterministicOutcomeSpec .leaveKw .leave)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulControlTokenDeterministicOutcomeSpec .breakKw .break)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact TransactionalFallbackRejects.disjointOrdinary
        (yulControlTokenDeterministicOutcomeSpec .continueKw .continue)
        yulExpressionStatementDeterministicOutcomeSpec (by assumption)
          ⟨_, _, by assumption⟩
    | exact yulNameStatementDeterministicOutcomeSpec.successRejectDisjoint
        (by assumption) ⟨_, _, by assumption⟩
    | exact yulExpressionStatementDeterministicOutcomeSpec
        |>.successRejectDisjoint (by assumption) ⟨_, _, by assumption⟩

/-- Construct the complete ordinary statement-core outcome contract. -/
theorem yulStatementCoreDeterministicOutcomeSpec
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (YulStatementCoreOrdinaryParses statementOrdinary statementRejects)
      (YulStatementCoreRejects statementOrdinary statementRejects) where
  successOutputUnique :=
    YulStatementCoreOrdinaryParses.output_unique statementOutcomes
  successRejectDisjoint :=
    YulStatementCoreRejects.disjointOrdinary statementOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementCoreEmbeddingProperties
/-! Clean embeddings and recovery-boundary exclusion for the Yul core. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem block_guard
    {statementClean : Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output statement}
    (parsed : YulBlockStatementParses statementClean input statement output) :
    YulStatementCoreGuardAt input .blockGuard := by
  cases parsed with
  | parsed blockParsed =>
      cases blockParsed with
      | parsed openingSpan openingParsed bodyParsed =>
          exact ⟨openingSpan, openingParsed.1⟩

private theorem let_guard {input output statement}
    (parsed : YulLetStatementParses YulExpressionParses input statement
      output) : YulStatementCoreGuardAt input .letGuard := by
  cases parsed with
  | parsed markerSpan namesSpan markerParsed namesParsed initializerParsed =>
      exact ⟨markerSpan, markerParsed.1⟩

private theorem if_guard
    {statementClean : Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output statement}
    (parsed : YulIfStatementParses statementClean YulExpressionParses input
      statement output) : YulStatementCoreGuardAt input .ifGuard := by
  cases parsed with
  | parsed markerSpan markerParsed conditionParsed bodyParsed =>
      exact ⟨markerSpan, markerParsed.1⟩

private theorem for_guard
    {statementClean : Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output statement}
    (parsed : YulForStatementParses statementClean YulExpressionParses input
      statement output) : YulStatementCoreGuardAt input .forGuard := by
  cases parsed with
  | parsed markerSpan markerParsed initializerParsed conditionParsed
      postParsed bodyParsed => exact ⟨markerSpan, markerParsed.1⟩

private theorem switch_guard
    {statementClean : Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output statement}
    (parsed : YulSwitchStatementParses statementClean YulExpressionParses input
      statement output) : YulStatementCoreGuardAt input .switchGuard := by
  cases parsed with
  | parsed markerSpan markerParsed scrutineeParsed casesParsed
      defaultParsed => exact ⟨markerSpan, markerParsed.1⟩

private theorem function_guard
    {statementClean : Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output statement}
    (parsed : YulFunctionStatementParses statementClean input statement
      output) : YulStatementCoreGuardAt input .functionGuard := by
  cases parsed with
  | parsed markerSpan bodySpan markerParsed nameParsed parametersParsed
      returnsParsed bodyParsed => exact ⟨markerSpan, markerParsed.1⟩

private theorem return_guard {input output statement}
    (parsed : YulReturnBuiltinParses YulExpressionParses input statement
      output) : YulStatementCoreGuardAt input .returnGuard := by
  cases parsed with
  | parsed markerSpan markerParsed argumentsParsed =>
      exact ⟨markerSpan, markerParsed.1⟩

private theorem control_guard {keyword : HardKeyword}
    {statementValue : Syntax.YulStmtValue} {input output statement}
    (parsed : YulControlTokenParses keyword statementValue input statement
      output) : YulStatementCoreTokenAt input (.keyword keyword) := by
  cases parsed with
  | parsed markerSpan markerParsed => exact ⟨markerSpan, markerParsed.1⟩

/-- Every clean prioritized core success embeds into ordinary success with the
same selected branch, AST, span, and output remainder. -/
theorem YulStatementCoreParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (_statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output statement}
    (parsed : YulStatementCoreParses statementClean YulExpressionParses
      yulAssignmentPublicFallbackSpec input statement output) :
    YulStatementCoreOrdinaryParses statementOrdinary statementRejects input
      statement output := by
  cases parsed with
  | block priority primary =>
      exact ⟨.blockGuard, .block priority (block_guard primary)
        (.primary (primary.toOrdinary cleanToOrdinary))⟩
  | letDecl priority primary =>
      exact ⟨.letGuard, .letDecl priority (let_guard primary)
        (.primary primary.toOrdinary)⟩
  | ifThen priority primary =>
      exact ⟨.ifGuard, .ifThen priority (if_guard primary)
        (.primary (primary.toOrdinary cleanToOrdinary))⟩
  | forLoop priority primary =>
      exact ⟨.forGuard, .forLoop priority (for_guard primary)
        (.primary (primary.toOrdinary cleanToOrdinary))⟩
  | switch priority primary =>
      exact ⟨.switchGuard, .switch priority (switch_guard primary)
        (.primary (primary.toOrdinary cleanToOrdinary))⟩
  | functionDef priority primary =>
      exact ⟨.functionGuard, .functionDef priority (function_guard primary)
        (.primary (primary.toOrdinary cleanToOrdinary))⟩
  | returnBuiltin priority primary =>
      exact ⟨.returnGuard, .returnBuiltin priority (return_guard primary)
        (.primary primary.toOrdinary)⟩
  | leave priority primary =>
      exact ⟨.leaveGuard, .leave priority (control_guard primary)
        (.primary primary.toOrdinary)⟩
  | «break» priority primary =>
      exact ⟨.breakGuard, .break priority (control_guard primary)
        (.primary primary.toOrdinary)⟩
  | «continue» priority primary =>
      exact ⟨.continueGuard, .continue priority (control_guard primary)
        (.primary primary.toOrdinary)⟩
  | nameChoice priority primary =>
      cases primary with
      | assignment nameStart assignmentParsed =>
          exact ⟨.nameGuard, .nameChoice priority nameStart
            (.primary assignmentParsed.toOrdinary)⟩
      | rewound nameStart assignmentRejected expressionParsed =>
          exact ⟨.nameGuard, .nameChoice priority nameStart
            ((YulNameStatementChoiceParses.rewound nameStart
              assignmentRejected expressionParsed).toOrdinary)⟩
  | expressionFallback priority fallback =>
      exact ⟨.fallback, .expressionFallback priority fallback.toOrdinary⟩

/-- Every outer statement boundary is also a public-expression rejection. -/
theorem YulStatementRejects.toYulExpressionRejects
    {input rejected : Remainder}
    (rejection : YulStatementRejects input rejected) :
    YulExpressionRejects input rejected := by
  cases rejection with
  | windowEnd atEnd => exact .windowEnd atEnd
  | rightBrace token => exact .rightBrace token
  | missingToken inside missing => exact .missingToken inside missing

/-- Outer statement rejection boundaries exclude every ordinary core success,
including the final expression fallback. -/
theorem YulStatementRejects.disjointCoreOrdinary
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (_statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulStatementRejects input rejected) :
    ¬ ∃ statement output,
      YulStatementCoreOrdinaryParses statementOrdinary statementRejects input
        statement output := by
  rintro ⟨statement, output, stage, parsed⟩
  by_cases fallback : stage = .fallback
  · subst stage
    cases parsed with
    | expressionFallback priority expressionParsed =>
        exact yulExpressionStatementDeterministicOutcomeSpec
          |>.successRejectDisjoint
            (.expressionRejected rejection.toYulExpressionRejects)
              ⟨_, _, expressionParsed⟩
  · exact rejection.not_coreGuard fallback parsed.guard

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementFuelGrammar
/-! Concrete fuel-indexed parser-independent outcomes for Yul statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

namespace YulStatementLevel

/-- Add one complete recursive Yul-statement layer. -/
def next (previous : YulStatementLevel) : YulStatementLevel :=
  ofCore
    (YulStatementCoreParses previous.cleanParses YulExpressionParses
      yulAssignmentPublicFallbackSpec)
    (YulStatementCoreOrdinaryParses previous.ordinaryParses previous.rejects)
    (YulStatementCoreRejects previous.ordinaryParses previous.rejects)
    (yulStatementCoreDeterministicOutcomeSpec previous.outcomes)
    (fun parsed => parsed.toOrdinary previous.outcomes
      previous.cleanToOrdinary)
    (YulStatementRejects.disjointCoreOrdinary previous.outcomes)

end YulStatementLevel

/-- Declarative recursive Yul-statement outcomes at exactly `fuel`. -/
def yulStatementLevel : Nat → YulStatementLevel
  | 0 => .empty
  | fuel + 1 => (yulStatementLevel fuel).next

/-- Diagnostic-free recursive Yul-statement success at one fuel. -/
def YulStatementCleanParsesWithFuel (fuel : Nat) :
    Remainder → Syntax.YulStmt → Remainder → Prop :=
  (yulStatementLevel fuel).cleanParses

/-- Ordinary recursive Yul-statement success at one fuel. -/
def YulStatementOrdinaryParsesWithFuel (fuel : Nat) :
    Remainder → Syntax.YulStmt → Remainder → Prop :=
  (yulStatementLevel fuel).ordinaryParses

/-- Exact recursive Yul-statement rejection at one fuel. -/
def YulStatementRejectsWithFuel (fuel : Nat) :
    Remainder → Remainder → Prop :=
  (yulStatementLevel fuel).rejects

/-- Deterministic outcome laws at one recursive fuel. -/
theorem yulStatementOutcomeSpecWithFuel (fuel : Nat) :
    DeterministicOutcomeSpec
      (YulStatementOrdinaryParsesWithFuel fuel)
      (YulStatementRejectsWithFuel fuel) :=
  (yulStatementLevel fuel).outcomes

/-- Clean successes at a fuel are ordinary successes at that fuel. -/
theorem YulStatementCleanParsesWithFuel.toOrdinary {fuel : Nat}
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulStatementCleanParsesWithFuel fuel input statement output) :
    YulStatementOrdinaryParsesWithFuel fuel input statement output :=
  (yulStatementLevel fuel).cleanToOrdinary parsed

@[simp] theorem YulStatementCleanParsesWithFuel.zero
    {input output : Remainder} {statement : Syntax.YulStmt} :
    ¬ YulStatementCleanParsesWithFuel 0 input statement output := by
  simp [YulStatementCleanParsesWithFuel, yulStatementLevel,
    YulStatementLevel.empty]

@[simp] theorem YulStatementOrdinaryParsesWithFuel.zero
    {input output : Remainder} {statement : Syntax.YulStmt} :
    ¬ YulStatementOrdinaryParsesWithFuel 0 input statement output := by
  simp [YulStatementOrdinaryParsesWithFuel, yulStatementLevel,
    YulStatementLevel.empty]

@[simp] theorem YulStatementRejectsWithFuel.zero
    {input rejected : Remainder} :
    ¬ YulStatementRejectsWithFuel 0 input rejected := by
  simp [YulStatementRejectsWithFuel, yulStatementLevel,
    YulStatementLevel.empty]

@[simp] theorem YulStatementCleanParsesWithFuel.succ_iff
    {fuel : Nat} {input output : Remainder}
    {statement : Syntax.YulStmt} :
    YulStatementCleanParsesWithFuel (fuel + 1) input statement output ↔
      YulStatementTerminatedParses
        (YulStatementCoreParses
          (YulStatementCleanParsesWithFuel fuel)
          YulExpressionParses yulAssignmentPublicFallbackSpec)
        input statement output := by
  simp only [YulStatementCleanParsesWithFuel, yulStatementLevel,
    YulStatementLevel.next, YulStatementLevel.ofCore]

@[simp] theorem YulStatementOrdinaryParsesWithFuel.succ_iff
    {fuel : Nat} {input output : Remainder}
    {statement : Syntax.YulStmt} :
    YulStatementOrdinaryParsesWithFuel (fuel + 1) input statement output ↔
      YulStatementLayerOrdinaryParses
        (YulStatementTerminatedOrdinaryParses
          (YulStatementCoreOrdinaryParses
            (YulStatementOrdinaryParsesWithFuel fuel)
            (YulStatementRejectsWithFuel fuel)))
        (YulStatementCoreRejects
          (YulStatementOrdinaryParsesWithFuel fuel)
          (YulStatementRejectsWithFuel fuel))
        input statement output := by
  simp only [YulStatementOrdinaryParsesWithFuel,
    YulStatementRejectsWithFuel, yulStatementLevel,
    YulStatementLevel.next, YulStatementLevel.ofCore]

@[simp] theorem YulStatementRejectsWithFuel.succ_iff
    {fuel : Nat} {input rejected : Remainder} :
    YulStatementRejectsWithFuel (fuel + 1) input rejected ↔
      YulStatementRejects input rejected := by
  simp only [YulStatementRejectsWithFuel, yulStatementLevel,
    YulStatementLevel.next, YulStatementLevel.ofCore]

/-- Exact recursive fuel selected by the public executable parser. -/
def yulStatementPublicFuel (input : Remainder) : Nat :=
  input.endIndex - input.cursor + 1

/-- Public diagnostic-free Yul-statement grammar with executable fuel. -/
def YulStatementParses (input : Remainder) (statement : Syntax.YulStmt)
    (output : Remainder) : Prop :=
  YulStatementCleanParsesWithFuel (yulStatementPublicFuel input)
    input statement output

/-- Public ordinary Yul-statement grammar with executable fuel. -/
def YulStatementOrdinaryParses (input : Remainder)
    (statement : Syntax.YulStmt) (output : Remainder) : Prop :=
  YulStatementOrdinaryParsesWithFuel (yulStatementPublicFuel input)
    input statement output

/-- Public exact Yul-statement rejection with executable fuel. -/
def YulStatementPublicRejects (input rejected : Remainder) : Prop :=
  YulStatementRejectsWithFuel (yulStatementPublicFuel input)
    input rejected

/-- Public rejection is definitionally the outer statement boundary. -/
@[simp] theorem yulStatementPublicRejects_iff
    {input rejected : Remainder} :
    YulStatementPublicRejects input rejected ↔
      YulStatementRejects input rejected := by
  simp only [YulStatementPublicRejects, yulStatementPublicFuel,
    YulStatementRejectsWithFuel, yulStatementLevel, YulStatementLevel.next,
    YulStatementLevel.ofCore]

/-- Deterministic ordinary outcomes of the public recursive grammar. -/
theorem yulStatementPublicOutcomeSpec :
    DeterministicOutcomeSpec YulStatementOrdinaryParses
      YulStatementPublicRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (yulStatementOutcomeSpecWithFuel
      (yulStatementPublicFuel input)).successOutputUnique
        leftParsed rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    exact (yulStatementOutcomeSpecWithFuel
      (yulStatementPublicFuel input)).successRejectDisjoint rejection

/-- The public outcome contract with the concrete recovery-boundary
rejection relation used by recursive consumers. -/
theorem yulStatementPublicDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulStatementOrdinaryParses
      YulStatementRejects where
  successOutputUnique :=
    yulStatementPublicOutcomeSpec.successOutputUnique
  successRejectDisjoint := by
    intro input rejected rejection
    exact yulStatementPublicOutcomeSpec.successRejectDisjoint
      (yulStatementPublicRejects_iff.mpr rejection)

/-- Every public clean Yul statement is a public ordinary statement. -/
theorem YulStatementParses.toOrdinary {input output : Remainder}
    {statement : Syntax.YulStmt}
    (parsed : YulStatementParses input statement output) :
    YulStatementOrdinaryParses input statement output :=
  YulStatementCleanParsesWithFuel.toOrdinary parsed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulBodyGrammar
/-!
Concrete parser-independent grammar and outcomes for the public braced
inline-Yul body parser.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-free public Yul body grammar. -/
abbrev YulBodyParses := YulBlockParses YulStatementParses

/-- Ordinary public Yul body grammar, including diagnosed statements. -/
abbrev YulBodyOrdinaryParses :=
  YulBlockOrdinaryParses YulStatementOrdinaryParses

/-- Exact rejection traces for the public Yul body parser. -/
abbrev YulBodyRejects :=
  YulBlockRejects YulStatementOrdinaryParses YulStatementRejects

/-- Packaged ordinary body relation used by deterministic outcome laws. -/
abbrev YulBodyOutcomeParses :=
  YulBlockOutcomeParses YulStatementOrdinaryParses

/-- Public Yul body success and rejection have deterministic outcomes. -/
theorem yulBodyDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulBodyOutcomeParses YulBodyRejects :=
  yulBlockDeterministicOutcomeSpec
    yulStatementPublicDeterministicOutcomeSpec

/-- Every diagnostic-free public body is the same ordinary body. -/
theorem YulBodyParses.toOrdinary
    {input output : Remainder} {bodySpan : SourceSpan}
    {body : List Syntax.YulStmt}
    (parsed : YulBodyParses input bodySpan body output) :
    YulBodyOrdinaryParses input bodySpan body output :=
  YulBlockParses.toOrdinary
    (fun statement => statement.toOrdinary) parsed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementCoreExactnessProperties
/-! Exact AST and rejection outcomes of the prioritized Yul statement core. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Name-start assignment-or-expression choice fixes the complete selected AST. -/
theorem YulNameStatementOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulNameStatementOrdinaryParses input left afterLeft)
    (rightParsed : YulNameStatementOrdinaryParses input right afterRight) :
    left = right :=
  TransactionalFallbackOrdinaryParses.value_unique_of_success
    (fallbackParses := YulExpressionStatementOrdinaryParses)
    yulAssignmentDeterministicOutcomeSpec YulAssignmentOrdinaryParses.value_unique
    YulExpressionStatementOrdinaryParses.value_unique leftParsed rightParsed

private theorem recognized_value_unique
    {primaryParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    {primaryRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec primaryParses primaryRejects)
    (values : ∀ {input left right afterLeft afterRight},
      primaryParses input left afterLeft → primaryParses input right afterRight → left = right)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulRecognizedStatementOrdinaryParses primaryParses primaryRejects
      input left afterLeft)
    (rightParsed : YulRecognizedStatementOrdinaryParses primaryParses primaryRejects
      input right afterRight) : left = right :=
  TransactionalFallbackOrdinaryParses.value_unique_of_success
    (fallbackParses := YulExpressionStatementOrdinaryParses) outcomes values
    YulExpressionStatementOrdinaryParses.value_unique leftParsed rightParsed

/-- Stage priority and exact primary ASTs fix the complete statement-core AST. -/
theorem YulStatementCoreOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementCoreOrdinaryParses statementOrdinary statementRejects
      input left afterLeft)
    (rightParsed : YulStatementCoreOrdinaryParses statementOrdinary statementRejects
      input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftStage, leftParsed⟩
  rcases rightParsed with ⟨rightStage, rightParsed⟩
  have selected := yulStatementCore_selectedStage_unique leftParsed.priority
    leftParsed.guard rightParsed.priority rightParsed.guard
  subst rightStage
  cases leftParsed <;> cases rightParsed
  all_goals first
    | exact recognized_value_unique
        (yulBlockStatementDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec)
        (YulBlockStatementOrdinaryParses.value_unique outcomes) (by assumption) (by assumption)
    | exact recognized_value_unique yulLetStatementDeterministicOutcomeSpec
        YulLetStatementOrdinaryParses.value_unique (by assumption) (by assumption)
    | exact recognized_value_unique
        (yulIfStatementDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec)
        (YulIfStatementOrdinaryParses.value_unique outcomes) (by assumption) (by assumption)
    | exact recognized_value_unique
        (yulForStatementDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec)
        (YulForStatementOrdinaryParses.value_unique outcomes) (by assumption) (by assumption)
    | exact recognized_value_unique
        (yulSwitchStatementDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec)
        (YulSwitchStatementOrdinaryParses.value_unique outcomes) (by assumption) (by assumption)
    | exact recognized_value_unique
        (yulFunctionStatementDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec)
        (YulFunctionStatementOrdinaryParses.value_unique outcomes) (by assumption) (by assumption)
    | exact recognized_value_unique yulReturnBuiltinDeterministicOutcomeSpec
        YulReturnBuiltinOrdinaryParses.value_unique (by assumption) (by assumption)
    | exact recognized_value_unique (yulControlTokenDeterministicOutcomeSpec _ _)
        YulControlTokenOrdinaryParses.value_unique (by assumption) (by assumption)
    | exact YulNameStatementOrdinaryParses.value_unique (by assumption) (by assumption)
    | exact YulExpressionStatementOrdinaryParses.value_unique (by assumption) (by assumption)

private theorem transactional_output_eq
    {primaryRejects fallbackRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : TransactionalFallbackRejects primaryRejects fallbackRejects input rejected) :
    rejected = input := by
  cases rejection
  rfl

/-- Every core branch rejects at the original remainder after transactional rewind. -/
theorem YulStatementCoreRejects.output_eq
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : YulStatementCoreRejects statementOrdinary statementRejects
      input rejected) : rejected = input := by
  rcases rejection with ⟨stage, rejection⟩
  cases rejection
  all_goals first
    | exact YulExpressionStatementRejects.output_eq (by assumption)
    | exact transactional_output_eq (by assumption)

/-- Exact recursive statements give exact outcomes of the entire Yul core. -/
theorem yulStatementCoreExactOutcomeSpec
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects) :
    ExactDeterministicOutcomeSpec
      (YulStatementCoreOrdinaryParses statementOrdinary statementRejects)
      (YulStatementCoreRejects statementOrdinary statementRejects) where
  toDeterministicOutcomeSpec :=
    yulStatementCoreDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec
  successValueUnique := YulStatementCoreOrdinaryParses.value_unique outcomes
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    rw [leftRejected.output_eq, rightRejected.output_eq]

end Solcore.Syntax.DeclarativeGrammar
end

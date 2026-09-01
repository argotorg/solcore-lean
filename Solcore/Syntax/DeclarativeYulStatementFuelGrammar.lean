import Solcore.Syntax.DeclarativeYulStatementCoreEmbeddingProperties
import Solcore.Syntax.DeclarativeYulStatementLevelGrammar

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

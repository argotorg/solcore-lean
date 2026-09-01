import Solcore.Syntax.DeclarativeYulExpressionOrdinaryOutcomeProperties

/-!
Parser-independent fuel-indexed outcomes for recursive inline-Yul expressions.

Each level packages its clean grammar, its broader ordinary-success grammar,
its exact rejection relation, and the laws needed to construct the next level.
This avoids a recursive inductive definition containing proof-bearing fallback
specifications in a negative position.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One complete declarative approximation of recursive Yul expressions. -/
structure YulExpressionLevel where
  cleanParses : Remainder → Syntax.YulExpr → Remainder → Prop
  ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop
  rejects : Remainder → Remainder → Prop
  outcomes : DeterministicOutcomeSpec ordinaryParses rejects
  cleanToOrdinary : ∀ {input expression output},
    cleanParses input expression output →
      ordinaryParses input expression output

namespace YulExpressionLevel

/-- Fuel zero recognizes no success or rejection outcome. -/
def empty : YulExpressionLevel where
  cleanParses := fun _ _ _ => False
  ordinaryParses := fun _ _ _ => False
  rejects := fun _ _ => False
  outcomes := {
    successOutputUnique := by
      intro input left right afterLeft afterRight leftParsed
      exact False.elim leftParsed
    successRejectDisjoint := by
      intro input rejected rejection
      exact False.elim rejection
  }
  cleanToOrdinary := by
    intro input expression output parsed
    exact False.elim parsed

/-- Transactional call-argument fallback induced by one previous level. -/
def callArgumentsFallback (level : YulExpressionLevel) :
    YulCallArgumentsFallbackSpec level.cleanParses :=
  YulCallArgumentsFallbackSpec.ofOutcomes level.ordinaryParses
    level.cleanParses level.rejects level.outcomes level.cleanToOrdinary

/-- Add one recursive Yul-expression layer. -/
def next (previous : YulExpressionLevel) : YulExpressionLevel where
  cleanParses := YulExpressionCoreParses previous.cleanParses
    previous.callArgumentsFallback
  ordinaryParses := YulExpressionLayerOrdinaryParses
    previous.ordinaryParses previous.rejects
  rejects := YulExpressionRejects
  outcomes := yulExpressionDeterministicOutcomeSpec previous.outcomes
  cleanToOrdinary := by
    intro input expression output parsed
    exact parsed.toOrdinaryLayer previous.outcomes previous.cleanToOrdinary

end YulExpressionLevel

/-- Declarative recursive Yul-expression outcomes at exactly `fuel`. -/
def yulExpressionLevel : Nat → YulExpressionLevel
  | 0 => .empty
  | fuel + 1 => (yulExpressionLevel fuel).next

/-- Diagnostic-free recursive Yul-expression successes at one fuel. -/
def YulExpressionCleanParsesWithFuel (fuel : Nat) :
    Remainder → Syntax.YulExpr → Remainder → Prop :=
  (yulExpressionLevel fuel).cleanParses

/-- Ordinary recursive Yul-expression successes at one fuel. -/
def YulExpressionOrdinaryParsesWithFuel (fuel : Nat) :
    Remainder → Syntax.YulExpr → Remainder → Prop :=
  (yulExpressionLevel fuel).ordinaryParses

/-- Exact recursive Yul-expression rejection at one fuel. -/
def YulExpressionRejectsWithFuel (fuel : Nat) :
    Remainder → Remainder → Prop :=
  (yulExpressionLevel fuel).rejects

/-- Deterministic outcome laws at one recursive fuel. -/
theorem yulExpressionOutcomeSpecWithFuel (fuel : Nat) :
    DeterministicOutcomeSpec
      (YulExpressionOrdinaryParsesWithFuel fuel)
      (YulExpressionRejectsWithFuel fuel) :=
  (yulExpressionLevel fuel).outcomes

/-- Clean successes at a fuel are ordinary successes at that fuel. -/
theorem YulExpressionCleanParsesWithFuel.toOrdinary {fuel : Nat}
    {input output : Remainder} {expression : Syntax.YulExpr}
    (parsed : YulExpressionCleanParsesWithFuel fuel input expression
      output) :
    YulExpressionOrdinaryParsesWithFuel fuel input expression output :=
  (yulExpressionLevel fuel).cleanToOrdinary parsed

/-- Call-argument fallback selected by the preceding recursive level. -/
def yulExpressionCallArgumentsFallbackWithFuel (fuel : Nat) :
    YulCallArgumentsFallbackSpec
      (YulExpressionCleanParsesWithFuel fuel) :=
  (yulExpressionLevel fuel).callArgumentsFallback

@[simp] theorem YulExpressionCleanParsesWithFuel.zero
    {input output : Remainder} {expression : Syntax.YulExpr} :
    ¬ YulExpressionCleanParsesWithFuel 0 input expression output := by
  simp [YulExpressionCleanParsesWithFuel, yulExpressionLevel,
    YulExpressionLevel.empty]

@[simp] theorem YulExpressionOrdinaryParsesWithFuel.zero
    {input output : Remainder} {expression : Syntax.YulExpr} :
    ¬ YulExpressionOrdinaryParsesWithFuel 0 input expression output := by
  simp [YulExpressionOrdinaryParsesWithFuel, yulExpressionLevel,
    YulExpressionLevel.empty]

@[simp] theorem YulExpressionRejectsWithFuel.zero
    {input rejected : Remainder} :
    ¬ YulExpressionRejectsWithFuel 0 input rejected := by
  simp [YulExpressionRejectsWithFuel, yulExpressionLevel,
    YulExpressionLevel.empty]

@[simp] theorem YulExpressionCleanParsesWithFuel.succ_iff
    {fuel : Nat} {input output : Remainder}
    {expression : Syntax.YulExpr} :
    YulExpressionCleanParsesWithFuel (fuel + 1) input expression output ↔
      YulExpressionCoreParses (YulExpressionCleanParsesWithFuel fuel)
        (yulExpressionCallArgumentsFallbackWithFuel fuel)
        input expression output := by
  simp only [YulExpressionCleanParsesWithFuel, yulExpressionLevel,
    YulExpressionLevel.next, yulExpressionCallArgumentsFallbackWithFuel]

@[simp] theorem YulExpressionOrdinaryParsesWithFuel.succ_iff
    {fuel : Nat} {input output : Remainder}
    {expression : Syntax.YulExpr} :
    YulExpressionOrdinaryParsesWithFuel (fuel + 1) input expression output ↔
      YulExpressionLayerOrdinaryParses
        (YulExpressionOrdinaryParsesWithFuel fuel)
        (YulExpressionRejectsWithFuel fuel) input expression output := by
  simp only [YulExpressionOrdinaryParsesWithFuel,
    YulExpressionRejectsWithFuel, yulExpressionLevel,
    YulExpressionLevel.next]

@[simp] theorem YulExpressionRejectsWithFuel.succ_iff
    {fuel : Nat} {input rejected : Remainder} :
    YulExpressionRejectsWithFuel (fuel + 1) input rejected ↔
      YulExpressionRejects input rejected := by
  simp only [YulExpressionRejectsWithFuel, yulExpressionLevel,
    YulExpressionLevel.next]

/-- Fuel chosen by the public parser from a parser-independent remainder. -/
def yulExpressionPublicFuel (input : Remainder) : Nat :=
  input.endIndex - input.cursor + 1

/-- Public diagnostic-free recursive inline-Yul expression grammar. -/
def YulExpressionParses (input : Remainder) (expression : Syntax.YulExpr)
    (output : Remainder) : Prop :=
  YulExpressionCleanParsesWithFuel (yulExpressionPublicFuel input)
    input expression output

/-- Public ordinary-success recursive inline-Yul expression grammar. -/
def YulExpressionOrdinaryParses (input : Remainder)
    (expression : Syntax.YulExpr) (output : Remainder) : Prop :=
  YulExpressionOrdinaryParsesWithFuel (yulExpressionPublicFuel input)
    input expression output

/-- Public fuel-indexed rejection, definitionally the boundary rejection. -/
def YulExpressionPublicRejects (input rejected : Remainder) : Prop :=
  YulExpressionRejectsWithFuel (yulExpressionPublicFuel input) input rejected

@[simp] theorem yulExpressionPublicRejects_iff
    {input rejected : Remainder} :
    YulExpressionPublicRejects input rejected ↔
      YulExpressionRejects input rejected := by
  simp only [YulExpressionPublicRejects, yulExpressionPublicFuel,
    YulExpressionRejectsWithFuel, yulExpressionLevel,
    YulExpressionLevel.next]

/-- Deterministic ordinary outcomes of the public recursive grammar. -/
theorem yulExpressionPublicOutcomeSpec :
    DeterministicOutcomeSpec YulExpressionOrdinaryParses
      YulExpressionPublicRejects where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (yulExpressionOutcomeSpecWithFuel
      (yulExpressionPublicFuel input)).successOutputUnique
        leftParsed rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    exact (yulExpressionOutcomeSpecWithFuel
      (yulExpressionPublicFuel input)).successRejectDisjoint rejection

/-- The public outcome contract stated with the concrete expression rejection
relation used by transactional consumers. -/
theorem yulExpressionPublicDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulExpressionOrdinaryParses
      YulExpressionRejects where
  successOutputUnique :=
    yulExpressionPublicOutcomeSpec.successOutputUnique
  successRejectDisjoint := by
    intro input rejected rejection
    exact yulExpressionPublicOutcomeSpec.successRejectDisjoint
      (yulExpressionPublicRejects_iff.mpr rejection)

/-- Public clean recursive expressions are public ordinary successes. -/
theorem YulExpressionParses.toOrdinary {input output : Remainder}
    {expression : Syntax.YulExpr} (parsed : YulExpressionParses input
      expression output) :
    YulExpressionOrdinaryParses input expression output :=
  YulExpressionCleanParsesWithFuel.toOrdinary parsed

end Solcore.Syntax.DeclarativeGrammar

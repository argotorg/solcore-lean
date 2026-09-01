import Solcore.Syntax.DeclarativeCorePatternCoreOutcomeSelectionProperties

/-! Deterministic outcomes for the generic ordered `patternCore` dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One selected branch has functional output. -/
theorem PatternCoreBranchOrdinaryParses.output_unique
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop}
    (parenthesizedOutcomes : DeterministicOutcomeSpec
      parenthesizedOrdinary parenthesizedRejects)
    (dotConstructorOutcomes : DeterministicOutcomeSpec
      dotConstructorOrdinary dotConstructorRejects)
    (comptimeOutcomes : DeterministicOutcomeSpec comptimeOrdinary
      comptimeRejects)
    (qualifiedOutcomes : DeterministicOutcomeSpec qualifiedOrdinary
      qualifiedRejects)
    {branch : PatternCoreBranch} {input : Remainder}
    {left right : Syntax.Pattern} {afterLeft afterRight : Remainder}
    (leftParsed : PatternCoreBranchOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary branch input
        left afterLeft)
    (rightParsed : PatternCoreBranchOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary branch input
        right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | wildcard left =>
      cases rightParsed with
      | wildcard right => exact left.output_unique right
  | literal left =>
      cases rightParsed with
      | literal right => exact left.output_unique right
  | boolean left =>
      cases rightParsed with
      | boolean right => exact left.output_unique right
  | parenthesized left =>
      cases rightParsed with
      | parenthesized right =>
          exact parenthesizedOutcomes.successOutputUnique left right
  | dotConstructor left =>
      cases rightParsed with
      | dotConstructor right =>
          exact dotConstructorOutcomes.successOutputUnique left right
  | comptime left =>
      cases rightParsed with
      | comptime right => exact comptimeOutcomes.successOutputUnique left right
  | qualified left =>
      cases rightParsed with
      | qualified right =>
          exact qualifiedOutcomes.successOutputUnique left right

/-- Ordered Core-pattern success has functional output. -/
theorem PatternCoreOrdinaryParses.output_unique
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop}
    (parenthesizedOutcomes : DeterministicOutcomeSpec
      parenthesizedOrdinary parenthesizedRejects)
    (dotConstructorOutcomes : DeterministicOutcomeSpec
      dotConstructorOrdinary dotConstructorRejects)
    (comptimeOutcomes : DeterministicOutcomeSpec comptimeOrdinary
      comptimeRejects)
    (qualifiedOutcomes : DeterministicOutcomeSpec qualifiedOrdinary
      qualifiedRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternCoreOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary input left
        afterLeft)
    (rightParsed : PatternCoreOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary input right
        afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | selected leftSelection leftBranch =>
      cases rightParsed with
      | selected rightSelection rightBranch =>
          have branchEq := leftSelection.branch_unique rightSelection
          subst branchEq
          exact leftBranch.output_unique parenthesizedOutcomes
            dotConstructorOutcomes comptimeOutcomes qualifiedOutcomes
              rightBranch

/-- A selected branch rejection excludes success of that branch. -/
theorem PatternCoreBranchRejects.disjointOrdinary
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop}
    (parenthesizedOutcomes : DeterministicOutcomeSpec
      parenthesizedOrdinary parenthesizedRejects)
    (dotConstructorOutcomes : DeterministicOutcomeSpec
      dotConstructorOrdinary dotConstructorRejects)
    (comptimeOutcomes : DeterministicOutcomeSpec comptimeOrdinary
      comptimeRejects)
    (qualifiedOutcomes : DeterministicOutcomeSpec qualifiedOrdinary
      qualifiedRejects)
    {branch : PatternCoreBranch} {input rejected : Remainder}
    (rejection : PatternCoreBranchRejects parenthesizedRejects
      dotConstructorRejects comptimeRejects qualifiedRejects branch input
        rejected) :
    ¬ ∃ pattern output,
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary branch input
          pattern output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | parenthesized rejected =>
      cases successful with
      | parenthesized parsed =>
          exact parenthesizedOutcomes.successRejectDisjoint rejected
            ⟨_, _, parsed⟩
  | dotConstructor rejected =>
      cases successful with
      | dotConstructor parsed =>
          exact dotConstructorOutcomes.successRejectDisjoint rejected
            ⟨_, _, parsed⟩
  | comptime rejected =>
      cases successful with
      | comptime parsed =>
          exact comptimeOutcomes.successRejectDisjoint rejected ⟨_, _, parsed⟩
  | qualified rejected =>
      cases successful with
      | qualified parsed =>
          exact qualifiedOutcomes.successRejectDisjoint rejected ⟨_, _, parsed⟩

/-- Exact selected/final rejection excludes every ordinary success. -/
theorem PatternCoreRejects.disjointOrdinary
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop}
    (parenthesizedOutcomes : DeterministicOutcomeSpec
      parenthesizedOrdinary parenthesizedRejects)
    (dotConstructorOutcomes : DeterministicOutcomeSpec
      dotConstructorOrdinary dotConstructorRejects)
    (comptimeOutcomes : DeterministicOutcomeSpec comptimeOrdinary
      comptimeRejects)
    (qualifiedOutcomes : DeterministicOutcomeSpec qualifiedOrdinary
      qualifiedRejects)
    {input rejected : Remainder}
    (rejection : PatternCoreRejects parenthesizedRejects
      dotConstructorRejects comptimeRejects qualifiedRejects input rejected) :
    ¬ ∃ pattern output,
      PatternCoreOrdinaryParses parenthesizedOrdinary dotConstructorOrdinary
        comptimeOrdinary qualifiedOrdinary input pattern output := by
  rintro ⟨pattern, output, successful⟩
  cases rejection with
  | selected rejectedSelection branchRejected =>
      cases successful with
      | selected successfulSelection branchParsed =>
          have branchEq := rejectedSelection.branch_unique successfulSelection
          subst branchEq
          exact branchRejected.disjointOrdinary parenthesizedOutcomes
            dotConstructorOutcomes comptimeOutcomes qualifiedOutcomes
              ⟨_, _, branchParsed⟩
  | final finalRejected =>
      exact finalRejected.disjointSelected
        successful.exists_branch_selected

/-- Lift four deterministic recursive branches through the ordered core. -/
theorem patternCoreDeterministicOutcomeSpec
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop}
    (parenthesizedOutcomes : DeterministicOutcomeSpec
      parenthesizedOrdinary parenthesizedRejects)
    (dotConstructorOutcomes : DeterministicOutcomeSpec
      dotConstructorOrdinary dotConstructorRejects)
    (comptimeOutcomes : DeterministicOutcomeSpec comptimeOrdinary
      comptimeRejects)
    (qualifiedOutcomes : DeterministicOutcomeSpec qualifiedOrdinary
      qualifiedRejects) :
    DeterministicOutcomeSpec
      (PatternCoreOrdinaryParses parenthesizedOrdinary dotConstructorOrdinary
        comptimeOrdinary qualifiedOrdinary)
      (PatternCoreRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects) where
  successOutputUnique := PatternCoreOrdinaryParses.output_unique
    parenthesizedOutcomes dotConstructorOutcomes comptimeOutcomes
      qualifiedOutcomes
  successRejectDisjoint := PatternCoreRejects.disjointOrdinary
    parenthesizedOutcomes dotConstructorOutcomes comptimeOutcomes
      qualifiedOutcomes

end Solcore.Syntax.DeclarativeGrammar

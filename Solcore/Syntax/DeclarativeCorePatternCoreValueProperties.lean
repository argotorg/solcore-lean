import Solcore.Syntax.DeclarativeCorePatternCoreOutcomeProperties
import Solcore.Syntax.DeclarativeCorePatternLeafValueProperties

/-! Successful-value functionality of the ordered Core pattern dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Value functionality of four recursive branches suffices for the complete
ordered Core-pattern success relation; no raw rejection uniqueness is needed. -/
theorem PatternCoreOrdinaryParses.value_unique
    {parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    (parenthesizedUnique : ∀ {input left right afterLeft afterRight},
      parenthesizedOrdinary input left afterLeft →
      parenthesizedOrdinary input right afterRight → left = right)
    (dotConstructorUnique : ∀ {input left right afterLeft afterRight},
      dotConstructorOrdinary input left afterLeft →
      dotConstructorOrdinary input right afterRight → left = right)
    (comptimeUnique : ∀ {input left right afterLeft afterRight},
      comptimeOrdinary input left afterLeft →
      comptimeOrdinary input right afterRight → left = right)
    (qualifiedUnique : ∀ {input left right afterLeft afterRight},
      qualifiedOrdinary input left afterLeft →
      qualifiedOrdinary input right afterRight → left = right)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : PatternCoreOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary input left
      afterLeft)
    (rightParsed : PatternCoreOrdinaryParses parenthesizedOrdinary
      dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | selected leftSelection leftBranch =>
      cases rightParsed with
      | selected rightSelection rightBranch =>
          have branchEq := leftSelection.branch_unique rightSelection
          subst branchEq
          cases leftBranch with
          | wildcard leftLeaf =>
              cases rightBranch with
              | wildcard rightLeaf =>
                  exact leftLeaf.value_unique rightLeaf
          | literal leftLeaf =>
              cases rightBranch with
              | literal rightLeaf =>
                  exact leftLeaf.value_unique rightLeaf
          | boolean leftLeaf =>
              cases rightBranch with
              | boolean rightLeaf =>
                  exact leftLeaf.value_unique rightLeaf
          | parenthesized leftLeaf =>
              cases rightBranch with
              | parenthesized rightLeaf =>
                  exact parenthesizedUnique leftLeaf rightLeaf
          | dotConstructor leftLeaf =>
              cases rightBranch with
              | dotConstructor rightLeaf =>
                  exact dotConstructorUnique leftLeaf rightLeaf
          | comptime leftLeaf =>
              cases rightBranch with
              | comptime rightLeaf => exact comptimeUnique leftLeaf rightLeaf
          | qualified leftLeaf =>
              cases rightBranch with
              | qualified rightLeaf => exact qualifiedUnique leftLeaf rightLeaf

end Solcore.Syntax.DeclarativeGrammar

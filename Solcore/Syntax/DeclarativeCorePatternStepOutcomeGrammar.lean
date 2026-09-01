import Solcore.Syntax.DeclarativeCorePatternComptimeOutcomeGrammar
import Solcore.Syntax.DeclarativeCorePatternCoreOutcomeGrammar
import Solcore.Syntax.DeclarativeCorePatternDotConstructorOutcomeGrammar
import Solcore.Syntax.DeclarativeCorePatternParenthesizedOutcomeGrammar
import Solcore.Syntax.DeclarativeCorePatternPublicOutcomeGrammar
import Solcore.Syntax.DeclarativeCorePatternQualifiedOutcomeGrammar

/-! Named relations for one complete recursive Core pattern step. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Recursive subordinate outcomes consumed by one Core pattern layer. -/
structure CorePatternStepRelations where
  nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop
  nestedRejects : Remainder → Remainder → Prop
  expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop
  expressionRejects : Remainder → Remainder → Prop

namespace CorePatternStepRelations

abbrev parenthesizedOrdinary (relations : CorePatternStepRelations) :=
  ParenthesizedPatternOrdinaryParses relations.nestedOrdinary

abbrev parenthesizedRejects (relations : CorePatternStepRelations) :=
  ParenthesizedPatternRejects relations.nestedOrdinary
    relations.nestedRejects

abbrev dotConstructorOrdinary (relations : CorePatternStepRelations) :=
  DotConstructorPatternOrdinaryParses relations.nestedOrdinary
    relations.nestedRejects

abbrev dotConstructorRejects (relations : CorePatternStepRelations) :=
  DotConstructorPatternRejects relations.nestedOrdinary
    relations.nestedRejects

abbrev comptimeOrdinary (relations : CorePatternStepRelations) :=
  ComptimePatternOrdinaryParses relations.expressionOrdinary

abbrev comptimeRejects (relations : CorePatternStepRelations) :=
  ComptimePatternRejects relations.expressionRejects

abbrev qualifiedOrdinary (relations : CorePatternStepRelations) :=
  QualifiedPatternOrdinaryParses relations.nestedOrdinary
    relations.nestedRejects

abbrev qualifiedRejects (relations : CorePatternStepRelations) :=
  QualifiedPatternRejects relations.nestedOrdinary relations.nestedRejects

abbrev coreOrdinary (relations : CorePatternStepRelations) :=
  PatternCoreOrdinaryParses relations.parenthesizedOrdinary
    relations.dotConstructorOrdinary relations.comptimeOrdinary
      relations.qualifiedOrdinary

abbrev coreRejects (relations : CorePatternStepRelations) :=
  PatternCoreRejects relations.parenthesizedRejects
    relations.dotConstructorRejects relations.comptimeRejects
      relations.qualifiedRejects

abbrev ordinaryParses (relations : CorePatternStepRelations) :=
  PatternLayerOrdinaryParses relations.coreOrdinary relations.coreRejects

abbrev rejects (relations : CorePatternStepRelations) :=
  PatternLayerRejects relations.coreRejects

end CorePatternStepRelations

/-- Ordinary success of one complete public Core pattern recursion step. -/
abbrev CorePatternStepOrdinaryParses (relations : CorePatternStepRelations) :=
  relations.ordinaryParses

/-- Exact rejection of one complete public Core pattern recursion step. -/
abbrev CorePatternStepRejects (relations : CorePatternStepRelations) :=
  relations.rejects

end Solcore.Syntax.DeclarativeGrammar

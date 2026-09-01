import Solcore.Syntax.DeclarativeCoreExpressionAtomCoreOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreExpressionAtomPublicOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreExpressionLayerOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreExpressionPostfixOutcomeGrammar

/-!
Named parser-independent ordinary outcomes for one complete Core expression
recursion step.

The bundle hides the atom-core, public recovery, postfix, and operator-stack
composition while leaving each recursive subordinate relation explicit.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Declarative subordinate relations used by one Core expression step. -/
structure CoreExpressionStepRelations where
  nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop
  nestedRejects : Remainder → Remainder → Prop
  parameterOrdinary : Remainder → Syntax.LambdaParameter → Remainder → Prop
  parameterRejects : Remainder → Remainder → Prop
  typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop
  typeRejects : Remainder → Remainder → Prop
  blockOrdinary : Remainder → Syntax.Block → Remainder → Prop
  blockRejects : Remainder → Remainder → Prop

namespace CoreExpressionStepRelations

/-- Ordered non-recovering atom success for this relation bundle. -/
abbrev atomCoreOrdinary (relations : CoreExpressionStepRelations) :=
  ExpressionAtomCoreOrdinaryParses relations.nestedOrdinary
    relations.parameterOrdinary relations.typeOrdinary relations.blockOrdinary

/-- Ordered non-recovering atom rejection for this relation bundle. -/
abbrev atomCoreRejects (relations : CoreExpressionStepRelations) :=
  ExpressionAtomCoreRejects relations.nestedOrdinary relations.nestedRejects
    relations.parameterOrdinary relations.parameterRejects
      relations.typeOrdinary relations.typeRejects relations.blockRejects

/-- Public recovering atom success for this relation bundle. -/
abbrev atomOrdinary (relations : CoreExpressionStepRelations) :=
  ExpressionAtomOrdinaryParses relations.atomCoreOrdinary
    relations.atomCoreRejects

/-- Public recovering atom rejection for this relation bundle. -/
abbrev atomRejects (relations : CoreExpressionStepRelations) :=
  ExpressionAtomRejects relations.atomCoreRejects

/-- Complete maximal postfix success for this relation bundle. -/
abbrev postfixOrdinary (relations : CoreExpressionStepRelations) :=
  ExpressionPostfixOrdinaryParses relations.atomOrdinary
    relations.nestedOrdinary

/-- Complete maximal postfix rejection for this relation bundle. -/
abbrev postfixRejects (relations : CoreExpressionStepRelations) :=
  ExpressionPostfixRejects relations.atomOrdinary relations.nestedOrdinary
    relations.atomRejects relations.nestedRejects

/-- One complete operator-stack success for this relation bundle. -/
abbrev ordinaryParses (relations : CoreExpressionStepRelations) :=
  ExpressionLayerOrdinaryParses relations.nestedOrdinary
    relations.postfixOrdinary

/-- One complete operator-stack rejection for this relation bundle. -/
abbrev rejects (relations : CoreExpressionStepRelations) :=
  ExpressionLayerRejects relations.nestedOrdinary relations.nestedRejects
    relations.postfixOrdinary relations.postfixRejects

end CoreExpressionStepRelations

/-- Ordinary success of one complete Core expression recursion step. -/
abbrev CoreExpressionStepOrdinaryParses
    (relations : CoreExpressionStepRelations) := relations.ordinaryParses

/-- Exact rejection of one complete Core expression recursion step. -/
abbrev CoreExpressionStepRejects
    (relations : CoreExpressionStepRelations) := relations.rejects

end Solcore.Syntax.DeclarativeGrammar

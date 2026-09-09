import Solcore.Frontend.LocalExpressionCost
import Solcore.Core.Machine

/-! Original recursive calls evaluate callee, argument and actual closure body
in order. Grouping preserves the exact value, stores and cost of its child. -/

set_option autoImplicit false

namespace Solcore.Frontend

inductive RecursiveLocalComputationEvaluates
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop where
  | pure {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value}
      (child : LocalExpressionEvaluates table environment initialStore source value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore source value finalStore
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value}
      (child : RecursiveLocalComputationEvaluates table environment initialStore inner value finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore ⟨span, .group inner⟩ value finalStore
  | application {initialStore argumentStore bodyStore finalStore : Core.Store}
      {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {parameterType resultType : Core.Ty} {body : Core.Expr}
      {captured : Core.Environment} {argumentValue result : Core.Value}
      (functionEvaluation : RecursiveLocalComputationEvaluates table environment initialStore
        callee (.closure parameterType resultType body captured) argumentStore)
      (argumentEvaluation : RecursiveLocalComputationEvaluates table environment argumentStore
        argument argumentValue bodyStore)
      (bodyEvaluation : Core.Evaluates (argumentValue :: captured) bodyStore body result finalStore) :
      RecursiveLocalComputationEvaluates table environment initialStore
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore

inductive RecursiveLocalComputationEvaluatesWithCost
    (table : LocalNameTable) (environment : Resolved.Environment) :
    Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop where
  | pure {initialStore finalStore : Core.Store} {source : Syntax.Expr}
      {value : Core.Value} {cost : Nat}
      (child : LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore source value finalStore cost
  | group {span : Syntax.SourceSpan} {inner : Syntax.Expr}
      {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
      (child : RecursiveLocalComputationEvaluatesWithCost table environment initialStore inner value finalStore cost) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .group inner⟩ value finalStore cost
  | application {initialStore argumentStore bodyStore finalStore : Core.Store}
      {span argumentsSpan : Syntax.SourceSpan} {callee argument : Syntax.Expr}
      {parameterType resultType : Core.Ty} {body : Core.Expr}
      {captured : Core.Environment} {argumentValue result : Core.Value}
      {functionCost argumentCost bodyCost : Nat}
      (functionEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        callee (.closure parameterType resultType body captured) argumentStore functionCost)
      (argumentEvaluation : RecursiveLocalComputationEvaluatesWithCost table environment argumentStore
        argument argumentValue bodyStore argumentCost)
      (bodyPath : Core.Steps bodyCost
        (Core.State.initial body (argumentValue :: captured) bodyStore)
        (Core.State.final result finalStore)) :
      RecursiveLocalComputationEvaluatesWithCost table environment initialStore
        ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ result finalStore
        (functionCost + argumentCost + bodyCost + 3)

end Solcore.Frontend

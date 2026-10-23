import Solcore.Frontend.SourceInference.NodeGraphProperties
import Solcore.SourceSemantics.SourceInferenceActualCallGraph
import Solcore.Frontend.SourceInference.OccurrenceProperties

/-! Actual nonrecursive prefixes leave the inference node table closed.
These facts use the saved states from each successful computation. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualNodeGraph
open Frontend SourceInference TypeSystem Detail

theorem expressionAllocation {initial allocated : State} {id : ExpressionId}
    (allocation : initial.allocateExpressionId = (id, allocated))
    (closed : NodesClosed initial.nodes) : NodesClosed allocated.nodes := by
  have same := congrArg (fun pair => pair.2.nodes) allocation
  exact same ▸ closed

theorem statementAllocation {initial allocated : State} {id : StatementId}
    (allocation : initial.allocateStatementId = (id, allocated))
    (closed : NodesClosed initial.nodes) : NodesClosed allocated.nodes := by
  have same := congrArg (fun pair => pair.2.nodes) allocation
  exact same ▸ closed

theorem freshAllocation {initial allocated : State} {type : Ty}
    (allocation : initial.fresh = (type, allocated))
    (closed : NodesClosed initial.nodes) : NodesClosed allocated.nodes := by
  have same := congrArg (fun pair => pair.2.nodes) allocation
  exact same ▸ closed

theorem hiddenAllocation {initial allocated : State} {id : Resolved.LocalId}
    (allocation : initial.allocateHiddenLocal = (id, allocated))
    (closed : NodesClosed initial.nodes) : NodesClosed allocated.nodes := by
  have same := congrArg (fun pair => pair.2.nodes) allocation
  exact same ▸ closed

theorem constructorAllocation {initial allocated : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {value : DataConstructorInstantiation}
    (allocation : freshDataConstructorInstantiation dataType constructor initial = (value, allocated))
    (closed : NodesClosed initial.nodes) : NodesClosed allocated.nodes := by
  have same := congrArg (fun pair => pair.2.nodes) allocation
  rw [freshDataConstructorInstantiation_nodes] at same
  exact same ▸ closed

theorem unifyRun {initial final : State} {left right : Ty}
    (accepted : unify initial left right = .ok final)
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes :=
  (unify_occurrenceState_eq accepted).1.symm ▸ closed

theorem optionalFit {initial fitted : State} {expected : Option Ty} {type : Ty}
    (accepted : (match expected with | none => pure initial | some expected => unify initial type expected) =
      (Except.ok fitted : Except Error State))
    (closed : NodesClosed initial.nodes) : NodesClosed fitted.nodes := by
  cases expected with
  | none => cases Except.ok.inj accepted; exact closed
  | some type => exact unifyRun accepted closed

theorem assignedFit {initial fitted : State} {operator : Syntax.ValueAssignOp} {target : Ty}
    (accepted : (match operator with | .equal => pure initial | _ => unify initial target .word) =
      (Except.ok fitted : Except Error State))
    (closed : NodesClosed initial.nodes) : NodesClosed fitted.nodes := by
  cases operator
  · cases Except.ok.inj accepted; exact closed
  all_goals exact unifyRun accepted closed

theorem parameters {context : SourceInference.Context} {sources : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State} {result : List TypedBinder × List Ty × State}
    (accepted : bindLambdaParameters context sources index seen initial = .ok result)
    (closed : NodesClosed initial.nodes) : NodesClosed result.2.2.nodes :=
  (bindLambdaParameters_occurrenceState_eq accepted).1.symm ▸ closed

theorem pattern {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Pattern}
    {expected : Ty} {initial : State} {result : TypedMatchPattern × State}
    (accepted : inferMatchPatternFuel fuel context source expected initial = .ok result)
    (closed : NodesClosed initial.nodes) : NodesClosed result.2.nodes :=
  (inferMatchPatternFuel_occurrenceState_eq accepted).1.symm ▸ closed

theorem lambdaPrefix {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial final : State} {result : Ty}
    (prefixFacts : LambdaPrefixFacts context expected annotation types initial result final)
    (closed : NodesClosed initial.nodes) : NodesClosed final.nodes := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => exact closed
  | noExpectedPartsFresh _ _ allocated => exact freshAllocation allocated closed
  | expectedPartsAnnotated _ unified => exact unifyRun unified closed
  | expectedPartsInferred _ unified => exact unifyRun unified closed

end Solcore.SourceSemantics.SourceInferenceExecution.ActualNodeGraph

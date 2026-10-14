import Solcore.SourceSemantics.Staging.SelectedExpressionPreservation
import Solcore.SourceSemantics.Staging.SelectedStatementsPreservation
import Solcore.SourceSemantics.Staging.SelectedLoopPreservation
import Solcore.SourceSemantics.Staging.SelectedMatchPreservation
import Solcore.SourceSemantics.Staging.SelectedForItemsPreservation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

private structure PreservedAt (program : Program) (registry : Registry) (size : Nat) : Prop where
  expression : ExpressionAt program registry size
  expressions : ExpressionsAt program registry size
  applies : AppliesAt program registry size
  statements : StatementsAt program registry size
  whileLoop : WhileAt program registry size
  matchArms : MatchAt program registry size
  matchControl : MatchControlAt program registry size
  forItems : ForItemsAt program registry size
  forLoop : ForLoopAt program registry size
  rawForm : RawFormAt program registry size
  coercionStep : CoercionStepAt program registry size
  coercionPath : CoercionPathAt program registry size

private theorem all (selectedBodies : SelectedBodies program registry) (size : Nat) :
    PreservedAt program registry size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      exact {
        expression := expression_step selectedBodies size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).expressions)
          (fun smaller below => (ih smaller below).applies)
          (fun smaller below => (ih smaller below).statements)
          (fun smaller below => (ih smaller below).rawForm)
          (fun smaller below => (ih smaller below).coercionPath)
        expressions := expressions_step size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).expressions)
        applies := applies_all_step selectedBodies.globals size
          (fun smaller below => (ih smaller below).statements)
        statements := statements_step size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).statements)
          (fun smaller below => (ih smaller below).whileLoop)
          (fun smaller below => (ih smaller below).matchArms)
          (fun smaller below => (ih smaller below).matchControl)
          (fun smaller below => (ih smaller below).forItems)
          (fun smaller below => (ih smaller below).forLoop)
        whileLoop := while_step size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).statements)
          (fun smaller below => (ih smaller below).whileLoop)
        matchArms := match_step size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).statements)
        matchControl := match_control_step selectedBodies.signatures size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).statements)
        forItems := for_items_step size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).forItems)
        forLoop := for_loop_step size
          (fun smaller below => (ih smaller below).expression)
          (fun smaller below => (ih smaller below).statements)
          (fun smaller below => (ih smaller below).forItems)
          (fun smaller below => (ih smaller below).forLoop)
        rawForm := raw_form_step size
          (fun smaller below => (ih smaller below).expressions)
          (fun smaller below => (ih smaller below).applies)
        coercionStep := coercion_step_step selectedBodies size
          (fun smaller below => (ih smaller below).statements)
        coercionPath := coercion_path_step size
          (fun smaller below => (ih smaller below).coercionStep)
          (fun smaller below => (ih smaller below).coercionPath)
      }

theorem expression (selectedBodies : SelectedBodies program registry) {size : Nat} :
    ExpressionAt program registry size := (all selectedBodies size).expression

theorem expressions (selectedBodies : SelectedBodies program registry) {size : Nat} :
    ExpressionsAt program registry size := (all selectedBodies size).expressions

theorem applies (selectedBodies : SelectedBodies program registry) {size : Nat} :
    AppliesAt program registry size := (all selectedBodies size).applies

theorem statements (selectedBodies : SelectedBodies program registry) {size : Nat} :
    StatementsAt program registry size := (all selectedBodies size).statements

theorem while_loop (selectedBodies : SelectedBodies program registry) {size : Nat} :
    WhileAt program registry size := (all selectedBodies size).whileLoop

theorem match_arms (selectedBodies : SelectedBodies program registry) {size : Nat} :
    MatchAt program registry size := (all selectedBodies size).matchArms

theorem match_control (selectedBodies : SelectedBodies program registry) {size : Nat} :
    MatchControlAt program registry size := (all selectedBodies size).matchControl

theorem for_items (selectedBodies : SelectedBodies program registry) {size : Nat} :
    ForItemsAt program registry size := (all selectedBodies size).forItems

theorem for_loop (selectedBodies : SelectedBodies program registry) {size : Nat} :
    ForLoopAt program registry size := (all selectedBodies size).forLoop

theorem raw_form (selectedBodies : SelectedBodies program registry) {size : Nat} :
    RawFormAt program registry size := (all selectedBodies size).rawForm

theorem coercion_step (selectedBodies : SelectedBodies program registry) {size : Nat} :
    CoercionStepAt program registry size := (all selectedBodies size).coercionStep

theorem coercion_path (selectedBodies : SelectedBodies program registry) {size : Nat} :
    CoercionPathAt program registry size := (all selectedBodies size).coercionPath

theorem applies_fault (selectedBodies : SelectedBodies program registry) {size : Nat} :
    FaultPreservation.AppliesAt program registry size :=
  AppliesAt.fault (applies selectedBodies)

theorem expression_fault (selectedBodies : SelectedBodies program registry) {size : Nat} :
    FaultPreservation.ExpressionAt program registry size :=
  ExpressionAt.fault (expression selectedBodies)

theorem statements_fault (selectedBodies : SelectedBodies program registry) {size : Nat} :
    FaultPreservation.StatementsAt program registry size :=
  StatementsAt.fault (statements selectedBodies)

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation

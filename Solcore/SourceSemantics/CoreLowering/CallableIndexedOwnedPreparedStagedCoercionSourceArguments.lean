import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionAuthority
import Solcore.SourceSemantics.CoreLowering.CallableCoercionRequirementSafety
import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! A reached coercion step retains its genuine selected body and dictionary.
The actual compiler requirement rows exclude competing requirement faults;
the selected method excludes primitive rules. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionSourceArguments
open Core Frontend SourceInference Staging.Recursive
open Solcore.SourceSemantics.Dynamic
open CallableIndexedOwnedPreparedStagedCoercionAuthority (Port)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : SourceInference.CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available
    scope node policy input coercion output call)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {stages : Staging.Recursive.Registry}
  (port : Port step context invocation.evidence stages)

private theorem roots_unique {nodes : List NodeId} {left right : List StatementId}
    (first : StatementRoots nodes left) (second : StatementRoots nodes right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons first ih => cases second with | cons second => exact congrArg (List.cons _) (ih second)

/-- Every method body remains a strict child of the original conversion step. -/
theorem body {before after : Dynamic.Heap} {value : Dynamic.Value}
    {size : Nat} {outcome : Staging.Recursive.Outcome}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (trace : Size.CoercionStep (Program.ofChecked compiled.sourceProgram) stages size
      invocation context before coercion value outcome after) :
    ∃ bodySize bodyEnvironment bound finalContext bodyOutcome child,
      stages.Closure port.principal.sourceFunction child ∧
      BindersAllocate [] before port.principal.sourceBody.source.inputs [value] bodyEnvironment bound ∧
      Size.StatementsIn (Program.ofChecked compiled.sourceProgram) stages true bodySize child port.sourceAt.context
        bodyEnvironment bound port.principal.cached.compilation.statements finalContext bodyOutcome after ∧
      BodyResult port.principal.sourceBody.resultType bodyOutcome outcome ∧ bodySize < size := by
  cases trace with
  | coercionPrimitive absent _ => exact False.elim (absent _ _ port.selected)
  | coercionPrimitiveInput absent _ _ => exact False.elim (absent _ _ port.selected)
  | coercionRequirement fault =>
      exact False.elim (CallableCoercionRequirementSafety.selected_safe ledger step.selectedMethod port.selected fault)
  | coercionMethod method rootsEq selected parameters allocate trace matched =>
      obtain ⟨rfl, rfl⟩ := port.agrees _ _ method
      have rootsSame := roots_unique rootsEq port.sourceAt.frame.roots
      cases rootsSame
      have typesSame := parameters.bodyTypes_eq.symm.trans port.sourceAt.extended.bodyTypes_eq
      cases typesSame
      have contextSame := parameters.functional port.sourceAt.extended
      cases contextSame
      exact ⟨_, _, _, _, _, _, selected, allocate, trace, matched, Size.child_lt_stepSize (by simp)⟩

/-- Actual parameter entry reconstructs the original independent conversion. -/
theorem applied {before bound after : Dynamic.Heap} {value : Dynamic.Value}
    {bodyEnvironment : Dynamic.Environment} {bodySize : Nat}
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {child : Staging.Recursive.Scope}
    (selected : stages.Closure port.principal.sourceFunction child)
    (allocate : BindersAllocate [] before port.principal.sourceBody.source.inputs [value] bodyEnvironment bound)
    (trace : Size.StatementsIn (Program.ofChecked compiled.sourceProgram) stages true bodySize child port.sourceAt.context
      bodyEnvironment bound port.principal.cached.compilation.statements finalContext bodyOutcome after)
    (matched : BodyResult port.principal.sourceBody.resultType bodyOutcome outcome) :
    ∃ size, Size.CoercionStep (Program.ofChecked compiled.sourceProgram) stages size
      invocation context before coercion value outcome after :=
  ⟨_, .coercionMethod port.selected port.sourceAt.frame.roots selected port.sourceAt.extended allocate trace matched⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionSourceArguments

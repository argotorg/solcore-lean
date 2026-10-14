import Solcore.SourceSemantics.Staging.RecursiveLiftOutcomes
import Solcore.SourceSemantics.CoreLowering.SourceExecutionSize

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionLiftBounds
open Frontend SourceInference
open Staging.Recursive.Lifting (Adapted)

inductive RawOutcome (program : Program) (size : Nat) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (form : ExpressionForm)
    (requirements : List RequirementId) (coercions : List CoercionStep) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {value after} (evaluated : SourceExecutionSize.ExpressionFormEvaluates program size
      context evidence source environment before form requirements coercions value after) :
      RawOutcome program size context evidence source environment before form requirements coercions (.value value) after
  | fault {reason after} (failed : SourceExecutionSize.ExpressionFormFaults program size
      context evidence source environment before form requirements coercions reason after) :
      RawOutcome program size context evidence source environment before form requirements coercions (.fault reason) after

inductive StepOutcome (program : Program) (size : Nat) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (step : CoercionStep) (input : Dynamic.Value) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {value after} (evaluated : SourceExecutionSize.CoercionStepExecutes program size
      context evidence before step input value after) :
      StepOutcome program size context evidence before step input (.value value) after
  | fault {reason after} (failed : SourceExecutionSize.CoercionStepFaults program size
      context evidence before step input reason after) :
      StepOutcome program size context evidence before step input (.fault reason) after

inductive PathOutcome (program : Program) (size : Nat) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (steps : List CoercionStep) (input : Dynamic.Value) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {value after} (evaluated : SourceExecutionSize.CoercionPathExecutes program size
      context evidence before steps input value after) :
      PathOutcome program size context evidence before steps input (.value value) after
  | fault {reason after} (failed : SourceExecutionSize.CoercionPathFaults program size
      context evidence before steps input reason after) :
      PathOutcome program size context evidence before steps input (.fault reason) after

def RawLift (program : Program) (registry : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (plain : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ staged reached, Staging.Recursive.RawForm program registry invocation context environment before
    form requirements coercions staged reached ∧ Adapted plain after staged reached

def StepLift (program : Program) (registry : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : Context) (before : Dynamic.Heap)
    (step : CoercionStep) (input : Dynamic.Value) (plain : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ staged reached, Staging.Recursive.CoercionStep program registry invocation context before
    step input staged reached ∧ Adapted plain after staged reached

def PathLift (program : Program) (registry : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : Context) (before : Dynamic.Heap)
    (steps : List CoercionStep) (input : Dynamic.Value) (plain : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ staged reached, Staging.Recursive.CoercionPath program registry invocation context before
    steps input staged reached ∧ Adapted plain after staged reached

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionLiftBounds

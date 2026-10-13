import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineCertificates

/-! Source parameter and result shapes are checked on each actual selected
coercion method in the finite final compilation plan. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceShapeTable
open Core Frontend SourceInference

structure Shape (step : CoercionStep) (method : ExecutableImplMethods.CheckedMethod) : Prop where
  parameters : method.specialized.function.typedBody.inputs.map (fun binder => binder.scheme.body) = [step.source]
  result : method.specialized.function.inferredBodyType = step.target

def validateShape (step : CoercionStep) (method : ExecutableImplMethods.CheckedMethod) : Option (PLift (Shape step method)) :=
  if parameters : method.specialized.function.typedBody.inputs.map (fun binder => binder.scheme.body) = [step.source] then
    if result : method.specialized.function.inferredBodyType = step.target then some ⟨⟨parameters,result⟩⟩
    else none
  else none

def StepReady (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (step : CoercionStep) : Prop :=
  ∀ available method,
    SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available →
    SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method → Shape step method

def validateStep (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (step : CoercionStep) : Option (PLift (StepReady program caller node step)) :=
  match resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions with
  | .error _ => some ⟨by
      intro available method actual _selected
      rw [resolved] at actual
      cases actual⟩
  | .ok available =>
      match selected : SourceCompilationPlan.checkedCoercionMethod program caller node available step with
      | .error _ => some ⟨by
          intro actualAvailable method actualResolved actualSelected
          have same := Except.ok.inj (resolved.symm.trans actualResolved)
          subst actualAvailable
          rw [selected] at actualSelected
          cases actualSelected⟩
      | .ok method => do
          let ⟨shape⟩ ← validateShape step method
          return ⟨by
            intro actualAvailable actualMethod actualResolved actualSelected
            have same := Except.ok.inj (resolved.symm.trans actualResolved)
            subst actualAvailable
            have same := Except.ok.inj (selected.symm.trans actualSelected)
            subst actualMethod
            exact shape⟩

private def validateSteps (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) : (steps : List CoercionStep) →
    Option (PLift (∀ step ∈ steps, StepReady program caller node step))
  | [] => some ⟨by intro step member; cases member⟩
  | step :: steps => do
      let ⟨head⟩ ← validateStep program caller node step
      let ⟨tail⟩ ← validateSteps program caller node steps
      return ⟨by
        intro actual member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail actual member⟩

def NodeReady (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) : Prop :=
  ∀ step ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node, StepReady program caller node step

def expressions (caller : SourceSpecialization.SpecializedFunction) : List ExpressionNode :=
  caller.function.typedBody.nodes.filterMap fun
    | .expression node => some node
    | _ => none

private def validateNodes (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction) :
    (nodes : List ExpressionNode) → Option (PLift (∀ node ∈ nodes, NodeReady program caller node))
  | [] => some ⟨by intro node member; cases member⟩
  | node :: nodes => do
      let ⟨head⟩ ← validateSteps program caller node (node.coercions ++ CallableCoercionPreparation.argumentSteps node)
      let ⟨tail⟩ ← validateNodes program caller nodes
      return ⟨by
        intro actual member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail actual member⟩

def Ready (program : CheckedProgram) (rows : List SourceSpecialization.SpecializedFunction) : Prop :=
  ∀ caller ∈ rows, ∀ node ∈ expressions caller, NodeReady program caller node

def validate (program : CheckedProgram) : (rows : List SourceSpecialization.SpecializedFunction) →
    Option (PLift (Ready program rows))
  | [] => some ⟨by intro caller member; cases member⟩
  | caller :: rows => do
      let ⟨head⟩ ← validateNodes program caller (expressions caller)
      let ⟨tail⟩ ← validate program rows
      return ⟨by
        intro actual member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail actual member⟩

theorem Ready.shape {program : CheckedProgram} {rows : List SourceSpecialization.SpecializedFunction}
    (ready : Ready program rows) {caller : SourceSpecialization.SpecializedFunction} (member : caller ∈ rows)
    {node : ExpressionNode} (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    {coercion : CoercionStep} (site : coercion ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node)
    {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available)
    {method : ExecutableImplMethods.CheckedMethod}
    (selected : SourceCompilationPlan.checkedCoercionMethod program caller node available coercion = .ok method) :
    Shape coercion method :=
  ready caller member node (List.mem_filterMap.mpr ⟨.expression node, nodeMember, rfl⟩)
    coercion site available method resolved selected

end Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceShapeTable

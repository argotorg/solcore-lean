import Solcore.SourceSemantics.SourcePreparedPlanGrowth
import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalSpecializationOrigins

/-! Final call-edge origins retain the actual checked method action and its
worklist extension. Supplied outer edges remain distinct from source calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourcePreparedCallEdgeOrigins
open Frontend SourceInference SourceSpecializationWorklist
open SourcePreparedPlanGrowth
open CoreLowering.CallableCoercionPreparationSteps (Specialized)

def CoercionAt (node : ExpressionNode) (step : CoercionStep) : Prop :=
  step ∈ node.coercions ∨ ∃ callee arguments metadata,
    node.form = .call callee arguments (.indirect metadata) ∧
      step ∈ metadata.argumentCoercions

inductive Selection (program : CheckedProgram) (caller : Specialized)
    (node : ExpressionNode) (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) :
    Specialized → Prop where
  | coercion {step : CoercionStep} {method : ExecutableImplMethods.CheckedMethod}
      (occurrence : CoercionAt node step)
      (selected : SourceCompilationPlan.checkedCoercionMethod program caller node available step = .ok method)
      (boundary : SourceCompilationPlan.validateStagedCallBoundary caller node [node.id] method.specialized = .ok ())
      (evidence : (discard <| SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method) = .ok ()) :
      Selection program caller node available method.specialized
  | unary {requirements : List RequirementId} {operator : Syntax.UnaryOp} {operand : ExpressionId}
      {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}
      (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements)
      (nonempty : requirements ≠ []) (form : node.form = .unary operator operand)
      (selected : SourceCompilationPlan.checkedUnaryOperatorMethod program caller
        { node with type := node.rawType, requirements, coercions := [] } available operator = .ok selection)
      (boundary : SourceCompilationPlan.validateStagedCallBoundary caller
        { node with type := node.rawType, requirements, coercions := [] } [operand]
        selection.method.specialized = .ok ())
      (evidence : (discard <| SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
        { node with type := node.rawType, requirements, coercions := [] } selection) = .ok ()) :
      Selection program caller node available selection.method.specialized
  | binary {requirements : List RequirementId} {operator : Syntax.BinaryOp} {left right : ExpressionId}
      {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}
      (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements)
      (nonempty : requirements ≠ []) (form : node.form = .binary left operator right)
      (selected : SourceCompilationPlan.checkedBinaryOperatorMethod program caller
        { node with type := node.rawType, requirements, coercions := [] } available operator = .ok selection)
      (boundary : SourceCompilationPlan.validateStagedCallBoundary caller
        { node with type := node.rawType, requirements, coercions := [] } [left, right]
        selection.method.specialized = .ok ())
      (evidence : (discard <| SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
        { node with type := node.rawType, requirements, coercions := [] } selection) = .ok ()) :
      Selection program caller node available selection.method.specialized

structure Event (program : CheckedProgram) where
  before : Plan
  after : Plan
  caller : Specialized
  callerMember : caller ∈ before.specializations
  node : ExpressionNode
  nodeMember : .expression node ∈ caller.function.typedBody.nodes
  available : SourceTypedRuntime.RuntimeEvidenceEnvironment
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available
  root : Specialized
  selection : Selection program caller node available root
  budget : Nat
  extended : extendCompletePlan program before root ⟨caller.key, node.id, root.key⟩ budget = .ok (.complete after)

def Event.outer {program : CheckedProgram} (event : Event program) : CallEdge :=
  ⟨event.caller.key, event.node.id, event.root.key⟩

theorem Event.growth {program : CheckedProgram} (event : Event program) : Growth event.before event.after :=
  SourcePreparedPlanGrowth.extend event.extended

inductive Origin (program : CheckedProgram) (input final : Plan) (edge : CallEdge) : Prop where
  | input (canonical : SourceCompilationPlan.validateCanonicalInputPlan program input = .ok ())
      (present : edge ∈ input.callEdges)
      (row : Specialized) (member : row ∈ input.specializations)
      (source : CallEdge.SourceOrigin program row.key row.function.typedBody edge)
  | outer (event : Event program) (later : Growth event.after final) (same : edge = event.outer)
  | suppliedRoot (event : Event program) (later : Growth event.after final)
      (source : CallEdge.SourceOrigin program event.root.key event.root.function.typedBody edge)
  | ordinary (event : Event program) (later : Growth event.after final)
      (row : Specialized) (member : row ∈ event.after.specializations)
      (source : CallEdge.SourceOrigin program row.key row.function.typedBody edge)

theorem Origin.later {program : CheckedProgram} {input before after : Plan} {edge : CallEdge}
    (origin : Origin program input before edge) (growth : Growth before after) :
    Origin program input after edge := by
  cases origin with
  | input canonical present row member source => exact .input canonical present row member source
  | outer event later same => exact .outer event (later.trans growth) same
  | suppliedRoot event later source => exact .suppliedRoot event (later.trans growth) source
  | ordinary event later row member source => exact .ordinary event (later.trans growth) row member source

def All (program : CheckedProgram) (input final : Plan) : Prop :=
  ∀ edge ∈ final.callEdges, Origin program input final edge

theorem from_extension {program : CheckedProgram} {input : Plan} (event : Event program)
    (previous : All program input event.before) : All program input event.after := by
  intro edge member
  rcases extendCompletePlan_call_origins event.extended member with inherited | outer | root | ordinary
  · exact (previous edge inherited).later event.growth
  · exact .outer event (.refl _) outer
  · exact .suppliedRoot event (.refl _) root
  · obtain ⟨row, present, source⟩ := ordinary
    exact .ordinary event (.refl _) row present source

end Solcore.SourceSemantics.SourcePreparedCallEdgeOrigins

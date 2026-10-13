import Solcore.SourceSemantics.CoreLowering.CallableMethodResolverEvidence
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection

/-! A finite static validation traverses actual retained caller rows and their
original expression nodes. Every successful operator selection retains its
full materialized/resolved dictionary and actual caller header coverage. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodResolverTable
open Core Frontend SourceInference
open CallableCoercionExpressionCertificates (rawNode)
open CallableMethodResolverEvidence (Materialized)

structure SelectedReady (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction) (node : ExpressionNode)
    (selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod) where
  materialized : Materialized program caller node selection
  covered : CallableCoercionEvidenceOrigins.CallerCovered caller selection.method

def validateSelection (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction) (node : ExpressionNode)
    (selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod) :
    Option (SelectedReady program caller node selection) := do
  let materialized ← CallableMethodResolverEvidence.validate program caller node selection
  if covered : selection.method.traitPredicates.all
      (fun goal => decide (goal ∈ caller.assumptions)) = true then
    return ⟨materialized, fun goal member =>
      of_decide_eq_true (List.all_eq_true.mp covered goal member)⟩
  else none

def select (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (requirements : List RequirementId)
    (available : SourceTypedRuntime.RuntimeEvidenceEnvironment) :
    Except SourceTypedRuntime.RuntimeError SourceCompilationPlan.CheckedRuntimeOperatorMethod :=
  match node.form with
  | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod
      program caller (rawNode node requirements) available operator
  | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod
      program caller (rawNode node requirements) available operator
  | _ => .error (.unsupportedRequirements requirements)

def NodeReady (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) : Prop :=
  ∀ requirements available selection,
    SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements →
    SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available →
    select program caller node requirements available = .ok selection →
    Nonempty (SelectedReady program caller (rawNode node requirements) selection)

/-- Errors in a selector cannot issue an operator receipt. A successful
selector must pass the additional complete-dictionary and coverage checks. -/
def validateNode (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) : Option (PLift (NodeReady program caller node)) :=
  match owned : SourceCompilationPlan.ordinaryOwnedRequirements? node with
  | none => some ⟨by
      intro requirements available selection ordinary _resolved _selected
      rw [owned] at ordinary
      cases ordinary⟩
  | some requirements =>
      match resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions with
      | .error _ => some ⟨by
          intro requirements available selection _ordinary actualResolved _selected
          rw [resolved] at actualResolved
          cases actualResolved⟩
      | .ok available =>
          match selected : select program caller node requirements available with
          | .error _ => some ⟨by
              intro actualRequirements actualAvailable selection ordinary actualResolved actualSelected
              have sameRequirements := Option.some.inj (owned.symm.trans ordinary)
              have sameAvailable := Except.ok.inj (resolved.symm.trans actualResolved)
              subst actualRequirements actualAvailable
              rw [selected] at actualSelected
              cases actualSelected⟩
          | .ok selection =>
              match validateSelection program caller (rawNode node requirements) selection with
              | none => none
              | some retained => some ⟨by
                  intro actualRequirements actualAvailable actualSelection ordinary actualResolved actualSelected
                  have sameRequirements := Option.some.inj (owned.symm.trans ordinary)
                  have sameAvailable := Except.ok.inj (resolved.symm.trans actualResolved)
                  subst actualRequirements actualAvailable
                  have sameSelection := Except.ok.inj (selected.symm.trans actualSelected)
                  subst actualSelection
                  exact ⟨retained⟩⟩

def expressions (caller : SourceSpecialization.SpecializedFunction) : List ExpressionNode :=
  caller.function.typedBody.nodes.filterMap fun
    | .expression node => some node
    | _ => none

private def validateNodes (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction) :
    (nodes : List ExpressionNode) → Option (PLift (∀ node ∈ nodes, NodeReady program caller node))
  | [] => some ⟨by intro node member; cases member⟩
  | node :: nodes => do
      let ⟨head⟩ ← validateNode program caller node
      let ⟨tail⟩ ← validateNodes program caller nodes
      return ⟨by
        intro actual member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail actual member⟩

def Ready (program : CheckedProgram) (rows : List SourceSpecialization.SpecializedFunction) : Prop :=
  ∀ caller ∈ rows, ∀ node ∈ expressions caller, NodeReady program caller node

/-- The finite producer is executable from the real retained source table.
Only a validated table can supply subsequent selected operator receipts. -/
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

/-- Actual lowering supplies the same owned requirement list, caller resolver
and selector equations checked by the finite table. -/
theorem Ready.operator {program : CheckedProgram}
    {rows : List SourceSpecialization.SpecializedFunction} (ready : Ready program rows)
    {caller : SourceSpecialization.SpecializedFunction} (member : caller ∈ rows)
    {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
    {child : SourceCoreEvidence.Child} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode}
    {output : SourceCoreBasic.LoweredExpr}
    (actual : CallablePreparedMethodSelection.Operator program project caller compilation child fuel
      source scope id reasonAt policy node output)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes) :
    Nonempty (SelectedReady program caller (rawNode node actual.requirements) actual.selection) := by
  have expressionMember : node ∈ expressions caller :=
    List.mem_filterMap.mpr ⟨.expression node, nodeMember, rfl⟩
  exact ready caller member node expressionMember actual.requirements actual.available actual.selection
    actual.ordinary actual.resolved actual.selectedMethod

end Solcore.SourceSemantics.CoreLowering.CallableMethodResolverTable

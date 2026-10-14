import Solcore.Test.SourceCoreCanonicalScopedCompilerBody
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionResidual
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open AcceptedNamedExpressionFlow

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

def RelayReached (observed : ObservedProgram fixture) (id : ExpressionId) : Prop :=
  id = observed.relayShape.initial.value.node.id ∨
    id = observed.relayShape.initialRead.node.id ∨ id = observed.relayShape.finalRead.node.id

theorem ActualHeader.relay_reached_form (actual : ActualHeader fixture observed.relayRow.row)
    {id : ExpressionId} {node : ExpressionNode} (reached : RelayReached observed id)
    (found : actual.header.function.source.lookupExpression? id = some node) :
    (∃ name binder, node.form = .reference name (.local binder)) ∨
      (∃ callee instantiation, node.form = .call callee [observed.relayShape.initialRead.node.id]
        (.declaration instantiation)) := by
  rw [actual.source] at found
  rcases reached with same | same | same
  · rw [same, observed.relayShape.initial.value.found] at found
    cases Option.some.inj found
    exact .inr ⟨_, _, observed.relayShape.initial.form⟩
  · rw [same, observed.relayShape.initialRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, observed.relayShape.initialRead.form⟩
  · rw [same, observed.relayShape.finalRead.found] at found
    cases Option.some.inj found
    exact .inl ⟨_, _, observed.relayShape.finalRead.form⟩

theorem ActualHeader.relay_reached_arguments (actual : ActualHeader fixture observed.relayRow.row)
    {id callee : ExpressionId} {node : ExpressionNode} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} (reached : RelayReached observed id)
    (found : actual.header.function.source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation)) :
    arguments = [observed.relayShape.initialRead.node.id] := by
  rcases actual.relay_reached_form reached found with ⟨name, binder, localForm⟩ | ⟨other, selected, directForm⟩
  · rw [localForm] at form
    cases form
  · cases form.symm.trans directForm
    rfl

variable (actual : ActualHeader fixture observed.relayRow.row)
  {rootFuel : Nat} {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
  {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
    (compiled := fixture.recipe.compiled) actual.prepared.named actual.prepared.diagnostics
    actual.prepared.code actual.prepared.compilation rootFuel actual.header.function.source
    rootScope rootId actual.header.reasonAt rootLowered)

private theorem no_method {id : ExpressionId} {node : ExpressionNode}
    (reached : RelayReached observed id)
    (found : actual.header.function.source.lookupExpression? id = some node)
    (method : MethodForm node.form) : False := by
  rcases actual.relay_reached_form reached found with ⟨name, binder, form⟩ | ⟨callee, instantiation, form⟩
  all_goals
    rcases method with ⟨operator, operand, operatorForm⟩ | ⟨operator, left, right, operatorForm⟩
    all_goals rw [form] at operatorForm; cases operatorForm

private theorem no_cause {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : Head root.selected.policy root.selected.lowerBody fuel
      (CallableIndexedNamedGeneration.context fixture.recipe.compiled.indexed actual.prepared.named)
      actual.header.function.source scope id actual.header.reasonAt lowered)
    (reached : RelayReached observed id) (cause : Cause root head) : False := by
  have forms := actual.relay_reached_form reached head.found
  cases cause with
  | form _ notLeaf notDirect _notIndirect _notMethod _notIndex _notConstructor _notComposite =>
      rcases forms with ⟨name, binder, form⟩ | ⟨callee, instantiation, form⟩
      · exact notLeaf (form ▸ LeafForm.read name binder)
      · exact notDirect ⟨_, _, _, form⟩
  | initializer _ selected =>
      have found := selected.found
      simp only [observed.noLocals, List.find?_nil, Option.filter_none] at found
      cases found
  | special selected outside _outsideMethod =>
      rcases forms with ⟨name, binder, form⟩ | ⟨callee, instantiation, form⟩
      · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy
          actual.relay_metadata head.found (.inr ⟨name, binder, form⟩)
          (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child
            root.selected.policy root.selected.lowerBody fuel
            (CallableIndexedNamedGeneration.context fixture.recipe.compiled.indexed actual.prepared.named))
          (fuel + 1) scope actual.header.reasonAt
        have same := head.selected.symm.trans profile.2.2
        rw [selected] at same
        cases same
      · exact outside ⟨_, _, _, form⟩
  | indexOperands _ form _ | constructorRange _ form _ =>
      rcases forms with ⟨name, binder, localForm⟩ | ⟨callee, instantiation, directForm⟩
      · rw [localForm] at form
        cases form
      · rw [directForm] at form
        cases form
  | operatorOrdinary _ operator _ | operatorCoercions _ operator _ =>
      exact no_method actual reached head.found operator

private theorem children_reached {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (step : Step root actual.header.function.source scope actual.header.reasonAt fuel id lowered)
    (reached : RelayReached observed id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : RelayReached observed entry.1 := by
  cases step with
  | leaf => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
      have args := actual.relay_reached_arguments reached receipt.metadata.found receipt.form
      have present := (List.of_mem_zip member).1
      rw [args] at present
      exact .inr (.inl (List.mem_singleton.mp present))
  | evidence head _ receipt =>
      have args := actual.relay_reached_arguments reached head.found receipt.form
      have present := (List.of_mem_zip member).1
      rw [args] at present
      exact .inr (.inl (List.mem_singleton.mp present))
  | indirect _head _plain receipt =>
      have form := receipt.originalForm
      rcases actual.relay_reached_form reached receipt.found with
        ⟨name, binder, localForm⟩ | ⟨callee, instantiation, directForm⟩
      · rw [localForm] at form
        cases form
      · rw [directForm] at form
        cases form
  | index _head _plain receipt =>
      have form := receipt.form
      rcases actual.relay_reached_form reached receipt.found with
        ⟨name, binder, localForm⟩ | ⟨callee, instantiation, directForm⟩
      · rw [localForm] at form
        cases form
      · rw [directForm] at form
        cases form
  | constructor _head _plain receipt =>
      have form := receipt.form
      rcases actual.relay_reached_form reached receipt.found with
        ⟨name, binder, localForm⟩ | ⟨callee, instantiation, directForm⟩
      · rw [localForm] at form
        cases form
      · rw [directForm] at form
        cases form
  | composite _head _plain receipt =>
      have form := receipt.form
      rcases actual.relay_reached_form reached receipt.found with
        ⟨name, binder, localForm⟩ | ⟨callee, instantiation, directForm⟩
      · rw [localForm] at form
        cases form
      · rw [directForm] at form
        cases form
  | method _head _selected receipt =>
      apply False.elim
      apply no_method actual reached receipt.metadata.found
      rcases receipt.operator.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
      · exact .inl ⟨operator, operand, form⟩
      · exact .inr ⟨operator, left, right, form⟩

/-- Only accepted argument edges are followed. The stored declaration callee
is preserved in Source, but is never substituted for an executed child. -/
theorem ActualHeader.relay_boundary_impossible {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : Trace root actual.header.function.source scope actual.header.reasonAt fuel id lowered}
    (boundary : Boundary tree) (reached : RelayReached observed id) : False := by
  induction boundary with
  | here head cause children => exact no_cause actual root head reached cause
  | child step children entry member next ih =>
      exact ih (children_reached actual root step reached member)

theorem ActualHeader.relay_expression_residual_impossible
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} (reached : RelayReached observed id)
    (residual : Residual actual.prepared actual.header
      (CallableIndexedOwnedPreparedNamedSyntaxAdmission.DirectSite observed.relayAdmission.table.rows)
      fuel actual.header.function.source scope id lowered) : False :=
  actual.relay_boundary_impossible residual.root residual.boundary reached

end Tests.SourceCoreCanonicalScoped

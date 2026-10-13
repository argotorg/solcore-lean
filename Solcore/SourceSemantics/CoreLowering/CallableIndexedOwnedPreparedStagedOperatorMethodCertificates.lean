import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallCertificates

/-! Selected operator methods retain the real evidence hook, complete method
record and ordered recursive children. Their physical slot is independent of
ordinary declaration headers. This receipt contains no execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodCertificates
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child Metadata)

structure Receipt (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (compilation : SourceCoreFunctions.Context)
    (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  program : CheckedProgram
  project : SourceCoreEvidence.Projector
  caller : SourceSpecialization.SpecializedFunction
  node : ExpressionNode
  metadata : Metadata values.checked source id node lowered.type
  operator : CallablePreparedMethodSelection.Operator program project caller compilation
    (Child policy body fuel compilation) (fuel + 1) source scope id reasonAt policy.callables node lowered
  special : (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation (Child policy body fuel compilation) (fuel + 1)
        source scope id reasonAt) = .ok (some lowered)
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
    compilation source scope id reasonAt = .ok lowered

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem call_index_eq {first second : SourceCoreCalls.Signature} {firstIndex secondIndex : Nat}
    {firstArguments secondArguments : Expr} {firstReason secondReason : Word}
    (same : SourceCoreCalls.call first firstIndex firstArguments firstReason =
      SourceCoreCalls.call second secondIndex secondArguments secondReason) : firstIndex = secondIndex := by
  simp only [SourceCoreCalls.call, LanguageResult.bind, OptionalCell.read] at same
  have tail := (Expr.caseE.inj same).2.2
  have read := (Expr.caseE.inj tail).1
  have reference := (Expr.caseE.inj read).1
  exact Nat.add_right_cancel (Expr.var.inj (Expr.loadCell.inj reference))

namespace Receipt
variable (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)

abbrev method := receipt.operator.selection.method
abbrev arguments := receipt.operator.arguments
abbrev codes := receipt.operator.loweredArguments
abbrev signature := receipt.operator.native.signature
abbrev index := receipt.operator.native.index

theorem generated : receipt.arguments.mapM (fun child =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt) =
      .ok receipt.codes := by
  simpa only [arguments, codes, Child, Nat.min_eq_right (Nat.le_succ fuel)] using receipt.operator.argumentsAccepted

theorem operand : receipt.operator.operand = lowered := by
  have suffix := receipt.operator.suffix.accepted
  simpa only [receipt.metadata.coercions, SourceCoreEvidence.applyCoercions, pure, Except.pure,
    Except.ok.injEq] using suffix

theorem parameter : receipt.signature.parameterType = (SourceCoreCalls.packArguments receipt.codes).type :=
  receipt.operator.native.inputType

theorem result : receipt.signature.resultType = lowered.type := by
  exact (congrArg SourceCoreBasic.LoweredExpr.type
    (receipt.operand.symm.trans receipt.operator.native.emitted)).symm

theorem emitted : lowered.expression = SourceCoreCalls.call receipt.signature
    (scope.length + compilation.administrativePrefix + receipt.index)
    (SourceCoreCalls.packArguments receipt.codes).expression compilation.internalReason :=
  congrArg SourceCoreBasic.LoweredExpr.expression
    (receipt.operand.symm.trans receipt.operator.native.emitted)

theorem global : compilation.globals[receipt.index]? = some receipt.signature := by
  have member : (receipt.signature, receipt.index) ∈ compilation.globals.zipIdx.filter
      (fun row => decide (row.1.key = receipt.operator.key)) := by
    rw [receipt.operator.native.global]
    exact List.mem_singleton.mpr rfl
  exact List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp member).1

theorem key : receipt.signature.key = receipt.operator.key := by
  have member : (receipt.signature, receipt.index) ∈ compilation.globals.zipIdx.filter
      (fun row => decide (row.1.key = receipt.operator.key)) := by
    rw [receipt.operator.native.global]
    exact List.mem_singleton.mpr rfl
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp member).2

theorem record : SourceCompilationPlan.exactSpecialization compilation.plan receipt.signature.key =
    .ok receipt.operator.target.specialized := by
  rw [receipt.key]
  exact receipt.operator.target.selected

theorem argument_references {child : ExpressionId} (member : child ∈ receipt.arguments) :
    (.expression child : NodeId) ∈ receipt.node.form.references := by
  rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ |
    ⟨operator, left, right, form, arguments⟩
  · simp only [Receipt.arguments, arguments, List.mem_singleton] at member
    subst child
    simp [form, ExpressionForm.references]
  · simp only [Receipt.arguments, arguments, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [form, ExpressionForm.references]

theorem unary_arguments {operator : Syntax.UnaryOp} {operand : ExpressionId}
    (form : receipt.node.form = .unary operator operand) : receipt.arguments = [operand] := by
  rcases receipt.operator.form with ⟨actual, child, actualForm, arguments⟩ |
    ⟨actual, left, right, actualForm, _⟩
  · obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (form.symm.trans actualForm)
    exact arguments
  · simp [form] at actualForm

theorem binary_arguments {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (form : receipt.node.form = .binary left operator right) : receipt.arguments = [left, right] := by
  rcases receipt.operator.form with ⟨actual, child, actualForm, _⟩ |
    ⟨actual, first, second, actualForm, arguments⟩
  · simp [form] at actualForm
  · obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (form.symm.trans actualForm)
    exact arguments

theorem node_eq (other : Receipt policy body fuel compilation values source scope id reasonAt lowered) :
    receipt.node = other.node :=
  Option.some.inj (receipt.metadata.found.symm.trans other.metadata.found)

theorem arguments_eq (other : Receipt policy body fuel compilation values source scope id reasonAt lowered) :
    receipt.arguments = other.arguments := by
  rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
  · have otherForm := receipt.node_eq other ▸ form
    exact arguments.trans (other.unary_arguments otherForm).symm
  · have otherForm := receipt.node_eq other ▸ form
    exact arguments.trans (other.binary_arguments otherForm).symm

theorem codes_eq (other : Receipt policy body fuel compilation values source scope id reasonAt lowered) :
    receipt.codes = other.codes := by
  have generated := receipt.generated
  rw [receipt.arguments_eq other] at generated
  exact Except.ok.inj (generated.symm.trans other.generated)

theorem index_eq (other : Receipt policy body fuel compilation values source scope id reasonAt lowered) :
    receipt.index = other.index := by
  have same := call_index_eq (receipt.emitted.symm.trans other.emitted)
  omega

theorem signature_eq (other : Receipt policy body fuel compilation values source scope id reasonAt lowered) :
    receipt.signature = other.signature := by
  have first := receipt.global
  rw [receipt.index_eq other] at first
  exact Option.some.inj (first.symm.trans other.global)

theorem arguments_typed {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type) :
    ∃ types, ExpressionsHaveTypes source context receipt.arguments types := by
  generalize typeEq : receipt.node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.metadata.found)
    subst actualNode
    rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ |
      ⟨operator, left, right, form, arguments⟩
    · rw [form] at raw
      cases raw with
      | @unary _ _ _ operandType _ _ child _ =>
          refine ⟨[operandType], ?_⟩
          change ExpressionsHaveTypes source context receipt.operator.arguments _
          rw [arguments]
          exact .cons child (.nil context)
    · rw [form] at raw
      cases raw with
      | @binary _ _ _ _ operandType _ _ first second _ =>
          refine ⟨[operandType, operandType], ?_⟩
          change ExpressionsHaveTypes source context receipt.operator.arguments _
          rw [arguments]
          exact .cons first (.cons second (.nil context))

end Receipt

/-- The real special branch fixes the same recursive budget and parent output.
Method Source selection and body support are supplied at the authority layer. -/
theorem of_evidence {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    (coercions : node.coercions = [])
    (projected : values.checked.catalog.project node.type = .ok lowered.type)
    (operator : CallablePreparedMethodSelection.Operator program project caller compilation
      (Child policy body fuel compilation) (fuel + 1) source scope id reasonAt policy.callables node lowered)
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation (Child policy body fuel compilation) (fuel + 1)
          source scope id reasonAt) = .ok (some lowered))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt policy body fuel compilation values source scope id reasonAt lowered) := by
  have owner : id.occurrence.owner = source.owner := by
    apply Classical.byContradiction
    intro mismatch
    simp [SourceCoreFunctions.lowerExpressionWithPolicy, mismatch, bind, Except.bind] at accepted
  exact ⟨⟨program, project, caller, node, ⟨operator.found, owner, coercions, projected⟩, operator, special, accepted⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodCertificates

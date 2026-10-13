import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodArgumentBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodAuthority
import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceBounds

/-! The independent unary/binary trace supplies actual ordered operand grades,
selected body and dictionary. Authentic roots and binder extensions identify
the compiler body's exact Source context without an execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open Staging.Recursive
open Solcore.SourceSemantics.Dynamic
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)
open CallableIndexedOwnedPreparedStagedMethodArgumentBounds (Trace)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id reasonAt lowered)
  {stages : Staging.Recursive.Registry}
  (port : Port (compiled := compiled) receipt context invocation.evidence stages)

private theorem roots_unique {nodes : List NodeId} {left right : List StatementId}
    (first : StatementRoots nodes left) (second : StatementRoots nodes right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons first ih => cases second with | cons second => exact congrArg (List.cons _) (ih second)

theorem unary_dispatch {operator : Syntax.UnaryOp} {operand : ExpressionId}
    (form : receipt.node.form = .unary operator operand) :
    UnaryTraitDispatch operator port.principal.traitName port.principal.methodName := by
  rcases port.dispatch with ⟨actual, child, actualForm, dispatch⟩ | ⟨actual, left, right, actualForm, _⟩
  · obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (actualForm.symm.trans form)
    exact dispatch
  · simp [form] at actualForm

theorem binary_dispatch {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (form : receipt.node.form = .binary left operator right) :
    BinaryTraitDispatch operator port.principal.traitName port.principal.methodName := by
  rcases port.dispatch with ⟨actual, child, actualForm, _⟩ | ⟨actual, first, second, actualForm, dispatch⟩
  · simp [form] at actualForm
  · obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actualForm.symm.trans form)
    exact dispatch

private theorem dispatch_continues {operator : Syntax.BinaryOp} {traitName methodName : String}
    (dispatch : BinaryTraitDispatch operator traitName methodName) (value : Dynamic.Value) :
    EvaluatesRightOperand operator value := by
  cases dispatch <;> exact .strict (by constructor)

include port in
theorem binary_continues {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (form : receipt.node.form = .binary left operator right) (value : Dynamic.Value) :
    EvaluatesRightOperand operator value :=
  dispatch_continues (binary_dispatch receipt port form) value

/-- The selected method body starts only after the actual ordered operands. -/
def Success (budget : Nat) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ argumentsHeap arguments,
    Trace budget (Program.ofChecked compiled.sourceProgram) stages invocation context environment
      before receipt.arguments (.values arguments) argumentsHeap ∧
    ∃ bodySize bodyEnvironment bound finalContext bodyOutcome child,
      stages.Closure port.principal.sourceFunction child ∧
      BindersAllocate [] argumentsHeap port.principal.sourceBody.source.inputs arguments bodyEnvironment bound ∧
      Size.StatementsIn (Program.ofChecked compiled.sourceProgram) stages true bodySize child port.sourceAt.context
        bodyEnvironment bound port.principal.cached.compilation.statements finalContext bodyOutcome after ∧
      BodyResult port.principal.sourceBody.resultType bodyOutcome outcome ∧ bodySize < budget

private theorem align_body {bodyInstance : BodyInstance} {dictionary : EvidenceEnvironment}
    {roots : List StatementId} {child : Staging.Recursive.Scope}
    {parameterTypes : List TypeSystem.Ty} {bodyContext : SourceSemantics.Context}
    {bodyEnvironment : Dynamic.Environment} {bound after : Dynamic.Heap} {bodySize : Nat}
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    (selection : OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context invocation.evidence
      port.principal.traitName port.principal.methodName receipt.node.requirements bodyInstance dictionary)
    (rootsEq : StatementRoots bodyInstance.source.roots roots)
    (selected : stages.Closure (methodView bodyInstance dictionary roots) child)
    (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
    (trace : Size.StatementsIn (Program.ofChecked compiled.sourceProgram) stages true bodySize child bodyContext
      bodyEnvironment bound roots finalContext bodyOutcome after) :
    bodyInstance = port.principal.sourceBody ∧ dictionary = port.principal.dictionary ∧
    stages.Closure port.principal.sourceFunction child ∧
    Size.StatementsIn (Program.ofChecked compiled.sourceProgram) stages true bodySize child port.sourceAt.context
      bodyEnvironment bound port.principal.cached.compilation.statements finalContext bodyOutcome after := by
  obtain ⟨rfl, rfl⟩ := port.agrees bodyInstance dictionary selection
  have rootsSame : roots = port.principal.cached.compilation.statements := roots_unique rootsEq port.sourceAt.frame.roots
  cases rootsSame
  have typesSame := parameters.bodyTypes_eq.symm.trans port.sourceAt.extended.bodyTypes_eq
  cases typesSame
  have contextSame := parameters.functional port.sourceAt.extended
  cases contextSame
  exact ⟨rfl, rfl, selected, trace⟩

theorem children {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (trace : Size.Expression (Program.ofChecked compiled.sourceProgram) stages size invocation context environment before id outcome after) :
    Success receipt port size environment before outcome after ∨
      ∃ failure, outcome = .fault failure ∧ Trace size (Program.ofChecked compiled.sourceProgram) stages
        invocation context environment before receipt.arguments (.fault failure) after := by
  have nonempty := CallableIndexedOwnedPreparedStagedMethodSourceInversion.requirements_nonempty port.selected
  rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
  · have dispatch := unary_dispatch receipt port form
    have original := CallableIndexedOwnedPreparedStagedMethodSourceInversion.unary unique receipt.metadata.found form nonempty trace
    cases original with
    | operandFault operandTrace =>
      refine .inr ⟨_, rfl, ?_⟩
      rw [Receipt.arguments, arguments]
      exact .headFault operandTrace (Size.child_lt_stepSize (by simp))
    | method selectedDispatch selection operandTrace rootsEq selected parameters allocate bodyTrace resultRule =>
      obtain ⟨rfl, rfl⟩ := CallablePreparedOperatorSourceBounds.unary_dispatch_unique selectedDispatch dispatch
      obtain ⟨bodyEq, dictionaryEq, selectedAligned, aligned⟩ := align_body receipt port selection rootsEq selected parameters bodyTrace
      cases bodyEq
      cases dictionaryEq
      refine .inl ⟨_, _, ?_, _, _, _, _, _, _, selectedAligned, allocate, aligned, resultRule, Size.child_lt_stepSize (by simp)⟩
      rw [Receipt.arguments, arguments]
      exact .cons operandTrace (Size.child_lt_stepSize (by simp)) .nil
  · have dispatch := binary_dispatch receipt port form
    have original := CallableIndexedOwnedPreparedStagedMethodSourceInversion.binary unique receipt.metadata.found form nonempty trace
    cases original with
    | leftFault first =>
      refine .inr ⟨_, rfl, ?_⟩
      rw [Receipt.arguments, arguments]
      exact .headFault first (Size.child_lt_stepSize (by simp))
    | rightFault first _continues second =>
      refine .inr ⟨_, rfl, ?_⟩
      rw [Receipt.arguments, arguments]
      exact .tailFault first (Size.child_lt_stepSize (by simp)) (.headFault second (Size.child_lt_stepSize (by simp)))
    | method selectedDispatch selection first _continues second rootsEq selected parameters allocate bodyTrace resultRule =>
      obtain ⟨rfl, rfl⟩ := CallablePreparedOperatorSourceBounds.binary_dispatch_unique selectedDispatch dispatch
      obtain ⟨bodyEq, dictionaryEq, selectedAligned, aligned⟩ := align_body receipt port selection rootsEq selected parameters bodyTrace
      cases bodyEq
      cases dictionaryEq
      refine .inl ⟨_, _, ?_, _, _, _, _, _, _, selectedAligned, allocate, aligned, resultRule, Size.child_lt_stepSize (by simp)⟩
      rw [Receipt.arguments, arguments]
      exact .cons first (Size.child_lt_stepSize (by simp)) (.cons second (Size.child_lt_stepSize (by simp)) .nil)

include port in
/-- An actual operand-list fault reconstructs the original operator fault. -/
theorem arguments_fault {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {failure : Staging.Recursive.Failure}
    (trace : Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size invocation context environment
      before receipt.arguments (.fault failure) after) :
    ∃ sourceSize, Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize invocation context
      environment before id (.fault failure) after := by
  rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
  · have occurrence : Occurrence invocation id (.unary operator operand) receipt.node.requirements :=
      ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, form, rfl, receipt.metadata.coercions⟩
    rw [Receipt.arguments, arguments] at trace
    cases trace with
    | headFault head => exact ⟨_, .unaryOperandFault occurrence head⟩
    | tailFault _ tail => cases tail
  · have occurrence : Occurrence invocation id (.binary left operator right) receipt.node.requirements :=
      ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, form, rfl, receipt.metadata.coercions⟩
    rw [Receipt.arguments, arguments] at trace
    cases trace with
    | headFault head => exact ⟨_, .binaryLeftFault occurrence head⟩
    | tailFault first tail =>
      cases tail with
      | headFault second => exact ⟨_, .binaryRightFault occurrence first (binary_continues receipt port form _) second⟩
      | tailFault _ tail => cases tail

/-- Real parameter entry and the selected body reconstruct the independent
operator call; ordered operands determine its exact arity. -/
theorem applied {environment bodyEnvironment : Dynamic.Environment}
    {before argumentsHeap bound after : Dynamic.Heap} {size bodySize : Nat}
    {arguments : List Dynamic.Value} {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {outcome : Staging.Recursive.Outcome}
    {child : Staging.Recursive.Scope}
    (trace : Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size invocation context environment
      before receipt.arguments (.values arguments) argumentsHeap)
    (selected : stages.Closure port.principal.sourceFunction child)
    (allocated : BindersAllocate [] argumentsHeap port.principal.sourceBody.source.inputs arguments bodyEnvironment bound)
    (bodyTrace : Size.StatementsIn (Program.ofChecked compiled.sourceProgram) stages true bodySize child port.sourceAt.context
      bodyEnvironment bound port.principal.cached.compilation.statements finalContext bodyOutcome after)
    (matched : BodyResult port.principal.sourceBody.resultType bodyOutcome outcome) :
    ∃ sourceSize, Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize invocation context
      environment before id outcome after := by
  rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
  · have occurrence : Occurrence invocation id (.unary operator operand) receipt.node.requirements :=
      ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, form, rfl, receipt.metadata.coercions⟩
    rw [Receipt.arguments, arguments] at trace
    cases trace with
    | cons operand tail =>
      cases tail
      exact ⟨_, .unaryMethod occurrence (unary_dispatch receipt port form) port.selected operand
        port.sourceAt.frame.roots selected port.sourceAt.extended allocated bodyTrace matched⟩
  · have occurrence : Occurrence invocation id (.binary left operator right) receipt.node.requirements :=
      ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, form, rfl, receipt.metadata.coercions⟩
    rw [Receipt.arguments, arguments] at trace
    cases trace with
    | cons first tail =>
      cases tail with
      | cons second tail =>
        cases tail
        exact ⟨_, .binaryMethod occurrence (binary_dispatch receipt port form) port.selected first
          (binary_continues receipt port form _) second port.sourceAt.frame.roots selected
          port.sourceAt.extended allocated bodyTrace matched⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceArguments

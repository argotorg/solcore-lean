import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConstructors
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinCallBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping

/-! Builtin applications have no nested body. Actual argument evaluation keeps
its original order, including a stage rejection in an argument prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBuiltin
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CompatibleExpressionPrimitives (Metadata)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

theorem builtin_application
    {program : Program} {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {function : Dynamic.BuiltinFunction}
    {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (applied : FunctionCallBody.Outcome program context callerEvidence invocationEvidence
      before (.builtin function) arguments outcome after) :
    Staging.Recursive.Applies program registry scope context before (.builtin function)
      arguments (embed outcome) after := by
  cases applied with
  | value applied =>
    cases applied with
    | builtin primitive => exact .builtin primitive
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | builtinArity mismatch => exact .builtinArity mismatch
    | builtinArgumentType arity mismatch => exact .builtinType arity mismatch

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {children : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep} {checked : SourceCoreCompatibleCatalog.Checked}


theorem builtin (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {function : BuiltinFunctionId}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .call callee ids (.builtinFunction function))
    (unique : NodeOccurrencesUnique invocation.source)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids types codes)
    (childLift : ∀ child, child < size → LiftsAt bridge context model registry invocation children child)
    (preservation : ∀ child, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation children faults child) :
    LiftsAt bridge context model registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨actualTypes, typing⟩ := ProtectedStateExpressionOperandTyping.operand_types unique metadata.found typed
  rw [form] at typing
  change ExpressionsHaveTypes invocation.source context ids actualTypes at typing
  cases SelectedCompilationStageLiftConstructors.tree_types sequence unique typing
  have occurrence : Staging.Recursive.Occurrence invocation expression (.call callee ids (.builtinFunction function)) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  cases RecursiveNamedBuiltinCallBounds.source_inv metadata form unique execution with
  | argumentsFault failed smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge
      size sequence unique typing childLift preservation environments heaps locals layout actualTyped
      initial admitted failed (Nat.le_of_lt smaller)
    cases adapted with
    | completed => exact ⟨_, _, .builtinArgumentsFault occurrence trace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .builtinArgumentsFault occurrence trace, .rejected origin call reason _⟩
  | apply evaluated applied smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge
      size sequence unique typing childLift preservation environments heaps locals layout actualTyped
      initial admitted evaluated (Nat.le_of_lt smaller)
    cases adapted with
    | completed => exact ⟨_, _, .builtinApplied occurrence trace (builtin_application applied), .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .builtinArgumentsFault occurrence trace, .rejected origin call reason _⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBuiltin

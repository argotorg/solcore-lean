import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping

/-! Primitive operators lift actual ordinary operands in evaluation order.
Short-circuiting retains its single evaluated operand. A second operand uses
the physical state recovered from the first completed staged prefix. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftOperators
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CompatibleExpressionPrimitives (Metadata)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

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

theorem unary (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id operand : ExpressionId} {node childNode : ExpressionNode}
    {lowered childCode : SourceCoreBasic.LoweredExpr} {operator : Syntax.UnaryOp}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .unary operator operand) (unique : NodeOccurrencesUnique invocation.source)
    (childFound : invocation.source.lookupExpression? operand = some childNode)
    (generated : children scope operand childCode)
    (childLift : ∀ child, child < size → LiftsAt bridge context model registry invocation children child) :
    LiftsAt bridge context model registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨types, operands⟩ := ProtectedStateExpressionOperandTyping.operand_types unique metadata.found typed
  have childTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operands
    (by rw [form]; change operand ∈ [operand]; simp) childFound
  have occurrence : Staging.Recursive.Occurrence invocation expression (.unary operator operand) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  cases RecursiveNamedExpressionSourceBounds.unary_inv metadata form unique execution with
  | value child applied smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller generated childFound
      childTyped environments heaps locals layout actualTyped initial admitted (.value child)
    cases adapted with
    | completed => exact ⟨_, _, .unary occurrence trace applied, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .unaryOperandFault occurrence trace, .rejected origin call reason _⟩
  | fault child smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller generated childFound
      childTyped environments heaps locals layout actualTyped initial admitted (.fault child)
    cases adapted with
    | completed => exact ⟨_, _, .unaryOperandFault occurrence trace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .unaryOperandFault occurrence trace, .rejected origin call reason _⟩
  | invalid child failed smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller generated childFound
      childTyped environments heaps locals layout actualTyped initial admitted (.value child)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .unaryOperandFault occurrence trace, .rejected origin call reason _⟩
    | completed =>
      cases failed with
      | primitive invalid => exact ⟨_, _, .unaryInvalid occurrence trace invalid, .completed⟩
      | requirement failed => cases failed
      | method _ selected _ => cases selected

theorem binary (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id left right : ExpressionId}
    {node leftNode rightNode : ExpressionNode}
    {lowered leftCode rightCode : SourceCoreBasic.LoweredExpr} {operator : Syntax.BinaryOp}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .binary left operator right) (unique : NodeOccurrencesUnique invocation.source)
    (leftFound : invocation.source.lookupExpression? left = some leftNode)
    (rightFound : invocation.source.lookupExpression? right = some rightNode)
    (leftGenerated : children scope left leftCode) (rightGenerated : children scope right rightCode)
    (childLift : ∀ child, child < size → LiftsAt bridge context model registry invocation children child)
    (preservation : ∀ child, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation children faults child) :
    LiftsAt bridge context model registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨types, operands⟩ := ProtectedStateExpressionOperandTyping.operand_types unique metadata.found typed
  have leftTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operands
    (by rw [form]; change left ∈ [left, right]; simp) leftFound
  have rightTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operands
    (by rw [form]; change right ∈ [left, right]; simp) rightFound
  have occurrence : Staging.Recursive.Occurrence invocation expression (.binary left operator right) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  cases RecursiveNamedExpressionSourceBounds.binary_inv metadata form unique execution with
  | leftFault child smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller leftGenerated leftFound
      leftTyped environments heaps locals layout actualTyped initial admitted (.fault child)
    cases adapted with
    | completed => exact ⟨_, _, .binaryLeftFault occurrence trace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .binaryLeftFault occurrence trace, .rejected origin call reason _⟩
  | leftInvalid child invalid smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller leftGenerated leftFound
      leftTyped environments heaps locals layout actualTyped initial admitted (.value child)
    cases adapted with
    | completed => exact ⟨_, _, .binaryLeftInvalid occurrence trace invalid, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .binaryLeftFault occurrence trace, .rejected origin call reason _⟩
  | short child circuit smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller leftGenerated leftFound
      leftTyped environments heaps locals layout actualTyped initial admitted (.value child)
    cases adapted with
    | completed => exact ⟨_, _, .binaryShortCircuit occurrence trace circuit, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .binaryLeftFault occurrence trace, .rejected origin call reason _⟩
  | rightFault first continues second firstSmaller secondSmaller =>
    obtain ⟨staged, reached, firstTrace, adapted⟩ := childLift _ firstSmaller leftGenerated leftFound
      leftTyped environments heaps locals layout actualTyped initial admitted (.value first)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .binaryLeftFault occurrence firstTrace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace firstTrace
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, _frame, heapMetadata, middleState, _related, post⟩ := preservation stagedSize
        leftGenerated leftFound leftTyped environments heaps locals layout actualTyped initial admitted measured
      obtain ⟨result, finalHeap, secondTrace, adapted⟩ := childLift _ secondSmaller rightGenerated rightFound rightTyped
        (environments.extend maps worlds) middleHeaps (locals.mono heapMetadata) layout
        (actualTyped.weaken worlds) middleState post.at_value.2 (.fault second)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .binaryRightFault occurrence firstTrace continues secondTrace, .rejected origin call reason _⟩
      | completed => exact ⟨_, _, .binaryRightFault occurrence firstTrace continues secondTrace, .completed⟩
  | value first continues second applied firstSmaller secondSmaller =>
    obtain ⟨staged, reached, firstTrace, adapted⟩ := childLift _ firstSmaller leftGenerated leftFound
      leftTyped environments heaps locals layout actualTyped initial admitted (.value first)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .binaryLeftFault occurrence firstTrace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace firstTrace
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, _frame, heapMetadata, middleState, _related, post⟩ := preservation stagedSize
        leftGenerated leftFound leftTyped environments heaps locals layout actualTyped initial admitted measured
      obtain ⟨result, finalHeap, secondTrace, adapted⟩ := childLift _ secondSmaller rightGenerated rightFound rightTyped
        (environments.extend maps worlds) middleHeaps (locals.mono heapMetadata) layout
        (actualTyped.weaken worlds) middleState post.at_value.2 (.value second)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .binaryRightFault occurrence firstTrace continues secondTrace, .rejected origin call reason _⟩
      | completed => exact ⟨_, _, .binary occurrence firstTrace continues secondTrace applied, .completed⟩
  | invalid first continues second failed firstSmaller secondSmaller =>
    obtain ⟨staged, reached, firstTrace, adapted⟩ := childLift _ firstSmaller leftGenerated leftFound
      leftTyped environments heaps locals layout actualTyped initial admitted (.value first)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .binaryLeftFault occurrence firstTrace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace firstTrace
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, _frame, heapMetadata, middleState, _related, post⟩ := preservation stagedSize
        leftGenerated leftFound leftTyped environments heaps locals layout actualTyped initial admitted measured
      obtain ⟨result, finalHeap, secondTrace, adapted⟩ := childLift _ secondSmaller rightGenerated rightFound rightTyped
        (environments.extend maps worlds) middleHeaps (locals.mono heapMetadata) layout
        (actualTyped.weaken worlds) middleState post.at_value.2 (.value second)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .binaryRightFault occurrence firstTrace continues secondTrace, .rejected origin call reason _⟩
      | completed =>
        cases failed with
        | primitive invalid => exact ⟨_, _, .binaryInvalid occurrence firstTrace continues secondTrace invalid, .completed⟩
        | requirement failed => cases failed
        | method _ selected _ => cases selected

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftOperators

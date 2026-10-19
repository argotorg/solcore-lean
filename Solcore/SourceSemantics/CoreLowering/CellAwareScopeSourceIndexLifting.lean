import Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeExpressionBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionSourceBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndexBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceIndexLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeSourceLiftBounds Staging.Recursive.Lifting
open CompatibleExpressionIndices
open CellAwareScopeIndexBounds (Point)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {values : SourceCoreCompatibleValues.Context}
  {scope : SourceCoreLocalCell.Scope} {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode}
  {layout : Core.OrderedMapping.Layout} {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
  {first second : SourceCoreBasic.LoweredExpr} {reason : Word}
  (header : Header values invocation.source id base node baseNode layout comparison first second)
  (keyFound : invocation.source.lookupExpression? key = some keyNode)
  (form : node.form = .index base key)

local notation "headCode" => SourceCoreBasic.LoweredExpr.mk layout.valueType
  (SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression reason)

include header keyFound form in
/-- Actual base and key outcomes lift in order. Completed prefixes supply the
physical caller state for the next child; stage rejection keeps its real heap. -/
theorem index (unique : NodeOccurrencesUnique invocation.source)
    (firstChild : children scope base first) (secondChild : children scope key second)
    (size : Nat)
    (childLift : ∀ childSize, childSize < size → LiftsAt bridge context model named registry invocation children childSize)
    (preservation : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation children faults childSize) :
    LiftsAt bridge context model named registry invocation (Point scope id headCode) size := by
  intro current child lowered point actualNode found typed
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨types, operands⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found typed
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operands
    (by rw [form]; change base ∈ [base, key]; simp) header.baseMetadata.found
  have keyTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operands
    (by rw [form]; change key ∈ [base, key]; simp) keyFound
  have occurrence : Staging.Recursive.Occurrence invocation child (.index base key) :=
    ⟨_, lookupExpression?_sound header.metadata.found, form, header.metadata.requirements, header.metadata.coercions⟩
  rcases (RecursiveNamedDataExpressionSourceBounds.index_inv header.metadata form unique trace).split with
    ⟨reason, childSize, rfl, failed, smaller⟩ |
    ⟨baseValue, middle, baseSize, baseTrace, baseSmaller, rest⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ := childLift childSize smaller firstChild header.baseMetadata.found baseTyped
      environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame (.fault failed)
    cases adapted with
    | completed => exact ⟨_, _, .indexBaseFault occurrence lifted, .completed⟩
    | rejected origin call why reached => exact ⟨_, _, .indexBaseFault occurrence lifted, .rejected origin call why _⟩
  · obtain ⟨staged, reached, liftedBase, adapted⟩ := childLift baseSize baseSmaller firstChild header.baseMetadata.found baseTyped
      environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame (.value baseTrace)
    cases adapted with
    | rejected origin call why reached => exact ⟨_, _, .indexBaseFault occurrence liftedBase, .rejected origin call why _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace liftedBase
      obtain ⟨_, middleStore, middleMap, middleWorld, _, _, middleHeaps,
        maps, worlds, frame, metadata, effect, reached, _, post⟩ := preservation stagedSize firstChild header.baseMetadata.found baseTyped
          environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame measured
      rcases rest with ⟨reason, keySize, rfl, failed, keySmaller⟩ | ⟨keyValue, keySize, keyTrace, keySmaller, terminal⟩
      · obtain ⟨staged, finalHeap, liftedKey, adaptedKey⟩ := childLift keySize keySmaller secondChild keyFound keyTyped
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
          reached post.at_value.2 (authority.transport effect) (physical.transport effect frame) owner ownerFrame (.fault failed)
        cases adaptedKey with
        | completed => exact ⟨_, _, .indexKeyFault occurrence liftedBase liftedKey, .completed⟩
        | rejected origin call why reached => exact ⟨_, _, .indexKeyFault occurrence liftedBase liftedKey, .rejected origin call why _⟩
      · obtain ⟨staged, finalHeap, liftedKey, adaptedKey⟩ := childLift keySize keySmaller secondChild keyFound keyTyped
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
          reached post.at_value.2 (authority.transport effect) (physical.transport effect frame) owner ownerFrame (.value keyTrace)
        cases adaptedKey with
        | rejected origin call why reached => exact ⟨_, _, .indexKeyFault occurrence liftedBase liftedKey, .rejected origin call why _⟩
        | completed =>
          exact ⟨_, _, .indexResult occurrence liftedBase liftedKey
            (CallableIndexedOwnedPreparedStagedIndexOutcomes.of_terminal terminal), .completed⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceIndexLifting

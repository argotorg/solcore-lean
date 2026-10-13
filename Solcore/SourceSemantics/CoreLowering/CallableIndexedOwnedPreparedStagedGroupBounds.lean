import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallTree

/-! A compiler group keeps the literal child code. Preservation uses the
strict Source child grade. Reflection uses the finite LiteralSites child
hypothesis at the same native grade, keeping the exact staged failure and
reached caller state. Semantic hypotheses are theorem arguments, never fields
of the static compiler receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CompatibleExpressionPrimitives (Metadata)
universe u

/-- The existing compiler grouping fields, including the SAME child code. -/
inductive Group (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (children : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | actual {id node inner innerNode lowered}
      (metadata : Metadata checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : children scope inner lowered) : Group checked source children scope id lowered

/-- Select the genuine used child from the original finite LiteralSites.
The original group head, child list, fuel and literal receipts are retained.
Use the actual node fields exposed by LiteralSites induction; the proof
index itself is not an inverse to an arbitrary external child list. -/
theorem of_literal_sites
    {calls : CompatibleExpressionCalls.CallHeads} {fuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {literals : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {id inner : ExpressionId}
    {node innerNode : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    {entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)}
    (metadata : Metadata values.checked source id node lowered.type)
    (form : node.form = .group inner)
    (innerFound : source.lookupExpression? inner = some innerNode)
    (sourceType : node.type = innerNode.type)
    (member : (inner, lowered) ∈ entries)
    (children : ∀ child code, (child, code) ∈ entries →
      CompatibleExpressionCalls.Tree calls fuel values source sourceContext solved reasonAt scope child code)
    (childSites : ∀ child code (entry : (child, code) ∈ entries),
      (children child code entry).LiteralSites literals) :
    Group values.checked source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls) (fuel := fuel)
        (values := values) (source := source) (context := sourceContext)
        (solved := solved) (reasonAt := reasonAt) literals) scope id lowered := by
  exact .actual metadata form innerFound sourceType
    ⟨children inner lowered member, childSites inner lowered member⟩

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

private theorem source_group_inv
    {id inner : ExpressionId} {node : ExpressionNode}
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .group inner)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context
      environment before id outcome after) :
    ∃ childSize, size = Staging.Recursive.Size.stepSize [childSize] ∧
      Staging.Recursive.Size.Expression program registry childSize invocation context
        environment before inner outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm requirements},
      Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .group inner := by
    intro actualForm requirements occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | atomicValue contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | atomicFault contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | group occurrence child =>
      cases ExpressionForm.group.inj (occurrence_form occurrence)
      exact ⟨_, rfl, child⟩
  | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _
  | applied occurrence _ _ _ _ _ _ => cases occurrence_form occurrence

private theorem child_typed
    {id inner : ExpressionId} {node innerNode : ExpressionNode} {type : Ty}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .group inner)
    (innerFound : invocation.source.lookupExpression? inner = some innerNode)
    (unique : NodeOccurrencesUnique invocation.source)
    (typed : ExpressionHasType invocation.source context id node.type) :
    ExpressionHasType invocation.source context inner innerNode.type := by
  obtain ⟨actualNode, found, _sourceType, child⟩ :=
    CompatibleExpressionProducts.group_source_types unique metadata.found form metadata.coercions typed
  have same := Option.some.inj (found.symm.trans innerFound)
  cases same
  exact child

/-- The Source group rule adds one genuine step above its executed child.
The child theorem carries either fault tag and the exact reached state. -/
theorem group_preserves
    (unique : NodeOccurrencesUnique invocation.source) (budget : Nat)
    (childMeaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation children faults budget) :
    ∀ size, size ≤ budget → CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation (Group checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  cases certified with
  | actual metadata form innerFound sourceType child =>
      have same := Option.some.inj (found.symm.trans metadata.found)
      cases same
      obtain ⟨childSize, sizeEq, childTrace⟩ := source_group_inv unique metadata.found form trace
      have smaller : childSize < budget := by
        rw [sizeEq] at within
        exact Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
        childMeaning childSize smaller child innerFound
          (child_typed metadata form innerFound unique typed)
          environments heaps locals agrees actualTyped initial admitted childTrace
      refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, ?_⟩
      · simpa only [sourceType] using represented
      · simpa only [sourceType] using post

/-- The native group is literally the child code. Its structural child IH
uses the SAME grade; this theorem requests no strict native inequality. -/
theorem group_reflects
    (unique : NodeOccurrencesUnique invocation.source) (size : Nat)
    (childMeaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsAt
      bridge context model registry invocation children faults size) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsAt
      bridge context model registry invocation (Group checked invocation.source children) faults size := by
  intro scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  cases certified with
  | actual metadata form innerFound sourceType child =>
      have same := Option.some.inj (found.symm.trans metadata.found)
      cases same
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
        childMeaning child innerFound (child_typed metadata form innerFound unique typed)
          environments heaps locals agrees actualTyped initial admitted completed
      have occurrence : Staging.Recursive.Occurrence invocation id (.group _) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome, after, finalMap, finalWorld,
        .group occurrence trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
        reached, related, ?_⟩
      · simpa only [sourceType] using represented
      · simpa only [sourceType] using post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds

import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForHeaderLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds SelectedCompilationStageForInitialBounds
open GenericLexicalStatements
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


private theorem restore_adapted {outer inner : SourceSemantics.Context}
    (environment : Dynamic.Environment) {plain : Dynamic.ControlOutcome} {staged : Staging.Recursive.BodyOutcome}
    {after reached : Dynamic.Heap}
    (adapted : BodyAdapted inner plain after inner staged reached) :
    BodyAdapted outer (Dynamic.restoreControl environment plain) after outer (staged.restore environment) reached := by
  cases adapted with
  | completed matched => cases matched <;> exact .completed (by constructor)
  | rejected origin call reason finalContext reached => exact .rejected origin call reason _ _

include bridge functions definitions registered producer acquire in
/-- The original absent allocation constructs the actual extended physical
state before the body suffix is lifted. -/
theorem absent {budget : Nat} {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {rest postItems : List ForItemForm} {test : ExpressionId} {statements : List StatementId}
    {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : compiled.compatible.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest invocation.source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest invocation.source scope binder payload))
    (same : annotation.original = allocation.expression)
    {administrative : Core.Context}
    (remaining : InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := nextContext) (scope := ((binder.id, payload) :: scope)) bridge functions condition rest test postItems statements budget) :
    InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.letDecl binder none :: rest) test postItems statements budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  obtain ⟨tailSize, location, bound, nextOutcome, strict, sameOutcome, allocated, tail⟩ :=
    SelectedCompilationStageForInitialInversion.absent mono extended trace
  subst outcome
  obtain ⟨_captured, _captures, _capturedTyped, _allocationEval, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, _allocatedRelated, nextAdmitted⟩ :=
    CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer
      mono extended ordinary projection allocation annotation same environments heaps locals agrees actualTyped
      reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
  obtain ⟨_, _, resultHeap, restTrace, restAdapted⟩ := remaining
    (Nat.le_trans (Nat.le_of_lt strict) within)
    ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      nextReference, nextRead, (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
      reached, conditioned, nextAdmitted⟩ tail
  exact ⟨_, _, resultHeap,
    CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_absent mono extended allocated restTrace, restore_adapted environment restAdapted⟩

include bridge functions definitions registered producer acquire in
/-- The initializer reaches its own heap first. Its real represented value
then initializes the original binder before the suffix executes. -/
theorem initialized {budget : Nat} {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {rest postItems : List ForItemForm} {test : ExpressionId} {statements : List StatementId}
    {binder : TypedBinder} {expression : ExpressionId}
    {expressionNode : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (sourceType : expressionNode.type = binder.scheme.body)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificates context scope expression lowered)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest invocation.source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest invocation.source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (children : ∀ childSize, childSize < budget →
      LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation (certificates context) faults childSize)
    {administrative : Core.Context}
    (remaining : InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := nextContext) (scope := ((binder.id, lowered.type) :: scope)) bridge functions condition rest test postItems statements budget) :
    InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.letDecl binder (some expression) :: rest) test postItems statements budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  rcases SelectedCompilationStageForInitialInversion.initialized mono extended trace with
    ⟨childSize, reason, strict, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, location, bound, nextOutcome, strict, tailStrict, sameOutcome, evaluated, allocated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.initializer_fault mono measured,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.initializer_fault mono measured,
        .rejected origin call reason _ reached⟩
  · subst outcome
    obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.initializer_fault mono measured,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨value, middleStore, middleMap, middleWorld, _evaluated, represented, middleHeaps,
          maps, worlds, framePreserved, metadata, middleState, _related, post⟩ :=
        preservation stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted measured
      cases represented with
      | value payload =>
        have frameRead := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        have stillUnmapped := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        obtain ⟨_captured, _captures, _capturedTyped, _allocationEval, nextEnvironments, nextHeaps, nextLocals,
            nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, nextState, _allocatedRelated, nextAdmitted⟩ :=
          CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer
            mono extended ordinary allocation annotation same (sourceType ▸ post.at_value.1) (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            reference frameRead allocated middleState ((acquire _ _ conditioned) middleState frameRead) post.at_value.2
        obtain ⟨_, _, resultHeap, restTrace, restAdapted⟩ := remaining
          (Nat.le_trans (Nat.le_of_lt tailStrict) within)
          ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            nextReference, nextRead, (allocationFrame contextLocation stillUnmapped (List.getElem?_eq_some_iff.mp frameRead).1).1,
            nextState, conditioned, nextAdmitted⟩ tail
        exact ⟨_, _, resultHeap,
          CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_initialized mono extended measured allocated restTrace,
          restore_adapted environment restAdapted⟩

variable {administrative : Core.Context}

include bridge functions condition in
/-- A completed expression supplies the real next physical state before the
suffix is lifted. A rejected expression stops at its own reached heap. -/
theorem discard {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest postItems : List ForItemForm} {test : ExpressionId} {statements : List StatementId}
    {expression : ExpressionId} {expressionNode : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificate scope expression lowered)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest test postItems statements budget) :
    InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.expression expression :: rest) test postItems statements budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  rcases SelectedCompilationStageForInitialInversion.discard trace with
    ⟨childSize, reason, strict, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, strict, tailStrict, evaluated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.expression_fault measured,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.expression_fault measured,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.expression_fault measured,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, framePreserved, metadata, middleState, _related, post⟩ :=
        preservation stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted measured
      have frameRead := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
      have stillUnmapped := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
      obtain ⟨_, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailStrict) within)
        ⟨_, _, _, environments.extend maps worlds, middleHeaps, locals.mono metadata, agrees,
          actualTyped.weaken worlds, reference, frameRead, stillUnmapped, middleState, conditioned, post.at_value.2⟩ tail
      exact ⟨_, result, finalHeap, CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_expression measured restTrace, restAdapted⟩

variable (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)

include bridge functions condition transport extension in
/-- Equal assignment lifts the RHS at the original target snapshot. The
existing real write producer supplies the next physical state for the suffix. -/
theorem assign {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest postItems : List ForItemForm} {test : ExpressionId} {statements : List StatementId}
    {assignment : AssignmentResolution} {rhs : ExpressionId} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment .equal rhs)
    (bare : assignment.target.projections = [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment .equal rhs)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest test postItems statements budget) :
    InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.assignValue assignment .equal rhs :: rest) test postItems statements budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨target, snapshot⟩ := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.target_snapshot
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
    (context := context) (scope := scope) (administrative := administrative)
    functions extension head bare environments heaps locals agrees
  rcases SelectedCompilationStageForInitialInversion.assign snapshot trace with
    ⟨childSize, reason, strict, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, updated, written, strict, tailStrict, evaluated, write, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment_fault snapshot measured,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment_fault snapshot measured,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment_fault snapshot measured,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
          _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
        CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_value
          (compiled := compiled) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
          (preservation stagedSize) snapshot measured write
      obtain ⟨_, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailStrict) within)
        ⟨_, _, _, environments.extend maps worlds, middleHeaps,
          locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, reference,
          ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
          (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
          middleState, conditioned, nextAdmitted⟩ tail
      exact ⟨_, result, finalHeap,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_assignment snapshot measured write restTrace, restAdapted⟩

include definitions registered transport extension in
/-- Empty initialization enters the same finite loop. Its post-header lifting
is built from the actual compiler tree, including all original allocations. -/
theorem done {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    (bindings : ProtectedStateTransition.Bindings callerProtocol)
    (marked : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame model)
    (markedAcquire : ∀ location native, condition location native →
      ProtectedStateTransition.OrdinaryAllocation.ReadyAt marked.toOrdinary location native)
    (children : ∀ context childSize, childSize < budget →
      LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ context childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {postItems : List ForItemForm}
    {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode postCode : Expr} {control : ControlContext}
    (found : invocation.source.lookupExpression? test = some node)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificates context scope test ⟨.bool, testCode⟩)
    (body : FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope false statements budget)
    (bodyPreservation : ∀ n, CallableIndexedOwnedAdmittedStagedConditionalHeads.FlowPreserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope false statements expected type loopCode n)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative
      type (TypedForHeader.Fallthrough type) context scope postItems postCode)
    (postShape : CallableIndexedOwnedPreparedStagedBranchingTree.ItemShape postItems)
    (postTyped : CallableIndexedOwnedPreparedStagedForItemsTyping.Facts invocation.source control context postItems) :
    InitializersLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (context := context) (scope := scope)
      bridge functions condition [] test postItems statements budget := by
  have postLift : ItemsLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (context := context) (scope := scope)
      bridge functions condition postItems budget :=
    SelectedCompilationStageForHeaderLifting.lifts bridge functions definitions registered marked.toOrdinary
      condition markedAcquire transport extension children preservation unique postTree postShape postTyped
  have postPreservation (n : Nat) : CallableIndexedOwnedAdmittedStagedForPostContracts.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope postItems expected type postCode n := by
    exact CallableIndexedOwnedAdmittedStagedForHeaderPreservation.preserves_at bridge bindings transport functions extension
      definitions registered marked condition markedAcquire (fun c m _ => preservation c m) unique postTree postShape postTyped
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  cases trace with
  | initializerFault initial => cases initial
  | loop initial loop =>
    cases initial
    obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageForLifting.for_ready
      bridge functions condition (children context) (preservation context) found typed generated body bodyPreservation
      postLift postPreservation (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
      ready loop
    obtain ⟨grade, measured⟩ := Staging.Recursive.Size.ForLoop.of_trace lifted
    exact ⟨_, _, _, .loop .empty measured, restore_adapted environment adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting

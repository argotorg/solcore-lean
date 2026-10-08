import Solcore.SourceSemantics.CoreLowering.ProtectedImperativeCatalogPayloadContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderAssignmentPayloadContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeControlBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForPreservation

/-! Original native children select the bounded reflected head and tail.
The same Match Tree supplies selected-child entry and catalog receipts.
Source costs are reconstructed independently, preserving the same lexical
exit context, typed hidden values and installed caller observations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalWhile (Scope ValuesContext FlowRep Restored restored restore_rep)
open TypedLexicalControl (LexicalResult selected_intro)
open CompatibleExpressionPrimitives (bool_fields)
open RecursiveNamedLoopContracts (ExecutesAt StatementOutcome)
namespace Control
variable {administrative : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (unique : NodeOccurrencesUnique source)
  {faults : FunctionCalls.FaultRep} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)
theorem block_reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → ReflectsAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadReflectsAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, innerTrace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    inner size bounded valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, restores, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.block_reflects_at_with_state (canonical := canonical) (functions := functions) (program := program) (evidence := evidence)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol (fun _ _ _ _ _ _ => True)) budget size found form ⟨trivial⟩
      ⟨sourceSize, innerContext, outcome, after, finalMap, finalWorld, innerTrace, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
        ⟨⟨trivial⟩, trivial⟩⟩
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, restores, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem block_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : ∀ child, child ≤ budget → ReflectsAt (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) false statements expected type code) :
    HeadReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type code := by
  apply block_reflects_at_with (functions := functions) (program := program) (evidence := evidence)
    (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
  all_goals assumption

include transport in
theorem sequence_reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadReflectsAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → ReflectsAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    ReflectsAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _⟩ :=
    Stateful.sequence_reflects_at_with (functions := functions) (program := program) (evidence := evidence)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (staticCondition := fun _ _ => True)
      validity budget size bounded found notTail
      (fun child childBound => Compatibility.legacy_head_reflects functions program evidence transport (first child childBound))
      (fun child childBound => Compatibility.legacy_reflects functions program evidence transport (remaining child childBound))
      valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

variable {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

include transport in
theorem sequence_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadReflectsAt (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (remaining : ∀ child, child ≤ budget → ReflectsAt (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) mode rest expected type body) :
    ReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  apply sequence_reflects_at_with (functions := functions) (program := program) (evidence := evidence)
    (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
  all_goals assumption

private theorem sequence_stopped_reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadReflectsAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    ReflectsAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _⟩ :=
    Stateful.sequence_stopped_reflects_at_with_state (canonical := canonical) (functions := functions) (program := program) (evidence := evidence)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol (fun _ _ _ _ _ _ => True)) validity budget size bounded found notTail environments locals ⟨trivial⟩
      (fun child childBound {_ _} headTrace => by
        obtain ⟨sourceSize, outcome, after, middleMap, middleWorld, sourceTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata⟩ :=
          first child childBound valid environments heaps locals agrees actualTyped reference read unmapped installed headTrace
        exact ⟨sourceSize, outcome, after, middleMap, middleWorld, sourceTrace, restores, represented, middleHeaps, maps, worlds, frame, metadata, ⟨⟨trivial⟩, trivial⟩⟩)
      stops evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

private theorem sequence_stopped_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {head body : Expr}
    (found : source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (first : ∀ child, child ≤ budget → HeadReflectsAt (administrative := administrative) (entry := entry) functions program evidence
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frameLayout) (globals := globals) child (scope := scope) id expected type head)
    (stops : ReachableStatementContinuations.StatementTerminates source id) :
    ReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context)
      (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type head body) := by
  apply sequence_stopped_reflects_at_with (functions := functions) (program := program) (evidence := evidence)
    (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
  all_goals assumption

include transport in
theorem conditional_reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → ReflectsAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → ReflectsAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadReflectsAtWith (validity := validity) (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults)  (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, restores, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.conditional_reflects_at_with (functions := functions) (program := program) (evidence := evidence)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (staticCondition := fun _ _ => True)
      validity budget size bounded (fun child childBound context valid => Compatibility.legacy_expression_reflects functions program evidence transport (expressionReflects child childBound context valid))
      found form conditionFound _conditionType conditionTree
      (fun child childBound => Compatibility.legacy_reflects functions program evidence transport (thenCorrect child childBound))
      (fun child childBound => Compatibility.legacy_reflects functions program evidence transport (elseCorrect child childBound))
      valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, restores, represented, finalHeaps, maps, worlds, frame, metadata⟩

include transport in
theorem conditional_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {scope : Scope} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody : List StatementId}
    {elseBody : Option (List StatementId)} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionFound : source.lookupExpression? condition = some conditionNode) (_conditionType : conditionNode.type = .bool)
    (conditionTree : expressions context scope condition ⟨.bool, conditionCode⟩)
    (thenCorrect : ∀ child, child ≤ budget → ReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false thenBody expected type thenCode)
    (elseCorrect : ∀ child, child ≤ budget → ReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      child (scope := scope) false (elseBody.getD []) expected type elseCode) :
    HeadReflectsAt (administrative := administrative) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals)
      size (scope := scope) id expected type (LocalLoop.conditional type conditionCode thenCode elseCode) := by
  apply conditional_reflects_at_with (functions := functions) (program := program) (evidence := evidence)
    (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
  all_goals assumption

end Control

open GenericImperativeFor (Tree Position)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
open TypedLexicalControl (allocate_absent allocate_initialized sequence_rename valid_extend)
namespace Stateful
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (producer : OrdinaryAllocation.Producer protocol layouts frame (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, conditionGate location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport protocol) (stateBindings : Bindings protocol)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (budget : Nat)
  {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  (assignments : ∀ context, validity context → ProtectedForHeader.Stateful.AssignmentReflectsAt protocol functions (registry := registry)
    program evidence source (certificates context) context administrative faults budget)
  (reflection : ∀ context, validity context → Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol
    (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size))
/-- Interpret one actual Header result and restore its selected final loop
witness through the original binder receipt. Empty headers keep the inclusive
native continuation grade. -/
theorem header_reflects_at_with_result (size : Nat) (bounded : size ≤ budget)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    {continuation : SourceSemantics.Context → Scope → Expr → Prop}
    (loopCorrect : ∀ {nextContext nextScope nextCode}, continuation nextContext nextScope nextCode →
      AtMost budget (fun child => ProtectedFor.Body.Stateful.LoopReflectsAtFor protocol conditionGate functions program evidence
        validity child (source := source) (context := nextContext) (registry := registry) (faults := faults)
        (frameLayout := frame) (globals := globals) (administrative := administrative)
        (scope := nextScope) condition post statements expected type nextCode))
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (result : ProtectedForHeader.Stateful.ResultAtFor protocol conditionGate validity size registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment
      ⟨scope, mapping, world, before, store, canonical⟩ initial items value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      TypedLexicalWhile.Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  cases result with
  | @continues initialSize remainingSize initialContext initialEnvironment initialized tail trace maps worlds frame metadata headerRelated returnReceipt remaining smaller =>
    obtain ⟨returnTo⟩ := returnReceipt
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, loop, represented, loopHeaps, loopMaps, loopWorlds, loopFrame, loopMetadata, loopTransition⟩ :=
      (loopCorrect tail.certificate) _ (Nat.le_trans smaller bounded) tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped tail.state tail.gate remaining
    obtain ⟨loopState, loopRelated⟩ := loopTransition
    refine ⟨SourceExecutionSize.stepSize [initialSize, sourceSize], Dynamic.restoreControl environment outcome, after, finalMap, finalWorld, ?_, restored environment outcome,
      restore_rep represented environment, loopHeaps, maps.trans loopMaps, worlds.trans loopWorlds,
      frame.trans loopFrame, metadata.trans loopMetadata,
      ⟨returnTo.restore loopState, protocol.trans headerRelated (protocol.trans loopRelated (returnTo.related loopState))⟩⟩
    cases loop with
    | control loop => exact .control (.forLoop (lookupStatement?_sound found) form trace loop)
    | fault loop => exact .fault (.forIteration (lookupStatement?_sound found) form trace loop)
  | fault trace same matched heaps maps worlds frame metadata transition =>
    subst value
    exact ⟨_, _, _, _, _, .fault (.forInitializer (lookupStatement?_sound found) form trace),
      (by intro next impossible; cases impossible), .fault matched, heaps, maps, worlds, frame, metadata, transition⟩

include definitions registered observations producer acquire stateTransport stateBindings assignments reflection extend solved in
theorem header_reflects_at_with (size : Nat) (bounded : size ≤ budget)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    {continuation : SourceSemantics.Context → Scope → Expr → Prop}
    (header : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type continuation context scope items code)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults header)
    (loopCorrect : ∀ {nextContext nextScope nextCode}, continuation nextContext nextScope nextCode →
      AtMost budget (fun child => ProtectedFor.Body.Stateful.LoopReflectsAtFor protocol conditionGate functions program evidence
        validity child (source := source) (context := nextContext) (registry := registry) (faults := faults)
        (frameLayout := frame) (globals := globals) (administrative := administrative)
        (scope := nextScope) condition post statements expected type nextCode)) :
    Control.Stateful.HeadReflectsAtWith protocol conditionGate (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults)  (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial guarded evaluated
  have result := ProtectedForHeader.Stateful.Tree.reflects_reachable_bounded_for (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
        (program := program) (evidence := evidence) (observations := observations)
        (protocol := protocol) (condition := conditionGate) (producer := producer) (acquire := acquire)
        (stateTransport := stateTransport) (stateBindings := stateBindings)
        validity extend budget assignments reflection header errors
    valid environments heaps locals agrees actualTyped reference read unmapped initial guarded evaluated bounded
  exact header_reflects_at_with_result (functions := functions) (program := program) (evidence := evidence)
    (protocol := protocol) (conditionGate := conditionGate) (validity := validity) (budget := budget)
    size bounded found form loopCorrect initial result

include definitions registered observations producer acquire stateTransport stateBindings assignments reflection extend solved in
theorem loop_reflects_at_with (size : Nat) (bounded : size ≤ budget)
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (correct : Below budget (fun child => ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol conditionGate (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults)  (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) child false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ProtectedFor.Body.Stateful.LoopReflectsAtFor protocol conditionGate (validity := validity) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults)  (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped initial gate evaluated
  have result := ProtectedFor.Body.Stateful.loop_reflects_bounded_for (protocol := protocol) (guard := conditionGate) (validity := validity) functions program evidence stateTransport budget (reflection _ valid)
    conditionFound conditionTree typed correct bodyCannotFault
    (by
      intro actualContext environment canonical actual ξ contextLocation location actualAgrees actualReference actualValid
        child small mapping world before store finalStore value state native realRead guarded continued execution
      exact ProtectedForHeader.Stateful.post_reflects_reachable_bounded_for (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
        (program := program) (evidence := evidence) (observations := observations)
        (protocol := protocol) (guard := conditionGate) (producer := producer) (acquire := acquire)
        (stateTransport := stateTransport) (stateBindings := stateBindings)
        validity extend budget assignments reflection postTree postErrors
        actualValid actualAgrees actualReference state realRead guarded continued execution (Nat.le_of_lt small))
  exact result size bounded valid environments heaps locals agrees actualTyped reference read unmapped initial gate evaluated



end Stateful

private theorem measure_result {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before : Dynamic.Heap} {mode : Bool} {statements : List StatementId}
    {P : SourceSemantics.Context → Dynamic.ControlOutcome → Dynamic.Heap → LocationMap → StoreTyping → Prop}
    (result : ∃ finalContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements finalContext outcome after ∧
      P finalContext outcome after finalMap finalWorld) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      P finalContext outcome after finalMap finalWorld := by
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, rest⟩ := result
  obtain ⟨sourceSize, trace⟩ := ExecutesAt.has_size trace
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, rest⟩

namespace Stateful.WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateImperativeCatalogReady
section CatalogSites
universe u v
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerSites : InitializerSites initializerFacts loopFacts source)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts headFacts exprFacts program evidence source)
  (assignmentSites : AssignmentSites headFacts assignmentFacts snapshotFacts source)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)
  (acquire : ∀ location native, conditionGate location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)
  (budget : Nat)
  (transfers : AllocationTransfers protocol readiness stateBindings source)
  (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
  (assignments : ∀ context, validity context → Assignment.AssignmentReflectsAt protocol readiness assignmentFacts functions
    (registry := registry) program evidence source (certificates context) context administrative faults budget)

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)


variable (reflection : ∀ context, validity context →
  Below budget (fun size => ExpressionReflectsAt protocol readiness program evidence
    (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
    (context := context) (source := source) (faults := faults) size))
include definitions registered stateTransport stateBindings producer acquire reflection observations extend sites transfers assignmentSites initializerSites snapshots in
theorem reflectsAt_match_with_eliminator
    (AP : GenericImperativeMatch.Structural.AssignmentPayload (values := values) (source := source) (certificates := certificates) (administrative := administrative) (definitions := ambient.definitions)) (UP : GenericImperativeMatch.Structural.UnaryPayload)
    (HP : GenericImperativeMatch.Structural.HeaderPayload (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative)) (MP : GenericImperativeMatch.Structural.MatchPayload)
    (R : ProtectedStateImperativeCatalogPayload.HeaderReceiptFamily)
    (headerAlgebra : ProtectedStateImperativeCatalogPayload.HeaderReceiptAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) R AP UP)
    (unaryErrors : ∀ {context scope assignment} {head : CompatibleBitNotStatements.Head context scope assignment}, UP head → head.Errors faults)
    (matchFields : ∀ compilation context, MP compilation context →
      SignatureCatalogWellFormed values.checked.signatures ∧ GenericImperativeMatch.Tree.MatchContextFields compilation context)
    (assignmentsWithPayload : ∀ context, validity context →
      ProtectedForHeader.Stateful.WithReady.AssignmentReflectsWithPayloadAt protocol readiness assignmentFacts functions
        (registry := registry) program evidence source (certificates context) context administrative faults budget (fun head => AP head))
    (_unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (headFor : ReflectingHeads protocol readiness conditionGate headFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity)
        (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget R))
    (loopFor : ProtectedStateImperativeCatalogPayload.ReflectingLoopsWithPayload protocol readiness conditionGate loopFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity)
        (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget R) HP)
    (eliminator : GenericImperativeMatch.Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative)
      AP UP HP MP context scope position expected type code) :
    ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) functions program evidence budget R
      (frame := frame) (globals := globals)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  have algebra : GenericImperativeMatch.Structural.BranchAlgebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) AP UP HP MP
      (ProtectedStateImperativeCatalogPayload.ReflectsAtWithReceipt protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) functions program evidence budget R (frame := frame) (globals := globals) (source := source) (administrative := administrative) (registry := registry) (faults := faults)) := by
    clear context scope position expected type code eliminator
    constructor
    · intro context scope mode statements expected type code syntaxTree body
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
        RecursiveNamedLexicalTreeBounds.Stateful.WithReady.reflects_at_for (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (transfers := transfers) (validity := validity) (extend := extend) functions definitions registered program evidence protocol conditionGate producer.toOrdinary stateBindings acquire size size (Nat.le_refl size)
          (fun child within context valid => reflection context valid child (Nat.lt_of_le_of_lt within bounded))
          body contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, FlowRep.of_lexical related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩
    · intro context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      apply measure_result
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationPost⟩ :=
        TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer.toOrdinary mono extended ordinary projected allocation annotation same
          environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append installed ((acquire _ _ guarded) installed read)
      obtain ⟨nextState, allocationRelated⟩ := allocationPost
      have nextReady := transfers.absent installed nextState initialReady extended Dynamic.Heap.Allocates.append preservation
      have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (by intro _ _ expression; simp [form])
        (.letUninitialized (lookupStatement?_sound found) form mono extended .append)
      obtain ⟨tailSize, smaller, continuation⟩ := evaluated.let_body allocationEval
      obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical, tailPost⟩ :=
        ih tailSize (Nat.lt_trans smaller bounded) (extend contextValid extended) tailFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          nextState guarded nextReady continuation
      obtain ⟨tailState, tailRelated, tailReady⟩ := tailPost
      let finalState := stateBindings.restore
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      have restoredRelated := protocol.trans tailRelated (stateBindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)
      have restoredReady := AllocationTransfers.restore_post (protocol := protocol) (readiness := readiness)
        (bindings := stateBindings) (source := source)
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (binder := binder) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) transfers extended tailState tailReady
      exact ⟨resultContext, outcome, after, finalMap, finalWorld,
        TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letUninitialized (lookupStatement?_sound found) form mono extended .append) trace.sound,
        represented, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata, lexical.bind extended, ⟨finalState, protocol.trans allocationRelated restoredRelated, restoredReady⟩⟩
    · intro context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      apply measure_result
      rw [sequence_rename] at evaluated
      obtain ⟨initialSize, middleStore, input, initialSmaller, initialEval⟩ := evaluated.bind_computation
      obtain ⟨initialSourceSize, sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata, expressionPost⟩ :=
        reflection _ contextValid initialSize (Nat.lt_trans initialSmaller bounded) initial initialFound
          (sites.expression (sites.head sourceFacts) (.initialized found form) initialFound) environments heaps locals agrees actualTyped installed initialReady initialEval
      cases represented with
      | fault matched =>
        cases initialTrace with | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LanguageResult.bind_failure _ initialEval.sound)
          exact ⟨context, _, middle, middleMap, middleWorld, TypedScopedStatements.head_fault mode rest (.letInitializer (lookupStatement?_sound found) form mono failed.sound),
            .fault matched, middleHeaps, maps, worlds, preservation, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, expressionPost⟩
      | value payload =>
        cases initialTrace with | value initialTrace =>
          obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionPost
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, allocationPost⟩ :=
            TypedLexicalControl.Stateful.allocate_initialized functions definitions registered protocol producer.toOrdinary mono extended ordinary allocation annotation same (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append middleState ((acquire _ _ guarded) middleState frameRead)
          obtain ⟨nextState, allocationRelated⟩ := allocationPost
          have nextReady := transfers.initialized middleState nextState middlePost.1 extended (sourceType ▸ middlePost.2) Dynamic.Heap.Allocates.append allocationFrame
          have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (by intro _ _ expression; simp [form])
            (.letInitialized (lookupStatement?_sound found) form initialTrace.sound mono extended .append)
          obtain ⟨branchSize, branchSmaller, branchEval⟩ := evaluated.bind_success initialEval.sound
          obtain ⟨tailSize, smaller, tailEval⟩ := branchEval.let_body allocationEval
          obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical, tailPost⟩ :=
            ih tailSize (Nat.lt_trans (Nat.lt_trans smaller branchSmaller) bounded) (extend contextValid extended) tailFacts
              nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
                (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                  (List.getElem?_eq_some_iff.mp frameRead).1).1
                nextState guarded nextReady tailEval
          obtain ⟨tailState, tailRelated, tailReady⟩ := tailPost
          let finalState := stateBindings.restore
            (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
          have restoredRelated := protocol.trans tailRelated (stateBindings.restore_related
            (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState)
          have restoredReady := AllocationTransfers.restore_post (protocol := protocol) (readiness := readiness)
            (bindings := stateBindings) (source := source)
            (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (binder := binder) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) transfers extended tailState tailReady
          exact ⟨resultContext, outcome, after, finalMap, finalWorld,
            TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letInitialized (lookupStatement?_sound found) form initialTrace.sound mono extended .append) trace.sound,
            related, finalHeaps,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata), lexical.bind extended, ⟨finalState, protocol.trans expressionRelated (protocol.trans allocationRelated restoredRelated), restoredReady⟩⟩
    · intro context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      apply measure_result
      rw [LoopRenaming.discard] at evaluated
      obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := evaluated.bind_computation
      obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, expressionPost⟩ :=
        reflection _ contextValid childSize (Nat.lt_trans smaller bounded) child expressionFound
          (sites.expression (sites.head sourceFacts) (.expression found form) expressionFound) environments heaps locals agrees actualTyped installed initialReady childEvaluation
      cases represented with
      | fault matched =>
        cases trace with | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalSequence.discard_failure _ childEvaluation.sound)
          exact ⟨context, _, middle, middleMap, middleWorld,
            head_fault mode rest (.expression (lookupStatement?_sound found) form failed.sound),
            .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
            ⟨_, _, _, .here, environments.extend firstMaps firstWorlds, locals.mono firstMetadata⟩, expressionPost⟩
      | @value _ coreValue payload =>
        cases trace with | value childTrace =>
          obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionPost
          have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (not_tail form guard)
            (.expression (lookupStatement?_sound found) form childTrace.sound)
          obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := evaluated.bind_success childEvaluation.sound
          obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, tail, related, finalHeaps, maps, worlds, preservation, metadata, lexical, tailPost⟩ :=
            ih tailSize (Nat.lt_trans tailSmaller bounded) contextValid tailFacts
              (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState guarded middlePost.1
              (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
          exact ⟨resultContext, outcome, after, finalMap, finalWorld,
            prepend (lookupStatement?_sound found) (not_tail form guard)
              (.expression (lookupStatement?_sound found) form childTrace.sound) tail.sound,
            related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans preservation, firstMetadata.trans metadata, lexical, Reached.continue (protocol := protocol) (readiness := readiness) expressionRelated tailPost⟩
    · intro context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH remainingIH
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      exact Control.Stateful.WithReady.sequence_reflects_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
        (fun child within => Control.Stateful.WithReady.block_reflects_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
          (frameLayout := frame) (globals := globals) size child within found form
          (fun child within => innerIH child (Nat.lt_of_le_of_lt within bounded)))
        (fun child within => remainingIH child (Nat.lt_of_le_of_lt within bounded))
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
    · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      exact Control.Stateful.WithReady.sequence_reflects_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
        (fun child within => Control.Stateful.WithReady.conditional_reflects_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
           (frameLayout := frame) (globals := globals) size child within
          (fun child within context valid => reflection context valid child (Nat.lt_of_le_of_lt within bounded))
          found form conditionFound conditionType conditionTree
          (fun child within => thenIH child (Nat.lt_of_le_of_lt within bounded))
          (fun child within => elseIH child (Nat.lt_of_le_of_lt within bounded)))
        (fun child within => remainingIH child (Nat.lt_of_le_of_lt within bounded))
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
    · intro context scope mode id node rest expected type found form
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      apply measure_result
      have nativeEval : Evaluates actual store ((LocalLoop.breaking type).rename ξ) (LocalLoop.breakingValue type) store := by
        simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates type actual store
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound nativeEval
      exact ⟨_, _, before, mapping, world,
        TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
          (.breakStmt (lookupStatement?_sound found) form) (.breaking environment),
        .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨_, _, _, .here, environments, locals⟩, ⟨installed, protocol.refl installed, initialReady⟩⟩
    · intro context scope mode id node rest expected type found form
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      apply measure_result
      have nativeEval : Evaluates actual store ((LocalLoop.continuing type).rename ξ) (LocalLoop.continuingValue type) store := by
        simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates type actual store
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound nativeEval
      exact ⟨_, _, before, mapping, world,
        TypedScopedStatements.terminal_intro _ _ (lookupStatement?_sound found) (by intro expression; simp [form])
          (.continueStmt (lookupStatement?_sound found) form) (.continuing environment),
        .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨_, _, _, .here, environments, locals⟩, ⟨installed, protocol.refl installed, initialReady⟩⟩
    · intro context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopIH restIH
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      exact Control.Stateful.WithReady.sequence_reflects_at_with (protocol := protocol) (staticCondition := conditionGate)
        (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
        (fun child within => headFor (.whileLoop found form conditionFound conditionType conditionTree loopTree nativeTyped loopIH)
          child (Nat.lt_of_le_of_lt within bounded))
        (fun child within => restIH child (Nat.lt_of_le_of_lt within bounded))
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
    · intro context scope mode id node assignment operator rhs rest expected type body found form head remaining ih headErrors
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      apply measure_result
      have assigned := assignmentsWithPayload _ contextValid head
        (assignmentSites.assignment (sites.head sourceFacts) found form)
        environments heaps locals agrees actualTyped installed initialReady headErrors
        evaluated (Nat.le_of_lt bounded)
      cases assigned with
      | @fault sourceSize reason token after finalMap finalWorld trace same matched finalHeaps maps worlds preservation metadata assignmentPost =>
        subst value
        exact ⟨context, .fault reason, after, finalMap, finalWorld,
            head_fault mode rest (.assignValue (lookupStatement?_sound found) form trace.sound), .fault matched,
            finalHeaps, maps, worlds, preservation, metadata,
            ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, assignmentPost⟩
      | @success sourceSize remainingSize updated middle written middleMap middleWorld slots trace middleHeaps maps worlds preservation metadata count typed assignmentPost smaller continuation =>
        obtain ⟨writeState, assignmentRelated, writeReady⟩ := assignmentPost
        have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (by intro _ _; simp [form])
          (.assignValue (lookupStatement?_sound found) form trace.sound)
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨tailSourceSize, resultContext, outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical, tailPost⟩ :=
          ih remainingSize (Nat.lt_trans smaller bounded) contextValid tailFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference frameRead
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 writeState guarded writeReady
            (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignValue (lookupStatement?_sound found) form trace.sound) tail.sound,
          represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, lexical, Reached.continue (protocol := protocol) (readiness := readiness) assignmentRelated tailPost⟩
    · intro context scope mode id node assignment rest expected type body found form head remaining ih headErrors
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      apply measure_result
      rcases head.reflects_sized functions program evidence observations
        environments heaps locals agrees actualTyped (unaryErrors headErrors) evaluated with
        ⟨sourceSize, reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, frame, metadata⟩ |
        ⟨sourceSize, updated, middle, written, middleMap, middleWorld, slots, remainingSize, trace, middleHeaps, maps, worlds, frame, metadata, count, typed, smaller, continuation⟩
      · exact ⟨context, .fault reason, after, finalMap, finalWorld,
          head_fault mode rest (.assignBitNot (lookupStatement?_sound found) form trace.sound), .fault matched,
          finalHeaps, maps, worlds, frame, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩,
          ⟨stateTransport.extend installed maps worlds frame metadata, stateTransport.related installed maps worlds frame metadata, readiness.fault_after installed _ (readiness.ready_fault initialReady) frame⟩⟩
      · let writtenState := stateTransport.extend installed maps worlds frame metadata
        have writtenReady := snapshots.ready installed writtenState initialReady contextValid
          (assignmentSites.snapshot (sites.head sourceFacts) found form) trace.sound locals frame
        have tailFacts := sites.tail (environment := environment) (before := before) sourceFacts found (by intro _ _; simp [form])
          (.assignBitNot (lookupStatement?_sound found) form trace.sound)
        obtain ⟨tailSourceSize, resultContext, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical, tailPost⟩ :=
          ih remainingSize (Nat.lt_trans smaller bounded) contextValid tailFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            writtenState guarded writtenReady
            (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignBitNot (lookupStatement?_sound found) form trace.sound) tailTrace.sound,
          represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical, Reached.continue (protocol := protocol) (readiness := readiness) (stateTransport.related installed maps worlds frame metadata) tailPost⟩
    · intro context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialIH restIH
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      exact Control.Stateful.WithReady.sequence_reflects_at_with (protocol := protocol) (staticCondition := conditionGate)
        (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
        (fun child within => headFor (.forLoop found form initialIH) child (Nat.lt_of_le_of_lt within bounded))
        (fun child within => restIH child (Nat.lt_of_le_of_lt within bounded))
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
    · intro context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason conditionFound conditionType conditionTree loopTree postTree nativeTyped loopIH postErrors
      intro initializerStatic
      have completed := And.intro (initializerSites.done initializerStatic)
        (loopFor (.mk conditionFound conditionType conditionTree loopTree postTree postErrors nativeTyped loopIH)
          (initializerSites.done initializerStatic))
      exact (headerAlgebra type _).nil completed
    · intro context nextContext scope binder rest body payload condition post statements expected type mono extended ordinary projected allocation annotation same remaining ih
      intro initializerStatic
      exact (headerAlgebra type _).uninitialized mono extended ordinary projected allocation annotation same (ih (initializerSites.absent initializerStatic extended))
    · intro context nextContext scope binder initializer initializerNode lowered body rest condition post statements expected type mono extended ordinary found sourceType child allocation annotation same remaining ih
      intro initializerStatic
      exact (headerAlgebra type _).initialized mono extended ordinary found sourceType child allocation annotation same (ih (initializerSites.initialized initializerStatic extended))
    · intro context scope expression expressionNode rest lowered body condition post statements expected type found child remaining ih
      intro initializerStatic
      exact (headerAlgebra type _).discard found child (ih (initializerSites.discard initializerStatic))
    · intro context scope assignment operator rhs rest body condition post statements expected type head remaining ih headErrors
      intro initializerStatic
      exact (headerAlgebra type _).assign head headErrors (ih (initializerSites.assignment initializerStatic))
    · intro context scope assignment rest body condition post statements expected type head remaining ih headErrors
      intro initializerStatic
      exact (headerAlgebra type _).bitNot head headErrors (ih (initializerSites.snapshot initializerStatic))
    · intro context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children remaining matchPayload childrenIH remainingIH
      obtain ⟨catalogValid, patternContext⟩ := matchFields compilation context matchPayload
      intro size bounded
      exact Control.Stateful.WithReady.sequence_reflects_at_with (protocol := protocol) (staticCondition := conditionGate)
        (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
        (fun child within => headFor (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions
          allocator requests receipt ordinary children catalogValid patternContext childrenIH) child (Nat.lt_of_le_of_lt within bounded))
        (fun child within => remainingIH child (Nat.lt_of_le_of_lt within bounded))
    · intro context scope mode id node statements rest expected type innerCode body exactUnique found form inner stops issued innerIH
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      exact Control.Stateful.WithReady.sequence_stopped_reflects_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
        (fun child within => Control.Stateful.WithReady.block_reflects_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
          (frameLayout := frame) (globals := globals) size child within found form
          (fun child within => innerIH child (Nat.lt_of_le_of_lt within bounded)))
        (GenericLexicalStatements.block_terminates exactUnique found form stops)
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
    · intro context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH
      intro size bounded contextValid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
      exact Control.Stateful.WithReady.sequence_stopped_reflects_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
        (fun child within => Control.Stateful.WithReady.conditional_reflects_at_with (protocol := protocol) (staticCondition := conditionGate) (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites) (validity := validity) (functions := functions) (program := program) (evidence := evidence)
           (frameLayout := frame) (globals := globals) size child within
          (fun child within context valid => reflection context valid child (Nat.lt_of_le_of_lt within bounded))
          found form conditionFound conditionType conditionTree
          (fun child within => thenIH child (Nat.lt_of_le_of_lt within bounded))
          (fun child within => elseIH child (Nat.lt_of_le_of_lt within bounded)))
        (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
        contextValid sourceFacts environments heaps locals agrees actualTyped reference read unmapped installed guarded initialReady evaluated
    · intro context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children stops issued matchPayload childrenIH
      obtain ⟨catalogValid, patternContext⟩ := matchFields compilation context matchPayload
      intro size bounded
      exact Control.Stateful.WithReady.sequence_stopped_reflects_at_with (protocol := protocol) (staticCondition := conditionGate)
        (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts) (sites := sites)
        (validity := validity) (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) size size (Nat.le_refl size) found (by intro expression; simp [form])
        (fun child within => headFor (.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions
          allocator requests receipt ordinary children catalogValid patternContext childrenIH) child (Nat.lt_of_le_of_lt within bounded))
        (ReachableMatchContinuations.DefaultStopped.terminates exactUnique stops)
  exact eliminator _ algebra

include definitions registered stateTransport stateBindings producer acquire reflection observations extend sites transfers assignmentSites initializerSites snapshots assignments in
theorem reflectsAt_match_with (diagnosticPolicy : AssignmentDiagnosticPolicy) (_unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (headFor : ReflectingHeads protocol readiness conditionGate headFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ReflectsAtWith protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) (diagnosticPolicy := diagnosticPolicy)
        (certificates := certificates) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget))
    (loopFor : ReflectingLoops protocol readiness conditionGate loopFacts functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (ReflectsAtWith protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) (diagnosticPolicy := diagnosticPolicy)
        (certificates := certificates) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults) functions program evidence budget) diagnosticPolicy)
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    ReflectsAtWith protocol readiness conditionGate facts loopFacts initializerFacts (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  exact reflectsAt_match_with_eliminator (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence) (protocol := protocol) (readiness := readiness)
    (conditionGate := conditionGate) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts)
    (loopFacts := loopFacts) (initializerFacts := initializerFacts) (assignmentFacts := assignmentFacts)
    (snapshotFacts := snapshotFacts) (producer := producer) (stateTransport := stateTransport)
    (stateBindings := stateBindings) (acquire := acquire) (validity := validity) (extend := extend)
    (budget := budget) (sites := sites) (assignmentSites := assignmentSites) (initializerSites := initializerSites)
    (transfers := transfers) (snapshots := snapshots) (observations := observations)
    (reflection := reflection)
    (fun head => head.ErrorsFor diagnosticPolicy registry faults) (fun head => head.Errors faults)
    (fun postTree => GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults postTree)
    (fun compilation context => SignatureCatalogWellFormed values.checked.signatures ∧ GenericImperativeMatch.Tree.MatchContextFields compilation context)
    (ProtectedStateImperativeCatalogPayload.LegacyHeaderReceipt (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
    (ProtectedStateImperativeCatalogPayload.legacy_header_algebra (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError) (values := values) (source := source) (certificates := certificates) (definitions := ambient.definitions) (administrative := administrative) diagnosticPolicy registry faults)
    (fun receipt => receipt) (fun _ _ receipt => receipt)
    (by
      intro context valid scope assignment operator rhs head sourceFacts mapping world environment canonical actual before store actualContext ξ environments heaps locals agrees typed installed ready receipt next output value finalStore size evaluated bounded
      exact assignments context valid head sourceFacts environments heaps locals agrees typed installed ready receipt.reachable evaluated bounded)
    _unique headFor
    (fun recipe => loopFor (recipe.to_legacy diagnosticPolicy))
    (GenericImperativeMatch.Structural.of_catalog_sites errors)

end CatalogSites
end Stateful.WithReady
namespace Stateful.WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateImperativeCatalogReady
section Compatibility
universe u v
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)
  (acquire : ∀ location native, conditionGate location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)
  (budget : Nat)

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)


variable (reflection : ∀ context, validity context →
  Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol
    (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source (certificates context) faults size))
include extension stateTransport reflection faithful observations in
theorem assignment_reflection_uniform (functionTypes : FunctionRuntimeViews functions) : ∀ context, validity context → ProtectedForHeader.Stateful.AssignmentReflectsAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget := by
    intro context valid scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
      environments heaps locals agrees typed state errors next output value finalStore child evaluated within
    exact ProtectedAssignmentHeads.Stateful.Head.reflects_reachable_bounded functions extension program evidence protocol stateTransport faithful observations
      head environments heaps locals agrees typed state budget (reflection context valid) functionTypes errors evaluated within
include definitions registered extension stateTransport stateBindings producer acquire reflection faithful observations extend runtimeOf solved in
theorem reflecting_heads_trivial (diagnosticPolicy : AssignmentDiagnosticPolicy) (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source) :
    ReflectingHeads protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ => True) functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults) (ReflectsAtWith protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget) := by
  have assignments := assignment_reflection_uniform (administrative := administrative) (protocol := protocol) (functions := functions) (program := program) (evidence := evidence)
    (extension := extension) (stateTransport := stateTransport) (faithful := faithful) (observations := observations) (reflection := reflection) (validity := validity) (budget := budget) functionTypes
  intro context scope id expected type code recipe size bounded
  apply Control.Stateful.WithReady.HeadReflectsAtWith.of_true (protocol := protocol) (condition := conditionGate)
    (functions := functions) (program := program) (evidence := evidence)
  cases recipe with
  | whileLoop found form conditionFound _conditionType conditionTree loopTree nativeTyped child =>
    intro valid
    exact ProtectedWhile.Body.Stateful.while_reflects_bounded_for (protocol := protocol) (guard := conditionGate)
      (validity := validity) (functions := functions) (program := program) (evidence := evidence) (transport := stateTransport)
      budget (reflection _ valid) found form conditionFound conditionTree nativeTyped
      (reflects_goal_forget_true (protocol := protocol) (conditionGate := conditionGate)
        (functions := functions) (program := program) (evidence := evidence) child)
      (fun executed => loopTree.control_not_fault unique executed) size (Nat.le_of_lt bounded) valid
  | forLoop found form child =>
    obtain ⟨header, errors⟩ := reflects_goal_forget_true (protocol := protocol) (conditionGate := conditionGate)
      (functions := functions) (program := program) (evidence := evidence) child
    exact Stateful.header_reflects_at_with (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (producer := producer.toOrdinary) (acquire := acquire) (stateTransport := stateTransport) (stateBindings := stateBindings)
      (validity := validity) (extend := extend) (budget := budget) (solved := solved)
      (assignments := assignments) (reflection := reflection)
      size (Nat.le_of_lt bounded) found form header errors.reachable (fun correct => correct)
  | matchWith found form scrutineeFound _scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary children catalogValid patternContext child =>
    rcases compilation with ⟨compiledValues, requirements, cells, nativeDefs⟩
    dsimp only at sameValues
    subst compiledValues
    intro contextValid
    exact CompatibleMatchRuntimeHead.Stateful.head_reflects_bounded onError allocator functions definitions registered extension receipt ordinary
      patternContext.signatures catalogValid scrutineeFound casesTyped defaultTyped
      (patternContext.ledger.symm.trans (runtimeOf context contextValid).ledger)
      budget size (Nat.le_of_lt bounded) protocol conditionGate producer stateBindings acquire validity
      (fun extended valid => ContextTransport.binders validity extend valid extended)
      (fun valid => runtimeOf context valid) (fun _ => reflection context contextValid)
      (fun request member childContext related childSize smaller _ =>
        (reflects_goal_forget_true (protocol := protocol) (conditionGate := conditionGate)
          (functions := functions) (program := program) (evidence := evidence) (child request member childContext related))
          childSize smaller (ContextTransport.scoped_context validity extend contextValid related))
      contextValid

include definitions registered extension stateTransport stateBindings producer acquire reflection faithful observations extend solved in
theorem reflecting_loops_trivial (diagnosticPolicy : AssignmentDiagnosticPolicy) (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source) :
    ReflectingLoops protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ _ => True) functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults) (ReflectsAtWith protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget) diagnosticPolicy := by
  have assignments := assignment_reflection_uniform (administrative := administrative) (protocol := protocol) (functions := functions) (program := program) (evidence := evidence)
    (extension := extension) (stateTransport := stateTransport) (faithful := faithful) (observations := observations) (reflection := reflection) (validity := validity) (budget := budget) functionTypes
  intro context scope condition post statements expected type code recipe _static size bounded
  cases recipe with
  | mk conditionFound _conditionType conditionTree loopTree postTree postErrors nativeTyped child =>
    apply loop_reflects_of_true (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (program := program) (evidence := evidence)
    exact Stateful.loop_reflects_at_with (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (producer := producer.toOrdinary) (acquire := acquire) (stateTransport := stateTransport) (stateBindings := stateBindings)
      (validity := validity) (extend := extend) (budget := budget) (solved := solved)
      (assignments := assignments) (reflection := reflection)
      size bounded conditionFound conditionTree nativeTyped postTree postErrors.reachable
      (reflects_goal_forget_true (protocol := protocol) (conditionGate := conditionGate)
        (functions := functions) (program := program) (evidence := evidence) child)
      (fun executed => loopTree.control_not_fault unique executed)

end Compatibility
end Stateful.WithReady


namespace Stateful
section CatalogSites
universe u v
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)
  (acquire : ∀ location native, conditionGate location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)
  (budget : Nat)

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)


variable (reflection : ∀ context, validity context →
  Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol
    (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source (certificates context) faults size))
include definitions registered extension stateTransport stateBindings producer acquire reflection faithful observations extend runtimeOf in
theorem reflectsAt_match_with (diagnosticPolicy : AssignmentDiagnosticPolicy) (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    ReflectsAtWith protocol conditionGate (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  have headFor : ProtectedStateImperativeCatalogReady.ReflectingHeads protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) conditionGate (fun _ _ _ => True) functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults) (WithReady.ReflectsAtWith protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget) := WithReady.reflecting_heads_trivial (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (program := program) (evidence := evidence)
    (definitions := definitions) (registered := registered) (extension := extension)
    (producer := producer) (stateTransport := stateTransport) (stateBindings := stateBindings) (acquire := acquire)
    (validity := validity) (extend := extend) (runtimeOf := runtimeOf) (solved := solved)
    (faithful := faithful) (observations := observations) (budget := budget) (reflection := reflection) diagnosticPolicy functionTypes unique
  have loopFor : ProtectedStateImperativeCatalogReady.ReflectingLoops protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) conditionGate (fun _ _ _ _ _ => True) functions program evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals) (onError := onError)
      (source := source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults) (WithReady.ReflectsAtWith protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget) diagnosticPolicy := WithReady.reflecting_loops_trivial (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (program := program) (evidence := evidence)
    (definitions := definitions) (registered := registered) (extension := extension)
    (producer := producer) (stateTransport := stateTransport) (stateBindings := stateBindings) (acquire := acquire)
    (validity := validity) (extend := extend) (solved := solved)
    (faithful := faithful) (observations := observations) (budget := budget) (reflection := reflection) diagnosticPolicy functionTypes unique
  have reflected := WithReady.assignment_reflection_uniform (protocol := protocol) (functions := functions) (program := program) (evidence := evidence)
    (administrative := administrative) (extension := extension) (stateTransport := stateTransport) (validity := validity)
    (faithful := faithful) (observations := observations) (budget := budget) (reflection := reflection) functionTypes
  apply ProtectedStateImperativeCatalogReady.reflects_goal_forget_true (protocol := protocol) (conditionGate := conditionGate)
    (functions := functions) (program := program) (evidence := evidence)
  exact WithReady.reflectsAt_match_with (protocol := protocol) (conditionGate := conditionGate)
    (functions := functions) (definitions := definitions) (registered := registered) (program := program) (evidence := evidence)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (loopFacts := fun _ _ _ _ _ => True) (initializerFacts := fun _ _ _ _ _ _ => True)
    (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program evidence source)
    (initializerSites := ProtectedStateImperativeCatalogReady.InitializerSites.trivial source)
    (assignmentSites := ProtectedStateImperativeCatalogReady.AssignmentSites.trivial source)
    (producer := producer) (stateTransport := stateTransport) (stateBindings := stateBindings) (acquire := acquire)
    (validity := validity) (extend := extend) (budget := budget) (observations := observations)
    (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial (protocol := protocol) stateBindings source)
    (snapshots := ProtectedForHeader.Stateful.WithReady.SnapshotTransfers.trivial protocol validity program evidence source)
    (assignments := fun context valid => ProtectedForHeader.Stateful.WithReady.assignment_reflection_trivial
      protocol functions program evidence source (certificates context) context administrative faults budget (reflected context valid))
    (reflection := fun context valid child within => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt.of_true
      (protocol := protocol) (program := program) (evidence := evidence) (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (certificate := certificates context) (reflection context valid child within))
    diagnosticPolicy unique headFor loopFor tree errors

end CatalogSites
end Stateful

section WithValidity
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (validity : SourceSemantics.Context → Prop)
  (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
    validity context → BinderExtends source.owner context binder next → validity next)
  (runtimeOf : ∀ context, validity context → CompatibleRuntimeContextValidity.Valid solved context evidence)
  (budget : Nat)
  (reflection : ∀ context, validity context →
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry))

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)


include definitions registered extension transport bindings reflection faithful observations extend solved in
set_option linter.unusedSectionVars false in
theorem header_reflects_at_with (size : Nat) (bounded : size ≤ budget) (functionTypes : FunctionRuntimeViews functions)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : ReflectingHeaderWith (validity := validity) (diagnosticPolicy := .reachable) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    Control.HeadReflectsAtWith (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults)  (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨header, errors⟩ := headers
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, preservation, metadata, _transition⟩ :=
    Stateful.header_reflects_at_with
      (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (conditionGate := fun _ _ => True)
      (producer := ForCompatibility.legacyProducer functions transport bindings)
      (acquire := fun location native _ => ProtectedStateTransition.OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
      (stateTransport := ProtectedStateTransition.Lexical.legacyTransport transport)
      (stateBindings := ForCompatibility.legacyBindings bindings)
      (validity := validity) (extend := extend) (budget := budget)
      (assignments := fun context valid => ForCompatibility.legacyAssignmentReflection functions extension program evidence transport faithful observations context budget
        (reflection context valid) functionTypes)
      (reflection := fun context valid child smaller => RecursiveNamedLexicalContracts.Stateful.legacy_expression_reflects
        functions program evidence transport (reflection context valid child smaller))
      size bounded found form header errors
      (fun old child within => ForCompatibility.legacyLoopReflects functions program evidence validity (old child within))
      valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, preservation, metadata⟩

include extension reflection transport bindings definitions registered faithful observations extend solved in
set_option linter.unusedSectionVars false in
theorem loop_reflects_at_with (size : Nat) (bounded : size ≤ budget) (functionTypes : FunctionRuntimeViews functions)
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (correct : Below budget (fun child => RecursiveNamedLoopContracts.ReflectsAtFor (validity := validity) (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults)  (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) child false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    RecursiveNamedForContracts.LoopReflectsAtFor (validity := validity) (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults)  (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata, transition⟩ :=
    Stateful.loop_reflects_at_with
      (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (conditionGate := fun _ _ => True)
      (producer := ForCompatibility.legacyProducer functions transport bindings)
      (acquire := fun location native _ => ProtectedStateTransition.OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
      (stateTransport := ProtectedStateTransition.Lexical.legacyTransport transport)
      (stateBindings := ForCompatibility.legacyBindings bindings)
      (validity := validity) (extend := extend) (budget := budget)
      (assignments := fun context valid => ForCompatibility.legacyAssignmentReflection functions extension program evidence transport faithful observations context budget
        (reflection context valid) functionTypes)
      (reflection := fun context valid child smaller => RecursiveNamedLexicalContracts.Stateful.legacy_expression_reflects
        functions program evidence transport (reflection context valid child smaller))
      size bounded conditionFound conditionTree typed postTree postErrors
      (fun child smaller => ProtectedStateTransition.Lexical.Gated.reflects_of_unguarded
        (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) functions program evidence
        (ProtectedStateTransition.Lexical.legacy_reflects functions program evidence transport (correct child smaller))) bodyCannotFault
      valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial evaluated
  obtain ⟨reached, _related⟩ := transition
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata, reached.down⟩

include definitions registered extension transport bindings reflection faithful observations extend runtimeOf in
theorem reflectsAt_match_with (diagnosticPolicy : AssignmentDiagnosticPolicy) (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    ReflectsAtWith (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  let stateBindings := ForCompatibility.legacyBindings bindings
  let producer := ProtectedStateTransition.MarkedAllocation.of_administrative
    (ProtectedStateTransition.Lexical.legacyProtocol entry)
    (ProtectedStateTransition.Lexical.legacyTransport transport) stateBindings layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions)
  have actual := Stateful.reflectsAt_match_with
    (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
    (program := program) (evidence := evidence) (faithful := faithful) (observations := observations)
    (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (conditionGate := fun _ _ => True)
    (producer := producer) (stateTransport := ProtectedStateTransition.Lexical.legacyTransport transport)
    (stateBindings := stateBindings) (acquire := fun _ _ _ => fun _ _ => True.intro)
    (validity := validity) (extend := extend) (runtimeOf := runtimeOf) (budget := budget)
    (reflection := fun context valid child within => ProtectedStateMatchBodyContracts.legacy_expression_reflects
      transport (reflection context valid child within))
    diagnosticPolicy functionTypes unique tree errors
  cases position with
  | statements mode statements =>
    intro size bounded
    exact CatalogCompatibility.reflects functions program evidence (actual size bounded)
  | initializers items condition post statements =>
    obtain ⟨header, errors⟩ := actual
    exact ⟨header.mapContinuation (fun actual child within =>
      CatalogCompatibility.loop_reflects functions program evidence (actual child within)),
      errors.mapContinuation (fun actual child within =>
        CatalogCompatibility.loop_reflects functions program evidence (actual child within))⟩

include definitions registered extension transport bindings reflection faithful observations extend runtimeOf in
theorem reflectsAt_for_with (diagnosticPolicy : AssignmentDiagnosticPolicy) (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    ReflectsAtWith (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source)  (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  exact reflectsAt_match_with (validity := validity) (extend := extend) (runtimeOf := runtimeOf) functions definitions registered extension program evidence transport bindings budget reflection faithful observations
    diagnosticPolicy functionTypes unique (GenericImperativeMatch.Tree.of_for tree) (GenericImperativeMatch.Tree.CatalogSites.of_for errors)

end WithValidity

section Ordinary
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}

variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (budget : Nat)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry))

variable {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code conditionCode postCode : Expr} {selfReason : Word}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

include definitions registered extension transport bindings reflection faithful observations in
theorem header_reflects_at (size : Nat) (bounded : size ≤ budget) (functionTypes : FunctionRuntimeViews functions)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : ReflectingHeaderFor (diagnosticPolicy := .reachable) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    Control.HeadReflectsAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      size (scope := scope) id expected type code := by
  apply header_reflects_at_with (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption


include extension reflection transport bindings definitions registered faithful observations in
theorem loop_reflects_at (size : Nat) (bounded : size ≤ budget) (functionTypes : FunctionRuntimeViews functions)
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : GenericForHeader.Tree.ReachableErrors registry faults postTree)
    (correct : Below budget (fun child => RecursiveNamedLoopContracts.ReflectsAt (entry := entry) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) child false statements expected type code))
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    RecursiveNamedForContracts.LoopReflectsAt (entry := entry) functions program evidence size (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frame) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  apply loop_reflects_at_with (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption


include definitions registered extension transport bindings reflection faithful observations in
theorem reflectsAt_match (diagnosticPolicy : AssignmentDiagnosticPolicy) (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults tree) :
    ReflectsAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  apply reflectsAt_match_with (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
    (runtimeOf := fun _ valid => CompatibleRuntimeContextValidity.of_ordinary valid)
  all_goals assumption


include definitions registered extension transport bindings reflection faithful observations in
theorem reflectsAt_for (diagnosticPolicy : AssignmentDiagnosticPolicy) (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {scope : Scope} {position : Position}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
      context scope position expected type code)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    ReflectsAtFor (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (entry := entry) functions program evidence budget (layouts := layouts) (owner := owner) (active := active)
      (frame := frame) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope position expected type code := by
  apply reflectsAt_for_with (validity := (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence))
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
    (runtimeOf := fun _ valid => CompatibleRuntimeContextValidity.of_ordinary valid)
  all_goals assumption

end Ordinary

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor

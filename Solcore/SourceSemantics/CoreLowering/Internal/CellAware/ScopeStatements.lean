import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeExpressions
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.CellAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFooter
import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary
import Solcore.SourceSemantics.Staging.RecursiveControlViews
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalHeads

/-!
# Cell-aware scopes: statement flows

Statement flows on the scope protocol: terminals, transfers, discards, blocks and conditionals, with their Source lifting.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeTerminalStatements
/-! Actual terminal statement composition over the same mixed heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeTerminalStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control ResultRepresents)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Terminal
variable {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Head invocation expression statements)
  (certified : certificate scope expression lowered)
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (sameLocation : owner.key.frameLocation = physical.location)

include head certified found sourceTyped environments heaps locals agrees typed admitted authority physical sameLocation in
/-- The real parent step gives a strict expression grade. The expression IH
runs once and the existing return helper preserves its exact endpoint. -/
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow
      bridge context model named registry invocation certificate faults budget)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have strict : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize)
      (children := [childSize]) (by simp)) within
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    children childSize strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
  refine ⟨head.trace child, ?_⟩
  cases represented with
  | value payload =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
      .returned payload, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  | fault matched =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
      .fault matched, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩

include head certified found sourceTyped environments heaps locals agrees typed admitted authority physical sameLocation in
/-- Native inversion uses the original sum bind and its strict child grade.
The Source result and parent grade are reconstructed from that one child IH. -/
theorem reflects (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow
      bridge context model named registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment
        before statements context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have original := completed
  rw [LoopRenaming.returnValue] at original
  change EvaluationSize size actual store
    (LanguageResult.bind (LocalLoop.controlType lowered.type) (lowered.expression.rename ξ)
      (LocalLoop.returned (.var 0))) value finalStore at original
  cases CallableIndirectCallBounds.bind_completed original within with
  | failed child strict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
    cases represented with
    | fault matched =>
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  | continued child remaining strict _remainingStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
    cases represented with
    | value payload =>
      have expected := LocalLoop.returnValue_success lowered.type child.sound
      obtain ⟨same, stores⟩ := evaluation_deterministic original.sound expected
      cases same
      subst stores
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .returned payload,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
end Terminal

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeTerminalStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceConditionalLifting
/-! Ordinary conditionals lift only the selected branch. The actual staged
condition supplies the physical state of that branch; a rejected condition
stops at its reached heap. Source Bool typing excludes the malformed ordinary
condition alternative using the genuine successful prefix receipt. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceConditionalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open CellAwareScopeSourceLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CompatibleExpressionPrimitives (Metadata)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {named : SourceCoreGeneralFunctions.Function}
  {receiving : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {children : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep} {checked : SourceCoreCompatibleCatalog.Checked}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

theorem conditional (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {lowered conditionCode thenCode elseCode : SourceCoreBasic.LoweredExpr}
    {condition thenId elseId : ExpressionId}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .conditional condition thenId elseId)
    (unique : NodeOccurrencesUnique invocation.source)
    (conditionNativeType : conditionCode.type = .bool)
    (conditionGenerated : children scope condition conditionCode)
    (thenGenerated : children scope thenId thenCode)
    (elseGenerated : children scope elseId elseCode)
    (childLift : ∀ child, child < size → LiftsAt bridge context model named registry invocation children child)
    (preservation : ∀ child, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation children faults child) :
    LiftsAt bridge context model named registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨conditionNode, thenNode, elseNode, conditionFound, thenFound, elseFound,
      _conditionType, _thenType, _elseType, conditionTyped, thenTyped, elseTyped⟩ :=
    CompatibleExpressionConditionals.conditional_source_types unique metadata.found form metadata.coercions typed
  have occurrence : Staging.Recursive.Occurrence invocation expression (.conditional condition thenId elseId) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  cases RecursiveNamedExpressionSourceBounds.conditional_inv metadata form unique execution with
  | fault failed smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller conditionGenerated conditionFound
      conditionTyped environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame (.fault failed)
    cases adapted with
    | completed => exact ⟨_, _, .conditionalFault occurrence trace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .conditionalFault occurrence trace, .rejected origin call reason _⟩
  | @branch childSize branchSize flag middle outcome after conditionTrace branchTrace smaller branchSmaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller conditionGenerated conditionFound
      conditionTyped environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame (.value conditionTrace)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .conditionalFault occurrence trace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, frame, heapMetadata, effect, middleState, _related, post⟩ := preservation stagedSize
        conditionGenerated conditionFound conditionTyped environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame measured
      cases flag with
      | false =>
        obtain ⟨result, finalHeap, branch, adapted⟩ := childLift _ branchSmaller elseGenerated elseFound elseTyped
          (environments.extend maps worlds) middleHeaps (locals.mono heapMetadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 (authority.transport effect) (physical.transport effect frame) owner ownerFrame branchTrace
        exact ⟨result, finalHeap, .conditional occurrence trace branch, adapted⟩
      | true =>
        obtain ⟨result, finalHeap, branch, adapted⟩ := childLift _ branchSmaller thenGenerated thenFound thenTyped
          (environments.extend maps worlds) middleHeaps (locals.mono heapMetadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 (authority.transport effect) (physical.transport effect frame) owner ownerFrame branchTrace
        exact ⟨result, finalHeap, .conditional occurrence trace branch, adapted⟩
  | invalid child invalid _runtimeType smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller conditionGenerated conditionFound
      conditionTyped environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame (.value child)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .conditionalFault occurrence trace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
      obtain ⟨_value, _store, _mapping, _world, _evaluated, represented, _heaps,
          _maps, _worlds, _frame, _metadata, _effect, _state, _related, _post⟩ := preservation stagedSize
        conditionGenerated conditionFound conditionTyped environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame measured
      cases represented with
      | value payload =>
        rw [conditionNativeType] at payload
        obtain ⟨flag, sourceEq, _coreEq⟩ := CompatibleExpressionPrimitives.bool_fields payload
        cases sourceEq
        exact False.elim (invalid trivial)

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceConditionalLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceSequenceLifting
/-! Lift ordered ordinary arguments at their actual intervening states.
A completed staged child is passed through the closed preservation family
before the next child is lifted. A rejection keeps that child's exact prefix
heap and does not require an argument-tail execution. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceSequenceLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open DataExpressionSequence
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open CallableIndexedOwnedSourceAdmission (Admission)
open CellAwareScopeSourceLiftBounds (LiftsAt)
open SelectedCompilationStageLiftSequence (SequenceLift)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

private def MemberTyping (ids : List ExpressionId) : Prop :=
  ∀ id, id ∈ ids → ∀ node, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type

private theorem values_members (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : ∀ size, size < budget → LiftsAt bridge context model named registry invocation certificate size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (execution : SourceExecutionSize.ExpressionsEvaluate program size context invocation.evidence
      invocation.source environment before ids sources after) (within : size ≤ budget) :
    SequenceLift program registry invocation context environment before ids (.ok sources) after := by
  induction tree generalizing size mapping world actual actualContext before store ξ sources after with
  | nil =>
    cases execution
    exact ⟨_, _, .nil, .completed⟩
  | single found generated =>
    cases execution with
    | cons head tail =>
      cases tail
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted authority physical owner ownerFrame (.value head)
      cases adapted with
      | completed => exact ⟨_, _, .cons trace .nil, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head rest =>
      have typed := sourceTyped _ (by simp) _ found
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found typed environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame (.value head)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
        obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
            maps, worlds, frame, metadata, effect, middleState, _related, post⟩ := preservation stagedSize
          generated found typed environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame measured
        obtain ⟨outcome, finalHeap, restTrace, restAdapted⟩ := ih
          (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 (authority.transport effect)
          (physical.transport effect frame) ownerFrame rest
          (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
        cases restAdapted with
        | completed => exact ⟨_, _, .cons trace restTrace, .completed⟩
        | rejected origin call reason reached =>
          exact ⟨_, _, .tailFault trace restTrace, .rejected origin call reason _⟩

theorem values (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique invocation.source)
    (sourceTyped : ExpressionsHaveTypes invocation.source context ids sourceTypes)
    (children : ∀ size, size < budget → LiftsAt bridge context model named registry invocation certificate size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (execution : SourceExecutionSize.ExpressionsEvaluate program size context invocation.evidence
      invocation.source environment before ids sources after) (within : size ≤ budget) :
    SequenceLift program registry invocation context environment before ids (.ok sources) after := by
  apply values_members bridge budget tree _ children preservation environments heaps locals layout actualTyped
    initial admitted authority physical owner ownerFrame execution within
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique sourceTyped member found

private theorem fault_members (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : ∀ size, size < budget → LiftsAt bridge context model named registry invocation certificate size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context invocation.evidence
      invocation.source environment before ids reason after) (within : size ≤ budget) :
    SequenceLift program registry invocation context environment before ids (.error reason) after := by
  induction tree generalizing size mapping world actual actualContext before store ξ reason after with
  | nil => cases execution
  | single found generated =>
    cases execution with
    | head failed =>
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted authority physical owner ownerFrame (.fault failed)
      cases adapted with
      | completed => exact ⟨_, _, .headFault trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
    | tail _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | head failed =>
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted authority physical owner ownerFrame (.fault failed)
      cases adapted with
      | completed => exact ⟨_, _, .headFault trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
    | tail head rest =>
      have typed := sourceTyped _ (by simp) _ found
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found typed environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame (.value head)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
        obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
            maps, worlds, frame, metadata, effect, middleState, _related, post⟩ := preservation stagedSize
          generated found typed environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame measured
        obtain ⟨outcome, finalHeap, restTrace, restAdapted⟩ := ih
          (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 (authority.transport effect)
          (physical.transport effect frame) ownerFrame rest
          (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
        cases restAdapted with
        | completed => exact ⟨_, _, .tailFault trace restTrace, .completed⟩
        | rejected origin call reason reached =>
          exact ⟨_, _, .tailFault trace restTrace, .rejected origin call reason _⟩

theorem fault (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique invocation.source)
    (sourceTyped : ExpressionsHaveTypes invocation.source context ids sourceTypes)
    (children : ∀ size, size < budget → LiftsAt bridge context model named registry invocation certificate size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context invocation.evidence
      invocation.source environment before ids reason after) (within : size ≤ budget) :
    SequenceLift program registry invocation context environment before ids (.error reason) after := by
  apply fault_members bridge budget tree _ children preservation environments heaps locals layout actualTyped
    initial admitted authority physical owner ownerFrame execution within
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique sourceTyped member found

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceSequenceLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds
/-! Common mixed-cell flow bounds retain ordinary control outcomes and exact
generalized descriptor effects. Scoped and function bodies differ only in their
mode; actual compiler trees close these internal recursive contracts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool) (statements : List StatementId)
  (expected : TypeSystem.Ty) (type : Ty) (code : Expr)

/-- Source and native grades remain independent. Every reached branch keeps
its exact mixed heap and restores the caller's lexical observations. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
        named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
      Staging.Recursive.Size.StatementsIn program registry mode size invocation context environment before
        statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename embedding) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached

/-- Actual native completion reconstructs the chosen Source branch and its
real allocations, failures and control transfers. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {mapping world actualContext environment canonical actual before store embedding value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
        named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
      ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    EvaluationSize size actual store (code.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program registry mode sourceSize invocation context environment before
        statements finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached

def PreservesAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → PreservesAt bridge context model named producer registry invocation faults administrative scope mode statements expected type code size

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt bridge context model named producer registry invocation faults administrative scope mode statements expected type code size

def ReflectsAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → ReflectsAt bridge context model named producer registry invocation faults administrative scope mode statements expected type code size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt bridge context model named producer registry invocation faults administrative scope mode statements expected type code size

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowFinish
/-! The genuine function footer consumes mixed imperative flow. Original
zero-loop-depth Source typing excludes escaped control; the actual result
projection validates Unit fallthrough. All reached heap effects survive. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowFinish
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  {named : SourceCoreGeneralFunctions.Function}

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {context : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
  {control : ControlContext} {staticFinal : SourceSemantics.Context} {facts : BodyFacts}

theorem preserves {budget : Nat}
    (bound : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope true statements expected type code budget)
    (sourceEq : invocation.source = source named)
    (sourceTyped : StatementsHaveType (source named) control context statements staticFinal facts)
    (depth : control.loopDepth = 0)
    (projection : whole.compatible.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    Staging.Recursive.Size.Statements program registry size invocation context environment before
      statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((CompatibleStatements.finish type code fellThrough escaped).rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected type faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  obtain ⟨flowValue, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    bound size within environments heaps locals agrees actualTyped runtime covers sameLedger typed
      initial admitted authority physical owner sameLocation ready trace
  have closed := Staging.Recursive.TypedControlBoundary.function
    (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
    (by simpa only [sourceEq] using sourceTyped) depth trace.sound
  have functionValue := Represents.to_function projection represented closed
  obtain ⟨value, complete, result⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates functionValue evaluated fellThrough escaped embedding
  exact ⟨value, finalStore, finalMap, finalWorld,
    by rwa [CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename], result,
    finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post⟩

theorem reflects {budget : Nat}
    (bound : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope true statements expected type code budget)
    (sourceEq : invocation.source = source named)
    (sourceTyped : StatementsHaveType (source named) control context statements staticFinal facts)
    (depth : control.loopDepth = 0)
    (projection : whole.compatible.checked.catalog.project expected = .ok type)
    (fellThrough escaped : Word) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (source named) →
    invocation.evidence.Covers context →
    context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements →
    ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world before store environment →
    ∀ physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {value finalStore}, EvaluationSize size actual store ((CompatibleStatements.finish type code fellThrough escaped).rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        statements finalContext outcome after ∧
      Staging.Recursive.BodyResult expected outcome (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected type faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected
          (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger typed initial admitted authority physical owner sameLocation ready
    value finalStore completed
  have original := completed
  rw [CallableIndexedOwnedAdmittedStagedLexicalFooter.finish_rename] at original
  obtain ⟨flowSize, flowValue, flowStore, flow, strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix original within
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    bound flowSize (Nat.le_of_lt strict) environments heaps locals agrees actualTyped runtime covers sameLedger typed
      initial admitted authority physical owner sameLocation ready flow
  have closed := Staging.Recursive.TypedControlBoundary.function
    (by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique)
    (by simpa only [sourceEq] using sourceTyped) depth trace.sound
  have functionValue := Represents.to_function projection represented closed
  obtain ⟨native, complete, result⟩ :=
    CallableIndexedOwnedAdmittedStagedLexicalFooter.evaluates functionValue flow.sound fellThrough escaped embedding
  obtain ⟨same, stores⟩ := evaluation_deterministic original.sound complete
  cases same
  subst stores
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented.body_result,
    result, finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post.to_function represented post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowFinish
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeTransferFlow
/-! Loop transfer leaves the actual mixed heap and all generalized descriptors intact.
The source occurrence authenticates the selected break or continue statement. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeTransferFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool)
  (expected : TypeSystem.Ty) (type : Ty)


variable {id : StatementId} {node : StatementNode} {rest : List StatementId}

theorem breaking_preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) (size : Nat) :
    CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.breaking type) size := by
  intro mapping world actualContext environment canonical actual before store embedding
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := Staging.Recursive.Size.StatementsIn.breaking_view unique found form trace
  exact ⟨_, store, mapping, world,
    LocalLoop.breaking_evaluates type actual store,
    .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

theorem breaking_reflects
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) (size : Nat) :
    CellAwareScopeFlowBounds.ReflectsAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.breaking type) size := by
  intro mapping world actualContext environment canonical actual before store embedding value finalStore
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready completed
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.breaking_evaluates type actual store)
  exact ⟨_, context, .breaking environment, before, mapping, world,
    .breaking (lookupStatement?_sound found) form,
    .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

variable {id : StatementId} {node : StatementNode} {rest : List StatementId}

theorem continuing_preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) (size : Nat) :
    CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.continuing type) size := by
  intro mapping world actualContext environment canonical actual before store embedding
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := Staging.Recursive.Size.StatementsIn.continuing_view unique found form trace
  exact ⟨_, store, mapping, world,
    LocalLoop.continuing_evaluates type actual store,
    .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

theorem continuing_reflects
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) (size : Nat) :
    CellAwareScopeFlowBounds.ReflectsAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.continuing type) size := by
  intro mapping world actualContext environment canonical actual before store embedding value finalStore
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready completed
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.continuing_evaluates type actual store)
  exact ⟨_, context, .continuing environment, before, mapping, world,
    .continuing (lookupStatement?_sound found) form,
    .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeTransferFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeEmptyFlow
/-! Empty scoped flow preserves the actual mixed heap and every descriptor.
Function fallthrough is admitted only at its real Unit result type. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeEmptyFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool)
  (expected : TypeSystem.Ty) (type : Ty)

theorem preserves (allowed : mode = false ∨ expected = .unit) (size : Nat) :
    CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope mode [] expected type (LocalLoop.fallthrough type) size := by
  intro mapping world actualContext environment canonical actual before store embedding
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  cases trace
  exact ⟨_, store, mapping, world,
    by simpa only [LoopRenaming.fallthrough] using LocalLoop.fallthrough_evaluates type actual store,
    .fallthrough environment allowed, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

theorem reflects (allowed : mode = false ∨ expected = .unit) (size : Nat) :
    CellAwareScopeFlowBounds.ReflectsAt bridge context model named producer registry invocation faults
      administrative scope mode [] expected type (LocalLoop.fallthrough type) size := by
  intro mapping world actualContext environment canonical actual before store embedding value finalStore
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready completed
  have expectedRun : Evaluates actual store ((LocalLoop.fallthrough type).rename embedding)
      (LocalLoop.fallthroughValue type) store := by
    simpa only [LoopRenaming.fallthrough] using LocalLoop.fallthrough_evaluates type actual store
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound expectedRun
  exact ⟨_, context, .fallthrough environment, before, mapping, world, .nil,
    .fallthrough environment allowed, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeEmptyFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeDiscardFlow
/-! Discarded expressions execute once before their actual remaining flow.
Their concrete descriptor effects compose at the reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeDiscardFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool)
  (expected : TypeSystem.Ty) (type : Ty)


variable {id : StatementId} {node : StatementNode} {expression : ExpressionId}
  {expressionNode : ExpressionNode} {semicolon : Bool} {rest : List StatementId}
  {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)
  (found : invocation.source.lookupStatement? id = some node)
  (form : node.form = .expression expression semicolon)
  (continuing : semicolon = true ∨ mode = false)
  (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
  (typed : ExpressionHasType invocation.source context expression expressionNode.type)
  (certified : certificate scope expression lowered)

include sourceEq unique found form continuing expressionFound typed certified in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context model named registry invocation certificate faults budget)
    (tail : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have suffix := ProtectedStateImperativeStatementSuffixTyping.discard
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  rw [LoopRenaming.discard]
  rcases CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion.child_and_tail unique
      (lookupStatement?_sound found) form continuing trace with
    ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
    ⟨childSize, tailSize, sourceValue, middle, sameSize, childTrace, remainingTrace⟩
  · subst finalContext
    subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      children childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
        initial admitted authority physical owner sameLocation childTrace
    cases represented with
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, post.at_fault_type⟩
  · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨value, middleStore, middleMap, middleWorld, first, represented,
        middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost⟩ :=
      children childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
        initial admitted authority physical owner sameLocation childTrace
    cases represented with
    | @value sourceValue coreValue payload =>
        obtain ⟨value, finalStore, finalMap, finalWorld, second, related,
            finalHeaps, maps, worlds, preservation, metadata, effect, reached, tailRelated, post⟩ :=
          tail tailSize tailWithin (environments.extend firstMaps firstWorlds)
            middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
            runtime covers sameLedger suffix middleState firstPost.at_value.2 (authority.transport firstEffect)
            (physical.transport firstEffect firstFrame) owner sameLocation ready remainingTrace
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
          related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
          firstMetadata.trans metadata, firstEffect.trans effect, reached, protocol.trans expressionRelated tailRelated, post⟩

include sourceEq unique found form continuing expressionFound typed certified in
theorem reflects (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context model named registry invocation certificate faults budget)
    (tail : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.ReflectsAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have suffix := ProtectedStateImperativeStatementSuffixTyping.discard
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  rw [LoopRenaming.discard] at completed
  obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
  obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, childTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost⟩ :=
    children childSize (Nat.lt_of_lt_of_le smaller within) certified expressionFound typed
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childEvaluation
  cases represented with
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalSequence.discard_failure _ childEvaluation.sound)
      exact ⟨Staging.Recursive.Size.stepSize [sourceSize], context, _, middle, middleMap, middleWorld,
        .expressionFault (lookupStatement?_sound found) form childTrace, .fault matched, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost.at_fault_type⟩
  | @value sourceValue coreValue payload =>
      obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := completed.bind_success childEvaluation.sound
      obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, related,
          finalHeaps, maps, worlds, preservation, metadata, effect, reached, tailRelated, post⟩ :=
        tail tailSize (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
          (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix agrees coreValue)
          (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) runtime covers sameLedger suffix
          middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
          owner sameLocation ready (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
      have combined : Staging.Recursive.Size.StatementsIn program registry mode
          (Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize]) invocation context environment before
          (id :: rest) finalContext outcome after := by
        cases semicolon with
        | true => exact .discard (lookupStatement?_sound found) form childTrace tailTrace
        | false =>
            have falseMode : mode = false := continuing.resolve_left (by decide)
            cases falseMode
            exact .discardValue (lookupStatement?_sound found) form childTrace tailTrace
      exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], finalContext, outcome, after, finalMap, finalWorld,
        combined, related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans preservation, firstMetadata.trans metadata, firstEffect.trans effect,
        reached, protocol.trans expressionRelated tailRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeDiscardFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeBlockFlow
/-! A scoped block restores its lexical observations while keeping the
actual mixed heap, every retained descriptor, and its original control outcome. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeBlockFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool)
  (expected : TypeSystem.Ty) (type : Ty)


variable {id : StatementId} {statement : StatementNode} {statements rest : List StatementId}
  {innerCode body : Expr}
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)
  (statementFound : invocation.source.lookupStatement? id = some statement)
  (form : statement.form = .block statements)

include sourceEq unique statementFound form in
theorem reflects (budget : Nat)
    (innerCorrect : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope false statements expected type innerCode budget)
    (remaining : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.ReflectsAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.sequence type innerCode body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, innerContext, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, headRelated, headPost⟩ :=
    innerCorrect _ (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
      initial admitted authority physical owner sameLocation ready headEval
  cases represented with
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .blockReturned (lookupStatement?_sound statementFound) form headTrace,
        .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | breaking innerEnvironment =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .blockBreaking (lookupStatement?_sound statementFound) form headTrace,
        .breaking environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | continuing innerEnvironment =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .blockContinuing (lookupStatement?_sound statementFound) form headTrace,
        .continuing environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .blockFault (lookupStatement?_sound statementFound) form headTrace,
        .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
      obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented,
          finalHeaps, maps, worlds, framePreserved, metadata, effect, reached, tailRelated, post⟩ :=
        remaining _ (Nat.le_trans (Nat.le_of_lt smaller) within)
          (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken firstWorlds)))) runtime covers sameLedger suffixTyped
          middleState headPost (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
          owner sameLocation ready
          (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
      exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
        .blockFallthrough (lookupStatement?_sound statementFound) form headTrace tailTrace,
        represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans framePreserved, firstMetadata.trans metadata, firstEffect.trans effect, reached,
        protocol.trans headRelated tailRelated, post⟩

include sourceEq unique statementFound form in
theorem preserves (budget : Nat)
    (innerCorrect : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope false statements expected type innerCode budget)
    (remaining : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.sequence type innerCode body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have finish {headSize : Nat} {innerContext : SourceSemantics.Context}
      {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Staging.Recursive.Size.StatementsIn program registry false headSize invocation context
        environment before statements innerContext headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type innerCode body).rename embedding) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults (headOutcome.restore environment) value ∧
        GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          protocol.Relates initial reached ∧ Post bridge context expected (headOutcome.restore environment) reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      innerCorrect _ bounded environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
        initial admitted authority physical owner sameLocation ready headTrace
    cases represented with
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | breaking innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .breaking environment, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | continuing innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .continuing environment, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion.block_and_tail unique statementFound form trace with
    ⟨innerSize, innerContext, sourceValue, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, innerContext, failure, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, innerContext, innerEnvironment, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, innerContext, innerEnvironment, sameSize, contextEq, outcomeEq, innerTrace⟩ |
    ⟨innerSize, tailSize, innerContext, innerEnvironment, middle, sameSize, innerTrace, tailTrace⟩
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish innerTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (sameSize ▸ Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · have headWithin : innerSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
        maps, worlds, preservation, metadata, firstEffect, middleState, headRelated, headPost⟩ :=
      innerCorrect _ headWithin environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
        initial admitted authority physical owner sameLocation ready innerTrace
    cases represented with
    | fallthrough innerEnvironment _ =>
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
            lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, tailRelated, post⟩ :=
          remaining _ tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) runtime covers sameLedger suffixTyped
            middleState headPost (authority.transport firstEffect) (physical.transport firstEffect preservation)
            owner sameLocation ready tailTrace
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
          metadata.trans lastMetadata, firstEffect.trans lastEffect, reached, protocol.trans headRelated tailRelated, post⟩
        rw [LoopRenaming.sequence]
        simp only [GenericExpressionMeaning.rename_prefix] at tailEval
        exact LocalLoop.sequence_fallthrough _ headEval tailEval

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeBlockFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeConditionalHead
/-! An actual Boolean condition chooses exactly one mixed scoped branch.
Both phases retain their concrete descriptor effects and reached admission. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeConditionalHead
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope)
  (expected : TypeSystem.Ty) (type : Ty)


open CallableIndexedOwnedAdmittedStagedConditionalHeads (Trace)
variable {test : ExpressionId} {node : ExpressionNode}
  {left : List StatementId} {right : Option (List StatementId)}
  {testCode leftCode rightCode : Expr} {certificate : GenericExpressionMeaning.Certificate}
  (booleans : ∀ {mapping world sourceValue nativeValue},
    model.Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
  (found : invocation.source.lookupExpression? test = some node)
  (nodeType : node.type = .bool)
  (typed : ExpressionHasType invocation.source context test node.type)
  (generated : certificate scope test ⟨.bool, testCode⟩)
  (leftTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context left)
  (rightTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context (right.getD []))

include booleans found nodeType typed generated leftTyped rightTyped in
theorem reflects (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context model named registry invocation certificate faults budget)
    (leftCorrect : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope false left expected type leftCode budget)
    (rightCorrect : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope false (right.getD []) expected type rightCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping world actualContext environment canonical actual before store embedding}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {value finalStore}
    (completed : EvaluationSize size actual store ((LocalLoop.conditional type testCode leftCode rightCode).rename embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Trace program registry invocation context environment before test left right sourceSize outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  rw [LoopRenaming.conditional] at completed
  obtain ⟨testSize, middleStore, input, smaller, testEval⟩ := completed.bind_computation
  obtain ⟨testSourceSize, testOutcome, middle, middleMap, middleWorld, testTrace, represented,
      middleHeaps, maps, worlds, preservation, metadata, firstEffect, middleState, expressionRelated, testPost⟩ :=
    children testSize (Nat.lt_of_lt_of_le smaller within) generated found typed
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation testEval
  cases represented with
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalControl.choose_failure _ testEval.sound)
      exact ⟨_, _, middle, middleMap, middleWorld, .fault testTrace, .fault matched, middleHeaps,
        maps, worlds, preservation, metadata, firstEffect, middleState, expressionRelated, testPost.at_fault_type⟩
  | value payload =>
      rw [nodeType] at payload
      obtain ⟨truth, sourceEq, coreEq⟩ := booleans payload
      subst sourceEq
      subst coreEq
      have selected : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
              administrative scope false (if truth then left else right.getD []) expected type
              (if truth then leftCode else rightCode) budget := by
        cases truth <;> assumption
      have branch : ∃ branchSize, branchSize < size ∧ EvaluationSize branchSize (.bool truth :: actual)
          middleStore (((if truth then leftCode else rightCode).rename embedding).weakenAt 0) value finalStore := by
        cases truth with
        | false => exact completed.choose_false testEval.sound
        | true => exact completed.choose_true testEval.sound
      obtain ⟨branchSize, branchSmaller, branchEval⟩ := branch
      obtain ⟨branchSourceSize, finalContext, outcome, after, finalMap, finalWorld, branchTrace,
          represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, branchRelated, post⟩ :=
        selected _ (Nat.le_trans (Nat.le_of_lt branchSmaller) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool truth))
          (.cons .bool (actualTyped.weaken worlds)) runtime covers sameLedger
          (by cases truth <;> assumption)
          middleState testPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect preservation)
          owner sameLocation ready
          (by simpa only [GenericExpressionMeaning.rename_prefix] using branchEval)
      exact ⟨_, outcome, after, finalMap, finalWorld, .branch testTrace branchTrace, represented, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, firstEffect.trans lastEffect,
        reached, protocol.trans expressionRelated branchRelated, post⟩

include booleans found nodeType typed generated leftTyped rightTyped in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context model named registry invocation certificate faults budget)
    (leftCorrect : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope false left expected type leftCode budget)
    (rightCorrect : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope false (right.getD []) expected type rightCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping world actualContext environment canonical actual before store embedding}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {outcome after}
    (trace : Trace program registry invocation context environment before test left right size outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.conditional type testCode leftCode rightCode).rename embedding) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  cases trace with
  | @fault testSize failure after testTrace =>
      have smaller : testSize < budget := Nat.lt_of_lt_of_le
        (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
        children testSize smaller generated found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation testTrace
      cases represented with
      | fault matched =>
          refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
            maps, worlds, preservation, metadata, effect, reached, related, post.at_fault_type⟩
          rw [LoopRenaming.conditional]
          exact LocalControl.choose_failure _ evaluated
  | @branch testSize branchSize truth middle innerContext outcome after testTrace branchTrace =>
      have smaller : testSize < budget := Nat.lt_of_lt_of_le
        (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, middleStore, middleMap, middleWorld, testEval, represented, middleHeaps,
          maps, worlds, preservation, metadata, firstEffect, middleState, expressionRelated, testPost⟩ :=
        children testSize smaller generated found typed environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation testTrace
      cases represented with
      | value payload =>
          rw [nodeType] at payload
          obtain ⟨actualTruth, sourceEq, coreEq⟩ := booleans payload
          cases sourceEq
          subst coreEq
          have selected : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
              administrative scope false (if truth then left else right.getD []) expected type
              (if truth then leftCode else rightCode) budget := by
            cases truth <;> assumption
          have branchWithin : branchSize ≤ budget := Nat.le_trans
            (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within
          obtain ⟨value, finalStore, finalMap, finalWorld, branchEval, represented, finalHeaps,
              lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, branchRelated, post⟩ :=
            selected _ branchWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool truth))
              (.cons .bool (actualTyped.weaken worlds)) runtime covers sameLedger
              (by cases truth <;> assumption)
              middleState testPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect preservation)
              owner sameLocation ready branchTrace
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
            maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, firstEffect.trans lastEffect,
            reached, protocol.trans expressionRelated branchRelated, post⟩
          rw [LoopRenaming.conditional]
          rw [GenericExpressionMeaning.rename_prefix] at branchEval
          cases truth with
          | false => exact LocalControl.choose_false _ testEval branchEval
          | true => exact LocalControl.choose_true _ testEval branchEval

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeConditionalHead
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeConditionalFlow
/-! An actual Boolean condition chooses exactly one mixed scoped branch.
Both phases retain their concrete descriptor effects and reached admission. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeConditionalFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope)
  (expected : TypeSystem.Ty) (type : Ty)


open CallableIndexedOwnedAdmittedStagedConditionalHeads (Trace)
variable {test : ExpressionId} {node : ExpressionNode}
  {left : List StatementId} {right : Option (List StatementId)}
  {testCode leftCode rightCode : Expr} {certificate : GenericExpressionMeaning.Certificate}
  (booleans : ∀ {mapping world sourceValue nativeValue},
    model.Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
  (found : invocation.source.lookupExpression? test = some node)
  (nodeType : node.type = .bool)
  (typed : ExpressionHasType invocation.source context test node.type)
  (generated : certificate scope test ⟨.bool, testCode⟩)

  {mode : Bool} {id : StatementId} {statement : StatementNode} {rest : List StatementId} {body : Expr}
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)
  (statementFound : invocation.source.lookupStatement? id = some statement)
  (form : statement.form = .ifThen test left right)


include sourceEq unique statementFound form booleans found nodeType typed generated in
theorem reflects (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context model named registry invocation certificate faults budget)
    (leftCorrect : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope false left expected type leftCode budget)
    (rightCorrect : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope false (right.getD []) expected type rightCode budget)
    (remaining : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.ReflectsAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (LocalLoop.sequence type (LocalLoop.conditional type testCode leftCode rightCode) body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, headRelated, headPost⟩ :=
    CellAwareScopeConditionalHead.reflects bridge context model named producer registry invocation faults
      administrative scope expected type booleans found nodeType typed generated leftTyped rightTyped
      budget children leftCorrect rightCorrect (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped runtime covers sameLedger
      initial admitted authority physical owner sameLocation ready headEval
  cases represented with
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      cases headTrace with
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifReturned (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
  | breaking innerEnvironment =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      cases headTrace with
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifBreaking (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .breaking environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
  | continuing innerEnvironment =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_transfer _ headEval.sound)
      cases headTrace with
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifContinuing (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .continuing environment, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      cases headTrace with
      | fault testTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifConditionFault (lookupStatement?_sound statementFound) form testTrace,
            .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
      | branch testTrace branchTrace =>
          exact ⟨_, context, _, middle, middleMap, middleWorld,
            .ifFault (lookupStatement?_sound statementFound) form testTrace branchTrace,
            .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
            middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      cases headTrace with
      | @branch testSize branchSize truth tested innerContext outcome after testTrace branchTrace =>
        obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
        obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented,
            finalHeaps, maps, worlds, framePreserved, metadata, effect, reached, tailRelated, post⟩ :=
          remaining _ (Nat.le_trans (Nat.le_of_lt smaller) within)
            (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken firstWorlds)))) runtime covers sameLedger suffixTyped
            middleState headPost (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
            owner sameLocation ready
            (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
        exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
          .ifFallthrough (lookupStatement?_sound statementFound) form testTrace branchTrace tailTrace,
          represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
          firstFrame.trans framePreserved, firstMetadata.trans metadata, firstEffect.trans effect, reached,
          protocol.trans headRelated tailRelated, post⟩

include sourceEq unique statementFound form booleans found nodeType typed generated in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context model named registry invocation certificate faults budget)
    (leftCorrect : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope false left expected type leftCode budget)
    (rightCorrect : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope false (right.getD []) expected type rightCode budget)
    (remaining : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) expected type
      (LocalLoop.sequence type (LocalLoop.conditional type testCode leftCode rightCode) body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false (sourceEq ▸ unique)
    (ProtectedStateImperativeTypedSourceSites.head sourceTyped) (sourceEq ▸ statementFound) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have finish {headSize : Nat} {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Trace program registry invocation context environment before test left right headSize headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type (LocalLoop.conditional type testCode leftCode rightCode) body).rename embedding) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults (headOutcome.restore environment) value ∧
        GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
          mapping world before store finalMap finalWorld after finalStore ∧
        ∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          protocol.Relates initial reached ∧ Post bridge context expected (headOutcome.restore environment) reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      CellAwareScopeConditionalHead.preserves bridge context model named producer registry invocation faults
        administrative scope expected type booleans found nodeType typed generated leftTyped rightTyped
        budget children leftCorrect rightCorrect bounded environments heaps locals agrees actualTyped runtime covers sameLedger
        initial admitted authority physical owner sameLocation ready headTrace
    cases represented with
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | breaking innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .breaking environment, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | continuing innerEnvironment =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .continuing environment, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_transfer _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion.children unique statementFound form trace with
    ⟨testSize, failure, sameSize, contextEq, outcomeEq, testTrace⟩ |
    ⟨testSize, branchSize, truth, sourceValue, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, truth, failure, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, truth, innerEnvironment, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, truth, innerEnvironment, middle, innerContext, sameSize, contextEq, outcomeEq, testTrace, branchTrace⟩ |
    ⟨testSize, branchSize, tailSize, truth, middle, branchHeap, innerContext, innerEnvironment, sameSize, testTrace, branchTrace, tailTrace⟩
  · subst outcome
    exact finish (.fault testTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.branch testTrace branchTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · have headWithin : Staging.Recursive.Size.stepSize [testSize, branchSize] ≤ budget := by
      rw [sameSize] at within
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within ⊢
      omega
    obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
        maps, worlds, preservation, metadata, firstEffect, middleState, headRelated, headPost⟩ :=
      CellAwareScopeConditionalHead.preserves bridge context model named producer registry invocation faults
        administrative scope expected type booleans found nodeType typed generated leftTyped rightTyped
        budget children leftCorrect rightCorrect headWithin environments heaps locals agrees actualTyped runtime covers sameLedger
        initial admitted authority physical owner sameLocation ready (.branch testTrace branchTrace)
    cases represented with
    | fallthrough innerEnvironment _ =>
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
            lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, tailRelated, post⟩ :=
          remaining _ tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) runtime covers sameLedger suffixTyped
            middleState headPost (authority.transport firstEffect) (physical.transport firstEffect preservation)
            owner sameLocation ready tailTrace
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
          metadata.trans lastMetadata, firstEffect.trans lastEffect, reached, protocol.trans headRelated tailRelated, post⟩
        rw [LoopRenaming.sequence]
        simp only [GenericExpressionMeaning.rename_prefix] at tailEval
        exact LocalLoop.sequence_fallthrough _ headEval tailEval

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeConditionalFlow
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeTerminalFlow
/-! Actual terminal statement composition over the same mixed heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeTerminalFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedScopedTerminalStatements (Head control ResultRepresents)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Terminal
variable {mode : Bool} {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Head invocation expression mode statements)
  (certified : certificate scope expression lowered)
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (sameLocation : owner.key.frameLocation = physical.location)

include head certified found sourceTyped environments heaps locals agrees typed admitted authority physical sameLocation in
/-- The real parent step gives a strict expression grade. The expression IH
runs once and the existing return helper preserves its exact endpoint. -/
private theorem preserves_child (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow
      bridge context model named registry invocation certificate faults budget)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.StatementsIn program registry mode (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have strict : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize)
      (children := [childSize]) (by simp)) within
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    children childSize strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
  refine ⟨head.trace child, ?_⟩
  cases represented with
  | value payload =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
      .returned payload, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  | fault matched =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
      .fault matched, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩

include head certified found sourceTyped environments heaps locals agrees typed admitted authority physical sameLocation in
/-- Native inversion uses the original sum bind and its strict child grade.
The Source result and parent grade are reconstructed from that one child IH. -/
private theorem reflects_child (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow
      bridge context model named registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program registry mode sourceSize invocation context environment
        before statements context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have original := completed
  rw [LoopRenaming.returnValue] at original
  change EvaluationSize size actual store
    (LanguageResult.bind (LocalLoop.controlType lowered.type) (lowered.expression.rename ξ)
      (LocalLoop.returned (.var 0))) value finalStore at original
  cases CallableIndirectCallBounds.bind_completed original within with
  | failed child strict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
    cases represented with
    | fault matched =>
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  | continued child remaining strict _remainingStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
    cases represented with
    | value payload =>
      have expected := LocalLoop.returnValue_success lowered.type child.sound
      obtain ⟨same, stores⟩ := evaluation_deterministic original.sound expected
      cases same
      subst stores
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .returned payload,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
end Terminal

section Bounds
variable {mode : Bool} {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {administrative : Core.Context}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))

theorem preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (head : Head invocation expression mode statements)
    (found : invocation.source.lookupExpression? expression = some node)
    (sourceTyped : ExpressionHasType invocation.source context expression node.type)
    (certified : certificate scope expression lowered)
    (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context model named registry invocation certificate faults budget) :
    CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope mode statements node.type lowered.type
      (LocalLoop.returnValue lowered.type lowered.expression) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees typed _runtime _covers _ledger _sourceSites initial admitted authority physical owner sameLocation _ready
    finalContext bodyOutcome after trace
  obtain ⟨childSize,outcome,rfl,rfl,rfl,child⟩ :=
    CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion.child_of_body unique head trace
  obtain ⟨_trace,value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,
      frame,metadata,effect,reached,related,post⟩ :=
    preserves_child bridge head certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation
      budget children child within
  cases represented with
  | returned payload => exact ⟨_,finalStore,finalMap,finalWorld,evaluated,.returned payload,
      finalHeaps,maps,worlds,frame,metadata,effect,reached,related,post⟩
  | fault matched => exact ⟨_,finalStore,finalMap,finalWorld,evaluated,.fault matched,
      finalHeaps,maps,worlds,frame,metadata,effect,reached,related,post⟩

theorem reflects
    (head : Head invocation expression mode statements)
    (found : invocation.source.lookupExpression? expression = some node)
    (sourceTyped : ExpressionHasType invocation.source context expression node.type)
    (certified : certificate scope expression lowered)
    (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context model named registry invocation certificate faults budget) :
    CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope mode statements node.type lowered.type
      (LocalLoop.returnValue lowered.type lowered.expression) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees typed _runtime _covers _ledger _sourceSites initial admitted authority physical owner sameLocation _ready completed
  obtain ⟨sourceSize,outcome,after,finalMap,finalWorld,trace,represented,finalHeaps,maps,worlds,
      frame,metadata,effect,reached,related,post⟩ :=
    reflects_child bridge head certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation
      budget children completed within
  cases represented with
  | returned payload => exact ⟨sourceSize,context,_,after,finalMap,finalWorld,trace,.returned payload,
      finalHeaps,maps,worlds,frame,metadata,effect,reached,related,post⟩
  | fault matched => exact ⟨sourceSize,context,_,after,finalMap,finalWorld,trace,.fault matched,
      finalHeaps,maps,worlds,frame,metadata,effect,reached,related,post⟩
end Bounds

section Unit
variable {mode : Bool} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {id : StatementId} {node : StatementNode} {rest : List StatementId}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (unitValue : ∀ mapping world, model.Represents mapping world .unit .unit .unit .unit)
  (found : invocation.source.lookupStatement? id = some node)
  (form : node.form = .returnStmt none)

include unitValue found form in
theorem unit_preserves (unique : NodeOccurrencesUnique invocation.source) (size : Nat) :
    CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) .unit .unit (LocalLoop.returned .unit) size := by
  intro mapping world actualContext environment canonical actual before store embedding
    _environments heaps _locals _agrees _typed _runtime _covers _ledger _sourceSites initial admitted
    _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl,rfl,rfl⟩ := CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.return_unit unique found form trace
  refine ⟨_,store,mapping,world,?_,.returned (unitValue mapping world),heaps,.refl _,.refl _,
    .refl _ _,.refl _,.refl _ _ _ _,initial,callerProtocol.refl initial,?_⟩
  · simpa only [LoopRenaming.returned, Expr.rename] using
      (LocalLoop.returned_evaluates (show Evaluates actual store .unit .unit store from .unit))
  · exact ⟨admitted.rows,by intro source same; cases same; exact ⟨.unit,admitted.heap⟩⟩

include unitValue found form in
theorem unit_reflects (size : Nat) :
    CellAwareScopeFlowBounds.ReflectsAt bridge context model named producer registry invocation faults
      administrative scope mode (id :: rest) .unit .unit (LocalLoop.returned .unit) size := by
  intro mapping world actualContext environment canonical actual before store embedding value finalStore
    _environments heaps _locals _agrees _typed _runtime _covers _ledger _sourceSites initial admitted
    _authority _physical _owner _sameLocation _ready completed
  have evaluated : Evaluates actual store ((LocalLoop.returned .unit).rename embedding)
      (LocalLoop.returnedValue .unit) store := by
    simpa only [LoopRenaming.returned, Expr.rename] using
      (LocalLoop.returned_evaluates (show Evaluates actual store .unit .unit store from .unit))
  obtain ⟨rfl,rfl⟩ := evaluation_deterministic completed.sound evaluated
  refine ⟨_,context,.returned .unit,before,mapping,world,
    .returnUnit (lookupStatement?_sound found) form,.returned (unitValue mapping world),heaps,.refl _,.refl _,
    .refl _ _,.refl _,.refl _ _ _ _,initial,callerProtocol.refl initial,?_⟩
  exact ⟨admitted.rows,by intro source same; cases same; exact ⟨.unit,admitted.heap⟩⟩
end Unit

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeTerminalFlow
end

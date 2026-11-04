import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationPhysical
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.SelectedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndexDiagnostics
import Solcore.SourceSemantics.CoreLowering.CompatibleCellIndexTerminal
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageMeaning

/-!
# Cell-aware invocations: expressions

Expression bounds and sequences of one actual body invocation: reads, literals, pairs, tuples, groups, operators, indices, builtin values and generalized reads.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionBounds
/-! Internal terminal-child bounds retain exact declaration authority and
return a concrete effect on every stored generalized row. Actual expression
proofs discharge these bounds; the public theorem does not assume them. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyRelation : ActualBodyInvocation.BodyRelation} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (certificate : GenericExpressionMeaning.Certificate) (faults : RecursiveStageMeaning.FaultRep)

/-- Source size is the grade of the genuine staged trace. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
    Staging.Recursive.Size.Expression program registry size invocation context environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

/-- Native size is measured independently; reflection returns the actual
Source grade and the exact staged outcome, including a nested failing scope. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
      owner.key.frameLocation = physical.location →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

def PreservesAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → PreservesAt (attachment := attachment) bridge context model index registry invocation certificate faults size

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt (attachment := attachment) bridge context model index registry invocation certificate faults size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt (attachment := attachment) bridge context model index registry invocation certificate faults size


end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionSequence
/-! Ordered staged arguments over mixed cells are constructed from the actual compiler Tree
and strictly smaller expression results. Each successful child passes its
actual reached caller state to the next child. Both failure tags retain the
same originating scope, token and final state. Native reflection reconstructs
an independent Source grade from the original packed-helper computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionSequence
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues DataExpressionSequence
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- Stable rows belong to the actual returned pool. Only a successful argument
list supplies the deep admission needed by a following application. -/
structure PostAdmission (outcome : Staging.Recursive.ValuesOutcome)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  rows : StableRows (bridge.pool reached)
  successful : ∀ values, outcome = .values values → Admission bridge context reached

theorem PostAdmission.at_values {values : List Dynamic.Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge (context := context) (.values values) reached) :
    Admission bridge context reached := post.successful values rfl

private def MemberTyping (ids : List ExpressionId) : Prop :=
  ∀ id, id ∈ ids → ∀ node, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type

private theorem member_typing {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids types) :
    MemberTyping (context := context) (invocation := invocation) ids := by
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member found

variable {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}

private theorem preserves_values_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (execution : Staging.Recursive.Size.Expressions program registry size invocation context environment
      before ids (.values sources) after) (within : size ≤ budget) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.values sources) reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ sources after with
  | nil =>
      cases execution
      exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _, initial, callerProtocol.refl initial,
        admitted.rows, fun _ _ => admitted⟩
  | single found generated =>
      cases execution with
      | cons head tail =>
          cases tail
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted authority physical owner ownerFrame head
          cases represented with
          | value payload =>
              exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
                finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post.rows,
                fun _ _ => post.at_value.2⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | cons head rest =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted authority physical owner ownerFrame head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
                  maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) ownerFrame rest
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
              have nonempty : values ≠ [] := by
                intro absent
                have lengths := restRep.length.2
                simp [absent] at lengths
              refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
                .cons (model.extend payload maps worlds) restRep, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, firstEffect.trans effect,
                reached, callerProtocol.trans firstRelated related, post.rows, fun _ _ => post.at_values⟩
              rw [rename_prefix] at second
              have combined := LocalSequence.pair_success lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
              simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

private theorem preserves_fault_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (execution : Staging.Recursive.Size.Expressions program registry size invocation context environment
      before ids (.fault failure) after) (within : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.fault failure) reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ after with
  | nil => cases execution
  | single found generated =>
      cases execution with
      | headFault failed =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted authority physical owner ownerFrame failed
          cases represented with
          | fault matched =>
              exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
                maps, worlds, frame, metadata, effect, reached, related, post.rows, by intro _ impossible; cases impossible⟩
      | tailFault _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | headFault failed =>
          obtain ⟨value, finalStore, finalMap, finalWorld, first, represented, finalHeaps,
              maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted authority physical owner ownerFrame failed
          cases represented with
          | fault matched =>
              refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
                maps, worlds, frame, metadata, effect, reached, related, post.rows, by intro _ impossible; cases impossible⟩
              simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first
      | tailFault head failed =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted authority physical owner ownerFrame head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
                  maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) ownerFrame failed
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
              refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, firstEffect.trans effect,
                reached, callerProtocol.trans firstRelated related, post⟩
              rw [rename_prefix] at second
              simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second

/-- Actual list typing supplies each used child's stored type. The successful
prefix retains the same cumulative caller records at every reached state. -/
theorem preserves_values (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ sources},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) index.owner index.active mapping world before store environment →
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment) →
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.frameLocation = physical.location → ∀ {size},
    Staging.Recursive.Size.Expressions program registry size invocation context environment before ids (.values sources) after →
    size ≤ budget →
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.values sources) reached :=
  preserves_values_with_members bridge budget tree (member_typing unique typing)

/-- A failing argument stops the original helper at the same reached caller
pool; no later argument runs and neither failure tag is relabeled. -/
theorem preserves_fault (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ failure},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) index.owner index.active mapping world before store environment →
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment) →
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.frameLocation = physical.location → ∀ {size},
    Staging.Recursive.Size.Expressions program registry size invocation context environment before ids (.fault failure) after →
    size ≤ budget →
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.fault failure) reached :=
  preserves_fault_with_members bridge budget tree (member_typing unique typing)

private theorem reflects_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) index.owner index.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
      value finalStore) (within : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expressions program registry sourceSize invocation context environment before ids outcome after ∧
      RecursiveStageArguments.ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) outcome reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ value finalStore with
  | nil =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (show Evaluates actual store
        ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
      exact ⟨_, .values [], before, mapping, world, .nil, .values (values := []) .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _, initial, callerProtocol.refl initial,
        admitted.rows, fun _ _ => admitted⟩
  | single found generated =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
        children _ within generated found (sourceTyped _ (by simp) _ found)
          environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame evaluated
      cases represented with
      | value payload =>
          exact ⟨_, .values [_], after, finalMap, finalWorld, .cons trace .nil,
            .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata, effect,
            reached, related, post.rows, fun _ _ => post.at_value.2⟩
      | fault matched =>
          exact ⟨_, .fault _, after, finalMap, finalWorld, .headFault trace,
            .fault matched, finalHeaps, maps, worlds, frame, metadata, effect,
            reached, related, post.rows, by intro _ impossible; cases impossible⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      change EvaluationSize size actual store ((LocalSequence.pair lowered.type
        (SourceCoreCalls.packArguments (nextCode :: codes)).type lowered.expression
        (SourceCoreCalls.packArguments (nextCode :: codes)).expression).rename ξ) value finalStore at evaluated
      rw [pair_rename] at evaluated
      have complete := evaluated
      cases evaluated with
      | caseLeft first _ =>
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
              maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
            children _ (by omega) generated found (sourceTyped _ (by simp) _ found)
              environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame first
          cases represented with
          | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                (LocalSequence.pair_left_failure lowered.type
                  (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound)
              exact ⟨_, .fault _, after, finalMap, finalWorld, .headFault trace, .fault matched,
                finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post.rows,
                by intro _ impossible; cases impossible⟩
      | caseRight first continuation =>
          obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            children _ (by omega) generated found (sourceTyped _ (by simp) _ found)
              environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame first
          cases represented with
          | @value sourceValue coreValue payload =>
              rename_i middleStore coreValue
              have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical
                  (coreValue :: actual) := agree_prefix layout coreValue
              cases continuation with
              | caseLeft second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, tailTrace, result, finalHeaps,
                      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
                    ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata) nextLayout
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) ownerFrame shifted (by omega)
                  cases result with
                  | fault matched =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_right_failure lowered.type
                          (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                      exact ⟨_, .fault _, after, finalMap, finalWorld, .tailFault firstTrace tailTrace, .fault matched,
                        finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                        firstFrame.trans frame, firstMetadata.trans metadata, firstEffect.trans effect,
                        reached, callerProtocol.trans firstRelated related, post⟩
              | caseRight second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, tailTrace, result, finalHeaps,
                      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
                    ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata) nextLayout
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) ownerFrame shifted (by omega)
                  cases result with
                  | @values sources values restRep =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_success lowered.type
                          (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                      have nonempty : values ≠ [] := by
                        intro absent
                        have lengths := restRep.length.2
                        simp [absent] at lengths
                      refine ⟨_, .values (sourceValue :: sources), after, finalMap, finalWorld,
                        .cons firstTrace tailTrace, ?_, finalHeaps,
                        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, firstEffect.trans effect,
                        reached, callerProtocol.trans firstRelated related, post.rows, fun _ _ => post.at_values⟩
                      simpa [packValues, nonempty] using
                        RecursiveStageArguments.ResultFor.values (codes := lowered :: nextCode :: codes)
                          (.cons (model.extend payload maps worlds) restRep)

/-- Original packed-helper inversion supplies strict native child bounds.
Each reflected Source child contributes its own independent list grade. -/
theorem reflects (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before store finalStore ξ value},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) index.owner index.active mapping world before store environment →
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment) →
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.frameLocation = physical.location → ∀ {size},
    EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore →
    size < budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expressions program registry sourceSize invocation context environment before ids outcome after ∧
      RecursiveStageArguments.ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) outcome reached :=
  reflects_with_members bridge budget tree (member_typing unique typing)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionSequence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTypedExpressionSequence
/-! Ordered staged argument conversion retains the original value types at
its actual final heap. Successful prefixes transport these types through each
later child's metadata-preserving heap change. Faults retain their exact tag,
heap and caller state without a successful value-typing obligation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTypedExpressionSequence
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues DataExpressionSequence
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

open CellAwareInvocationExpressionSequence (PostAdmission)

private def MemberTyping (ids : List ExpressionId) : Prop :=
  ∀ id, id ∈ ids → ∀ node, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type

private theorem member_typing {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids types) :
    MemberTyping (context := context) (invocation := invocation) ids := by
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member found

variable {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}

private theorem preserves_values_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model bodyIndex registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) bodyIndex.owner bodyIndex.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (execution : Staging.Recursive.Size.Expressions program registry size invocation context environment
      before ids (.values sources) after) (within : size ≤ budget) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      Dynamic.ValuesHaveTypes context after sources sourceTypes ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.values sources) reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ sources after with
  | nil =>
      cases execution
      exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _, .nil, initial, callerProtocol.refl initial,
        admitted.rows, fun _ _ => admitted⟩
  | single found generated =>
      cases execution with
      | cons head tail =>
          cases tail
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted authority physical owner ownerFrame head
          cases represented with
          | value payload =>
              exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
                finalHeaps, maps, worlds, frame, metadata, effect, .cons post.at_value.1 .nil, reached, related, post.rows,
                fun _ _ => post.at_value.2⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | cons head rest =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted authority physical owner ownerFrame head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
                  maps, worlds, frame, metadata, effect, restTyped, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) ownerFrame rest
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
              have nonempty : values ≠ [] := by
                intro absent
                have lengths := restRep.length.2
                simp [absent] at lengths
              refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
                .cons (model.extend payload maps worlds) restRep, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, firstEffect.trans effect,
                .cons (Dynamic.ValueHasType.mono metadata firstPost.at_value.1) restTyped, reached, callerProtocol.trans firstRelated related, post.rows, fun _ _ => post.at_values⟩
              rw [rename_prefix] at second
              have combined := LocalSequence.pair_success lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
              simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

/-- Actual list typing supplies each used child's stored type. The successful
prefix retains the same cumulative caller records at every reached state. -/
theorem preserves_values (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model bodyIndex registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ sources},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) bodyIndex.owner bodyIndex.active mapping world before store environment →
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment) →
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.frameLocation = physical.location → ∀ {size},
    Staging.Recursive.Size.Expressions program registry size invocation context environment before ids (.values sources) after →
    size ≤ budget →
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      Dynamic.ValuesHaveTypes context after sources sourceTypes ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.values sources) reached :=
  preserves_values_with_members bridge budget tree (member_typing unique typing)

private theorem reflects_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model bodyIndex registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) bodyIndex.owner bodyIndex.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location) {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
      value finalStore) (within : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expressions program registry sourceSize invocation context environment before ids outcome after ∧
      RecursiveStageArguments.ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      (∀ sources, outcome = .values sources → Dynamic.ValuesHaveTypes context after sources sourceTypes) ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) outcome reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ value finalStore with
  | nil =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (show Evaluates actual store
        ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
      exact ⟨_, .values [], before, mapping, world, .nil, .values (values := []) .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _, (by intro values eq; cases eq; exact .nil), initial, callerProtocol.refl initial,
        admitted.rows, fun _ _ => admitted⟩
  | single found generated =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
        children _ within generated found (sourceTyped _ (by simp) _ found)
          environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame evaluated
      cases represented with
      | value payload =>
          exact ⟨_, .values [_], after, finalMap, finalWorld, .cons trace .nil,
            .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata, effect,
            (by intro values eq; cases eq; exact .cons post.at_value.1 .nil), reached, related, post.rows, fun _ _ => post.at_value.2⟩
      | fault matched =>
          exact ⟨_, .fault _, after, finalMap, finalWorld, .headFault trace,
            .fault matched, finalHeaps, maps, worlds, frame, metadata, effect,
            (by intro values eq; cases eq), reached, related, post.rows, by intro _ impossible; cases impossible⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      change EvaluationSize size actual store ((LocalSequence.pair lowered.type
        (SourceCoreCalls.packArguments (nextCode :: codes)).type lowered.expression
        (SourceCoreCalls.packArguments (nextCode :: codes)).expression).rename ξ) value finalStore at evaluated
      rw [pair_rename] at evaluated
      have complete := evaluated
      cases evaluated with
      | caseLeft first _ =>
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
              maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
            children _ (by omega) generated found (sourceTyped _ (by simp) _ found)
              environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame first
          cases represented with
          | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                (LocalSequence.pair_left_failure lowered.type
                  (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound)
              exact ⟨_, .fault _, after, finalMap, finalWorld, .headFault trace, .fault matched,
                finalHeaps, maps, worlds, frame, metadata, effect, (by intro values eq; cases eq), reached, related, post.rows,
                by intro _ impossible; cases impossible⟩
      | caseRight first continuation =>
          obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            children _ (by omega) generated found (sourceTyped _ (by simp) _ found)
              environments heaps locals layout actualTyped initial admitted authority physical owner ownerFrame first
          cases represented with
          | @value sourceValue coreValue payload =>
              rename_i middleStore coreValue
              have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical
                  (coreValue :: actual) := agree_prefix layout coreValue
              cases continuation with
              | caseLeft second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, tailTrace, result, finalHeaps,
                      maps, worlds, frame, metadata, effect, restTyped, reached, related, post⟩ :=
                    ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata) nextLayout
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) ownerFrame shifted (by omega)
                  cases result with
                  | fault matched =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_right_failure lowered.type
                          (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                      exact ⟨_, .fault _, after, finalMap, finalWorld, .tailFault firstTrace tailTrace, .fault matched,
                        finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                        firstFrame.trans frame, firstMetadata.trans metadata, firstEffect.trans effect,
                        (by intro values eq; cases eq), reached, callerProtocol.trans firstRelated related, post⟩
              | caseRight second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, tailTrace, result, finalHeaps,
                      maps, worlds, frame, metadata, effect, restTyped, reached, related, post⟩ :=
                    ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata) nextLayout
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) ownerFrame shifted (by omega)
                  cases result with
                  | @values sources values restRep =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_success lowered.type
                          (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                      have nonempty : values ≠ [] := by
                        intro absent
                        have lengths := restRep.length.2
                        simp [absent] at lengths
                      refine ⟨_, .values (sourceValue :: sources), after, finalMap, finalWorld,
                        .cons firstTrace tailTrace, ?_, finalHeaps,
                        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, firstEffect.trans effect,
                        (by intro values eq; cases eq; exact .cons (Dynamic.ValueHasType.mono metadata firstPost.at_value.1) (restTyped _ rfl)), reached, callerProtocol.trans firstRelated related, post.rows, fun _ _ => post.at_values⟩
                      simpa [packValues, nonempty] using
                        RecursiveStageArguments.ResultFor.values (codes := lowered :: nextCode :: codes)
                          (.cons (model.extend payload maps worlds) restRep)

/-- Original packed-helper inversion supplies strict native child bounds.
Each reflected Source child contributes its own independent list grade. -/
theorem reflects (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model bodyIndex registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before store finalStore ξ value},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical compiled.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) bodyIndex.owner bodyIndex.active mapping world before store environment →
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment) →
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.frameLocation = physical.location → ∀ {size},
    EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore →
    size < budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expressions program registry sourceSize invocation context environment before ids outcome after ∧
      RecursiveStageArguments.ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      (∀ sources, outcome = .values sources → Dynamic.ValuesHaveTypes context after sources sourceTypes) ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) outcome reached :=
  reflects_with_members bridge budget tree (member_typing unique typing)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTypedExpressionSequence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationReadBounds
/-! Actual monomorphic reads retain generalized cells elsewhere in the same
Source heap. Descriptor absence is derived only at the selected binding from
its compiler receipt and Source heap typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationReadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CompatibleExpressionReads
open CallableIndexedOwnedFunctionState
open CellAwareInvocationExpressionBounds
universe u

private theorem no_stage
    {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {size : Nat}
    {name : String} {binder : Resolved.LocalId} {failedScope call reason}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (coercions : node.coercions = [])
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      before id (.fault (.stage failedScope call reason)) after) : False := by
  have reference : ∀ {shape requirements}, Staging.Recursive.Occurrence invocation id shape requirements →
      shape = .reference name (.local binder) := by
    intro shape requirements occurrence
    obtain ⟨other, contains, sameForm, _, _⟩ := occurrence
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    exact sameForm.symm.trans form
  cases trace with
  | generalizedLocal contains _ _ _ _ _ _ _ path =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [coercions] at path
      cases path
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found coercions contains))
  | group occurrence _
  | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _
  | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
      cases reference occurrence

/-- Reconstruct only an ordinary readable local, using its actual cell. The
generalized-local alternatives are excluded by that same cell's descriptor. -/
private theorem staged_of_read
    {fuel : Nat} {values : ValuesContext} {invocation : Staging.Recursive.Scope}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel values invocation.source scope id reason code)
    {program : Program} {registry : Staging.Recursive.Registry} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    (read : Dynamic.Heap.Reads before location cell)
    (ordinary : cell.generalized = none)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
      environment before id outcome after) :
    Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [])
      invocation context environment before id
      (match outcome with | .value value => .value value | .fault fault => .fault (.semantic fault)) after := by
  have same_node : ∀ {other}, ContainsExpression invocation.source id other → other = certificate.node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans certificate.metadata.found)
  have same_cell : ∀ {otherLocation otherCell},
      Dynamic.Environment.LooksUp environment certificate.binder otherLocation →
      Dynamic.Heap.Reads before otherLocation otherCell → otherCell = cell := by
    intro otherLocation otherCell otherLookup otherRead
    have sameLocation := otherLookup.functional lookup
    subst otherLocation
    exact otherRead.functional read
  have contains := lookupExpression?_sound certificate.metadata.found
  have atomic : Staging.Recursive.AtomicForm certificate.node.form := by
    rw [certificate.form]
    exact .reference _ _
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro otherContains raw coercions =>
      cases same_node otherContains
      rw [certificate.metadata.coercions] at coercions
      cases coercions
      exact .atomicValue contains atomic certificate.metadata.coercions
        (by simpa only [certificate.metadata.coercions] using raw)
    | generalizedLocal otherContains otherForm _ otherLookup otherRead descriptor _ _ _ =>
      cases same_node otherContains
      rw [certificate.form] at otherForm
      cases otherForm
      cases same_cell otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
    | form otherContains raw =>
      cases same_node otherContains
      exact .atomicFault contains atomic certificate.metadata.coercions
        (by simpa only [certificate.metadata.coercions] using raw)
    | coercion otherContains _ failed =>
      cases same_node otherContains
      rw [certificate.metadata.coercions] at failed
      cases failed
    | generalizedLocalRequirement otherContains otherForm _ otherLookup otherRead descriptor _ _ _
    | generalizedLocalCoercion otherContains otherForm _ otherLookup otherRead descriptor _ _ _ =>
      cases same_node otherContains
      rw [certificate.form] at otherForm
      cases otherForm
      cases same_cell otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  (ordinaryCells : GenericHeap.OrdinaryCells
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {fuel : Nat} {reasonAt : ExpressionId → Word}
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ scope id lowered,
    LoweredRead fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "reads" => LoweredRead fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) invocation.source context reasonAt

include extension ordinaryCells semantic unique in
/-- The accepted local-read compiler discharges preservation internally. A
stage failure at this atomic occurrence is impossible; semantic failures keep
their original token, heap and actual caller state. -/
theorem preserves_local (size : Nat) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation
      (fun scope id lowered => reads scope id lowered ∧
        ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) faults size := by
  intro scope id lowered ⟨receipt, readFault⟩ node found sourceTyped
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted _authority _physical _owner _ownerFrame trace
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  have ordinary := locals.descriptor_empty_of_monomorphic admitted.heap
    binding.declared lookup read certificate.monomorphic
  have plain : ∃ plainOutcome : Dynamic.ExpressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
        environment before id plainOutcome after ∧
      outcome = (match plainOutcome with | .value value => .value value | .fault reason => .fault (.semantic reason)) := by
    cases outcome with
    | value value => exact ⟨.value value, .value trace.sound.value_plain, rfl⟩
    | fault failure => cases failure with
      | semantic reason => exact ⟨.fault reason, .fault trace.sound.semanticFault_plain, rfl⟩
      | stage failedScope call reason =>
        exact False.elim (no_stage unique found (nodeEq ▸ certificate.form) (nodeEq ▸ certificate.metadata.coercions) trace)
  obtain ⟨plainOutcome, plainTrace, outcomeEq⟩ := plain
  obtain ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata, effect⟩ :=
    certificate.scoped_preserves_with_diagnostics functions extension ordinaryCells program context invocation.evidence binding
      environments heaps admitted.heap locals agrees (fun location _ _ => readFault location) unique plainTrace
  simp only [SourceCoreCompatibleValues.Context.initial, nodeEq, typeEq] at represented finalHeaps
  let transport := administrativeTransport headers keys
  let reachedPool := transport.extend (bridge.pool initial) (.refl _) (.refl _) frame metadata
  obtain ⟨reached, _poolEq, related⟩ := bridge.restore initial reachedPool (.refl _) (.refl _)
    frame metadata (transport.related (bridge.pool initial) (.refl _) (.refl _) frame metadata)
  refine ⟨value, finalStore, mapping, world, ?_, ?_, finalHeaps, .refl _, .refl _,
    frame, metadata, effect, reached, related, ?_⟩
  · simpa only [← typeEq] using evaluated
  · cases represented with
    | value payload =>
      rw [outcomeEq]
      exact .value payload
    | fault matched =>
      rw [outcomeEq]
      exact .fault (semantic _ _ matched)
  · have rows := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
      (bridge.pool initial) (bridge.pool reached) admitted.rows frame
    cases outcome with
    | value sourceValue =>
      refine ⟨rows, ?_⟩
      intro value same
      cases same
      have preserved := SelectedCompilationReadAdmission.read_preserved certificate unique lookup read
        ordinary locals admitted.heap sourceTyped trace.sound.value_plain
      exact ⟨preserved.value_typed, preserved.heap_typed⟩
    | fault failure =>
      cases failure with
      | semantic reason => exact ⟨rows, by intro value same; cases same⟩
      | stage origin call reason => exact rows

include extension ordinaryCells semantic unique in
/-- A completed native read reconstructs the original atomic Source outcome
at grade one. Lazy mapping initialization retains its exact written cell and
every caller row at the same final store. -/
theorem reflects_local (size : Nat) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation
      (fun scope id lowered => reads scope id lowered ∧
        ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) faults size := by
  intro scope id lowered ⟨receipt, readFault⟩ node found sourceTyped
    mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted _authority _physical _owner _ownerFrame completed
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  have ordinary := locals.descriptor_empty_of_monomorphic admitted.heap
    binding.declared lookup read certificate.monomorphic
  obtain ⟨outcome, after, sourceTrace, represented, finalHeaps, frame, metadata, effect⟩ :=
    certificate.scoped_reflects_with_diagnostics functions extension ordinaryCells program context invocation.evidence binding
      environments heaps admitted.heap locals agrees (fun location _ _ => readFault location) (by simpa only [← typeEq] using completed.sound)
  simp only [SourceCoreCompatibleValues.Context.initial, nodeEq, typeEq] at represented finalHeaps
  have staged := staged_of_read (registry := registry) certificate unique lookup read ordinary sourceTrace
  let transport := administrativeTransport headers keys
  let reachedPool := transport.extend (bridge.pool initial) (.refl _) (.refl _) frame metadata
  obtain ⟨reached, _poolEq, related⟩ := bridge.restore initial reachedPool (.refl _) (.refl _)
    frame metadata (transport.related (bridge.pool initial) (.refl _) (.refl _) frame metadata)
  refine ⟨Staging.Recursive.Size.stepSize [], _, after, mapping, world, staged, ?_, finalHeaps,
    .refl _, .refl _, frame, metadata, effect, reached, related, ?_⟩
  · cases represented with
    | value payload => exact .value payload
    | fault matched => exact .fault (semantic _ _ matched)
  · have rows := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
      (bridge.pool initial) (bridge.pool reached) admitted.rows frame
    cases outcome with
    | value sourceValue =>
      refine ⟨rows, ?_⟩
      intro value same
      cases same
      have preserved := SelectedCompilationReadAdmission.read_preserved certificate unique lookup read
        ordinary locals admitted.heap sourceTyped staged.sound.value_plain
      exact ⟨preserved.value_typed, preserved.heap_typed⟩
    | fault reason => exact ⟨rows, by intro value same; cases same⟩

include extension ordinaryCells uninitialized semantic unique in
/-- The global diagnostic interface follows by restricting it to the actual read. -/
theorem preserves (size : Nat) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation reads faults size := by
  intro scope id lowered receipt
  exact preserves_local bridge functions extension ordinaryCells semantic unique size
    ⟨receipt, uninitialized scope id lowered receipt⟩

include extension ordinaryCells uninitialized semantic unique in
/-- The global diagnostic interface follows by restricting it to the actual read. -/
theorem reflects (size : Nat) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation reads faults size := by
  intro scope id lowered receipt
  exact reflects_local bridge functions extension ordinaryCells semantic unique size
    ⟨receipt, uninitialized scope id lowered receipt⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationReadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLiterals
/-! Literal execution reuses the existing cell-aware Source proof. Native
purity supplies the extra retention of the same stored contextual descriptors;
the invocation index and its captured frame are unrestricted. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLiterals
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyRelation : ActualBodyInvocation.BodyRelation} {program : Program}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)

abbrev Certificate : GenericExpressionMeaning.Certificate :=
  fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved invocation.source id lowered

theorem preserves
    (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context)
    (unique : NodeOccurrencesUnique invocation.source) (size : Nat) :
    PreservesAt (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) index
      registry invocation (Certificate (solved := solved) (invocation := invocation)) faults size := by
  intro scope id lowered receipt node found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted _authority _physical _owner _ownerFrame trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CellAwareSelectedLiteralBounds.literal_preserves functions bridge sameLedger runtimeLedger unique
      faults size receipt found typed environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨literalNode, _, literal, selected⟩ := receipt
  have evidence := selected.evidence sameLedger runtimeLedger invocation.evidence
  obtain ⟨_, _, _, _, pureEvaluation⟩ :=
    literal.evaluates_with_evidence (registry := rawRegistry) functions program context invocation.evidence evidence invocation.source
      environment before mapping world actual store ξ
  have unchanged := (evaluation_deterministic pureEvaluation evaluated).2
  have effect :
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore := by
    rw [← unchanged]
    simpa only [List.append_nil] using
      (CellAwareScopeAuthority.Effect.append (instances :=
        GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) store [] metadata maps worlds)
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, effect, reached, related, post⟩

theorem reflects
    (sameLedger : context.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid context) (size : Nat) :
    ReflectsAt (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) index
      registry invocation (Certificate (solved := solved) (invocation := invocation)) faults size := by
  intro scope id lowered receipt node found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted _authority _physical _owner _ownerFrame completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CellAwareSelectedLiteralBounds.literal_reflects functions bridge sameLedger runtimeLedger
      faults size receipt found typed environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨literalNode, _, literal, selected⟩ := receipt
  have evidence := selected.evidence sameLedger runtimeLedger invocation.evidence
  obtain ⟨_, _, _, _, pureEvaluation⟩ :=
    literal.evaluates_with_evidence (registry := rawRegistry) functions program context invocation.evidence evidence invocation.source
      environment before mapping world actual store ξ
  have unchanged := (evaluation_deterministic pureEvaluation completed.sound).2
  have effect :
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore := by
    rw [← unchanged]
    simpa only [List.append_nil] using
      (CellAwareScopeAuthority.Effect.append (instances :=
        GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) store [] metadata maps worlds)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, effect, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLiterals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPairBounds
/-! Ordered pair children transport actual generalized lexical authority. Their
concrete effects compose across both successful and failing evaluations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPairBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CompatibleExpressionProducts (Metadata)
open CallableIndexedOwnedPreparedStagedPairBounds (Pair ProductValues)
universe u

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- A payload model may combine two represented values at the same reached
heap/world. This is a representation constructor, with no execution input. -/
private inductive SourceChildren (size : Nat) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (left right : ExpressionId) :
    Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | leftFault {childSize after failure}
      (smaller : childSize < size)
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context
        environment before left (.fault failure) after) :
      SourceChildren size environment before left right (.fault failure) after
  | rightFault {firstSize secondSize middle after value failure}
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size)
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context
        environment before left (.value value) middle)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context
        environment middle right (.fault failure) after) :
      SourceChildren size environment before left right (.fault failure) after
  | values {firstSize secondSize middle after leftValue rightValue}
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size)
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context
        environment before left (.value leftValue) middle)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context
        environment middle right (.value rightValue) after) :
      SourceChildren size environment before left right (.value (.product leftValue rightValue)) after

private theorem source_children
    {id left right : ExpressionId} {node : ExpressionNode}
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .tuple [left, right])
    (trace : Staging.Recursive.Size.Expression program registry size invocation context
      environment before id outcome after) :
    SourceChildren (program := program) (registry := registry) (invocation := invocation)
      (context := context) size environment before left right outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm requirements},
      Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .tuple [left, right] := by
    intro actualForm requirements occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | generalizedLocal contains localForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _ =>
      cases same_node contains
      rw [form] at localForm
      cases localForm
  | pair occurrence first second =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .values (Staging.Recursive.Size.child_lt_stepSize (by simp))
          (Staging.Recursive.Size.child_lt_stepSize (by simp)) first second
  | pairLeftFault occurrence child =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .leftFault (Staging.Recursive.Size.child_lt_stepSize (by simp)) child
  | pairRightFault occurrence first second =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .rightFault (Staging.Recursive.Size.child_lt_stepSize (by simp))
          (Staging.Recursive.Size.child_lt_stepSize (by simp)) first second
  | tupleValue occurrence sequence packed =>
      cases ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases sequence with
      | cons first rest =>
          cases rest with
          | cons second tail =>
              cases tail
              cases packed with
              | cons last =>
                  cases last
                  exact .values (by simp [Staging.Recursive.Size.stepSize]; omega)
                    (by simp [Staging.Recursive.Size.stepSize]; omega) first second
  | tupleFault occurrence sequence =>
      cases ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases sequence with
      | headFault first =>
          exact .leftFault (by simp [Staging.Recursive.Size.stepSize]; omega) first
      | tailFault first rest =>
          cases rest with
          | headFault second =>
              exact .rightFault (by simp [Staging.Recursive.Size.stepSize]; omega)
                (by simp [Staging.Recursive.Size.stepSize]; omega) first second
          | tailFault _ rest => cases rest
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _
  | group occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _
  | applied occurrence _ _ _ _ _ _ => cases occurrence_form occurrence

private theorem child_typing
    {id left right : ExpressionId} {node leftNode rightNode : ExpressionNode} {type : Ty}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .tuple [left, right])
    (leftFound : invocation.source.lookupExpression? left = some leftNode)
    (rightFound : invocation.source.lookupExpression? right = some rightNode)
    (unique : NodeOccurrencesUnique invocation.source)
    (typed : ExpressionHasType invocation.source context id node.type) :
    ExpressionHasType invocation.source context left leftNode.type ∧
      ExpressionHasType invocation.source context right rightNode.type := by
  obtain ⟨first, second, firstFound, secondFound, _sourceType, firstTyped, secondTyped⟩ :=
    CompatibleExpressionProducts.pair_source_types unique metadata.found form metadata.coercions typed
  cases Option.some.inj (firstFound.symm.trans leftFound)
  cases Option.some.inj (secondFound.symm.trans rightFound)
  exact ⟨firstTyped, secondTyped⟩

/-- Two genuine Source children are executed in their actual successive heaps.
Either failure keeps its original scoped representation and exact endpoint. -/
theorem pair_preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (products : ProductValues (model := model)) (budget : Nat)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context model index registry invocation children faults budget) :
    ∀ size, size ≤ budget → PreservesAt (attachment := attachment) bridge context model index registry invocation
      (Pair checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  cases certified with
  | actual metadata form leftFound rightFound sourceType firstChild secondChild =>
      cases Option.some.inj (found.symm.trans metadata.found)
      obtain ⟨firstTyped, secondTyped⟩ := child_typing metadata form leftFound rightFound unique typed
      have parts := source_children unique metadata.found form trace
      cases parts with
      | leftFault smaller first =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le smaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame first
          cases represented with
          | fault matched =>
              refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
                maps, worlds, frame, heapMetadata, effect, reached, related, post.at_fault_type⟩
              rw [DataExpressionSequence.pair_rename]
              exact LocalSequence.pair_left_failure _ _ evaluated
      | rightFault firstSmaller secondSmaller first second =>
          obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le firstSmaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame first
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps,
                  maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
                childMeaning _ (Nat.lt_of_lt_of_le secondSmaller within) secondChild rightFound secondTyped
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix agrees _) (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame second
              cases represented with
              | fault matched =>
                  refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
                    firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                    firstMetadata.trans heapMetadata, firstEffect.trans effect, reached, callerProtocol.trans firstRelated related,
                    post.at_fault_type⟩
                  rw [DataExpressionSequence.pair_rename]
                  rw [rename_prefix] at secondEval
                  exact LocalSequence.pair_right_failure _ _ firstEval secondEval
      | values firstSmaller secondSmaller first second =>
          obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le firstSmaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame first
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps,
                  maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
                childMeaning _ (Nat.lt_of_lt_of_le secondSmaller within) secondChild rightFound secondTyped
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix agrees _) (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame second
              cases represented with
              | @value lastSource lastCoreValue lastPayload =>
                  refine ⟨.inRight .word (.pair coreValue lastCoreValue), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
                    firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                    firstMetadata.trans heapMetadata, firstEffect.trans effect, reached, callerProtocol.trans firstRelated related, ?_⟩
                  · rw [DataExpressionSequence.pair_rename]
                    rw [rename_prefix] at secondEval
                    exact LocalSequence.pair_success _ _ firstEval secondEval
                  · exact .value (sourceType ▸ products (model.extend payload maps worlds) lastPayload)
                  · refine ⟨post.rows, ?_⟩
                    intro value same
                    cases same
                    refine ⟨?_, post.at_value.2.heap⟩
                    rw [sourceType]
                    exact .product (firstPost.at_value.1.mono heapMetadata) post.at_value.1

/-- Actual native bind inversion supplies strictly smaller executed children;
the Source pair grade is constructed independently from their Source traces. -/
theorem pair_reflects
    (unique : NodeOccurrencesUnique invocation.source)
    (products : ProductValues (model := model)) (budget : Nat)
    (childMeaning : ReflectsBelow (attachment := attachment) bridge context model index registry invocation children faults budget) :
    ∀ size, size ≤ budget → ReflectsAt (attachment := attachment) bridge context model index registry invocation
      (Pair checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame completed
  cases certified with
  | actual metadata form leftFound rightFound sourceType firstChild secondChild =>
      cases Option.some.inj (found.symm.trans metadata.found)
      obtain ⟨firstTyped, secondTyped⟩ := child_typing metadata form leftFound rightFound unique typed
      have occurrence : Staging.Recursive.Occurrence invocation id (.tuple [_, _]) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      change EvaluationSize size actual store ((LocalSequence.pair _ _ _ _).rename ξ) value finalStore at completed
      rw [DataExpressionSequence.pair_rename] at completed
      have complete := completed
      cases completed with
      | caseLeft first _ =>
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
            childMeaning _ (by omega) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame first
          cases represented with
          | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                (LocalSequence.pair_left_failure _ _ first.sound)
              exact ⟨_, .fault _, after, finalMap, finalWorld, .pairLeftFault occurrence trace,
                .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related,
                post.at_fault_type⟩
      | caseRight first continuation =>
          obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (by omega) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame first
          cases represented with
          | @value sourceValue coreValue payload =>
              cases continuation with
              | caseLeft second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps,
                      maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
                    childMeaning _ (by omega) secondChild rightFound secondTyped
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                      (agree_prefix agrees _)
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame shifted
                  cases represented with
                  | fault matched =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_right_failure _ _ first.sound second.sound)
                      exact ⟨_, .fault _, after, finalMap, finalWorld,
                        .pairRightFault occurrence firstTrace secondTrace, .fault matched,
                        finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                        firstMetadata.trans heapMetadata, firstEffect.trans effect, reached, callerProtocol.trans firstRelated related,
                        post.at_fault_type⟩
              | caseRight second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps,
                      maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
                    childMeaning _ (by omega) secondChild rightFound secondTyped
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                      (agree_prefix agrees _)
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame shifted
                  cases represented with
                  | @value lastSource lastCoreValue lastPayload =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_success _ _ first.sound second.sound)
                      have trace := Staging.Recursive.Size.Expression.pair occurrence firstTrace secondTrace
                      refine ⟨_, .value _, after, finalMap, finalWorld, trace, ?_, finalHeaps,
                        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                        firstMetadata.trans heapMetadata, firstEffect.trans effect, reached, callerProtocol.trans firstRelated related, ?_⟩
                      · exact .value (sourceType ▸ products (model.extend payload maps worlds) lastPayload)
                      · refine ⟨post.rows, ?_⟩
                        intro value same
                        cases same
                        refine ⟨?_, post.at_value.2.heap⟩
                        rw [sourceType]
                        exact .product (firstPost.at_value.1.mono heapMetadata) post.at_value.1

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPairBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGroups
/-! Group evaluation runs its actual child in the same invocation. The child
keeps every stored attachment and returns the same exact heap effect. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGroups
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedGroupBounds (Group)
open CellAwareStagedGroupBounds (source_group_inv child_typed)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- The Source group rule adds one genuine step above its executed child.
The child theorem carries either fault tag and the exact reached state. -/
theorem group_preserves
    (unique : NodeOccurrencesUnique invocation.source) (budget : Nat)
    (childMeaning : CellAwareInvocationExpressionBounds.PreservesBelow
      (attachment := attachment) bridge context model index registry invocation children faults budget) :
    ∀ size, size ≤ budget → CellAwareInvocationExpressionBounds.PreservesAt
      (attachment := attachment) bridge context model index registry invocation (Group compiled.compatible.checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  cases certified with
  | actual metadata form innerFound sourceType child =>
      have same := Option.some.inj (found.symm.trans metadata.found)
      cases same
      obtain ⟨childSize, sizeEq, childTrace⟩ := source_group_inv unique metadata.found form trace
      have smaller : childSize < budget := by
        rw [sizeEq] at within
        exact Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
        childMeaning childSize smaller child innerFound
          (child_typed metadata form innerFound unique typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childTrace
      refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, ?_⟩
      · simpa only [sourceType] using represented
      · simpa only [sourceType] using post

/-- The native group is literally the child code. Its structural child IH
uses the SAME grade; this theorem requests no strict native inequality. -/
theorem group_reflects
    (unique : NodeOccurrencesUnique invocation.source) (size : Nat)
    (childMeaning : CellAwareInvocationExpressionBounds.ReflectsAt
      (attachment := attachment) bridge context model index registry invocation children faults size) :
    CellAwareInvocationExpressionBounds.ReflectsAt
      (attachment := attachment) bridge context model index registry invocation (Group compiled.compatible.checked invocation.source children) faults size := by
  intro scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame completed
  cases certified with
  | actual metadata form innerFound sourceType child =>
      have same := Option.some.inj (found.symm.trans metadata.found)
      cases same
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
        childMeaning child innerFound (child_typed metadata form innerFound unique typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame completed
      have occurrence : Staging.Recursive.Occurrence invocation id (.group _) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome, after, finalMap, finalWorld,
        .group occurrence trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata, effect,
        reached, related, ?_⟩
      · simpa only [sourceType] using represented
      · simpa only [sourceType] using post

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGroups
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationReadProductBounds
/-! One accepted compiler extraction retains the actual finite literal/read/
group/pair tree and its selected literal sites. Structural recursion constructs
every staged child meaning internally, including ordinary local reads and lazy
mapping initialization at the actual reached state. Source and native grades
remain independent: transparent group reflection uses the same native grade,
while evaluated pair binds use their real strict child grades. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationReadProductBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
universe u
open CallableLambdaBodyReachability

open CallableIndexedOwnedPreparedStagedReadProductTreeBounds (Certificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  (ordinaryCells : GenericHeap.OrdinaryCells
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions)
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  {semanticFaults : FunctionCalls.FaultRep}
  (faults : RecursiveStageMeaning.FaultRep)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  {faultRoot : ExpressionId}
  (uninitializedOn : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    Reaches invocation.source [.expression faultRoot] (.expression id) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "trees" => Certificate readFuel
  (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
  invocation.source context solved reasonAt

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues
      (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include extension ordinaryCells sameLedger runtimeLedger uninitializedOn semantic unique in
/-- LiteralSites recursion proves each actual Source child internally. A read
uses its genuine local certificate; no read or whole-child meaning is supplied. -/
theorem preserves_reached (size : Nat) :
    PreservesAt (attachment := attachment) bridge context valueModel index registry invocation
      (fun scope id lowered => trees scope id lowered ∧
        Reaches invocation.source [.expression faultRoot] (.expression id)) faults size := by
  intro scope id lowered ⟨⟨tree, sites⟩, reached⟩
  revert reached
  induction sites generalizing size with
  | literal _ receipt =>
      intro _reached actualNode
      exact CellAwareInvocationLiterals.preserves
        functions bridge faults sameLedger runtimeLedger unique size receipt
  | read receipt =>
      intro reached actualNode
      exact CellAwareInvocationReadBounds.preserves_local bridge functions extension ordinaryCells
        semantic unique size ⟨receipt, uninitializedOn scope _ _ receipt reached⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
      intro reached
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation
          (Point scope inner lowered) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih childSize innerReached
      intro actualNode
      exact CellAwareInvocationGroups.group_preserves bridge unique size children
        size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
      intro reached
      have leftReached : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have rightReached : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation
          (Two scope left right first second) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, alternative⟩ := point
        cases alternative with
        | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize leftReached
        | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize rightReached
      intro actualNode
      exact CellAwareInvocationPairBounds.pair_preserves bridge unique (product_values functions) size children size (Nat.le_refl _)
        (.actual metadata form leftFound rightFound sourceType
          ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

include extension ordinaryCells sameLedger runtimeLedger uninitializedOn semantic unique in
/-- Reflection follows the same finite sites at independent native grades.
Grouping recurses at the same grade; actual pair binds supply strict children. -/
theorem reflects_reached (size : Nat) :
    ReflectsAt (attachment := attachment) bridge context valueModel index registry invocation
      (fun scope id lowered => trees scope id lowered ∧
        Reaches invocation.source [.expression faultRoot] (.expression id)) faults size := by
  intro scope id lowered ⟨⟨tree, sites⟩, reached⟩
  revert reached
  induction sites generalizing size with
  | literal _ receipt =>
      intro _reached actualNode
      exact CellAwareInvocationLiterals.reflects
        functions bridge faults sameLedger runtimeLedger size receipt
  | read receipt =>
      intro reached actualNode
      exact CellAwareInvocationReadBounds.reflects_local bridge functions extension ordinaryCells
        semantic unique size ⟨receipt, uninitializedOn scope _ _ receipt reached⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
      intro reached
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : ReflectsAt (attachment := attachment) bridge context valueModel index registry invocation
          (Point scope inner lowered) faults size := by
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih size innerReached
      intro actualNode
      exact CellAwareInvocationGroups.group_reflects bridge unique size children
        (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
      intro reached
      have leftReached : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have rightReached : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : ReflectsBelow (attachment := attachment) bridge context valueModel index registry invocation
          (Two scope left right first second) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, alternative⟩ := point
        cases alternative with
        | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize leftReached
        | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize rightReached
      intro actualNode
      exact CellAwareInvocationPairBounds.pair_reflects bridge unique (product_values functions) size children size (Nat.le_refl _)
        (.actual metadata form leftFound rightFound sourceType
          ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

include extension ordinaryCells sameLedger runtimeLedger uninitialized semantic unique in
/-- Global diagnostic facts restrict to each authentic expression root. -/
theorem preserves (size : Nat) :
    PreservesAt (attachment := attachment) bridge context valueModel index registry invocation trees faults size := by
  intro scope id lowered tree
  exact preserves_reached (faultRoot := id) bridge functions extension ordinaryCells sameLedger runtimeLedger faults
    (fun current child code receipt _reached => uninitialized current child code receipt)
    semantic unique size ⟨tree, .root (by simp)⟩

include extension ordinaryCells sameLedger runtimeLedger uninitialized semantic unique in
/-- Global diagnostic facts restrict to each authentic expression root. -/
theorem reflects (size : Nat) :
    ReflectsAt (attachment := attachment) bridge context valueModel index registry invocation trees faults size := by
  intro scope id lowered tree
  exact reflects_reached (faultRoot := id) bridge functions extension ordinaryCells sameLedger runtimeLedger faults
    (fun current child code receipt _reached => uninitialized current child code receipt)
    semantic unique size ⟨tree, .root (by simp)⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationReadProductBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOperatorBounds
/-! Primitive operators and conditional expressions retain generalized cells.
Executed children carry exact descriptor effects and caller admission through
the reached heap; skipped branches perform no evaluation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOperatorBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CompatibleExpressionPrimitives CompatibleExpressionConditionals
open ProtectedStateExpressionOperandTyping
universe u
open CellAwareScopeOperatorBounds (Head)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {registry : SourceCoreRawMetadata.Registry} {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

/-- Strict Source children preserve the exact staged result and owned state. -/
theorem preserves_at_selected (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique invocation.source) (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program stages)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source) (covers : invocation.evidence.Covers context)
    (meaning : PreservesBelow (attachment := attachment) bridge context model index stages invocation certificate faults budget) :
    PreservesAt (attachment := attachment) bridge context model index stages invocation (Head compiled.compatible.checked invocation.source certificate) faults size := by
  intro scope id lowered tree root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    cases tree with
    | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have ih := fun n (bound : n < budget) => @meaning n bound _ _ _ child _ childFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change operand ∈ [operand]; simp) childFound)
      have sourceStep := CallableIndexedOwnedPreparedStagedOperatorSourceBounds.unary_inv metadata form unique trace
      cases sourceStep with
      | value childTrace applied childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
          ih _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childTrace
        cases represented with
        | value payload =>
          rw [inputType] at payload
          obtain ⟨sourceResult, result, actualApplied, coreApplied, resultRep⟩ := profile.preserves payload
          have same := actualApplied.functional applied
          subst sourceResult
          refine ⟨.inRight .word result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, effect, ⟨reached, related⟩⟩
          · rw [unary_rename]; exact LocalPrimitiveResults.unary_success evaluated coreApplied
          · exact .value (outputType ▸ resultRep)
      | fault childTrace childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
          ih _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [unary_rename]; exact LocalPrimitiveResults.unary_failure evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      | invalid childTrace failed childSmaller =>
        obtain ⟨_, _, _, _, _, represented, _⟩ := ih _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childTrace
        cases represented with
        | value payload =>
          rw [inputType] at payload
          obtain ⟨_, _, applied, _, _⟩ := profile.preserves payload
          exact False.elim (failed.excludes_application ⟨_, applied⟩)
    | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have leftIH := fun n (bound : n < budget) => @meaning n bound _ _ _ leftTree _ leftFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change left ∈ [left, right]; simp) leftFound)
      have rightIH := fun n (bound : n < budget) => @meaning n bound _ _ _ rightTree _ rightFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change right ∈ [left, right]; simp) rightFound)
      have sourceStep := CallableIndexedOwnedPreparedStagedOperatorSourceBounds.binary_inv metadata form unique trace
      cases sourceStep with
      | leftFault childTrace childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact mode.left_failure operator evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      | leftInvalid childTrace invalid childSmaller =>
        obtain ⟨_, _, _, _, _, represented, _⟩ := leftIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childTrace
        cases represented with
        | value payload =>
          rw [leftType] at payload
          exact False.elim (profile.left_valid payload invalid)
      | short childTrace circuit childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childTrace
        cases represented with
        | value payload =>
          rw [leftType] at payload
          obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit evaluated
          exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, effect, ⟨reached, related⟩⟩
      | rightFault firstTrace continues secondTrace firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
          rw [GenericExpressionMeaning.rename_prefix] at second
          cases represented with
          | fault matched =>
            exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact profile.right_failure payload continues first second,
              .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, firstEffect.trans effect, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
      | value firstTrace continues secondTrace applied firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
          rw [GenericExpressionMeaning.rename_prefix] at second
          cases represented with
          | value rightPayload =>
            rw [rightType] at rightPayload
            have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
            obtain ⟨sourceResult, result, actualApplied, resultRep, combined⟩ := profile.right_success leftPayload rightPayload continues first second
            have same := actualApplied.functional applied
            subst sourceResult
            exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
              .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, firstEffect.trans effect, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
      | invalid firstTrace continues secondTrace failed firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, _, _, _, second, represented, _, maps, worlds, _⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
          rw [GenericExpressionMeaning.rename_prefix] at second
          cases represented with
          | value rightPayload =>
            rw [rightType] at rightPayload
            have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
            obtain ⟨_, _, applied, _, _⟩ := profile.right_success leftPayload rightPayload continues first second
            exact False.elim (failed.excludes_application ⟨_, applied⟩)

    | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have conditionIH := fun n (bound : n < budget) => @meaning n bound _ _ _ conditionTree _ conditionFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change condition ∈ [condition, thenId, elseId]; simp) conditionFound)
      have thenIH := fun n (bound : n < budget) => @meaning n bound _ _ _ thenTree _ thenFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change thenId ∈ [condition, thenId, elseId]; simp) thenFound)
      have elseIH := fun n (bound : n < budget) => @meaning n bound _ _ _ elseTree _ elseFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change elseId ∈ [condition, thenId, elseId]; simp) elseFound)
      have sourceStep := CallableIndexedOwnedPreparedStagedOperatorSourceBounds.conditional_inv metadata form unique trace
      cases sourceStep with
      | fault childTrace childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
          conditionIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [choose_rename]; exact LocalControl.choose_failure type evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      | @branch conditionSize branchSize flag middle outcome after conditionTrace branchTrace conditionSmaller branchSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          conditionIH _ (Nat.lt_of_lt_of_le conditionSmaller bounded) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame conditionTrace
        cases represented with
        | value payload =>
          obtain ⟨actualFlag, sourceEq, coreEq⟩ := bool_fields payload
          cases sourceEq
          subst coreEq
          cases flag with
          | false =>
            obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
              elseIH _ (Nat.lt_of_lt_of_le branchSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
                (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame branchTrace
            rw [GenericExpressionMeaning.rename_prefix] at branch
            refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, firstEffect.trans effect, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            · rw [choose_rename]; exact LocalControl.choose_false type first branch
            · simpa only [elseType, CallableIndexedAmbient.ambientDefinitions] using represented
          | true =>
            obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
              thenIH _ (Nat.lt_of_lt_of_le branchSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
                (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame branchTrace
            rw [GenericExpressionMeaning.rename_prefix] at branch
            refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, firstEffect.trans effect, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            · rw [choose_rename]; exact LocalControl.choose_true type first branch
            · simpa only [thenType, CallableIndexedAmbient.ambientDefinitions] using represented

  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals sourceTyped trace frame⟩

/-- Completed native children produce their own staged grades and exact state. -/
theorem reflects_at_selected (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique invocation.source) (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program stages)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source) (covers : invocation.evidence.Covers context)
    (meaning : ReflectsBelow (attachment := attachment) bridge context model index stages invocation certificate faults budget) :
    ReflectsAt (attachment := attachment) bridge context model index stages invocation (Head compiled.compatible.checked invocation.source certificate) faults size := by
  intro scope id lowered tree root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame evaluated
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    cases tree with
    | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have ih := fun n (bound : n < budget) => @meaning n bound _ _ _ child _ childFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change operand ∈ [operand]; simp) childFound)
      have occurrence : Staging.Recursive.Occurrence invocation id (.unary operator operand) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      rw [unary_rename] at evaluated
      have complete := evaluated.sound
      cases evaluated with
      | caseLeft childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
          ih _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childEvaluation
        cases represented with
        | fault matched =>
          have failed := trace
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_failure (operator := core) childEvaluation.sound) complete
          exact ⟨_, _, after, finalMap, finalWorld, .unaryOperandFault occurrence failed, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      | caseRight childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
          ih _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childEvaluation
        cases represented with
        | value payload =>
          rw [inputType] at payload
          obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_success childEvaluation.sound coreApplied) complete
          have childTrace := trace
          exact ⟨_, _, after, finalMap, finalWorld, .unary occurrence childTrace applied,
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, effect, ⟨reached, related⟩⟩
    | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have leftIH := fun n (bound : n < budget) => @meaning n bound _ _ _ leftTree _ leftFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change left ∈ [left, right]; simp) leftFound)
      have rightIH := fun n (bound : n < budget) => @meaning n bound _ _ _ rightTree _ rightFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change right ∈ [left, right]; simp) rightFound)
      have occurrence : Staging.Recursive.Occurrence invocation id (.binary left operator right) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      rw [Mode.binary_rename] at evaluated
      have complete := evaluated.sound
      rw [Mode.binary_eq] at evaluated
      cases evaluated with
      | caseLeft leftEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
          leftIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame leftEvaluation
        cases represented with
        | fault matched =>
          have failed := trace
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (mode.left_failure operator leftEvaluation.sound)
          exact ⟨_, _, after, finalMap, finalWorld, .binaryLeftFault occurrence failed, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      | caseRight leftEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame leftEvaluation
        cases represented with
        | @value sourceValue coreValue payload =>
          rw [leftType] at payload
          have firstTrace := trace
          rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
          · obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit leftEvaluation.sound
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            exact ⟨_, _, middle, middleMap, middleWorld, .binaryShortCircuit occurrence firstTrace circuit,
              .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, ⟨middleState, firstRelated⟩⟩
          · obtain ⟨rightSize, rightValue, rightStore, rightEvaluation, rightSmaller⟩ := RecursiveNamedExpressionSourceBounds.right_evaluated profile payload continues branch
            have shifted := rightEvaluation
            rw [← GenericExpressionMeaning.rename_prefix] at shifted
            obtain ⟨rightSourceSize, rightOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
              rightIH rightSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame shifted
            cases represented with
            | fault matched =>
              have failed := trace
              have combined := profile.right_failure payload continues leftEvaluation.sound rightEvaluation.sound
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              exact ⟨_, _, after, finalMap, finalWorld, .binaryRightFault occurrence firstTrace continues failed,
                .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                firstFrame.trans frame, firstMetadata.trans heapMetadata, firstEffect.trans effect, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            | value rightPayload =>
              rw [rightType] at rightPayload
              have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
              obtain ⟨sourceResult, result, applied, resultRep, combined⟩ :=
                profile.right_success leftPayload rightPayload continues leftEvaluation.sound rightEvaluation.sound
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              have secondTrace := trace
              exact ⟨_, _, after, finalMap, finalWorld, .binary occurrence firstTrace continues secondTrace applied,
                .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                firstFrame.trans frame, firstMetadata.trans heapMetadata, firstEffect.trans effect, ⟨reached, callerProtocol.trans firstRelated related⟩⟩

    | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have conditionIH := fun n (bound : n < budget) => @meaning n bound _ _ _ conditionTree _ conditionFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change condition ∈ [condition, thenId, elseId]; simp) conditionFound)
      have thenIH := fun n (bound : n < budget) => @meaning n bound _ _ _ thenTree _ thenFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change thenId ∈ [condition, thenId, elseId]; simp) thenFound)
      have elseIH := fun n (bound : n < budget) => @meaning n bound _ _ _ elseTree _ elseFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change elseId ∈ [condition, thenId, elseId]; simp) elseFound)
      have occurrence : Staging.Recursive.Occurrence invocation id (.conditional condition thenId elseId) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      rw [choose_rename] at evaluated
      have complete := evaluated.sound
      cases evaluated with
      | caseLeft childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
          conditionIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childEvaluation
        cases represented with
        | fault matched =>
          have failed := trace
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalControl.choose_failure type childEvaluation.sound)
          exact ⟨_, _, after, finalMap, finalWorld, .conditionalFault occurrence failed, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      | caseRight childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          conditionIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childEvaluation
        cases represented with
        | value payload =>
          obtain ⟨flag, sourceEq, coreEq⟩ := bool_fields payload
          subst sourceEq
          subst coreEq
          have conditionTrace := trace
          obtain ⟨selectedSize, selected, selectedSmaller⟩ := RecursiveNamedExpressionSourceBounds.choose_branch_evaluated branch
          cases flag with
          | false =>
            change EvaluationSize selectedSize _ _ ((elseCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
              elseIH selectedSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame selected
            refine ⟨_, outcome, after, finalMap, finalWorld, .conditional occurrence conditionTrace branchTrace,
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, firstEffect.trans effect, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            simpa only [elseType, CallableIndexedAmbient.ambientDefinitions] using represented
          | true =>
            change EvaluationSize selectedSize _ _ ((thenCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
              thenIH selectedSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame selected
            refine ⟨_, outcome, after, finalMap, finalWorld, .conditional occurrence conditionTrace branchTrace,
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, firstEffect.trans effect, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            simpa only [thenType, CallableIndexedAmbient.ambientDefinitions] using represented

  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals sourceTyped trace frame⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique invocation.source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source) (covers : invocation.evidence.Covers context)
    (meaning : PreservesBelow (attachment := attachment) bridge context model index stages invocation certificate faults budget) :
    PreservesAt (attachment := attachment) bridge context model index stages invocation (Head compiled.compatible.checked invocation.source certificate) faults size := by
  apply preserves_at_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed)  <;> assumption

theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique invocation.source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source) (covers : invocation.evidence.Covers context)
    (meaning : ReflectsBelow (attachment := attachment) bridge context model index stages invocation certificate faults budget) :
    ReflectsAt (attachment := attachment) bridge context model index stages invocation (Head compiled.compatible.checked invocation.source certificate) faults size := by
  apply reflects_at_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed)  <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationOperatorBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBuiltinValueBounds
/-! Actual builtin references are pure leaves in a heap containing generalized
cells. Their real descriptor and captured runtime environment are retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBuiltinValueBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
universe u

private theorem unchanged {program : Program} {stages : Staging.Recursive.Registry}
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {id : ExpressionId}
    {node : ExpressionNode} {name : String} {function : BuiltinFunctionId} {size : Nat}
    {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinFunction function))
    (empty : node.coercions = [])
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before id outcome after) :
    outcome = .value (.builtin ⟨function⟩) ∧ after = before := by
  have same_node : ∀ {other}, ContainsExpression invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have same_occurrence : ∀ {actual requirements}, Staging.Recursive.Occurrence invocation id actual requirements →
      actual = .reference name (.builtinFunction function) := by
    intro actual requirements occurrence
    obtain ⟨other, contains, same, _requirements, _coercions⟩ := occurrence
    cases same_node contains
    exact same.symm.trans form
  cases trace with
  | atomicValue contains _ _ raw =>
    cases same_node contains
    rw [form] at raw
    cases raw
    exact ⟨rfl, rfl⟩
  | atomicFault contains _ _ raw =>
    cases same_node contains
    rw [form] at raw
    cases raw
  | generalizedLocal contains localForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _ =>
    cases same_node contains
    simp [form] at localForm
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
    exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found empty contains))
  | pair occurrence _ _ | tupleValue occurrence _ _ | constructorValue occurrence _ _
  | unary occurrence _ _ | unaryInvalid occurrence _ _
  | binaryLeftInvalid occurrence _ _ | binaryShortCircuit occurrence _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | notCallable occurrence _ _ | sourceArity occurrence _ _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _
  | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _
  | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _
  | group occurrence _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _ | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _
  | conditional occurrence _ _ | conditionalFault occurrence _ | calleeFault occurrence _
  | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
    cases same_occurrence occurrence

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (included : (CallableIndexedBuiltinValues.model compiled.indexed profile).Includes functions)
  {context : SourceSemantics.Context} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)

private abbrev Certificate : GenericExpressionMeaning.Certificate :=
  fun _ id lowered => Nonempty (CellAwareBuiltinValueCertificates.Header compiled.indexed invocation.source id lowered)

include included in
theorem preserves (unique : NodeOccurrencesUnique invocation.source) (size : Nat) :
    PreservesAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions)
      index stages invocation (Certificate (compiled := compiled) (invocation := invocation)) faults size := by
  intro scope id lowered receipt node found typed mapping world administrative environment canonical actual actualContext
    before store embedding outcome after environments heaps locals agrees actualTyped initial admitted _authority _physical _owner _ownerFrame trace
  obtain ⟨receipt⟩ := receipt
  have same := Option.some.inj (receipt.found.symm.trans found)
  cases same
  obtain ⟨rfl, rfl⟩ := unchanged unique found receipt.form receipt.coercions trace
  let native := BuiltinCalls.Protocol.contractedValue receipt.function receipt.identity receipt.descriptor.id actual
  have related : (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions).Represents
      mapping world receipt.node.type (.builtin ⟨receipt.function⟩) native lowered.type := by
    rw [receipt.sourceType, receipt.nativeType]
    exact .function (included (.builtin receipt.inventory receipt.number receipt.descriptor actualTyped))
  have evaluated : Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
    rw [receipt.rename, receipt.emitted]
    exact BuiltinCalls.Protocol.contracted_evaluates _ _ _ actual store
  refine ⟨.inRight .word native, store, mapping, world, evaluated, .value related,
    heaps, .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _, initial, callerProtocol.refl initial, ?_⟩
  exact ⟨admitted.rows, by
    intro value same
    cases same
    exact ⟨receipt.sourceType.symm ▸ Dynamic.ValueHasType.builtin ⟨receipt.function⟩, admitted.heap⟩⟩

include included in
theorem reflects (size : Nat) :
    ReflectsAt (attachment := attachment) bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions)
      index stages invocation (Certificate (compiled := compiled) (invocation := invocation)) faults size := by
  intro scope id lowered receipt node found typed mapping world administrative environment canonical actual actualContext
    before store embedding value finalStore environments heaps locals agrees actualTyped initial admitted _authority _physical _owner _ownerFrame completed
  obtain ⟨receipt⟩ := receipt
  have same := Option.some.inj (receipt.found.symm.trans found)
  cases same
  let native := BuiltinCalls.Protocol.contractedValue receipt.function receipt.identity receipt.descriptor.id actual
  have related : (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions).Represents
      mapping world receipt.node.type (.builtin ⟨receipt.function⟩) native lowered.type := by
    rw [receipt.sourceType, receipt.nativeType]
    exact .function (included (.builtin receipt.inventory receipt.number receipt.descriptor actualTyped))
  have evaluated : Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
    rw [receipt.rename, receipt.emitted]
    exact BuiltinCalls.Protocol.contracted_evaluates _ _ _ actual store
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed.sound
  have sourceTrace : Staging.Recursive.Size.Expression program stages (Staging.Recursive.Size.stepSize [])
      invocation context environment before id (.value (.builtin ⟨receipt.function⟩)) before :=
    .atomicValue (lookupExpression?_sound found) (receipt.form.symm ▸ .reference _ _) receipt.coercions
      (by rw [receipt.form, receipt.requirements]; exact .builtinFunction rfl)
  refine ⟨Staging.Recursive.Size.stepSize [], .value (.builtin ⟨receipt.function⟩), before, mapping, world,
    sourceTrace, .value related, heaps, .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _,
    initial, callerProtocol.refl initial, ?_⟩
  exact ⟨admitted.rows, by
    intro value same
    cases same
    exact ⟨receipt.sourceType.symm ▸ Dynamic.ValueHasType.builtin ⟨receipt.function⟩, admitted.heap⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBuiltinValueBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedReads
/-! A genuine local read selects the stored Snapshot from the same physical
heap entry. Its allocation attachment survives a larger read-time context;
body-view transport across that change is a separate obligation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalLocatedRows GeneralizedLocalBundleContexts
open GeneralizedLocalAcceptedInstances GeneralizedLocalAcceptedLocatedRows
open GeneralizedLocalReachedAllocation (Attachment)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {canonical actual : Core.Environment}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment}

/-- Actual scope lookup, catalog lookup, native bundle projection, and stored
frame agreement select one retained candidate. The returned relation still
uses its original lexical context and captured body proof. -/
theorem Physical.generalized_read
    (physical : Physical (attachment := Attachment) compiled index context scope canonical
      mapping world heap store environment)
    {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals
      index.owner index.active index.compilerSource scope id reason lowered)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (read : Dynamic.Heap.Reads heap location cell) (descriptor : cell.generalized = some function)
    {catalog : SourceCoreDataCatalog.Catalog} {administrative : Core.Context} {embedding : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment
      canonical compiled.indexed.layouts.definitions)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual) :
    ∃ lexical native,
      ContextExtension lexical index.active ∧
      Attachment function receipt.binding lexical ∧
      Snapshot compiled.indexed mapping world function receipt.binding lexical physical.location
        (Attachment function receipt.binding lexical) receipt.candidate native ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
  obtain ⟨binding, lexical, located, owner, binder, extension, frames, _, _⟩ :=
    physical.generalized lookup read descriptor
  have sameBinding : receipt.binding = binding := by
    have selected : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok receipt.binding := by
      simpa only [owner, binder] using receipt.bindingFound
    have registered : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding :=
      located.attachment.registered
    exact Except.ok.inj (selected.symm.trans registered)
  obtain ⟨native, snapshot, evaluated⟩ := GeneralizedLocalAcceptedLocatedRows.Located.preserves_snapshot located frames receipt
    owner.symm binder.symm extension environments lookup agrees
  have attached : Attachment function binding lexical := by
    cases snapshot with
    | retained _ _ _ _ _ _ _ _ attached _ _ _ _ _ _ _ _ => exact attached
  rw [← sameBinding] at snapshot attached
  exact ⟨lexical, native, extension, attached, snapshot, evaluated⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationGeneralizedReadAttachments
/-! A real heap read retains the same saved Snapshot with arbitrary proof
attachment. The descriptor initializer and captures come from that same cell. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
open Core Frontend SourceInference TypeSystem GeneralHeap
open GeneralizedLocalLocatedRows GeneralizedLocalBundleContexts
open GeneralizedLocalAcceptedInstances GeneralizedLocalAcceptedLocatedRows

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {canonical actual : Core.Environment}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment}

/-- Actual scope lookup, catalog lookup, native bundle projection, and stored
frame agreement select one retained candidate. The returned relation still
uses its original lexical context and captured body proof. -/
theorem Physical.generalized_read_with
    {attachment : Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → Substitution → Prop}
    (physical : Physical (attachment := attachment) compiled index context scope canonical
      mapping world heap store environment)
    {id : ExpressionId} {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate compiled.indexed.base.locals
      index.owner index.active index.compilerSource scope id reason lowered)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure}
    (lookup : Dynamic.Environment.LooksUp environment receipt.binder location)
    (read : Dynamic.Heap.Reads heap location cell) (descriptor : cell.generalized = some function)
    {catalog : SourceCoreDataCatalog.Catalog} {administrative : Core.Context} {embedding : Renaming}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment
      canonical compiled.indexed.layouts.definitions)
    (agrees : ReadOnly.EnvironmentsAgree embedding canonical actual) :
    ∃ lexical native,
      ContextExtension lexical index.active ∧
      attachment function receipt.binding lexical ∧
      Snapshot compiled.indexed mapping world function receipt.binding lexical physical.location
        (attachment function receipt.binding lexical) receipt.candidate native ∧
      function.initializer = receipt.binding.initializer ∧
      Dynamic.GeneralizedClosureCaptures function.definitionContext function.source
        function.captured function.binder function.initializer function ∧
      Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
  obtain ⟨binding, lexical, located, owner, binder, extension, frames, _, _⟩ :=
    physical.generalized lookup read descriptor
  have sameBinding : receipt.binding = binding := by
    have selected : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok receipt.binding := by
      simpa only [owner, binder] using receipt.bindingFound
    have registered : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding :=
      located.attachment.registered
    exact Except.ok.inj (selected.symm.trans registered)
  obtain ⟨native, snapshot, evaluated⟩ := GeneralizedLocalAcceptedLocatedRows.Located.preserves_snapshot located frames receipt
    owner.symm binder.symm extension environments lookup agrees
  have attached : attachment function binding lexical := by
    cases snapshot with
    | retained _ _ _ _ _ _ _ _ attached _ _ _ _ _ _ _ _ => exact attached
  rw [← sameBinding] at snapshot attached
  exact ⟨lexical, native, extension, attached, snapshot,
    located.attachment.initializer.trans (congrArg SourceCoreLocalPolymorphism.Binding.initializer sameBinding.symm),
    located.attachment.captures, evaluated⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysical
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationIndexBounds
/-! Recursive mapping lookup consumes the actual base and key child states in
order. The lookup suffix keeps their Source heap and transports the retained
caller through its real administrative allocations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationIndexBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CompatibleExpressionIndices CallableIndexedOwnedPreparedStagedIndexOutcomes
open GenericExpressionMeaning (agree_prefix rename_prefix)
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private theorem completed {values : ValuesContext} {source : TypedSource} {id base : ExpressionId}
    {node baseNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {first second : SourceCoreBasic.LoweredExpr}
    (header : Header values source id base node baseNode layout comparison first second)
    {environment : Environment} {store middleStore keyStore finalStore : Store}
    {baseValue keyValue result : Value} {ξ : Renaming} {reason : Word}
    (firstEval : Evaluates environment store (first.expression.rename ξ) (.inRight .word baseValue) middleStore)
    (secondEval : Evaluates (baseValue :: environment) middleStore (second.expression.rename ((Renaming.insertion 0).comp ξ)) (.inRight .word keyValue) keyStore)
    (lookup : Evaluates (keyValue :: baseValue :: environment) keyStore
      (SourceCoreMappingWithDefault.lookup layout reason comparison.expression (.var 1) (.var 0)) result finalStore) :
    Evaluates environment store
      ((SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression reason).rename ξ)
      result finalStore := by
  rw [index_rename comparison header.registered header.comparisonType]
  rw [rename_prefix] at secondEval
  apply SourceCoreCompatibleDataExpressions.index_completed layout reason firstEval secondEval
  simpa only [CompatibleMapping.Transport.expression_weaken] using lookup

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)
  {compileRegistry : SourceCoreRawMetadata.Registry}
  {extension : SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry compileRegistry}
  {scope : SourceCoreLocalCell.Scope} {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode}
  {layout : Core.OrderedMapping.Layout} {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
  {first second : SourceCoreBasic.LoweredExpr} {reason : Word}
  (header : Header ⟨compiled.compatible.checked, compileRegistry, extension⟩ invocation.source id base node baseNode layout comparison first second)
  (keyFound : invocation.source.lookupExpression? key = some keyNode)
  (form : node.form = .index base key)
  (sourceType : baseNode.type = .mapping keyNode.type node.type)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "headCode" => SourceCoreBasic.LoweredExpr.mk layout.valueType
  (SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression reason)

include bridge functions faults unique selectedBodies runtime covers header keyFound form sourceType faithful functionLeaves functionTypes in
theorem preserves_selected {children : GenericExpressionMeaning.Certificate}
    (firstChild : children scope base first) (secondChild : children scope key second)
    (missing : ∀ mapping world baseSource keySource baseValue,
      MissingPolicy (keyNode := keyNode) (registry := receiving) header
        functions mapping world baseSource keySource baseValue reason
        (fun error token => faults (.semantic error) token))
    (size : Nat)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context model index registry invocation children faults size) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation (Point scope id headCode) faults size := by
  intro current child lowered point root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ header.baseMetadata.found
    (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
      (by rw [form]; change base ∈ [base, key]; simp) header.baseMetadata.found)
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ keyFound
    (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
      (by rw [form]; change key ∈ [base, key]; simp) keyFound)
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression reason).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type layout.valueType faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨current, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    cases CallableIndexedOwnedPreparedStagedIndexSourceInversion.children unique found form trace with
    | baseFault firstTrace smaller =>
      obtain ⟨_, finalStore, finalMap, finalWorld, firstEval, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ smaller environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame firstTrace
      cases represented with
      | fault matched =>
        rw [header.baseType] at firstEval
        exact ⟨_, finalStore, finalMap, finalWorld, by
          rw [index_rename comparison header.registered header.comparisonType]
          exact SourceCoreCompatibleDataExpressions.index_base_failure layout reason firstEval,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | keyFault firstTrace secondTrace firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
        firstIH _ firstSmaller environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame firstTrace
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨_, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
          secondIH _ secondSmaller (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
        cases represented with
        | fault matched =>
          rw [rename_prefix, header.keyType] at secondEval
          exact ⟨_, finalStore, finalMap, finalWorld, by
            rw [index_rename comparison header.registered header.comparisonType]
            exact SourceCoreCompatibleDataExpressions.index_key_failure layout reason firstEval secondEval,
            .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
    | result firstTrace secondTrace sourceResult firstSmaller secondSmaller =>
      obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
        firstIH _ firstSmaller environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame firstTrace
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨_, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
          secondIH _ secondSmaller (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
        cases represented with
        | value keyPayload =>
          obtain ⟨plain, result, finalStore, futureWorld, suffixCells, terminal, resultRep, lookup, finalHeaps, suffixWorlds, suffixFrame, suffixAppend, functional⟩ :=
            CompatibleCellIndex.finish_with_diagnostics header sourceType faithful functionLeaves functionTypes (payload.extend (.refl _) maps worlds) keyPayload
              (actualTyped.weaken (firstWorlds.trans worlds)) keyHeaps reason (missing _ _ _ _ _)
          obtain ⟨original, same, originalTerminal⟩ := to_terminal sourceResult
          have outcomeEq := (functional _ originalTerminal)
          subst original
          subst outcome
          have suffixEffect := suffixAppend.symm ▸ CellAwareScopeAuthority.Effect.append
            (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) _ suffixCells
            (.refl after) (.refl keyMap) suffixWorlds
          let suffixPool : State headers keys ⟨current, keyMap, futureWorld, after, finalStore, canonical⟩ := (bridge.pool reached).extend (.refl _) suffixWorlds suffixFrame (.refl _)
          obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
            (.refl _) suffixWorlds suffixFrame (.refl _) (Relates.of_records_eq rfl)
          refine ⟨result, finalStore, keyMap, futureWorld, completed header firstEval secondEval lookup, ?_,
            finalHeaps, firstMaps.trans maps, (firstWorlds.trans worlds).trans suffixWorlds,
            (firstFrame.trans frame).trans suffixFrame, firstMetadata.trans heapMetadata, (firstEffect.trans effect).trans suffixEffect,
            returned, callerProtocol.trans (callerProtocol.trans firstRelated related) returnedRelated⟩
          cases resultRep with
          | value represented => exact .value represented
          | fault matched => exact .fault matched
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, metadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, metadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals sourceTyped trace frame⟩


include bridge functions faults unique selectedBodies runtime covers header keyFound form sourceType faithful functionLeaves functionTypes in
theorem reflects_selected {children : GenericExpressionMeaning.Certificate}
    (firstChild : children scope base first) (secondChild : children scope key second)
    (missing : ∀ mapping world baseSource keySource baseValue,
      MissingPolicy (keyNode := keyNode) (registry := receiving) header
        functions mapping world baseSource keySource baseValue reason
        (fun error token => faults (.semantic error) token))
    (size : Nat)
    (childMeaning : ReflectsBelow (attachment := attachment) bridge context model index registry invocation children faults size) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation (Point scope id headCode) faults size := by
  intro current child lowered point root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame evaluated
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ header.baseMetadata.found
    (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
      (by rw [form]; change base ∈ [base, key]; simp) header.baseMetadata.found)
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ keyFound
    (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
      (by rw [form]; change key ∈ [base, key]; simp) keyFound)
  have occurrence : Staging.Recursive.Occurrence invocation child (.index base key) :=
    ⟨_, lookupExpression?_sound header.metadata.found, form, header.metadata.requirements, header.metadata.coercions⟩
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before child outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type layout.valueType faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨current, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft firstEvaluation branch =>
      have firstShifted := firstEvaluation
      obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame firstShifted
      cases represented with
      | fault matched =>
        have failed := firstEvaluation.sound
        rw [header.baseType] at failed
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
          (SourceCoreCompatibleDataExpressions.index_base_failure layout reason failed)
        exact ⟨_, _, after, finalMap, finalWorld, .indexBaseFault occurrence firstTrace,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | caseRight firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame firstEvaluation
      cases represented with
      | @value baseSource coreValue payload =>
        cases branch with
        | caseLeft secondEvaluation lookup =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
            secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame shifted
          cases represented with
          | fault matched =>
            have failed := secondEvaluation.sound
            rw [header.keyType] at failed
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
              (SourceCoreCompatibleDataExpressions.index_key_failure layout reason firstEvaluation.sound failed)
            exact ⟨_, _, after, finalMap, finalWorld, .indexKeyFault occurrence firstTrace secondTrace,
              .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
        | caseRight secondEvaluation lookup =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, after, keyMap, keyWorld, secondTrace, represented, keyHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
            secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame shifted
          cases represented with
          | value keyPayload =>
            obtain ⟨plain, result, lastStore, futureWorld, suffixCells, terminal, resultRep, suffix, finalHeaps, suffixWorlds, suffixFrame, suffixAppend, _functional⟩ :=
              CompatibleCellIndex.finish_with_diagnostics header sourceType faithful functionLeaves functionTypes (payload.extend (.refl _) maps worlds) keyPayload
                (actualTyped.weaken (firstWorlds.trans worlds)) keyHeaps reason (missing _ _ _ _ _)
            have combined := completed header firstEvaluation.sound shifted.sound suffix
            rw [index_rename comparison header.registered header.comparisonType] at combined
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            have suffixEffect := suffixAppend.symm ▸ CellAwareScopeAuthority.Effect.append
              (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) _ suffixCells
              (.refl after) (.refl keyMap) suffixWorlds
            let suffixPool : State headers keys ⟨current, keyMap, futureWorld, after, finalStore, canonical⟩ :=
              (bridge.pool reached).extend (.refl _) suffixWorlds suffixFrame (.refl _)
            obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
              (.refl _) suffixWorlds suffixFrame (.refl _) (Relates.of_records_eq rfl)
            refine ⟨_, liftOutcome plain, after, keyMap, futureWorld,
              .indexResult occurrence firstTrace secondTrace (of_terminal terminal), ?_, finalHeaps,
              firstMaps.trans maps, (firstWorlds.trans worlds).trans suffixWorlds,
              (firstFrame.trans frame).trans suffixFrame, firstMetadata.trans heapMetadata, (firstEffect.trans effect).trans suffixEffect,
              returned, callerProtocol.trans (callerProtocol.trans firstRelated related) returnedRelated⟩
            cases resultRep with
            | value represented => exact .value represented
            | fault matched => exact .fault matched
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, metadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, metadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals sourceTyped trace frame⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include bridge functions faults unique wellFormed runtime covers header keyFound form sourceType faithful functionLeaves functionTypes in
theorem preserves {children : GenericExpressionMeaning.Certificate}
    (firstChild : children scope base first) (secondChild : children scope key second)
    (missing : ∀ mapping world baseSource keySource baseValue,
      MissingPolicy (keyNode := keyNode) (registry := receiving) header
        functions mapping world baseSource keySource baseValue reason
        (fun error token => faults (.semantic error) token))
    (size : Nat)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context model index registry invocation children faults size) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation (Point scope id headCode) faults size := by
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (bridge := bridge) (functions := functions) (faults := faults) (unique := unique) (runtime := runtime) (covers := covers) (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes) <;> assumption

include bridge functions faults unique wellFormed runtime covers header keyFound form sourceType faithful functionLeaves functionTypes in
theorem reflects {children : GenericExpressionMeaning.Certificate}
    (firstChild : children scope base first) (secondChild : children scope key second)
    (missing : ∀ mapping world baseSource keySource baseValue,
      MissingPolicy (keyNode := keyNode) (registry := receiving) header
        functions mapping world baseSource keySource baseValue reason
        (fun error token => faults (.semantic error) token))
    (size : Nat)
    (childMeaning : ReflectsBelow (attachment := attachment) bridge context model index registry invocation children faults size) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation (Point scope id headCode) faults size := by
  apply reflects_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (bridge := bridge) (functions := functions) (faults := faults) (unique := unique) (runtime := runtime) (covers := covers) (header := header) (keyFound := keyFound) (form := form) (sourceType := sourceType) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationIndexBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTupleBounds
/-! Invocation tuple heads retain the actual ordered child certificate
vector. The original Source inversion, legacy binary pair rules and reached
state proofs supply the head semantics. Child hypotheses are theorem arguments;
static compiler receipts carry no execution law. Singleton reflection permits
the same native grade and constructs its independent Source grade. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTupleBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
universe u

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private theorem occurrence_form {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    {node : ExpressionNode} {form : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (owned : Staging.Recursive.Occurrence invocation id form requirements) : node.form = form := by
  obtain ⟨other, contains, formed, _, _⟩ := owned
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact formed

/-- Outside the two-element legacy rules, the actual list grade is bounded
by the original Source parent. The empty atomic tuple is childless. -/
private theorem source_sequence {program : Program} {registry : Staging.Recursive.Registry}
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {checked : SourceCoreCompatibleCatalog.Checked} {id : ExpressionId} {node : ExpressionNode}
    {type : Core.Ty} {ids : List ExpressionId} {size : Nat}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (metadata : CompatibleExpressionPrimitives.Metadata checked invocation.source id node type)
    (form : node.form = .tuple ids) (unique : NodeOccurrencesUnique invocation.source)
    (notPair : ids.length ≠ 2)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context
      environment before id outcome after) :
    ∃ childSize sequence, childSize ≤ size ∧
      Staging.Recursive.Size.Expressions program registry childSize invocation context
        environment before ids sequence after ∧
      RecursiveStageTupleMeaning.PacksOutcome sequence outcome := by
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique metadata.found metadata.coercions contains))
  | atomicValue contains atomic uncoerced raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      subst node
      rw [form] at atomic raw
      cases atomic
      cases raw with
      | tuple _ children pack =>
          cases children
          cases pack
          exact ⟨_, _, Nat.le_refl _, .nil, .values .nil⟩
  | atomicFault contains atomic uncoerced raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      subst node
      rw [form] at atomic raw
      cases atomic
      cases raw with | tuple _ children => cases children
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | pair owned first second =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      simp at notPair
  | pairLeftFault owned child =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      simp at notPair
  | pairRightFault owned first failed =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      simp at notPair
  | tupleValue owned children pack =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      exact ⟨_, _, Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp)), children, .values pack⟩
  | tupleFault owned children =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      exact ⟨_, _, Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp)), children, .fault _⟩
  | indexBaseFault owned _ | indexKeyFault owned _ _ | indexResult owned _ _ _ | builtinArgumentsFault owned _ | builtinApplied owned _ _ | directArgumentsFault owned _ _ | directApplied owned _ _ _ _ _
  | constructorValue owned _ _ | constructorFault owned _
  | group owned _
  | unaryMethod owned _ _ _ _ _ _ _ _ _ | binaryMethod owned _ _ _ _ _ _ _ _ _ _ _
  | unary owned _ _ | unaryOperandFault owned _ | unaryInvalid owned _ _
  | binaryLeftFault owned _ | binaryLeftInvalid owned _ _
  | binaryShortCircuit owned _ _ | binaryRightFault owned _ _ _
  | binary owned _ _ _ _ | binaryInvalid owned _ _ _ _
  | conditional owned _ _ | conditionalFault owned _
  | calleeFault owned _ | notCallable owned _ _ | rejected owned _ _
  | argumentsFault owned _ _ _ | sourceArity owned _ _ _ _
  | applied owned _ _ _ _ _ _ =>
      have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
      cases impossible

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "valuesContext" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues (model := valueModel) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include unique selectedBodies runtime covers in
private theorem nonpair_preserves {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {children : GenericExpressionMeaning.Certificate}
    (header : CompatibleExpressionTuples.Header valuesContext invocation.source id node ids types codes)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids types codes)
    (notPair : ids.length ≠ 2) (size : Nat)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation children faults size) :
    PreservesAt (attachment := attachment) bridge context valueModel index registry invocation
      (Point scope id (SourceCoreCalls.packArguments codes)) faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨originalTypes, typing, _sourceType⟩ := CompatibleExpressionTuples.source_types
    unique header.metadata.found header.form header.metadata.coercions typed
  obtain ⟨childSize, sourceOutcome, within, childTrace, packed⟩ :=
    source_sequence header.metadata header.form unique notPair trace
  cases packed with
  | @values sources sourceValue sourcePack =>
      obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, relatedValues, finalHeaps,
          maps, worlds, frame, metadata, effect, reached, related, _post⟩ :=
        CellAwareInvocationExpressionSequence.preserves_values bridge size sequence unique typing
          childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childTrace within
      have represented : RecursiveStageArguments.ResultFor valueModel finalMap finalWorld types codes faults
          (.values sources) (.inRight .word (packValues values)) := .values relatedValues
      obtain ⟨result, packed, payload⟩ := RecursiveStageTupleMeaning.sequence_result represented
      have same := (RecursiveStageTupleMeaning.PacksOutcome.values sourcePack).functional packed
      cases same
      refine ⟨_, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame,
        metadata, effect, reached, related, ?_⟩
      · simpa only [header.sourceType, CallableIndexedAmbient.ambientDefinitions] using payload
      · exact SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals typed trace frame
  | fault failure =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
          maps, worlds, frame, metadata, effect, reached, related, _post⟩ :=
        CellAwareInvocationExpressionSequence.preserves_fault bridge size sequence unique typing
          childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame childTrace within
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related,
        SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals typed trace frame⟩

include unique selectedBodies runtime covers in
/-- Ordered tuple preservation consumes only the actual strict Source child
hypothesis. The binary legacy rules use the genuine pair producer. -/
theorem tuple_preserves {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation children faults size) :
    PreservesAt (attachment := attachment) bridge context valueModel index registry invocation
      (CompatibleExpressionTuples.Certificate valuesContext invocation.source children) faults size := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, header, sequence⟩ := certified
  subst lowered
  cases sequence with
  | nil =>
      intro actualNode
      exact nonpair_preserves bridge functions faults unique selectedBodies runtime covers
        header .nil (by simp) size childMeaning ⟨rfl, rfl, rfl⟩
  | single childFound generated =>
      intro actualNode
      exact nonpair_preserves bridge functions faults unique selectedBodies runtime covers
        header (.single childFound generated) (by simp) size childMeaning ⟨rfl, rfl, rfl⟩
  | cons firstFound firstChild tail =>
      cases tail with
      | single secondFound secondChild =>
          intro actualNode
          exact CellAwareInvocationPairBounds.pair_preserves bridge unique (product_values functions) size childMeaning size (Nat.le_refl _)
            (.actual header.metadata header.form firstFound secondFound header.sourceType firstChild secondChild)
      | cons nextFound nextChild rest =>
          intro actualNode
          exact nonpair_preserves bridge functions faults unique selectedBodies runtime covers
            header (.cons firstFound firstChild (.cons nextFound nextChild rest)) (by simp) size
            childMeaning ⟨rfl, rfl, rfl⟩

include unique selectedBodies runtime covers in
/-- Singleton reflection permits the same native child grade. Every branch
retains the exact recursive failure and actual reached caller state. -/
theorem tuple_reflects {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (childMeaning : ReflectsBelow (attachment := attachment) bridge context valueModel index registry invocation children faults (size + 1)) :
    ReflectsAt (attachment := attachment) bridge context valueModel index registry invocation
      (CompatibleExpressionTuples.Certificate valuesContext invocation.source children) faults size := by
  intro scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame completed
  obtain ⟨node, ids, types, codes, emitted, header, sequence⟩ := certified
  subst lowered
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨originalTypes, typing, _sourceType⟩ := CompatibleExpressionTuples.source_types
    unique header.metadata.found header.form header.metadata.coercions typed
  obtain ⟨sourceSize, sourceOutcome, after, finalMap, finalWorld, childTrace, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, _post⟩ :=
    CellAwareInvocationExpressionSequence.reflects bridge (size + 1) sequence unique typing
      childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame completed (Nat.lt_succ_self _)
  obtain ⟨outcome, packed, payload⟩ := RecursiveStageTupleMeaning.sequence_result represented
  have occurrence : Staging.Recursive.Occurrence invocation id (.tuple ids) :=
    ⟨actualNode, lookupExpression?_sound header.metadata.found, header.form,
      header.metadata.requirements, header.metadata.coercions⟩
  have trace : Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [sourceSize])
      invocation context environment before id outcome after := by
    cases packed with
    | values pack => exact .tupleValue occurrence childTrace pack
    | fault failure => exact .tupleFault occurrence childTrace
  refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds, frame,
    metadata, effect, reached, related, ?_⟩
  · simpa only [header.sourceType, CallableIndexedAmbient.ambientDefinitions] using payload
  · exact SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals typed trace frame

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTupleBounds
end

import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.RecursiveStageArguments

/-! Ordered staged arguments are constructed from the actual compiler Tree
and strictly smaller expression results. Each successful child passes its
actual reached caller state to the next child. Both failure tags retain the
same originating scope, token and final state. Native reflection reconstructs
an independent Source grade from the original packed-helper computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence
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
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
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
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (execution : Staging.Recursive.Size.Expressions program registry size invocation context environment
      before ids (.values sources) after) (within : size ≤ budget) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.values sources) reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ sources after with
  | nil =>
      cases execution
      exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial,
        admitted.rows, fun _ _ => admitted⟩
  | single found generated =>
      cases execution with
      | cons head tail =>
          cases tail
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | value payload =>
              exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
                finalHeaps, maps, worlds, frame, metadata, reached, related, post.rows,
                fun _ _ => post.at_value.2⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | cons head rest =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
                  maps, worlds, frame, metadata, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 rest
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
              have nonempty : values ≠ [] := by
                intro absent
                have lengths := restRep.length.2
                simp [absent] at lengths
              refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
                .cons (model.extend payload maps worlds) restRep, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                reached, callerProtocol.trans firstRelated related, post.rows, fun _ _ => post.at_values⟩
              rw [rename_prefix] at second
              have combined := LocalSequence.pair_success lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
              simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

private theorem preserves_fault_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (execution : Staging.Recursive.Size.Expressions program registry size invocation context environment
      before ids (.fault failure) after) (within : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.fault failure) reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ after with
  | nil => cases execution
  | single found generated =>
      cases execution with
      | headFault failed =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted failed
          cases represented with
          | fault matched =>
              exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
                maps, worlds, frame, metadata, reached, related, post.rows, by intro _ impossible; cases impossible⟩
      | tailFault _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | headFault failed =>
          obtain ⟨value, finalStore, finalMap, finalWorld, first, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted failed
          cases represented with
          | fault matched =>
              refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
                maps, worlds, frame, metadata, reached, related, post.rows, by intro _ impossible; cases impossible⟩
              simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first
      | tailFault head failed =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
                  maps, worlds, frame, metadata, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 failed
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
              refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                reached, callerProtocol.trans firstRelated related, post⟩
              rw [rename_prefix] at second
              simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second

/-- Actual list typing supplies each used child's stored type. The successful
prefix retains the same cumulative caller records at every reached state. -/
theorem preserves_values (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ sources},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial → ∀ {size},
    Staging.Recursive.Size.Expressions program registry size invocation context environment before ids (.values sources) after →
    size ≤ budget →
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.values sources) reached :=
  preserves_values_with_members bridge budget tree (member_typing unique typing)

/-- A failing argument stops the original helper at the same reached caller
pool; no later argument runs and neither failure tag is relabeled. -/
theorem preserves_fault (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ failure},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial → ∀ {size},
    Staging.Recursive.Size.Expressions program registry size invocation context environment before ids (.fault failure) after →
    size ≤ budget →
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.fault failure) reached :=
  preserves_fault_with_members bridge budget tree (member_typing unique typing)

private theorem reflects_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
      value finalStore) (within : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expressions program registry sourceSize invocation context environment before ids outcome after ∧
      RecursiveStageArguments.ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) outcome reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ value finalStore with
  | nil =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (show Evaluates actual store
        ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
      exact ⟨_, .values [], before, mapping, world, .nil, .values (values := []) .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial,
        admitted.rows, fun _ _ => admitted⟩
  | single found generated =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post⟩ :=
        children _ within generated found (sourceTyped _ (by simp) _ found)
          environments heaps locals layout actualTyped initial admitted evaluated
      cases represented with
      | value payload =>
          exact ⟨_, .values [_], after, finalMap, finalWorld, .cons trace .nil,
            .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata,
            reached, related, post.rows, fun _ _ => post.at_value.2⟩
      | fault matched =>
          exact ⟨_, .fault _, after, finalMap, finalWorld, .headFault trace,
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
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
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (by omega) generated found (sourceTyped _ (by simp) _ found)
              environments heaps locals layout actualTyped initial admitted first
          cases represented with
          | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                (LocalSequence.pair_left_failure lowered.type
                  (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound)
              exact ⟨_, .fault _, after, finalMap, finalWorld, .headFault trace, .fault matched,
                finalHeaps, maps, worlds, frame, metadata, reached, related, post.rows,
                by intro _ impossible; cases impossible⟩
      | caseRight first continuation =>
          obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ (by omega) generated found (sourceTyped _ (by simp) _ found)
              environments heaps locals layout actualTyped initial admitted first
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
                      maps, worlds, frame, metadata, reached, related, post⟩ :=
                    ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata) nextLayout
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 shifted (by omega)
                  cases result with
                  | fault matched =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_right_failure lowered.type
                          (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                      exact ⟨_, .fault _, after, finalMap, finalWorld, .tailFault firstTrace tailTrace, .fault matched,
                        finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                        firstFrame.trans frame, firstMetadata.trans metadata,
                        reached, callerProtocol.trans firstRelated related, post⟩
              | caseRight second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, tailTrace, result, finalHeaps,
                      maps, worlds, frame, metadata, reached, related, post⟩ :=
                    ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata) nextLayout
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 shifted (by omega)
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
                        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                        reached, callerProtocol.trans firstRelated related, post.rows, fun _ _ => post.at_values⟩
                      simpa [packValues, nonempty] using
                        RecursiveStageArguments.ResultFor.values (codes := lowered :: nextCode :: codes)
                          (.cons (model.extend payload maps worlds) restRep)

/-- Original packed-helper inversion supplies strict native child bounds.
Each reflected Source child contributes its own independent list grade. -/
theorem reflects (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before store finalStore ξ value},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial → ∀ {size},
    EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore →
    size < budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expressions program registry sourceSize invocation context environment before ids outcome after ∧
      RecursiveStageArguments.ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) outcome reached :=
  reflects_with_members bridge budget tree (member_typing unique typing)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence

import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxyMeaning
import Solcore.SourceSemantics.Staging.RecursiveAtomicLifting
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StagedProjected
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StatementAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementHead
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.AssignmentHeads

/-!
# Admitted staged profile: assignments

Bare and projected assignment heads in both directions, typed expression sequences and proxy bounds.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProxyBounds
/-! A proxy leaf keeps its original raw type header, both heaps and the actual
caller. Its compiler receipt supplies all native and Source behavior. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProxyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CompatibleExpressionProxies
universe u

private theorem no_stage
    {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {size : Nat}
    {inner : TypeSystem.Ty} {failedScope call reason}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .proxy inner) (empty : node.coercions = [])
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      before id (.fault (.stage failedScope call reason)) after) : False := by
  have occurrence_form : ∀ {actual requirements},
      Staging.Recursive.Occurrence invocation id actual requirements → actual = .proxy inner := by
    intro actual requirements occurrence
    obtain ⟨actualNode, contains, sameForm, _requirements, _coercions⟩ := occurrence
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    exact sameForm.symm.trans form
  cases trace with
  | generalizedLocal contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found empty contains)
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _
  | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _
  | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _ | group occurrence _
  | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _ | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _
  | applied occurrence _ _ _ _ _ _ => cases occurrence_form occurrence

variable {values : SourceCoreCompatibleValues.Context} {rawRegistry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry rawRegistry)
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  (unique : NodeOccurrencesUnique invocation.source)
  (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel values.checked rawRegistry functions

include extension unique in
theorem preserves (size : Nat) :
    PreservesAt bridge context model registry invocation
      (Certificate values invocation.source) faults size := by
  intro scope id lowered certificate node found typed
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  cases certificate with
  | @proxy other inner owner header receipt =>
    cases Option.some.inj (receipt.metadata.found.symm.trans found)
    have unchanged : outcome = .value (.proxy inner) ∧ after = before := by
      cases outcome with
      | value value =>
        obtain ⟨same, heap⟩ := receipt.source_outcome unique (.value trace.sound.value_plain)
        exact ⟨congrArg Staging.Recursive.Outcome.value (Dynamic.ExpressionOutcome.value.inj same), heap⟩
      | fault failure =>
        cases failure with
        | semantic reason =>
          obtain ⟨impossible, _⟩ := receipt.source_outcome unique (.fault trace.sound.semanticFault_plain)
          cases impossible
        | stage failedScope call reason =>
          exact False.elim (no_stage unique found receipt.form receipt.metadata.coercions trace)
    obtain ⟨rfl, rfl⟩ := unchanged
    refine ⟨.inRight .word (.constructed ⟨owner, 0⟩ (.word header)), store, mapping, world,
      receipt.native_evaluates actual store ξ, .value (receipt.represents functions extension mapping world),
      heaps, .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, ?_⟩
    exact ⟨admitted.rows, by
      intro result same
      cases same
      exact ⟨by rw [receipt.sourceType]; exact .proxy inner, admitted.heap⟩⟩

include extension in
theorem reflects (size : Nat) :
    ReflectsAt bridge context model registry invocation
      (Certificate values invocation.source) faults size := by
  intro scope id lowered certificate node found typed
    mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  cases certificate with
  | @proxy other inner owner header receipt =>
    cases Option.some.inj (receipt.metadata.found.symm.trans found)
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic (receipt.native_evaluates actual store ξ) completed.sound
    have sourceTrace : Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [])
        invocation context environment before id (.value (.proxy inner)) before :=
      .atomicValue (lookupExpression?_sound found) (by rw [receipt.form]; exact .proxy inner)
        receipt.metadata.coercions (by rw [receipt.form, receipt.metadata.requirements]; exact .proxy rfl)
    refine ⟨Staging.Recursive.Size.stepSize [], .value (.proxy inner), before, mapping, world,
      sourceTrace, .value (receipt.represents functions extension mapping world), heaps,
      .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, ?_⟩
    exact ⟨admitted.rows, by
      intro result same
      cases same
      exact ⟨by rw [receipt.sourceType]; exact .proxy inner, admitted.heap⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProxyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTypedExpressionSequence
/-! Ordered staged argument conversion retains the original value types at
its actual final heap. Successful prefixes transport these types through each
later child's metadata-preserving heap change. Faults retain their exact tag,
heap and caller state without a successful value-typing obligation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTypedExpressionSequence
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

open CallableIndexedOwnedAdmittedStagedExpressionSequence (PostAdmission)

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
      Dynamic.ValuesHaveTypes context after sources sourceTypes ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.values sources) reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ sources after with
  | nil =>
      cases execution
      exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, .nil, initial, callerProtocol.refl initial,
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
                finalHeaps, maps, worlds, frame, metadata, .cons post.at_value.1 .nil, reached, related, post.rows,
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
                  maps, worlds, frame, metadata, restTyped, reached, related, post⟩ :=
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
      Dynamic.ValuesHaveTypes context after sources sourceTypes ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) (.values sources) reached :=
  preserves_values_with_members bridge budget tree (member_typing unique typing)

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
      (∀ sources, outcome = .values sources → Dynamic.ValuesHaveTypes context after sources sourceTypes) ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) outcome reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ value finalStore with
  | nil =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (show Evaluates actual store
        ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
      exact ⟨_, .values [], before, mapping, world, .nil, .values (values := []) .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, (by intro values eq; cases eq; exact .nil), initial, callerProtocol.refl initial,
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
            (by intro values eq; cases eq; exact .cons post.at_value.1 .nil), reached, related, post.rows, fun _ _ => post.at_value.2⟩
      | fault matched =>
          exact ⟨_, .fault _, after, finalMap, finalWorld, .headFault trace,
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
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
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (by omega) generated found (sourceTyped _ (by simp) _ found)
              environments heaps locals layout actualTyped initial admitted first
          cases represented with
          | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                (LocalSequence.pair_left_failure lowered.type
                  (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound)
              exact ⟨_, .fault _, after, finalMap, finalWorld, .headFault trace, .fault matched,
                finalHeaps, maps, worlds, frame, metadata, (by intro values eq; cases eq), reached, related, post.rows,
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
                      maps, worlds, frame, metadata, restTyped, reached, related, post⟩ :=
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
                        (by intro values eq; cases eq), reached, callerProtocol.trans firstRelated related, post⟩
              | caseRight second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, tailTrace, result, finalHeaps,
                      maps, worlds, frame, metadata, restTyped, reached, related, post⟩ :=
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
                        (by intro values eq; cases eq; exact .cons (Dynamic.ValueHasType.mono metadata firstPost.at_value.1) (restTyped _ rfl)), reached, callerProtocol.trans firstRelated related, post.rows, fun _ _ => post.at_values⟩
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
      (∀ sources, outcome = .values sources → Dynamic.ValuesHaveTypes context after sources sourceTypes) ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge (context := context) outcome reached :=
  reflects_with_members bridge budget tree (member_typing unique typing)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTypedExpressionSequence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
/-! Projected assignment heads run the ordered staged key row and the RHS at
their actual reached callers. A successful write keeps the saved target path,
the latest root and all compiler temporary slots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Rhs
variable {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {before targetHeap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
  {leaf : TypeSystem.Ty} {target : Dynamic.ResolvedPlace}
  (resolution : CompatiblePlaceResolution.Execution values.checked registry functions prepared
    (CompatibleRenamedPlace.renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before targetHeap)

structure RhsResult (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) (value : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop where
  trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap id outcome after
  evaluated : Evaluates
    (DataPlaceExecution.snapshotEnvironment prepared.route.rootType resolution.target (DataPatternValues.packValues resolution.values)
      (.inRight .unit resolution.snapshot) actual)
    resolution.store (shift 3 (lowered.expression.rename ξ)) value finalStore
  represented : RecursiveStageMeaning.ResultRepresentsFor (payloadModel values.checked registry functions)
    finalMap finalWorld node.type lowered.type faults outcome value
  heaps : HeapRepresents values.checked registry functions finalMap finalWorld after finalStore
  maps : LocationMap.Extends resolution.mapping finalMap
  worlds : WorldExtends resolution.world finalWorld
  frame : AdministrativePreserved resolution.mapping resolution.store finalMap finalStore
  metadata : Dynamic.HeapMetadataExtend targetHeap after
  sourcePost : ∀ right, outcome = .value right →
    Dynamic.ValueHasType context after right node.type ∧ Dynamic.HeapWellTyped context after

theorem rhs_preserves_at (size : Nat)
    (meaning : PreservesAt bridge context (payloadModel values.checked registry functions) stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
      resolution.mapping resolution.world administrativeContext scope environment canonical)
    (heaps : HeapRepresents values.checked registry functions resolution.mapping resolution.world targetHeap resolution.store)
    (locals : Dynamic.EnvironmentAgrees targetHeap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (admitted : Admission bridge context initial)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment targetHeap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      RhsResult (values := values) (environment := environment) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        resolution size outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, DataPatternValues.packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target])
      (ProtectedPlaceRhs.snapshot_runtimeTyped resolution actualTyped) initial admitted trace
  refine ⟨value, finalStore, finalMap, finalWorld,
    ⟨trace, ?_, represented, finalHeaps, maps, worlds, frame, metadata, ?_⟩, reached, related⟩
  · simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
    DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated
  · intro right same
    cases same
    exact ⟨post.at_value.1, post.at_value.2.heap⟩

theorem rhs_reflects_at (size : Nat)
    (meaning : ReflectsAt bridge context (payloadModel values.checked registry functions) stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
      resolution.mapping resolution.world administrativeContext scope environment canonical)
    (heaps : HeapRepresents values.checked registry functions resolution.mapping resolution.world targetHeap resolution.store)
    (locals : Dynamic.EnvironmentAgrees targetHeap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (admitted : Admission bridge context initial)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size
      (DataPlaceExecution.snapshotEnvironment prepared.route.rootType resolution.target (DataPatternValues.packValues resolution.values) (.inRight .unit resolution.snapshot) actual)
      resolution.store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RhsResult (values := values) (environment := environment) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        resolution sourceSize outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, DataPatternValues.packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target])
      (ProtectedPlaceRhs.snapshot_runtimeTyped resolution actualTyped) initial admitted
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
        DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld,
    ⟨trace, evaluated.sound, represented, finalHeaps, maps, worlds, frame, metadata, by
      intro right same
      cases same
      exact ⟨post.at_value.1, post.at_value.2.heap⟩⟩, reached, related⟩
end Rhs

theorem tree_typed {source : TypedSource} {context : SourceSemantics.Context}
    {certificate : Certificate} {scope : Scope} {ids : List ExpressionId} {types original : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope ids types codes)
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids original) :
    ExpressionsHaveTypes source context ids types := by
  have members : ∀ id, id ∈ ids → ∀ node, source.lookupExpression? id = some node → ExpressionHasType source context id node.type :=
    fun _ member _ found => CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typed member found
  clear typed
  induction tree with
  | nil => exact .nil _
  | single found _ => exact .cons (members _ (by simp) _ found) (.nil _)
  | cons found _ _ ih =>
      exact .cons (members _ (by simp) _ found) (ih (fun id member => members id (List.mem_cons_of_mem _ member)))

inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (context : SourceSemantics.Context) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (faults : RecursiveStageMeaning.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | keyFault {keySize : Nat} {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target)
      (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | getterFault {keySize : Nat} {sources : List Dynamic.Value} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) after)
      (failed : Staging.Recursive.ProjectedTarget.GetterFault environment before after assignment.target sources reason)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic reason) token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | rhsFault {keySize sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      {sources : List Dynamic.Value} {targetHeap : Dynamic.Heap}
      (keys : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) targetHeap)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before targetHeap assignment.target sources target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap rhs (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | writeFault {keySize sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {right : Dynamic.Value} {after : Dynamic.Heap}
      {token : Word}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      {sources : List Dynamic.Value} {targetHeap : Dynamic.Heap}
      (keys : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) targetHeap)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before targetHeap assignment.target sources target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap rhs (.value right) after)
      {reason : Dynamic.SemanticFault}
      (failed : Staging.Recursive.ProjectedTarget.WriteFault operator target right after reason)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic reason) token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | success {keySize sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace}
      {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      {sources : List Dynamic.Value} {targetHeap : Dynamic.Heap}
      (keys : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) targetHeap)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before targetHeap assignment.target sources target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap rhs (.value right) middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
        middle target updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentPreservation
/-! The actual staged key row and RHS produce the physical write and its
reached admission. Structural faults retain their actual diagnostic phase. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Rhs
variable {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {before targetHeap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
  {leaf : TypeSystem.Ty} {target : Dynamic.ResolvedPlace}
  (resolution : CompatiblePlaceResolution.Execution values.checked registry functions prepared
    (CompatibleRenamedPlace.renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before targetHeap)


/-- Only an actual successful staged RHS is erased to the ordinary suffix
receipt. Its current root is read from the actual represented RHS heap. -/
theorem RhsResult.to_ordinary_value {size : Nat} {right : Dynamic.Value} {after : Dynamic.Heap}
    {native : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : RhsResult (values := values) (program := program) (context := context) (stages := stages)
      (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
      (environment := environment) resolution size (.value right) after native finalStore finalMap finalWorld) :
    CompatiblePlaceRhs.Result (program := program) (context := context)
      (evidence := invocation.evidence) (source := invocation.source)
      (faults := fun reason token => faults (.semantic reason) token)
      resolution id node (renamed lowered ξ) environment (.value right) after native finalStore finalMap finalWorld := by
  refine ⟨.value result.trace.sound.value_plain, result.evaluated, ?_, result.heaps,
    result.maps, result.worlds, result.frame, result.metadata, ?_⟩
  · cases result.represented with
    | value related => exact .value related
  · obtain ⟨cell, read, sameType, _⟩ := result.metadata _ _ resolution.currentRead
    have reference := resolution.reference.extend result.maps result.worlds
    obtain ⟨optional, nativeRead, represented⟩ := CompatibleHeap.HeapRepresents.read_at result.heaps reference read
    exact ⟨⟨cell, optional, read, sameType.trans resolution.currentType, reference, nativeRead, represented⟩⟩
end Rhs

section Resolution
variable {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {faults : RecursiveStageMeaning.FaultRep} {scope : Scope}
  {site : SourceCoreElaboration.ErrorSite} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {rhsType : Core.Ty} {administrative actualContext : Core.Context} {ξ : Renaming}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before getter : Dynamic.Heap} {store : Store} {index : Nat}
  {target : Dynamic.ResolvedPlace} {sources : List Dynamic.Value}

/-- The independent ordered key trace determines the getter state before any
RHS execution. The original key value types and deep heap typing are retained. -/
theorem preserves_keys (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) values invocation.source
      certificate scope site place prepared codes sourceTypes leaf administrative rhsType)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical)
    (heaps : HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (unique : NodeOccurrencesUnique invocation.source)
    {originalTypes : List TypeSystem.Ty}
    (originalKeyTyped : ExpressionsHaveTypes invocation.source context (DataPlaceKeyOrder.sourceKeys place.projections) originalTypes)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (writable : WritableLocal context place.root prepared.route.rootSourceType)
    {keySize : Nat}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection}
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (ordered : Staging.Recursive.ProjectedTarget.Values place.projections sources resolved) :
    ∃ execution : CompatiblePlaceTargetKeys.Execution values.checked registry functions prepared place
      (renamedCodes codes ξ) sourceTypes location resolved actual before getter store mapping world (ξ index),
      Dynamic.ValuesHaveTypes context getter sources sourceTypes ∧ Dynamic.HeapWellTyped context getter ∧
      ∃ reached : callerProtocol.State ⟨scope, execution.keyMap, execution.keyWorld, getter, execution.keyStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  obtain ⟨native, keyStore, keyMap, keyWorld, evaluated, represented, keyHeaps,
    maps, worlds, frame, metadata, typed, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedTypedExpressionSequence.preserves_values bridge budget
      layout.children unique originalKeyTyped meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) actualTyped) initial admitted
      (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTrace) keyBound
  obtain ⟨scheme, staticLookup, _wellFormed, _monomorphic, bodyEq⟩ := writable.scheme
  obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
  cases lookup.functional staticLookupRuntime
  cases initialRead.functional staticRead
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ initialRead
  refine ⟨⟨target, sources, native, keyStore, keyMap, keyWorld, cell, read,
    sameType.trans (staticCellType.trans bodyEq), reference.extend maps worlds, agrees selected,
    ordered.to_data, ?_, ?_, keyHeaps, maps, worlds, frame, metadata⟩,
    typed, post.at_values.heap, reached, related, post.at_values⟩
  · simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated
  · simpa only [renamedCodes_types] using represented

theorem preserves_resolution (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) values invocation.source
      certificate scope site place prepared codes sourceTypes leaf administrative rhsType)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (extension : SourceCoreRawMetadata.Extends values.registry registry)
    (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations values.checked.catalog functions identities)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical)
    (heaps : HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (unique : NodeOccurrencesUnique invocation.source)
    {originalTypes : List TypeSystem.Ty}
    (originalKeyTyped : ExpressionsHaveTypes invocation.source context (DataPlaceKeyOrder.sourceKeys place.projections) originalTypes)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (writable : WritableLocal context place.root prepared.route.rootSourceType)
    {keySize : Nat}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys place.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter place sources target) :
    ∃ resolution : CompatiblePlaceResolution.Execution values.checked registry functions prepared
      (renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before getter,
      resolution.sources = sources ∧ Dynamic.ValuesHaveTypes context getter sources sourceTypes ∧
      Dynamic.HeapWellTyped context getter ∧
      actual[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target) ∧
      ∃ reached : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, getter, resolution.store, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, reached, related⟩ :=
    ProtectedStagedProjectedResolution.preserves layout.path layout.views layout.keyTypes layout.leafProjected
      layout.virtual extension layout.nonempty
      (CompatibleRenamedPlace.getter_typed layout (CompatibleRenamedPlace.virtual_closed layout ordinary)
        (CompatibleRenamedPlace.environment_respects environments.runtime_hasTypes actualTyped agrees))
      callerProtocol transport faithful observations environments locals agrees actualTyped initial
      (fun target _ hiddenTyped => by
        obtain ⟨native, keyStore, keyMap, keyWorld, evaluated, represented, keyHeaps,
          maps, worlds, frame, metadata, typed, reached, related, post⟩ :=
          CallableIndexedOwnedAdmittedStagedTypedExpressionSequence.preserves_values bridge budget
            layout.children unique originalKeyTyped meaning environments heaps locals
            (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
            hiddenTyped initial admitted
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTrace) keyBound
        exact ⟨native, keyStore, keyMap, keyWorld, evaluated, represented, keyHeaps, maps, worlds,
          frame, metadata, typed, post.at_values.heap, reached, related⟩)
      slot writable snapshot
  exact ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, reached, related, keyHeap,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows resolution.frame⟩
end Resolution

section Heads
variable {values : SourceCoreCompatibleValues.Context}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values invocation.source context certificate scope administrative ambient.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)


include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected faithful observations in
theorem preserves_value (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    {keySize rhsSize : Nat} {sources : List Dynamic.Value}
    {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value} {getter middle after : Dynamic.Heap}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter assignment.target sources target)
    (trace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment getter rhs (.value right) middle)
    (rhsBound : rhsSize < budget)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | projected layout ordinary =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    have keyTyped := tree_typed layout.children unique originalKeyTyped
    obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, resolutionState, resolutionRelated, resolutionAdmission⟩ :=
      preserves_resolution bridge budget layout ordinary extension transport faithful observations
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        slot writable keyTrace keyBound snapshot
    obtain ⟨native, rhsStore, rhsMap, rhsWorld, rhsResult, rhsPost⟩ :=
      rhs_preserves_at bridge resolution rhsSize (meaning rhsSize rhsBound) generated found sourceTyped
        (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
        agrees actualTyped resolutionState resolutionAdmission trace
    cases represented : rhsResult.represented with
    | value payload =>
      have ordinaryRhs := rhsResult.to_ordinary_value
      obtain ⟨updatedValue, finalStore, finalMap, finalWorld, _root, finalHeaps, maps, worlds, frame, metadata,
          slots, count, typed, agreement, reached, related⟩ :=
        ProtectedStagedProjectedCommit.preserves layout ordinary extension callerProtocol transport faithful observations
          generated found rightView rightType profile environments heaps agrees actualTyped initial resolution coreLookup
          resolutionState resolutionRelated ordinaryRhs rhsPost write invalid
      refine ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata,
        count, ?_, ⟨reached, related, ?_, ?_⟩, agreement⟩
      · simpa only [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext,
          ProtectedPlaceAssignmentSuccess.writtenContext] using typed
      · exact CallableIndexedOwnedStagedProjectedAssignmentAdmission.heap_after_assignment unique found assignmentTyped
          locals (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keyTyped)
          keyValues keyHeap resolution.metadata snapshot (rhsResult.sourcePost _ rfl).2
          (rhsResult.sourcePost _ rfl).1 rhsResult.metadata write
      · exact StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame

include environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected in
/-- A failed key row stops before the getter and RHS. -/
theorem preserves_key_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    {keySize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target)
    (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.fault failure) after)
    (bounded : keySize ≤ budget) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | projected layout ordinary =>
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    cases ready with
    | intro lookup read =>
      obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
        CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_fault bridge budget layout.children unique originalKeyTyped
          meaning environments heaps locals
          (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
          (.cons (.cellRef reference.typed) actualTyped) initial admitted
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using trace) bounded
      refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata,
        reached, related, post.rows⟩
      change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
        next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
      rw [execute_rename layout.path (virtual_closed layout ordinary)]
      simp only [renamed_packed, Expr.rename]
      unfold execute
      simp only [packed_renamed_type]
      apply Evaluates.letE (.var (agrees selected))
      apply LanguageResult.bind_failure
      simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected faithful observations in
/-- A successful key row and getter precede the actual staged RHS fault. -/
theorem preserves_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    {keySize rhsSize : Nat} {sources : List Dynamic.Value} {target : Dynamic.ResolvedPlace}
    {failure : Staging.Recursive.Failure} {getter after : Dynamic.Heap}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter assignment.target sources target)
    (trace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment getter rhs (.fault failure) after)
    (rhsBound : rhsSize < budget) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | projected layout ordinary =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, resolutionState, resolutionRelated, resolutionAdmission⟩ :=
      preserves_resolution bridge budget layout ordinary extension transport faithful observations
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        slot writable keyTrace keyBound snapshot
    obtain ⟨native, rhsStore, rhsMap, rhsWorld, rhsResult, rhsState, rhsRelated⟩ :=
      rhs_preserves_at bridge resolution rhsSize (meaning rhsSize rhsBound) generated found sourceTyped
        (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
        agrees actualTyped resolutionState resolutionAdmission trace
    cases represented : rhsResult.represented with
    | fault matched =>
      refine ⟨_, rhsStore, rhsMap, rhsWorld, ?_, matched, rhsResult.heaps,
        resolution.maps.trans rhsResult.maps, resolution.worlds.trans rhsResult.worlds,
        resolution.frame.trans rhsResult.frame, resolution.metadata.trans rhsResult.metadata,
        rhsState, callerProtocol.trans resolutionRelated rhsRelated,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool rhsState) admitted.rows (resolution.frame.trans rhsResult.frame)⟩
      change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
        next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
      rw [execute_rename layout.path (virtual_closed layout ordinary)]
      simp only [renamed_packed, Expr.rename]
      unfold execute
      simp only [packed_renamed_type]
      have snapshotEvaluated := resolution.snapshotEvaluated
      simp only [packed_renamed_type] at snapshotEvaluated
      exact .letE (.var coreLookup) (LanguageResult.bind_success _ resolution.keysEvaluated
        (LanguageResult.bind_success _ snapshotEvaluated (LanguageResult.bind_failure _ rhsResult.evaluated)))


include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected faithful observations in
/-- Getter faults preserve the original reached diagnostic witness. -/
theorem preserves_getter_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol invocation.source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial
      (fun reason token => faults (.semantic reason) token) head.shape)
    {keySize : Nat} {sources : List Dynamic.Value} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) after)
    (bounded : keySize ≤ budget)
    (failed : Staging.Recursive.ProjectedTarget.GetterFault environment before after assignment.target sources reason)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults (.semantic reason) token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol invocation.source context certificate
    scope administrative environment assignment.target prepared operator invalid initial
    (fun reason token => faults (.semantic reason) token) shape at errors
  cases errors with
  | @bare empty _ _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary missing uninitialized =>
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    cases failed with
    | dangling lookup initialRead ordered absent =>
      obtain ⟨execution, _, _, reached, related, post⟩ := preserves_keys bridge budget layout
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        slot writable trace bounded lookup initialRead ordered
      exact (absent.excludes_read execution.read).elim
    | projection lookup initialRead ordered currentRead initialValue fault =>
      obtain ⟨execution, _, _, keyState, keyRelated, _post⟩ := preserves_keys bridge budget layout
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        slot writable trace bounded lookup initialRead ordered
      obtain ⟨token, count, root, finalStore, finalMap, finalWorld, _sourceFault, _initial, _receipt,
          evaluated, finalHeaps, maps, worlds, frame, metadata, reached, related, diagnostic⟩ :=
        ProtectedStagedProjectedFaults.preserves_projection layout ordinary callerProtocol transport
          environments agrees actualTyped initial execution ⟨keyState, keyRelated⟩ lookup initialRead
          (ordered.evaluates (ProtectedStagedProjectedPrefix.values_plain trace)) currentRead extension faithful observations
          initialValue fault operator rhs (lowered.expression.rename ξ) (next.rename ξ) output invalid
      refine ⟨token, finalStore, finalMap, finalWorld, ?_, missing reached related diagnostic,
        finalHeaps, maps, worlds, frame, metadata, reached, related,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
      change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
        next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
      simpa only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename] using evaluated
    | uninitialized lookup initialRead ordered currentRead empty notMapping nonempty =>
      obtain ⟨execution, _, _, keyState, keyRelated, _post⟩ := preserves_keys bridge budget layout
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        slot writable trace bounded lookup initialRead ordered
      obtain ⟨finalStore, finalMap, finalWorld, _sourceFault, evaluated, finalHeaps, maps, worlds,
          frame, metadata, reached, related, diagnostic⟩ :=
        ProtectedStagedProjectedFaults.preserves_uninitialized layout callerProtocol initial execution ⟨keyState, keyRelated⟩
          lookup initialRead (ordered.evaluates (ProtectedStagedProjectedPrefix.values_plain trace)) currentRead
          ordinary empty notMapping nonempty operator rhs (lowered.expression.rename ξ) (next.rename ξ) output invalid
      refine ⟨prepared.invalidProjection, finalStore, finalMap, finalWorld, ?_, uninitialized reached related diagnostic,
        finalHeaps, maps, worlds, frame, metadata, reached, related,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
      change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
        next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
      simpa only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename] using evaluated


include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected faithful observations in
/-- Structural write failure is checked against the latest root after the
successful RHS. Represented initialized scalar operands cannot create an
additional operand fault in this projected profile. -/
theorem preserves_write_fault (budget : Nat)
    (meaning : PreservesBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol invocation.source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial
      (fun reason token => faults (.semantic reason) token) head.shape)
    {keySize rhsSize : Nat} {sources : List Dynamic.Value} {target : Dynamic.ResolvedPlace}
    {right : Dynamic.Value} {reason : Dynamic.SemanticFault} {getter after : Dynamic.Heap}
    (keyTrace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
      (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) getter)
    (keyBound : keySize ≤ budget)
    (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before getter assignment.target sources target)
    (trace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment getter rhs (.value right) after)
    (rhsBound : rhsSize < budget)
    (failed : Staging.Recursive.ProjectedTarget.WriteFault operator target right after reason)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults (.semantic reason) token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol invocation.source context certificate
    scope administrative environment assignment.target prepared operator invalid initial
    (fun reason token => faults (.semantic reason) token) shape at errors
  cases errors with
  | @bare empty _ _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary missing uninitialized =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    obtain ⟨resolution, sameSources, keyValues, keyHeap, coreLookup, resolutionState, resolutionRelated, resolutionAdmission⟩ :=
      preserves_resolution bridge budget layout ordinary extension transport faithful observations
        environments heaps locals agrees actualTyped initial admitted unique originalKeyTyped meaning
        slot writable keyTrace keyBound snapshot
    obtain ⟨native, rhsStore, rhsMap, rhsWorld, rhsResult, rhsPost⟩ :=
      rhs_preserves_at bridge resolution rhsSize (meaning rhsSize rhsBound) generated found sourceTyped
        (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
        agrees actualTyped resolutionState resolutionAdmission trace
    cases represented : rhsResult.represented with
    | @value _ native rightRep =>
      have ordinaryRhs := rhsResult.to_ordinary_value
      cases failed with
      | operands read rootType initialValue pathRead invalidOperands =>
        have rightRep : ValueRep values.checked registry functions rhsMap rhsWorld leaf right native prepared.route.leafType :=
          .compatible rightView (by simpa only [payloadModel, renamed, rightType] using rightRep)
        obtain ⟨replacement, replacementValue, replacementRep, applies, evaluated, valid⟩ :=
          CompatiblePlaceModifier.initialized_success observations profile ordinaryRhs.saved_snapshot rightRep
            (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) native actual)
            (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid
        rw [resolution.selectedEq] at invalidOperands
        exact (valid invalidOperands).elim
      | structural read rootType initialValue fault =>
        obtain ⟨token, count, root, finalStore, finalMap, finalWorld, _sourceFault, _initial, _receipt,
            evaluated, finalHeaps, maps, worlds, frame, metadata, reached, related, diagnostic⟩ :=
          ProtectedStagedProjectedFaults.preserves_structural layout ordinary extension callerProtocol transport faithful observations
            generated found rightView rightType profile environments agrees actualTyped initial resolution coreLookup
            resolutionState resolutionRelated ordinaryRhs rhsPost
            (snapshot.resolves (ProtectedStagedProjectedPrefix.values_plain keyTrace)) trace.sound.value_plain
            read rootType initialValue fault (next.rename ξ) output invalid
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, missing reached related diagnostic,
          finalHeaps, maps, worlds, frame, metadata, reached, related,
          StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
        change Evaluates actual store ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression
          next output (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) _ _
        simpa only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename] using evaluated

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentReflection
/-! Native projected writes reconstruct the ordered staged key row and RHS
at their actual reached states. Only successful children are erased for the
existing pure setter; staged faults retain their own tag and endpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPlaceExecution DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Heads
variable {values : SourceCoreCompatibleValues.Context}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values invocation.source context certificate scope administrative ambient.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)

include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped projected observations faithful in
theorem reflects_bounded (budget : Nat)
    (boundedReflection : ReflectsBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (functionTypes : FunctionRuntimeViews functions)
    (errors : ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol invocation.source context certificate
      scope administrative environment assignment.target head.prepared operator head.invalid initial
      (fun reason token => faults (.semantic reason) token) head.shape)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt bridge size values.checked registry functions context stages invocation faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  change ProtectedPlaceReachedDiagnostics.ShapeErrors values registry functions callerProtocol invocation.source context certificate
    scope administrative environment assignment.target prepared operator invalid initial
    (fun reason token => faults (.semantic reason) token) shape at errors
  cases errors with
  | @bare empty _ _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary missing uninitialized =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨type, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
    obtain ⟨originalTypes, keyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
    have keyRow : ExpressionsHaveTypes invocation.source context
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) sourceTypes := by
      simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using tree_typed layout.children unique keyTyped
    have nativeCompleted := completed
    change EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next output
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore at nativeCompleted
    rw [execute_rename layout.path (virtual_closed layout ordinary)] at nativeCompleted
    simp only [renamed_packed, Expr.rename] at nativeCompleted
    have prefixResult := ProtectedStagedProjectedPrefix.reflects_getter budget layout ordinary extension
      callerProtocol transport functionTypes faithful observations environments heaps locals agrees actualTyped initial missing uninitialized
      (by
        intro target _ hiddenTyped keySize keyValue keyStore evaluated smaller
        obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
            frame, metadata, typedValues, reached, related, post⟩ :=
          CallableIndexedOwnedAdmittedStagedTypedExpressionSequence.reflects bridge budget layout.children unique keyTyped
            boundedReflection environments heaps locals
            (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
            hiddenTyped initial admitted evaluated smaller
        refine ⟨sourceSize, outcome, after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds,
          frame, metadata, ?_, reached, related⟩
        · simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using trace
        · intro sources same
          exact ⟨typedValues sources same, (post.successful sources same).heap⟩)
      slot writable nativeCompleted bounded
    cases prefixResult with
    | keyFault ready trace same matched finalHeaps maps worlds frame metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .keyFault ready trace same matched finalHeaps maps worlds frame metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
    | getterFault trace failed same matched finalHeaps maps worlds frame metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .getterFault trace failed same matched finalHeaps maps worlds frame metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
    | resolved resolution keyTrace snapshot keyValues getterHeap prefixBound remaining prefixPost =>
      obtain ⟨getterState, getterRelated⟩ := prefixPost
      have getterAdmission : Admission bridge context getterState :=
        ⟨getterHeap, StableRows.after_administrative (bridge.pool initial) (bridge.pool getterState) admitted.rows resolution.frame⟩
      have reflectRhs := fun {child : Nat} {value : Value} {finalStore : Store}
          (evaluated : EvaluationSize child
            (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) actual) resolution.store (shift 3 (lowered.expression.rename ξ)) value finalStore)
          (smaller : child < budget) =>
        rhs_reflects_at bridge resolution child (boundedReflection child smaller) generated found sourceTyped
          (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
          agrees actualTyped getterState getterAdmission evaluated
      cases remaining with
      | caseLeft evaluated failed =>
        obtain ⟨rhsSize, outcome, after, finalMap, finalWorld, result, rhsPost⟩ := reflectRhs evaluated (by omega)
        cases represented : result.represented with
        | fault matched =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var foundValue =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at foundValue
              subst_vars
              obtain ⟨reached, related⟩ := rhsPost
              exact .rhsFault keyTrace snapshot result.trace rfl matched result.heaps
                (resolution.maps.trans result.maps) (resolution.worlds.trans result.worlds)
                (resolution.frame.trans result.frame) (resolution.metadata.trans result.metadata) reached
                (callerProtocol.trans getterRelated related)
                (StableRows.after_administrative (bridge.pool getterState) (bridge.pool reached) getterAdmission.rows result.frame)
      | caseRight evaluated continuation =>
        rename_i rhsStore rightValue
        obtain ⟨rhsSize, outcome, after, finalMap, finalWorld, result, rhsPost⟩ := reflectRhs evaluated (by omega)
        cases represented : result.represented with
        | @value right _ payload =>
          obtain ⟨rhsState, rhsRelated⟩ := rhsPost
          obtain ⟨rightTyped, middleTyped⟩ := result.sourcePost _ rfl
          obtain ⟨plainRhs, _⟩ := ProtectedPlaceRhs.rhs_of_expression resolution callerProtocol getterState
            (faults := fun reason token => faults (.semantic reason) token)
            (.value result.trace.sound.value_plain) result.evaluated (.value payload)
            result.heaps result.maps result.worlds result.frame result.metadata ⟨rhsState, rhsRelated⟩
          have rightRep : CompatiblePayload.ValueRep values.checked registry functions finalMap finalWorld leaf right rightValue prepared.route.leafType :=
            .compatible rightView (by simpa only [payloadModel, rightType] using payload)
          let rightExecution : CompatiblePlaceRhsReflection.Execution values.checked registry functions program context
              invocation.evidence invocation.source (fun reason token => faults (.semantic reason) token) environment
              prepared (renamedCodes codes ξ) sourceTypes assignment.target leaf _ actual store mapping world before _
              resolution rhs node (renamed lowered ξ) :=
            ⟨right, rightValue, after, _, finalMap, finalWorld, plainRhs, rightRep⟩
          obtain ⟨resolveSize, resolve⟩ := SourceExecutionSize.SourcePlaceResolves.has_size
            (snapshot.resolves (ProtectedStagedProjectedPrefix.values_plain keyTrace))
          obtain ⟨plainRhsSize, plainRhsTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size result.trace.sound.value_plain
          simp only [packed_renamed_type] at continuation
          have tail := ProtectedStagedProjectedTail.reflects callerProtocol transport layout ordinary extension functionTypes faithful observations
            profile environments agrees actualTyped resolve resolution rightExecution plainRhsTrace initial rhsState
            (callerProtocol.trans getterRelated rhsRelated) missing continuation
          cases tail with
          | fault failed same matched finalHeaps maps worlds frame metadata post =>
            obtain ⟨reached, related⟩ := post
            exact .writeFault keyTrace snapshot result.trace failed same matched finalHeaps maps worlds frame metadata reached related
              (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame)
          | committed write finalHeaps maps worlds frame metadata count typed post strict continuation =>
            obtain ⟨reached, related⟩ := post
            exact .success keyTrace snapshot result.trace write finalHeaps maps worlds frame metadata count
              (by simpa only [GenericAssignmentStatements.Head.writtenContext] using typed)
              reached related
              ⟨CallableIndexedOwnedStagedProjectedAssignmentAdmission.heap_after_assignment unique found assignmentTyped locals
                keyRow keyValues getterHeap resolution.metadata snapshot middleTyped rightTyped result.metadata write,
                StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩
              (by omega) continuation

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareAssignmentHeads
/-! Actual bare assignment Heads use the same admitted staged RHS and preserve
its exact reached caller. Source assignment typing establishes admission after
the write; failures keep the precise staged tag and the RHS endpoint. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Rhs
variable {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
  {faults : RecursiveStageMeaning.FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate}
  (snapshot : CompatibleBareAssignment.Snapshot values.checked registry functions prepared place environment actual heap store mapping world (ξ index))

private theorem rhs_preserves_at (size : Nat)
    (meaning : PreservesAt bridge context (payloadModel values.checked registry functions) stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents values.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (admitted : Admission bridge context initial)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      ProtectedStagedBareAssignment.RhsResult (compilation := values) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        snapshot size outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial admitted trace
  refine ⟨value, finalStore, finalMap, finalWorld,
    ⟨trace, ?_, represented, finalHeaps, maps, worlds, frame, metadata, ?_⟩, reached, related⟩
  · simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
    DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated
  · intro right same
    cases same
    exact ⟨post.at_value.1, post.at_value.2.heap⟩

private theorem rhs_reflects_at (size : Nat)
    (meaning : ReflectsAt bridge context (payloadModel values.checked registry functions) stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents values.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (admitted : Admission bridge context initial)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size
      (DataPlaceExecution.snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      ProtectedStagedBareAssignment.RhsResult (compilation := values) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        snapshot sourceSize outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial admitted
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
        DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld,
    ⟨trace, evaluated.sound, represented, finalHeaps, maps, worlds, frame, metadata, by
      intro right same
      cases same
      exact ⟨post.at_value.1, post.at_value.2.heap⟩⟩, reached, related⟩
end Rhs

inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (context : SourceSemantics.Context) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (faults : RecursiveStageMeaning.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | operands {sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {right : Dynamic.Value} {after : Dynamic.Heap} {current : Dynamic.Cell}
      {initialValue selected : Option Dynamic.Value} {token : Word}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) after)
      (currentRead : Dynamic.Heap.Reads after target.location current)
      (rootType : current.type = target.rootType)
      (initialized : Dynamic.RootInitialValue current initialValue)
      (path : Dynamic.ProjectionsRead initialValue target.projections selected)
      (invalid : Dynamic.AssignmentOperandsInvalid operator target.selected right)
      (same : value = .inLeft output (.word token))
      (matched : faults (.semantic (.invalidAssignmentOperands operator)) token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | success {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace}
      {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
        middle target updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore

section Heads
variable {values : SourceCoreCompatibleValues.Context}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values invocation.source context certificate scope administrative ambient.definitions assignment operator rhs)
  (bare : assignment.target.projections = [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)

include extension environments heaps locals agrees bare head in
/-- The accepted writable root and actual represented heap determine the
pre-RHS snapshot; no Source assignment execution is assumed. -/
theorem target_snapshot :
    ∃ target, Staging.Recursive.BareTarget environment before assignment.target target := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    obtain ⟨snapshot⟩ := CompatibleBareAssignment.snapshot_of_heap layout extension environments heaps locals agrees slot writable
    exact ⟨snapshot.resolved, .intro empty snapshot.lookup snapshot.read snapshot.root⟩

include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare in
theorem reflects_bounded (budget : Nat)
    (boundedReflection : ReflectsBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator head.invalid)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt bridge size values.checked registry functions context stages invocation faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    have result := ProtectedStagedBareAssignment.reflects_with_rhs callerProtocol transport budget initial layout empty extension
      (fun snapshot child smaller {_ _} evaluated => rhs_reflects_at bridge snapshot child (boundedReflection child smaller)
        right found sourceTyped environments heaps locals agrees actualTyped initial admitted evaluated)
      rightView rightType (CallableIndexedOwnedBareAssignmentAdmission.source_profile unique found assignmentTyped rightView)
      environments heaps locals agrees actualTyped slot writable invalidToken completed bounded
    cases result with
    | fault snapshot trace same matched finalHeaps maps worlds preservation metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .fault snapshot trace same matched finalHeaps maps worlds preservation metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation)
    | operands snapshot trace currentRead rootType initialized path invalidOperands same matched finalHeaps maps worlds preservation metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .operands snapshot trace currentRead rootType initialized path invalidOperands same matched finalHeaps maps worlds preservation metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation)
    | success snapshot trace rightTyped middleTyped write finalHeaps maps worlds preservation metadata count typed strict remaining post =>
      obtain ⟨reached, related⟩ := post
      exact .success snapshot trace write finalHeaps maps worlds preservation metadata count
        (by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
          Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed)
        reached related ⟨CallableIndexedOwnedBareAssignmentAdmission.heap_after_assignment unique found assignmentTyped
          locals snapshot middleTyped rightTyped write,
          StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation⟩ strict remaining
include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare in
theorem preserves_value {sourceSize : Nat}
    (meaning : PreservesAt bridge context (payloadModel values.checked registry functions) stages invocation certificate faults sourceSize)
    {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
    (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
    (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) middle)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨finalStore, finalMap, finalWorld, slots, rightTyped, middleTyped, finalHeaps, maps, worlds, frame, metadata, count, typed, post, agreement⟩ :=
      ProtectedStagedBareAssignment.preserves_value_with_rhs callerProtocol transport initial layout empty extension snapshot trace write
        (fun snapshot => rhs_preserves_at bridge snapshot sourceSize meaning generated found sourceTyped
          environments heaps locals agrees actualTyped initial admitted trace)
        rightView rightType (CallableIndexedOwnedBareAssignmentAdmission.source_profile unique found assignmentTyped rightView)
        environments heaps locals agrees actualTyped slot writable invalid
    obtain ⟨reached, related⟩ := post
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count,
      by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
        Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed,
      ⟨reached, related, CallableIndexedOwnedBareAssignmentAdmission.heap_after_assignment unique found assignmentTyped
        locals snapshot middleTyped rightTyped write,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩,
      agreement⟩

include extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare in
theorem preserves_fault {sourceSize : Nat}
    (meaning : PreservesAt bridge context (payloadModel values.checked registry functions) stages invocation certificate faults sourceSize)
    {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.fault failure) after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
      ProtectedStagedBareAssignment.preserves_fault_with_rhs callerProtocol initial layout extension
        (fun snapshot => rhs_preserves_at bridge snapshot sourceSize meaning generated found sourceTyped
          environments heaps locals agrees actualTyped initial admitted trace)
        environments heaps locals agrees slot writable next output invalid
    obtain ⟨reached, related⟩ := post
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata,
      reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

include extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare in
theorem preserves_operands {sourceSize : Nat}
    (meaning : PreservesAt bridge context (payloadModel values.checked registry functions) stages invocation certificate faults sourceSize)
    {right : Dynamic.Value} {after : Dynamic.Heap} {target : Dynamic.ResolvedPlace}
    (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
    (invalidOperands : Dynamic.AssignmentOperandsInvalid operator target.selected right)
    (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) after)
    (next : Expr) (output : Ty)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator head.invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults (.semantic (.invalidAssignmentOperands operator)) token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
      ProtectedStagedBareAssignment.preserves_operands_with_rhs callerProtocol initial layout empty extension snapshot invalidOperands
        (fun snapshot => rhs_preserves_at bridge snapshot sourceSize meaning generated found sourceTyped
          environments heaps locals agrees actualTyped initial admitted trace)
        rightView rightType (CallableIndexedOwnedBareAssignmentAdmission.source_profile unique found assignmentTyped rightView)
        environments heaps locals agrees slot writable next output invalid invalidToken
    obtain ⟨reached, related⟩ := post
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata,
      reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareAssignmentHeads
end

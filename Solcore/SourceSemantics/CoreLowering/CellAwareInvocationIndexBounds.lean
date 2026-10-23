import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexOutcomes
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleCellIndexTerminal
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence

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

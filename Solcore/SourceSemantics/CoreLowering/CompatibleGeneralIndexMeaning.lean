import Solcore.SourceSemantics.CoreLowering.IndexFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexTree

/-! Whole finite index trees evaluate base, then key, then the actual generated
comparator. Every child meaning is discharged by structural induction; actual
hidden slots are typed because comparator closures capture those slots. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CompatibleExpressionIndices (index_inv index_intro index_rename)

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include unique in
theorem preserves_with_post {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    (fragment : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionTyped.Tree fuel values source context solved reasonAt) faults post)
    (terminalProvider : IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt (fun _ => True) faults post)
    (joins : IndexFaultPostContracts.IndexJoins post values program context evidence source) :
    ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults post := by
  intro scope id lowered tree
  induction tree with
  | fragment child =>
    exact fragment child
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree firstIH secondIH =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rcases (index_inv header.metadata form unique trace).split with ⟨reason, rfl, failed⟩ | ⟨baseSource, middle, baseTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, childPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, metadata,
          joins.base_outcome header keyFound form sourceType failed childPost⟩
        rw [index_rename comparison header.registered header.comparisonType]
        exact LanguageResult.bind_failure _ evaluated
    · obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped (.value baseTrace)
      cases represented with
      | @value _ baseValue baseRep =>
        have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
        rcases tail with ⟨reason, rfl, failed⟩ | ⟨keySource, keyTrace, terminal⟩
        · obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, metadata, childPost⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (.fault failed)
          cases represented with
          | fault matched =>
            refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
              joins.key_outcome header keyFound form sourceType baseTrace failed childPost⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            exact LanguageResult.bind_success _ firstEval (LanguageResult.bind_failure _ secondEval)
        · obtain ⟨value, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, _keyPost⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (.value keyTrace)
          cases represented with
          | @value _ keyValue keyRep =>
            obtain ⟨actualOutcome, result, finalStore, finalWorld, terminal', related, lookup, finalHeaps, worlds, frame, uniqueResult, _terminalTrace, terminalPost⟩ :=
              terminalProvider header sourceType True.intro (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace keyTrace
            have same := uniqueResult outcome terminal
            subst actualOutcome
            refine ⟨result, finalStore, keyMap, finalWorld, ?_, related, finalHeaps,
              firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
              (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, terminalPost⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            apply SourceCoreCompatibleDataExpressions.index_completed layout (reasonAt id) firstEval secondEval
            simpa only [Transport.expression_weaken] using lookup

theorem reflects_with_post {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    (fragment : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionTyped.Tree fuel values source context solved reasonAt) faults post)
    (terminalProvider : IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt (fun _ => True) faults post)
    (joins : IndexFaultPostContracts.IndexJoins post values program context evidence source) :
    ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults post := by
  intro scope id lowered tree
  induction tree with
  | fragment child =>
    exact fragment child
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree firstIH secondIH =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, childPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure layout.valueType baseEvaluation (body :=
          LanguageResult.bind layout.valueType ((second.expression.rename ξ).weakenAt 0)
            (SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.baseFailure failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
            joins.base_outcome header keyFound form sourceType failed childPost⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨outcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | @value baseSource baseValue baseRep =>
        cases trace with
        | value baseTrace =>
          have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
          cases branch with
          | caseLeft keyEvaluation ignored =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, childPost⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment keyEvaluation
            cases represented with
            | fault matched =>
              rw [rename_prefix] at keyEvaluation
              have expected := LanguageResult.bind_success layout.valueType baseEvaluation
                (LanguageResult.bind_failure layout.valueType keyEvaluation (body :=
                  SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              cases trace with
              | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.keyFailure baseTrace failed),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                  joins.key_outcome header keyFound form sourceType baseTrace failed childPost⟩
          | caseRight keyEvaluation lookupEvaluation =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, keyMap, keyWorld, trace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, _keyPost⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment keyEvaluation
            cases represented with
            | @value keySource keyValue keyRep =>
              cases trace with
              | value keyTrace =>
                obtain ⟨outcome, result, endStore, finalWorld, terminal, related, lookup, finalHeaps, worlds, frame, uniqueResult, _terminalTrace, terminalPost⟩ :=
                  terminalProvider header sourceType True.intro (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                    (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace keyTrace
                rw [rename_prefix] at keyEvaluation
                have expected := SourceCoreCompatibleDataExpressions.index_completed (comparison := comparison.expression) layout (reasonAt id) baseEvaluation keyEvaluation
                  (by simpa only [Transport.expression_weaken] using lookup)
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
                exact ⟨outcome, after, keyMap, finalWorld, index_intro header.metadata form (terminal.trace baseTrace keyTrace),
                    related, finalHeaps, firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
                    (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, terminalPost⟩

include extension faithful functionLeaves functionTypes valid unique uninitialized missing in
theorem preserves :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  exact ExpressionFailurePostContracts.TypedPreserves.forget
    (preserves_with_post (functions := functions) (program := program) (evidence := evidence) (unique := unique)
      (ExpressionFailurePostContracts.TypedPreserves.of_trivial
        (CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing))
      (IndexFaultPostContracts.trivial_general_terminal functions registry program context evidence reasonAt faithful functionLeaves functionTypes missing)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source))

include extension faithful functionLeaves functionTypes valid uninitialized missing in
theorem reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  exact ExpressionFailurePostContracts.TypedReflects.forget
    (reflects_with_post (functions := functions) (program := program) (evidence := evidence)
      (ExpressionFailurePostContracts.TypedReflects.of_trivial
        (CompatibleExpressionTyped.reflects functions extension program evidence valid uninitialized missing))
      (IndexFaultPostContracts.trivial_general_terminal functions registry program context evidence reasonAt faithful functionLeaves functionTypes missing)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source))

end Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex

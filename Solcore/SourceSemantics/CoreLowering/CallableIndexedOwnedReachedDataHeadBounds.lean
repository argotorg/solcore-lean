import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedDataHeadBounds

/-! The original constructor/member/index head preserves and reflects finite
execution with a fault policy selected only at its actual index header and
ordered Source prefixes. Each unavailable lookup keeps its real raw mapping
fields, Source runtime views, final store and caller transition. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedDataHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open CompatibleExpressionIndices CoreProof
open GenericExpressionMeaning (agree_prefix rename_prefix)
open DataPatternValues RecursiveNamedCallBounds RecursiveNamedBoundedContracts
open ProtectedStateExpressionOperandTyping
open CompatibleExpressionCalls (Head CallHeads)
open RecursiveNamedDataExpressionHeadBounds (Certificate)
open RecursiveNamedDataExpressionHeadBounds.Stateful (constructor_preserves_after_sequence constructor_reflects_after_sequence)
open RecursiveNamedDataExpressionHeadBounds.Stateful.WithReady (SequencePreservesFor SequenceReflectsFor)

private theorem missing_excludes {values : List Dynamic.Value} {index : Nat} {value : Dynamic.Value}
    (missing : Dynamic.ValueIndexMissing values index) (selected : Dynamic.ValueAt values index value) : False := by
  induction missing with
  | nil => cases selected
  | tail rest ih => cases selected with | tail child => exact ih child

private theorem at_functional {values : List Dynamic.Value} {index : Nat} {first second : Dynamic.Value}
    (left : Dynamic.ValueAt values index first) (right : Dynamic.ValueAt values index second) : first = second := by
  induction left with
  | head => cases right; rfl
  | tail _ ih => cases right with | tail rest => exact ih rest

variable {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
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
  (missing : IndexFaultPostContracts.MissingPolicies values source functions registry program context evidence reasonAt faults)

universe u v
variable {calls : CallHeads} {certificate : GenericExpressionMeaning.Certificate}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop)

private theorem forget_reached {initial final : ProtectedStateTransition.Index}
    {first : protocol.State initial} {outcome : Dynamic.ExpressionOutcome}
    (post : ProtectedStateTransition.WithReady.Reached protocol ready outcome first final) :
    ProtectedStateTransition.Transition protocol first final := by
  obtain ⟨reached, related, _⟩ := post
  exact ⟨reached, related⟩

include transport extension faithful functionLeaves functionTypes unique missing in
theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (certified : Certificate calls values source context reasonAt certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.PreservesAt protocol ready
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize)
    (sequences : SequencePreservesFor (values := values) (source := source) (context := context)
      (registry := registry) (faults := faults) (certificate := certificate) functions program evidence protocol ready budget scope root) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩, ready initial →
    ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld root.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨head, data⟩ := certified
  cases data with
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨sequenceSize, sourceOutcome, sourceTrace, packed, sequenceSmaller⟩ := RecursiveNamedDataExpressionSourceBounds.constructor_inv receipt.metadata form unique valid trace
    exact constructor_preserves_after_sequence functions extension program evidence protocol (budget + 1) receipt installedEntry
      (sequences (by simp only [form, actualOperandIds]) sequence environments heaps locals agrees actualTyped installedEntry initialReady)
      sourceTrace packed (by omega)

  | @member node base baseNode name index identity branches result child metadata baseMetadata form layout childTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry initialReady trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base]; simp) n bound _ _ _ ⟨rfl, childTree⟩
    have raw := RecursiveNamedDataExpressionSourceBounds.member_inv metadata form unique trace
    cases raw with
    | value childTrace selected childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, sourceChild, native, shape, sourceAt, related, completed⟩ := member_success layout payload evaluated
        cases shape
        have same := at_functional sourceAt selected
        subst sourceChild
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact completed,
          .value related, finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩
    | failure childTrace childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact LanguageResult.bind_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩
    | shape childTrace invalid childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, _⟩ := member_success layout payload evaluated
        subst_vars
        exact False.elim (invalid .intro)
    | position childTrace missing childSmaller =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt childSmaller) bounded) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, selected, _⟩ := member_success layout payload evaluated
        cases shape
        exact False.elim (missing_excludes missing selected)

  | @index node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry initialReady trace
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    have firstIH := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, firstTree⟩
    have secondIH := fun n (bound : n ≤ budget) => @meaning key (by rw [form]; change key ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, secondTree⟩
    rcases (RecursiveNamedDataExpressionSourceBounds.index_inv header.metadata form unique trace).split with ⟨reason, baseSize, rfl, failed, baseSmaller⟩ | ⟨baseSource, middle, baseSize, baseTrace, baseSmaller, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
        firstIH _ (Nat.le_trans (Nat.le_of_lt baseSmaller) bounded) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, metadata, forget_reached protocol ready transition⟩
        rw [index_rename comparison header.registered header.comparisonType]
        exact LanguageResult.bind_failure _ evaluated
    · obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        firstIH _ (Nat.le_trans (Nat.le_of_lt baseSmaller) bounded) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady (.value baseTrace)
      cases represented with
      | @value _ baseValue baseRep =>
        obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
        have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
        rcases tail with ⟨reason, keySize, rfl, failed, keySmaller⟩ | ⟨keySource, keySize, keyTrace, keySmaller, terminal⟩
        · obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
            secondIH _ (Nat.le_trans (Nat.le_of_lt keySmaller) bounded) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) (.fault failed)
          cases represented with
          | fault matched =>
            obtain ⟨finalState, secondRelated, _⟩ := transition
            refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, ⟨finalState, protocol.trans firstRelated secondRelated⟩⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            exact LanguageResult.bind_success _ firstEval (LanguageResult.bind_failure _ secondEval)
        · obtain ⟨value, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, keyTransition⟩ :=
            secondIH _ (Nat.le_trans (Nat.le_of_lt keySmaller) bounded) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) (.value keyTrace)
          cases represented with
          | @value _ keyValue keyRep =>
            obtain ⟨actualOutcome, result, finalStore, finalWorld, terminal', related, lookup, finalHeaps, worlds, frame, uniqueResult, _sourceTrace, _post⟩ :=
              ReachedExpressionPrimitiveOutcomeProviders.general_index_finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace.sound keyTrace.sound (reasonAt id)
                  (missing header keyFound form baseTrace.sound keyTrace.sound)
            obtain ⟨keyState, keyRelated, _⟩ := keyTransition
            obtain ⟨finalState, terminalRelated⟩ := transport.transition protocol keyState (.refl _) worlds frame (.refl _)
            have same := uniqueResult outcome terminal
            subst actualOutcome
            refine ⟨result, finalStore, keyMap, finalWorld, ?_, related, finalHeaps,
              firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
              (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, ⟨finalState, protocol.trans firstRelated (protocol.trans keyRelated terminalRelated)⟩⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            apply SourceCoreCompatibleDataExpressions.index_completed layout (reasonAt id) firstEval secondEval
            simpa only [CompatibleMapping.Transport.expression_weaken] using lookup



include transport extension faithful functionLeaves functionTypes missing in
theorem Head.reflects_raw_at (budget size : Nat) (bounded : size ≤ budget)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {root : ExpressionNode} (certified : Certificate calls values source context reasonAt certificate scope id lowered)
    (found : source.lookupExpression? id = some root)
    (meaning : ∀ childId, childId ∈ actualOperandIds root.form → ∀ childSize, childSize ≤ budget →
      ProtectedStateTransition.WithReady.ReflectsAt protocol ready
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source
        (fun current expression code => expression = childId ∧ certificate current expression code) faults childSize)
    (sequences : SequenceReflectsFor (values := values) (source := source) (context := context)
      (registry := registry) (faults := faults) (certificate := certificate) functions program evidence protocol ready budget scope root) :
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrativeContext scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩, ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld root.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨head, data⟩ := certified
  cases data with
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    rw [CompatibleExpressionConstructors.construct_rename] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft childEvaluation branch =>
      exact constructor_reflects_after_sequence functions extension program evidence protocol (budget + 1) receipt installedEntry form valid
        (sequences (by simp only [form, actualOperandIds]) sequence environments heaps locals agrees actualTyped installedEntry initialReady)
        childEvaluation (by omega) complete
    | caseRight childEvaluation branch =>
      exact constructor_reflects_after_sequence functions extension program evidence protocol (budget + 1) receipt installedEntry form valid
        (sequences (by simp only [form, actualOperandIds]) sequence environments heaps locals agrees actualTyped installedEntry initialReady)
        childEvaluation (by omega) complete

  | @member node base baseNode name index identity branches result child metadata baseMetadata form layout childTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have ih := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base]; simp) n bound _ _ _ ⟨rfl, childTree⟩
    rw [member_rename layout] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (by omega) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure result baseEvaluation.sound (body := .matchData identity (LanguageResult.resultType result) (.var 0) branches)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.failure failed.sound), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
        ih _ (by omega) baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, selected, native, shape, sourceAt, related, expected⟩ := member_success layout payload baseEvaluation.sound
        subst_vars
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.value childTrace.sound sourceAt), .value related,
            finalHeaps, maps, worlds, frame, heapMetadata, forget_reached protocol ready transition⟩

  | @index node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree =>
    intro mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry initialReady evaluated
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    have firstIH := fun n (bound : n ≤ budget) => @meaning base (by rw [form]; change base ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, firstTree⟩
    have secondIH := fun n (bound : n ≤ budget) => @meaning key (by rw [form]; change key ∈ [base, key]; simp) n bound _ _ _ ⟨rfl, secondTree⟩
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated.sound
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
        firstIH _ (by omega) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure layout.valueType baseEvaluation.sound (body :=
          LanguageResult.bind layout.valueType ((second.expression.rename ξ).weakenAt 0)
            (SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.baseFailure failed.sound),
            .fault matched, finalHeaps, maps, worlds, frame, metadata, forget_reached protocol ready transition⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨childSourceSize, outcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstTransition⟩ :=
        firstIH _ (by omega) header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry initialReady baseEvaluation
      cases represented with
      | @value baseSource baseValue baseRep =>
        cases trace with
        | value baseTrace =>
          obtain ⟨middleState, firstRelated, firstReady⟩ := firstTransition
          have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
          cases branch with
          | caseLeft keyEvaluation ignored =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
              secondIH _ (by omega) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) keyEvaluation
            cases represented with
            | fault matched =>
              obtain ⟨finalState, secondRelated, _⟩ := transition
              rw [rename_prefix] at keyEvaluation
              have expected := LanguageResult.bind_success layout.valueType baseEvaluation.sound
                (LanguageResult.bind_failure layout.valueType keyEvaluation.sound (body :=
                  SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              cases trace with
              | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.keyFailure baseTrace.sound failed.sound),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, ⟨finalState, protocol.trans firstRelated secondRelated⟩⟩
          | caseRight keyEvaluation lookupEvaluation =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨keySourceSize, outcome, after, keyMap, keyWorld, trace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, keyTransition⟩ :=
              secondIH _ (by omega) keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment middleState (firstReady _ rfl) keyEvaluation
            cases represented with
            | @value keySource keyValue keyRep =>
              obtain ⟨outcome, result, endStore, finalWorld, terminal, related, lookup, finalHeaps, worlds, frame, uniqueResult, _sourceTrace, _post⟩ :=
                ReachedExpressionPrimitiveOutcomeProviders.general_index_finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                  (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace.sound
                    (by cases trace with | value keyTrace => exact keyTrace.sound) (reasonAt id)
                  (missing header keyFound form baseTrace.sound
                    (by cases trace with | value keyTrace => exact keyTrace.sound))
              rw [rename_prefix] at keyEvaluation
              have expected := SourceCoreCompatibleDataExpressions.index_completed (comparison := comparison.expression) layout (reasonAt id) baseEvaluation.sound keyEvaluation.sound
                (by simpa only [CompatibleMapping.Transport.expression_weaken] using lookup)
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              obtain ⟨keyState, keyRelated, _⟩ := keyTransition
              obtain ⟨finalState, terminalRelated⟩ := transport.transition protocol keyState (.refl _) worlds frame (.refl _)
              cases trace with
              | value keyTrace =>
                exact ⟨outcome, after, keyMap, finalWorld, index_intro header.metadata form (terminal.trace baseTrace.sound keyTrace.sound),
                  related, finalHeaps, firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
                  (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, ⟨finalState, protocol.trans firstRelated (protocol.trans keyRelated terminalRelated)⟩⟩





end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReachedDataHeadBounds

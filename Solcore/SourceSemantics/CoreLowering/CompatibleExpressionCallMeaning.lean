import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.NamedCallExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallTree

/-! Protected administrative entries compose with every ordinary recursive
expression head. Runtime child obligations are used only inside the generic
composition layer and discharged by the final concrete tree induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedBuiltinCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload DataPatternValues
open BuiltinCalls BuiltinCalls.Protocol
open BuiltinCalls.Typed (Head)
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CompatibleExpressionPrimitives (Metadata)
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
private theorem values_rep {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world types natives sources payloads) :
    ValuesRep values.checked registry functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

private theorem contracted_typed {definitions : DataEnvironment} {world : StoreTyping}
    {environment : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world environment actualContext definitions)
    (function : BuiltinFunctionId) (identity contract : Word) :
    RuntimeValueHasType world (contractedValue function identity contract environment)
      (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function))
      definitions := by
  have closureTyped := SourceCoreInteger.builtinClosure_hasType (scope := actualContext) (definitions := definitions) function
  cases closureTyped with
  | lambda _ _ body => exact .pair (.pair (.inRight .word) (.closure typed body)) .word

private theorem contracted_rename (function : BuiltinFunctionId) (identity contract : Word) (ξ : Renaming) :
    (Protocol.contracted function identity contract).rename ξ = Protocol.contracted function identity contract := by
  cases function <;> rfl

private theorem call_rename (function : BuiltinFunctionId) (identity contract unknown : Word)
    (arguments : Expr) (ξ : Renaming) :
    (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (Protocol.contracted function identity contract) arguments).rename ξ =
    CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (Protocol.contracted function identity contract) (arguments.rename ξ) := by
  simp [CallableContract.call, LanguageResult.bind, CallableContract.dispatch, CallableContract.guardResult,
    CallableContract.Gate.reason, LanguageResult.success, LanguageResult.failure,
    contracted_rename, Expr.rename, Renaming.lift]


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

variable {certificate : GenericExpressionMeaning.Certificate}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport

include functionLeaves unique in
theorem Head.preserves
    (argumentMeaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType children nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have prefixedLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        canonical (.unit :: contractedValue function identity contract actual :: actual) := agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
    have prefixedTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
      (.cons (contracted_typed actualTyped function identity contract) actualTyped)
    have sourceTrace := source_inv metadata form unique trace
    cases sourceTrace with
    | argumentsFault failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, argumentEval, matched, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ProtectedDataExpressionSequence.preserves_fault transport children argumentMeaning environments heaps locals prefixedLayout prefixedTyped installedEntry failed
      rw [rename_prefix, rename_prefix] at argumentEval
      refine ⟨.inLeft _ (.word token), finalStore, finalMap, finalWorld, ?_, .fault matched,
        finalHeaps, maps, worlds, frame, heapMetadata⟩
      rw [call_rename]
      exact CallableContract.call_argument_failure [⟨contract, none, none⟩] unknown
        (contracted_evaluates function identity contract actual store) (gates_accept contract unknown .beforeArguments) argumentEval
    | apply argumentsEvaluated application =>
      obtain ⟨payloads, argumentStore, finalMap, finalWorld, argumentEval, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ProtectedDataExpressionSequence.preserves_values transport children argumentMeaning environments heaps locals prefixedLayout prefixedTyped installedEntry argumentsEvaluated
      have related := values_rep represented
      rw [nativeTypes] at related
      have inputs := CompatibleBuiltinMeaning.input_of_values functionLeaves related
      rw [rename_prefix, rename_prefix] at argumentEval
      cases application with
      | value applied =>
        cases applied with
        | builtin applied =>
          obtain ⟨sourceResult, nativeResult, appliedAgain, resultRep, completed⟩ := contracted_preserves inputs argumentEval
          have same := appliedAgain.functional applied
          subst sourceResult
          refine ⟨.inRight .word nativeResult, argumentStore, finalMap, finalWorld, ?_, ?_,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
          · rw [call_rename]; exact completed
          · rw [sourceType]; exact .value (CompatibleBuiltinMeaning.result_represents inputs applied resultRep)
      | fault failed => exact False.elim (InputRep.excludes_callable_fault inputs failed)

include functionLeaves in
theorem Head.reflects
    (argumentMeaning : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry) :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType children nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ result finalStore
      environments heaps locals agrees actualTyped installedEntry completed
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [call_rename] at completed
    obtain ⟨argumentValue, argumentStore, argumentEval⟩ := contracted_argument_completes completed
    have shifted := argumentEval
    rw [← rename_prefix, ← rename_prefix] at shifted
    have prefixedLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        canonical (.unit :: contractedValue function identity contract actual :: actual) := agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
    have prefixedTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
      (.cons (contracted_typed actualTyped function identity contract) actualTyped)
    obtain ⟨argumentOutcome, middle, finalMap, finalWorld, argumentTrace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata⟩ :=
      ProtectedDataExpressionSequence.reflects transport children argumentMeaning environments heaps locals prefixedLayout prefixedTyped installedEntry shifted
    cases represented with
    | values represented =>
      cases argumentTrace with
      | values sourceArgs =>
        have related := values_rep represented
        rw [nativeTypes] at related
        have inputs := CompatibleBuiltinMeaning.input_of_values functionLeaves related
        obtain ⟨sourceResult, nativeResult, applied, resultRep, resultEq, storesEq⟩ := contracted_reflects inputs argumentEval completed
        subst result
        subst finalStore
        refine ⟨.value sourceResult, middle, finalMap, finalWorld,
          source_intro metadata form (.apply sourceArgs (.value (.builtin applied))), ?_,
          finalHeaps, maps, worlds, frame, heapMetadata⟩
        rw [sourceType]; exact .value (CompatibleBuiltinMeaning.result_represents inputs applied resultRep)
    | fault matched =>
      cases argumentTrace with
      | fault sourceArgs =>
        have failed := CallableContract.call_argument_failure (result := SourceCoreInteger.builtinResult function)
          [⟨contract, none, none⟩] unknown (contracted_evaluates function identity contract actual store)
          (gates_accept contract unknown .beforeArguments) argumentEval
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed failed
        exact ⟨.fault _, middle, finalMap, finalWorld, source_intro metadata form (.argumentsFault sourceArgs),
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedBuiltinCalls

namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open CompatibleExpressionIndices CoreProof
open GenericExpressionMeaning (agree_prefix rename_prefix)
open DataPatternValues
private theorem valuesRep {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world types natives sources payloads) :
    ValuesRep values.checked registry functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

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


variable {calls : CallHeads} {certificate : GenericExpressionMeaning.Certificate}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include transport extension faithful functionLeaves functionTypes unique missing in
theorem Head.preserves
    (meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
    (callMeaning : ∀ {children},
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source children faults entry →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (calls children) faults entry) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head calls values source context reasonAt certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | primitive head => exact ProtectedExpressionCompositions.Head.preserves functions program evidence transport unique meaning head
  | builtin head => exact ProtectedBuiltinCalls.Head.preserves functions functionLeaves program evidence unique transport meaning head
  | call head => exact callMeaning meaning head
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨sourceOutcome, sourceTrace, packed⟩ := constructor_inv receipt.metadata form unique valid trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ProtectedDataExpressionSequence.preserves transport sequence meaning environments heaps locals agrees actualTyped installedEntry sourceTrace
    cases represented with
    | @values sources payloadValues payloads =>
      cases packed
      have projected := receipt.metadata.projected
      rw [receipt.sourceType] at projected
      refine ⟨.inRight .word (.constructed tag (.pair (.word header) (packValues payloadValues))), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
      · rw [CompatibleExpressionConstructors.construct_rename]; exact CompatibleExpressionConstructors.construct_success tag header evaluated
      · rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
          receipt.selected projected receipt.registered (valuesRep payloads))
    | fault matched =>
      cases packed
      exact ⟨_, finalStore, finalMap, finalWorld, by rw [CompatibleExpressionConstructors.construct_rename]; exact CompatibleExpressionConstructors.construct_failure tag header evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩

  | @member node base baseNode name index identity branches result child metadata baseMetadata form layout childTree =>
    have ih := @meaning _ _ _ childTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have raw := member_inv metadata form unique trace
    cases raw with
    | value childTrace selected =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, sourceChild, native, shape, sourceAt, related, completed⟩ := member_success layout payload evaluated
        cases shape
        have same := at_functional sourceAt selected
        subst sourceChild
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact completed,
          .value related, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | failure childTrace =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped installedEntry (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact LanguageResult.bind_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | shape childTrace invalid =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, _⟩ := member_success layout payload evaluated
        subst_vars
        exact False.elim (invalid .intro)
    | position childTrace missing =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, selected, _⟩ := member_success layout payload evaluated
        cases shape
        exact False.elim (missing_excludes missing selected)

  | @index node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree =>
    have firstIH := @meaning _ _ _ firstTree
    have secondIH := @meaning _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rcases (index_inv header.metadata form unique trace).split with ⟨reason, rfl, failed⟩ | ⟨baseSource, middle, baseTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
        rw [index_rename comparison header.registered header.comparisonType]
        exact LanguageResult.bind_failure _ evaluated
    · obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry (.value baseTrace)
      cases represented with
      | @value _ baseValue baseRep =>
        have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
        rcases tail with ⟨reason, rfl, failed⟩ | ⟨keySource, keyTrace, terminal⟩
        · obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.fault failed)
          cases represented with
          | fault matched =>
            refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            exact LanguageResult.bind_success _ firstEval (LanguageResult.bind_failure _ secondEval)
        · obtain ⟨value, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.value keyTrace)
          cases represented with
          | @value _ keyValue keyRep =>
            obtain ⟨actualOutcome, result, finalStore, finalWorld, terminal', related, lookup, finalHeaps, worlds, frame, uniqueResult⟩ :=
              CompatibleGeneralIndex.finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps (reasonAt id) (missing id)
            have same := uniqueResult outcome terminal
            subst actualOutcome
            refine ⟨result, finalStore, keyMap, finalWorld, ?_, related, finalHeaps,
              firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
              (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            apply SourceCoreCompatibleDataExpressions.index_completed layout (reasonAt id) firstEval secondEval
            simpa only [CompatibleMapping.Transport.expression_weaken] using lookup


include transport extension faithful functionLeaves functionTypes missing in
theorem Head.reflects
    (meaning : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
    (callMeaning : ∀ {children},
      ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source children faults entry →
      ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (calls children) faults entry) :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head calls values source context reasonAt certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | primitive head => exact ProtectedExpressionCompositions.Head.reflects functions program evidence transport meaning head
  | builtin head => exact ProtectedBuiltinCalls.Head.reflects functions functionLeaves program evidence transport meaning head
  | call head => exact callMeaning meaning head
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    rw [CompatibleExpressionConstructors.construct_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ProtectedDataExpressionSequence.reflects transport sequence meaning environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_failure tag header childEvaluation)
        exact ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace (.fault _),
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ProtectedDataExpressionSequence.reflects transport sequence meaning environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | values payloads =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_success tag header childEvaluation)
        have projected := receipt.metadata.projected
        rw [receipt.sourceType] at projected
        refine ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace (.values _),
          ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
        rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
          receipt.selected projected receipt.registered (valuesRep payloads))

  | @member node base baseNode name index identity branches result child metadata baseMetadata form layout childTree =>
    have ih := @meaning _ _ _ childTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [member_rename layout] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped installedEntry baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure result baseEvaluation (body := .matchData identity (LanguageResult.resultType result) (.var 0) branches)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.failure failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped installedEntry baseEvaluation
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, selected, native, shape, sourceAt, related, expected⟩ := member_success layout payload baseEvaluation
        subst_vars
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.value childTrace sourceAt), .value related,
            finalHeaps, maps, worlds, frame, heapMetadata⟩

  | @index node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree =>
    have firstIH := @meaning _ _ _ firstTree
    have secondIH := @meaning _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure layout.valueType baseEvaluation (body :=
          LanguageResult.bind layout.valueType ((second.expression.rename ξ).weakenAt 0)
            (SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.baseFailure failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨outcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry baseEvaluation
      cases represented with
      | @value baseSource baseValue baseRep =>
        cases trace with
        | value baseTrace =>
          have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
          cases branch with
          | caseLeft keyEvaluation ignored =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) keyEvaluation
            cases represented with
            | fault matched =>
              rw [rename_prefix] at keyEvaluation
              have expected := LanguageResult.bind_success layout.valueType baseEvaluation
                (LanguageResult.bind_failure layout.valueType keyEvaluation (body :=
                  SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              cases trace with
              | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.keyFailure baseTrace failed),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
          | caseRight keyEvaluation lookupEvaluation =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, keyMap, keyWorld, trace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) keyEvaluation
            cases represented with
            | @value keySource keyValue keyRep =>
              obtain ⟨outcome, result, endStore, finalWorld, terminal, related, lookup, finalHeaps, worlds, frame, uniqueResult⟩ :=
                CompatibleGeneralIndex.finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                  (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps (reasonAt id) (missing id)
              rw [rename_prefix] at keyEvaluation
              have expected := SourceCoreCompatibleDataExpressions.index_completed (comparison := comparison.expression) layout (reasonAt id) baseEvaluation keyEvaluation
                (by simpa only [CompatibleMapping.Transport.expression_weaken] using lookup)
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              cases trace with
              | value keyTrace =>
                exact ⟨outcome, after, keyMap, finalWorld, index_intro header.metadata form (terminal.trace baseTrace keyTrace),
                  related, finalHeaps, firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
                  (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata⟩



end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls

namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {calls : CallHeads} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)

include extension faithful functionLeaves functionTypes valid uninitialized missing transport in
/-- The finite tree induction supplies every recursive child meaning. The
call-head interface is an inner composition law supplied by a concrete caller
adapter; it is not stored in an expression certificate. -/
theorem preserves (unique : NodeOccurrencesUnique source)
    (callMeaning : ∀ {children},
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source children faults entry →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (calls children) faults entry) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree calls fuel values source context solved reasonAt) faults entry := by
  intro scope id lowered tree
  induction tree with
  | fragment child =>
    exact ProtectedExpressionMeaning.preserves_of_typed entry
      (CompatibleExpressionBuiltins.preserves functions extension faithful functionLeaves functionTypes
        program evidence valid unique uninitialized missing) child
  | @node id lowered entries head children ih =>
    have meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope entries) faults entry := by
      intro current child code certified
      obtain ⟨rfl, member⟩ := certified
      exact ih child code member
    intro root found
    exact Head.preserves functions extension faithful functionLeaves functionTypes program evidence unique missing
      transport meaning callMeaning head found

include extension faithful functionLeaves functionTypes valid uninitialized missing transport in
/-- Native completion recursively builds all source child traces, including
skipped branches and first argument faults, with the actual protected entry. -/
theorem reflects
    (callMeaning : ∀ {children},
      ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source children faults entry →
      ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (calls children) faults entry) :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree calls fuel values source context solved reasonAt) faults entry := by
  intro scope id lowered tree
  induction tree with
  | fragment child =>
    exact ProtectedExpressionMeaning.reflects_of_typed entry
      (CompatibleExpressionBuiltins.reflects functions extension faithful functionLeaves functionTypes
        program evidence valid uninitialized missing) child
  | @node id lowered entries head children ih =>
    have meaning : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope entries) faults entry := by
      intro current child code certified
      obtain ⟨rfl, member⟩ := certified
      exact ih child code member
    intro root found
    exact Head.reflects functions extension faithful functionLeaves functionTypes program evidence missing
      transport meaning callMeaning head found

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls

namespace Solcore.SourceSemantics.CoreLowering.NamedCallExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

/-- Concrete recursive ordinary named expressions. The retained body inventory
contains static compiler/body receipts; its installed observations remain a
separate, protected dynamic entry. -/
abbrev Tree (bodies : Bodies prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree (Head bodies compilation source context)
    fuel values source context solved reasonAt

variable (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {bodies : Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (caller : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context caller)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include extension faithful functionLeaves functionTypes valid uninitialized missing bodyUninitialized bodyMissing in
/-- All recursive child and named body meanings are discharged by the finite
Tree and concrete builtin-lexical body certificates. Actual global/frame
provenance, context/evidence validity and static source ownership stay explicit. -/
theorem Tree.preserves (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context caller source (Tree bodies compilation fuel source context solved reasonAt) faults
      (Entry functions registry bodies compilation.administrativePrefix) := by
  apply CompatibleExpressionCalls.preserves functions extension faithful functionLeaves functionTypes
    program caller valid uninitialized missing
    (entry_transport functions registry bodies compilation.administrativePrefix) unique
  intro children meaning
  exact Head.preserves functions extension caller bodyUninitialized bodyMissing faithful functionLeaves
    functionTypes unique owners meaning

include extension faithful functionLeaves functionTypes valid uninitialized missing bodyUninitialized bodyMissing in
/-- Native finite completion constructs the complete independent expression
outcome, including named calls at arbitrary child positions and first faults.
No external recursive child or body meaning is required. -/
theorem Tree.reflects :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context caller source (Tree bodies compilation fuel source context solved reasonAt) faults
      (Entry functions registry bodies compilation.administrativePrefix) := by
  apply CompatibleExpressionCalls.reflects functions extension faithful functionLeaves functionTypes
    program caller valid uninitialized missing
    (entry_transport functions registry bodies compilation.administrativePrefix)
  intro children meaning
  exact Head.reflects functions extension caller bodyUninitialized bodyMissing faithful functionLeaves
    functionTypes meaning

end Solcore.SourceSemantics.CoreLowering.NamedCallExpressions

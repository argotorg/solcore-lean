import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinCallBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceKeyContracts
import Solcore.SourceSemantics.CoreLowering.NamedCallExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallTree

/-! The existing contracted builtin Head composes only finite argument
obligations within the fixed outer bound. It does not close the full recursive
expression Tree; source and native sizes remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload DataPatternValues CoreProof
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
theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (argumentMeaning : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
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
    have childrenMeaning : ∀ child, child < budget + 1 → ProtectedDataExpressionSequence.ExpressionPreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults entry := by
      intro child within
      exact RecursiveNamedPlaceKeyContracts.preserves_at (argumentMeaning child (by omega))
    have sourceTrace := RecursiveNamedBuiltinCallBounds.source_inv metadata form unique trace
    cases sourceTrace with
    | argumentsFault failed smaller =>
      obtain ⟨token, finalStore, finalMap, finalWorld, argumentEval, matched, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ProtectedDataExpressionSequence.preserves_fault_bounded transport (budget + 1) children childrenMeaning environments heaps locals prefixedLayout prefixedTyped installedEntry failed (by omega)
      rw [rename_prefix, rename_prefix] at argumentEval
      refine ⟨.inLeft _ (.word token), finalStore, finalMap, finalWorld, ?_, .fault matched,
        finalHeaps, maps, worlds, frame, heapMetadata⟩
      rw [call_rename]
      exact CallableContract.call_argument_failure [⟨contract, none, none⟩] unknown
        (contracted_evaluates function identity contract actual store) (gates_accept contract unknown .beforeArguments) argumentEval
    | apply argumentsEvaluated application smaller =>
      obtain ⟨payloads, argumentStore, finalMap, finalWorld, argumentEval, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ProtectedDataExpressionSequence.preserves_values_bounded transport (budget + 1) children childrenMeaning environments heaps locals prefixedLayout prefixedTyped installedEntry argumentsEvaluated (by omega)
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
theorem Head.reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (argumentMeaning : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType children nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ result finalStore
      environments heaps locals agrees actualTyped installedEntry completed
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [call_rename] at completed
    obtain ⟨argumentSize, argumentValue, argumentStore, argumentSmaller, argumentEval⟩ :=
      RecursiveNamedBuiltinCallBounds.contracted_arguments_sized completed
    have shifted := argumentEval
    rw [← rename_prefix, ← rename_prefix] at shifted
    have prefixedLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        canonical (.unit :: contractedValue function identity contract actual :: actual) := agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
    have prefixedTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
      (.cons (contracted_typed actualTyped function identity contract) actualTyped)
    have childrenMeaning : ∀ child, child < budget + 1 → ProtectedDataExpressionSequence.ExpressionReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source certificate faults entry := by
      intro child within
      exact RecursiveNamedPlaceKeyContracts.reflects_at (argumentMeaning child (by omega))
    obtain ⟨argumentSourceSize, argumentOutcome, middle, finalMap, finalWorld, argumentTrace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata⟩ :=
      ProtectedDataExpressionSequence.reflects_bounded transport (budget + 1) children childrenMeaning environments heaps locals prefixedLayout prefixedTyped installedEntry shifted (by omega)
    cases represented with
    | values represented =>
      cases argumentTrace with
      | values sourceArgs =>
        have related := values_rep represented
        rw [nativeTypes] at related
        have inputs := CompatibleBuiltinMeaning.input_of_values functionLeaves related
        obtain ⟨sourceResult, nativeResult, applied, resultRep, resultEq, storesEq⟩ := contracted_reflects inputs argumentEval.sound completed.sound
        subst result
        subst finalStore
        obtain ⟨sourceSize, sourceTrace⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
          (BuiltinCalls.source_intro metadata form (.apply sourceArgs.sound (.value (.builtin applied))))
        refine ⟨sourceSize, .value sourceResult, middle, finalMap, finalWorld, sourceTrace, ?_,
          finalHeaps, maps, worlds, frame, heapMetadata⟩
        rw [sourceType]; exact .value (CompatibleBuiltinMeaning.result_represents inputs applied resultRep)
    | fault matched =>
      cases argumentTrace with
      | fault sourceArgs =>
        have failed := CallableContract.call_argument_failure (result := SourceCoreInteger.builtinResult function)
          [⟨contract, none, none⟩] unknown (contracted_evaluates function identity contract actual store)
          (gates_accept contract unknown .beforeArguments) argumentEval.sound
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
        obtain ⟨sourceSize, sourceTrace⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
          (BuiltinCalls.source_intro metadata form (.argumentsFault sourceArgs.sound))
        exact ⟨sourceSize, .fault _, middle, finalMap, finalWorld, sourceTrace,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinHeadBounds

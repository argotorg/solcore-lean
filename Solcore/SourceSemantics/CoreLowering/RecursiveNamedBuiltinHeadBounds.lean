import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinCallBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceKeyContracts
import Solcore.SourceSemantics.CoreLowering.NamedCallExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallTree

import Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignment
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionSequenceProducer

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
namespace Stateful
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)

/-- The guarded environment retains its original runtime typing. -/
theorem prefixed_typed {definitions : DataEnvironment} {world : StoreTyping}
    {actual : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (function : BuiltinFunctionId) (identity contract : Word) :
    RuntimeEnvironmentHasTypes world (.unit :: contractedValue function identity contract actual :: actual)
      (.unit :: CallableContract.functionType (SourceCoreInteger.builtinParameter function)
        (SourceCoreInteger.builtinResult function) :: actualContext) definitions :=
  .cons .unit (.cons (contracted_typed typed function identity contract) typed)

include functionLeaves unique in
/-- The original Source head consumes a whole sequence at the real guarded
caller input. Builtin application keeps that exact argument post. -/
theorem Head.preserves_bounded_with_sequence (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {node : ExpressionNode} {codes : List SourceCoreBasic.LoweredExpr}
    {identity contract unknown : Word}
    (metadata : Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (sourceType : node.type = function.returnType)
    (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequence : ProtectedStateExpressionSequenceProducer.Preserves
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := .unit :: contractedValue function identity contract actual :: actual)
      (ξ := Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      (ids := arguments) (sourceTypes := function.parameterTypes) (codes := codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial (budget + 1))
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
        (Protocol.contracted function identity contract) (SourceCoreCalls.packArguments codes).expression).rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld node.type
        (SourceCoreInteger.builtinResult function) faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have sourceTrace := RecursiveNamedBuiltinCallBounds.source_inv metadata form unique trace
  cases sourceTrace with
  | argumentsFault failed smaller =>
    obtain ⟨argumentValue, finalStore, finalMap, finalWorld, argumentEval, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
      sequence (.fault failed) (by omega)
    cases represented with
    | @fault reason token matched =>
      rw [rename_prefix, rename_prefix] at argumentEval
      refine ⟨.inLeft _ (.word token), finalStore, finalMap, finalWorld, ?_, .fault matched,
        finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
      rw [call_rename]
      exact CallableContract.call_argument_failure [⟨contract, none, none⟩] unknown
        (contracted_evaluates function identity contract actual store) (gates_accept contract unknown .beforeArguments) argumentEval
  | apply argumentsEvaluated application smaller =>
    obtain ⟨argumentValue, argumentStore, finalMap, finalWorld, argumentEval, represented, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩ :=
      sequence (.values argumentsEvaluated) (by omega)
    cases represented with
    | values represented =>
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
            finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
          · rw [call_rename]; exact completed
          · rw [sourceType]; exact .value (CompatibleBuiltinMeaning.result_represents inputs applied resultRep)
      | fault failed => exact False.elim (InputRep.excludes_callable_fault inputs failed)


include functionLeaves in
/-- The original reflection suffix uses the actual measured argument child
and retains its real post with an independent Source grade. -/
theorem Head.reflects_after_arguments_with_sequence (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {node : ExpressionNode} {codes : List SourceCoreBasic.LoweredExpr}
    {identity contract unknown : Word}
    (metadata : Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (sourceType : node.type = function.returnType)
    (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := .unit :: contractedValue function identity contract actual :: actual)
      (ξ := Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      (ids := arguments) (sourceTypes := function.parameterTypes) (codes := codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial (budget + 1))
    {result : Value} {finalStore : Store} (argumentSize : Nat)
    {argumentValue : Value} {argumentStore : Store}
    (argumentSmaller : argumentSize < size)
    (argumentEval : EvaluationSize argumentSize (.unit :: contractedValue function identity contract actual :: actual) store
      (((SourceCoreCalls.packArguments codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0) argumentValue argumentStore)
    (completed : EvaluationSize size actual store (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
        (Protocol.contracted function identity contract) ((SourceCoreCalls.packArguments codes).expression.rename ξ)) result finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld node.type
        (SourceCoreInteger.builtinResult function) faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have shifted := argumentEval
  rw [← rename_prefix, ← rename_prefix] at shifted
  obtain ⟨argumentSourceSize, argumentOutcome, middle, finalMap, finalWorld, argumentTrace, represented, finalHeaps,
    maps, worlds, frame, heapMetadata, transition⟩ :=
    sequence shifted (by omega)
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
        finalHeaps, maps, worlds, frame, heapMetadata, transition⟩
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
        .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, transition⟩

include functionLeaves in
/-- Invert the same original contracted call once before consuming its real
argument child through the shared reflection suffix. -/
theorem Head.reflects_bounded_with_sequence (budget size : Nat) (bounded : size ≤ budget)
    {scope : Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {node : ExpressionNode} {codes : List SourceCoreBasic.LoweredExpr}
    {identity contract unknown : Word}
    (metadata : Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (sourceType : node.type = function.returnType)
    (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequence : ProtectedStateExpressionSequenceProducer.Reflects
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := .unit :: contractedValue function identity contract actual :: actual)
      (ξ := Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      (ids := arguments) (sourceTypes := function.parameterTypes) (codes := codes) (faults := faults)
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) initial (budget + 1))
    {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store ((CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
        (Protocol.contracted function identity contract) (SourceCoreCalls.packArguments codes).expression).rename ξ) result finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld node.type
        (SourceCoreInteger.builtinResult function) faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  rw [call_rename] at completed
  obtain ⟨argumentSize, argumentValue, argumentStore, argumentSmaller, argumentEval⟩ :=
    RecursiveNamedBuiltinCallBounds.contracted_arguments_sized completed
  exact Head.reflects_after_arguments_with_sequence functions functionLeaves program evidence protocol budget size bounded
    metadata form sourceType nativeTypes initial sequence argumentSize argumentSmaller argumentEval completed

include functionLeaves unique in
theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (argumentMeaning : ∀ child, child ≤ budget → ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults child) :
    ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults size := by
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
    exact Head.preserves_bounded_with_sequence functions functionLeaves program evidence unique protocol budget size bounded
      metadata form sourceType nativeTypes installedEntry
      (ProtectedStateExpressionSequenceProducer.Preserves.of_uniform installedEntry (budget + 1) children
        (fun child within => ProtectedStateTransition.SequenceBridge.preserves_at protocol (argumentMeaning child (by omega)))
        environments heaps locals prefixedLayout prefixedTyped) trace

include functionLeaves in
theorem Head.reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (argumentMeaning : ∀ child, child ≤ budget → ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults child) :
    ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults size := by
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
    have prefixedLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        canonical (.unit :: contractedValue function identity contract actual :: actual) := agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
    have prefixedTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
      (.cons (contracted_typed actualTyped function identity contract) actualTyped)
    exact Head.reflects_after_arguments_with_sequence functions functionLeaves program evidence protocol budget size bounded
      metadata form sourceType nativeTypes installedEntry
      (ProtectedStateExpressionSequenceProducer.Reflects.of_uniform installedEntry (budget + 1) children
        (fun child within => ProtectedStateTransition.SequenceBridge.reflects_at protocol (argumentMeaning child (by omega)))
        environments heaps locals prefixedLayout prefixedTyped) argumentSize argumentSmaller argumentEval completed

end Stateful

variable {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport

include functionLeaves unique in
theorem Head.preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (argumentMeaning : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults entry := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped installedEntry trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.Head.preserves_at functions functionLeaves program evidence unique (ProtectedStatePlaceAssignment.legacyProtocol entry) budget size bounded
      (fun child bound => ProtectedStatePlaceAssignment.legacy_preserves transport (argumentMeaning child bound))
      tree found environments heaps locals agrees actualTyped (PLift.up installedEntry) trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

include functionLeaves in
theorem Head.reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (argumentMeaning : ∀ child, child ≤ budget → RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults entry := by
  intro scope id lowered tree node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installedEntry evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.Head.reflects_at functions functionLeaves program evidence (ProtectedStatePlaceAssignment.legacyProtocol entry) budget size bounded
      (fun child bound => ProtectedStatePlaceAssignment.legacy_reflects transport (argumentMeaning child bound))
      tree found environments heaps locals agrees actualTyped (PLift.up installedEntry) evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinHeadBounds

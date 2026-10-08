import Solcore.SourceSemantics.CoreLowering.BuiltinFaultPostContracts
import Solcore.SourceSemantics.CoreLowering.BuiltinCallCertificates
import Solcore.SourceSemantics.CoreLowering.BuiltinCallProtocol
import Solcore.SourceSemantics.CoreLowering.BuiltinCallSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralMeaning

/-! Ordinary contracted builtin calls compose concrete recursive argument
trees. The callee and both gates are pure; argument effects and failures are
provided by the independently closed expression meanings, in source order. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinCalls.Typed
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload DataPatternValues
open Protocol
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CompatibleExpressionPrimitives (Metadata)
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Head (values : ValuesContext) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (scope : Scope) : ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | contracted {id callee arguments function node codes identity contract unknown}
      (metadata : Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
      (form : node.form = .call callee arguments (.builtinFunction function))
      (sourceType : node.type = function.returnType)
      (children : DataExpressionSequence.Tree source
        certificate scope
        arguments function.parameterTypes codes)
      (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function) :
      Head values source certificate scope id
        ⟨SourceCoreInteger.builtinResult function,
          CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
            (Protocol.contracted function identity contract) (SourceCoreCalls.packArguments codes).expression⟩

abbrev Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) : GenericExpressionMeaning.Certificate :=
  Head values source (CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt)

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
    contracted_rename, Expr.rename, Expr.rename_comp, Expr.rename_insertion, Renaming.lift]


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

include functionLeaves unique in
theorem Head.preserves_with_post
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (builtinJoins : BuiltinFaultPostContracts.Joins post listPost values program context evidence source)
    (argumentMeaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults post) :
    ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults post := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType children nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have prefixedLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        canonical (.unit :: contractedValue function identity contract actual :: actual) := agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
    have prefixedTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
      (.cons (contracted_typed actualTyped function identity contract) actualTyped)
    have sourceTrace := source_inv metadata form unique trace
    cases sourceTrace with
    | argumentsFault failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, argumentEval, matched, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        TypedDataExpressionSequence.preserves_fault_with_post children sequenceJoins argumentMeaning environments heaps locals prefixedLayout prefixedTyped failed
      rw [rename_prefix, rename_prefix] at argumentEval
      refine ⟨.inLeft _ (.word token), finalStore, finalMap, finalWorld, ?_, .fault matched,
        finalHeaps, maps, worlds, frame, heapMetadata,
        BuiltinFaultPostContracts.arguments_fault_outcome builtinJoins metadata form sourceType children nativeTypes failed retained⟩
      rw [call_rename]
      exact CallableContract.call_argument_failure [⟨contract, none, none⟩] unknown
        (contracted_evaluates function identity contract actual store) (gates_accept contract unknown .beforeArguments) argumentEval
    | apply argumentsEvaluated application =>
      obtain ⟨payloads, argumentStore, finalMap, finalWorld, argumentEval, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        TypedDataExpressionSequence.preserves_values children (ExpressionFailurePostContracts.TypedPreserves.forget argumentMeaning) environments heaps locals prefixedLayout prefixedTyped argumentsEvaluated
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
            finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
          · rw [call_rename]; exact completed
          · rw [sourceType]; exact .value (CompatibleBuiltinMeaning.result_represents inputs applied resultRep)
      | fault failed => exact False.elim (InputRep.excludes_callable_fault inputs failed)

include functionLeaves unique in
theorem Head.preserves
    (argumentMeaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults := by
  exact ExpressionFailurePostContracts.TypedPreserves.forget
    (Head.preserves_with_post functions functionLeaves program evidence unique
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (BuiltinFaultPostContracts.trivial_joins values program context evidence source)
      (ExpressionFailurePostContracts.TypedPreserves.of_trivial argumentMeaning))

include functionLeaves in
theorem Head.reflects_with_post
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (builtinJoins : BuiltinFaultPostContracts.Joins post listPost values program context evidence source)
    (argumentMeaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults post) :
    ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults post := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType children nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ result finalStore
      environments heaps locals agrees actualTyped completed
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
      maps, worlds, frame, heapMetadata, retained⟩ :=
      TypedDataExpressionSequence.reflects_with_post children sequenceJoins argumentMeaning environments heaps locals prefixedLayout prefixedTyped shifted
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
          finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
        rw [sourceType]; exact .value (CompatibleBuiltinMeaning.result_represents inputs applied resultRep)
    | fault matched =>
      cases argumentTrace with
      | fault sourceArgs =>
        have failed := CallableContract.call_argument_failure (result := SourceCoreInteger.builtinResult function)
          [⟨contract, none, none⟩] unknown (contracted_evaluates function identity contract actual store)
          (gates_accept contract unknown .beforeArguments) argumentEval
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed failed
        exact ⟨.fault _, middle, finalMap, finalWorld, source_intro metadata form (.argumentsFault sourceArgs),
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          BuiltinFaultPostContracts.arguments_fault_outcome builtinJoins metadata form sourceType children nativeTypes sourceArgs
            (ExpressionFailurePostContracts.ListOutcomePost.fault retained)⟩

include functionLeaves in
theorem Head.reflects
    (argumentMeaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults) :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults := by
  exact ExpressionFailurePostContracts.TypedReflects.forget
    (Head.reflects_with_post functions functionLeaves program evidence
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (BuiltinFaultPostContracts.trivial_joins values program context evidence source)
      (ExpressionFailurePostContracts.TypedReflects.of_trivial argumentMeaning))

include extension faithful functionLeaves functionTypes valid unique uninitialized missing in
/-- Concrete recursive General arguments close every runtime child obligation. -/
theorem preserves :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults :=
  Head.preserves functions functionLeaves program evidence unique
    (CompatibleExpressionGeneral.preserves functions extension faithful functionLeaves functionTypes
      program evidence valid unique uninitialized missing)

include extension faithful functionLeaves functionTypes valid uninitialized missing in
/-- Completed Core calls construct source traces using concrete argument reflection. -/
theorem reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults :=
  Head.reflects functions functionLeaves program evidence
    (CompatibleExpressionGeneral.reflects functions extension faithful functionLeaves functionTypes
      program evidence valid uninitialized missing)

end Solcore.SourceSemantics.CoreLowering.BuiltinCalls.Typed

import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConditionals
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionTyped
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors

/-!
# Builtin calls

Certificates, meaning, typing and fault contracts of builtin calls.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinFaultPostContracts
/-! Builtin argument fault joins retain the real direct-call metadata,
ordered compiled children and original Source failure. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinFaultPostContracts
open Core Frontend SourceInference GeneralHeap CompatiblePayload ExpressionFailurePostContracts

structure Joins (post : ExpressionFaultPost) (listPost : ExpressionsFaultPost)
    (values : SourceCoreCompatibleValues.Context) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) : Prop where
  arguments : ∀ {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
    {node : ExpressionNode} {codes : List SourceCoreBasic.LoweredExpr}
    {environment before reason after token mapping world store},
    CompatibleExpressionPrimitives.Metadata values.checked source id node (SourceCoreInteger.builtinResult function) →
    node.form = .call callee ids (.builtinFunction function) →
    node.type = function.returnType →
    DataExpressionSequence.Tree source certificate scope ids function.parameterTypes codes →
    codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function →
    Dynamic.ExpressionsFault program context evidence source environment before ids reason after →
    listPost program context evidence source environment before ids reason after token mapping world store →
    post program context evidence source environment before id reason after token mapping world store

theorem trivial_joins (values : SourceCoreCompatibleValues.Context) (program : Program)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    Joins TrivialExpressionPost TrivialExpressionsPost values program context evidence source where
  arguments := by intros; trivial

theorem arguments_fault_outcome {post : ExpressionFaultPost} {listPost : ExpressionsFaultPost}
    {values : SourceCoreCompatibleValues.Context} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    (joins : Joins post listPost values program context evidence source)
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
    {node : ExpressionNode} {codes : List SourceCoreBasic.LoweredExpr}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {token : Word} {parentType : Ty} {mapping : LocationMap} {world : StoreTyping} {store : Store}
    (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
    (form : node.form = .call callee ids (.builtinFunction function))
    (sourceType : node.type = function.returnType)
    (children : DataExpressionSequence.Tree source certificate scope ids function.parameterTypes codes)
    (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
    (failed : Dynamic.ExpressionsFault program context evidence source environment before ids reason after)
    (retained : listPost program context evidence source environment before ids reason after token mapping world store) :
    OutcomePost post program context evidence source environment before id parentType (.fault reason) after
      (.inLeft parentType (.word token)) mapping world store :=
  ⟨token, rfl, joins.arguments metadata form sourceType children nativeTypes failed retained⟩

end Solcore.SourceSemantics.CoreLowering.BuiltinFaultPostContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinCallCertificates
/-! Static receipts from the actual builtin reference and direct-call branches.
The identity comes from the real global prefix and builtin inventory; callable
decoration and argument children retain their actual compiler equations. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinCalls
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

inductive Reference (callables : SourceCoreFunctions.CallablePolicy) (compilation : SourceCoreFunctions.Context)
    (source : TypedSource) (node : ExpressionNode) (name : String) (function : BuiltinFunctionId) :
    SourceCoreBasic.LoweredExpr → Prop where
  | intro {index : Nat} {identity : Word} {expression : Expr}
      (spelling : name = function.spelling) (sourceType : node.type = function.type)
      (inventory : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index))
      (identitySelected : Word.ofNat? (compilation.globals.length + index + 1) = some identity)
      (decorated : callables.decorateCallable compilation source node (.builtin function)
        (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)
        (LanguageResult.success (TaggedFunction.identified identity (SourceCoreInteger.builtinClosure function))) = .ok expression) :
      Reference callables compilation source node name function
        ⟨callables.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function), expression⟩

theorem reference_of_accepted
    {callables : SourceCoreFunctions.CallablePolicy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {name : String} {function : BuiltinFunctionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.builtinReference callables compilation source node name function = .ok lowered) :
    Reference callables compilation source node name function lowered := by
  by_cases spelling : name = function.spelling
  · by_cases sourceType : node.type = function.type
    · cases inventory : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) with
      | none => simp [SourceCoreFunctions.builtinReference, spelling, sourceType, inventory, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at accepted
      | some item =>
        have same : item.1 = function := by simpa using List.find?_some inventory
        obtain ⟨actual, index⟩ := item
        change actual = function at same
        subst actual
        cases selected : Word.ofNat? (compilation.globals.length + index + 1) with
        | none => simp [SourceCoreFunctions.builtinReference, spelling, sourceType, inventory, selected, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at accepted
        | some identity =>
          simp only [SourceCoreFunctions.builtinReference, spelling, sourceType, ne_eq,
            not_true_eq_false, decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
            inventory, selected, bind, Except.bind, pure, Except.pure] at accepted
          obtain ⟨expression, decorated, accepted⟩ := bind_ok accepted
          cases accepted
          exact .intro spelling sourceType inventory selected decorated
    · simp [SourceCoreFunctions.builtinReference, sourceType, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at accepted
  · simp [SourceCoreFunctions.builtinReference, spelling, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at accepted

/-- Successful production builtin-call lowering exposes the exact callee
receipt, ordered argument compilation and call hook. No child execution is
part of this certificate. The ordinary special-hook condition stays explicit. -/
theorem call_of_accepted
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {node : ExpressionNode} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ calleeNode calleeType calleeCode codes expression,
      SourceCoreElaboration.validateBuiltinFunctionCall source node callee arguments function = .ok () ∧
      policy.readExpression source callee = .ok (calleeNode, calleeType) ∧
      Reference policy.callables compilation source calleeNode function.spelling function calleeCode ∧
      arguments.mapM (fun argument => SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel
        compilation source scope argument reasonAt) = .ok codes ∧
      (SourceCoreCalls.packArguments codes).type = SourceCoreInteger.builtinParameter function ∧
      type = SourceCoreInteger.builtinResult function ∧
      policy.callables.callCallable compilation source node type calleeCode.expression
        (SourceCoreCalls.packArguments codes).expression = .ok expression ∧
      lowered = ⟨type, expression⟩ := by
  cases hook : policy.lowerSpecial? <;> simp only [hook] at special
  all_goals
    unfold SourceCoreFunctions.lowerExpressionWithPolicy at accepted
    simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, hook, special, form, read,
      bind, Except.bind, pure, Except.pure] at accepted
    obtain ⟨validation, validated, accepted⟩ := bind_ok accepted
    have validatedRaw : SourceCoreElaboration.validateBuiltinFunctionCall source node callee arguments function = .ok () := by
      cases actual : SourceCoreElaboration.validateBuiltinFunctionCall source node callee arguments function <;>
        simp_all [Except.mapError]
    obtain ⟨calleePair, calleeRead, accepted⟩ := bind_ok accepted
    obtain ⟨calleeNode, calleeType⟩ := calleePair
    obtain ⟨calleeCode, calleeAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨codes, argumentsAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨packedCheck, packedChecked, accepted⟩ := bind_ok accepted
    have packedType := (ensureType_ok packedChecked).symm
    obtain ⟨resultCheck, resultChecked, accepted⟩ := bind_ok accepted
    have resultType := (ensureType_ok resultChecked).symm
    obtain ⟨expression, emitted, accepted⟩ := bind_ok accepted
    cases accepted
    exact ⟨calleeNode, calleeType, calleeCode, codes, expression, validatedRaw, calleeRead,
      reference_of_accepted calleeAccepted, argumentsAccepted, packedType, resultType, emitted, rfl⟩
end Solcore.SourceSemantics.CoreLowering.BuiltinCalls
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinCallMeaning
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
theorem preserves [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults :=
  Head.preserves functions functionLeaves program evidence unique
    (CompatibleExpressionGeneral.preserves functions extension faithful functionLeaves functionTypes
      program evidence valid unique uninitialized missing)

include extension faithful functionLeaves functionTypes valid uninitialized missing in
/-- Completed Core calls construct source traces using concrete argument reflection. -/
theorem reflects [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults :=
  Head.reflects functions functionLeaves program evidence
    (CompatibleExpressionGeneral.reflects functions extension faithful functionLeaves functionTypes
      program evidence valid uninitialized missing)

end Solcore.SourceSemantics.CoreLowering.BuiltinCalls.Typed
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinCallTypedCertificates
/-! Successful production lowering authenticates contracted builtin selection,
identity and the complete argument bundle. The remaining premises are static
source metadata and concrete argument receipts, with no child execution premise. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinCalls.Typed
open Core Frontend SourceInference

private theorem descriptor_reconstructs {table : SourceCoreStageCodebook.Table}
    {origin : SourceCoreStageCodebook.Origin} (descriptor : SourceCoreCallableContracts.Descriptor table origin) :
    SourceCoreCallableContracts.descriptor table origin = .ok descriptor := by
  cases descriptor
  rename_i identity found
  unfold SourceCoreCallableContracts.descriptor
  split
  · rename_i absent
    rw [found] at absent
    contradiction
  · rename_i selected actual
    have same := Option.some.inj (actual.symm.trans found)
    subst selected
    rfl

theorem builtin_call (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource) (node : ExpressionNode)
    (callee : ExpressionId) (arguments : List ExpressionId) (function : BuiltinFunctionId)
    (result : Ty) (calleeCode argumentCode : Expr)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin function))
    (form : node.form = .call callee arguments (.builtinFunction function)) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).callCallable
      compilation source node result calleeCode argumentCode =
      .ok (CallableContract.call [⟨descriptor.id, none, none⟩] native.diagnostics.unknown result calleeCode argumentCode) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, form, descriptor_reconstructs descriptor,
    Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem argument_types {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (children : DataExpressionSequence.Tree source
      (CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt) scope ids types codes) :
    types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) := by
  induction children with
  | nil => rfl
  | single found child => simp [child.projected found, Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
  | cons found child _ ih => simp [List.mapM_cons, child.projected found, ih, Functor.map, Except.map, bind, Except.bind]

/-- The child extraction is a static compiler receipt. Concrete General trees
close their meaning independently through `Typed.preserves` and `Typed.reflects`.
The supplied source types are raw builtin types, as required by the validator. -/
theorem tree_of_functions
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel readFuel : Nat} {compilation : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {sourceContext : SourceSemantics.Context} {solved : List SolvedRequirement}
    {scope : Scope} {id callee : ExpressionId} {arguments : List ExpressionId} {function : BuiltinFunctionId}
    {node : ExpressionNode} {type : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin function))
    (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (sourceType : node.type = function.returnType)
    (read : policy.readExpression source id = .ok (node, type))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (children : ∀ codes, arguments.mapM (fun argument =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel compilation source scope argument reasonAt) = .ok codes →
      DataExpressionSequence.Tree source (CompatibleExpressionGeneral.Tree readFuel values source sourceContext solved reasonAt)
        scope arguments function.parameterTypes codes)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext solved reasonAt scope id lowered := by
  obtain ⟨calleeNode, calleeType, calleeCode, codes, expression, _, _, reference,
    argumentsAccepted, _, resultType, emitted, rfl⟩ :=
    call_of_accepted metadata.owner metadata.found read form special accepted
  cases reference with
  | @intro index identity calleeExpression _ _ _ _ decorated =>
    rw [profile, ActualCallablePolicy.builtin_decoration native active compilation source calleeNode function
      (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) _ descriptor] at decorated
    cases decorated
    rw [profile, builtin_call native active compilation source node callee arguments function type _ _ descriptor form] at emitted
    cases emitted
    subst type
    have argumentTrees := children codes argumentsAccepted
    have projected := argument_types argumentTrees
    rw [CompatibleBuiltinMeaning.argumentTypes_project function] at projected
    have nativeTypes := (Except.ok.inj projected).symm
    exact .contracted metadata form sourceType argumentTrees nativeTypes
end Solcore.SourceSemantics.CoreLowering.BuiltinCalls.Typed
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinCallNativeTyping
/-! Native typing follows the actual contracted builtin and ordered argument
packing. The scalar consumer extracts all child receipts from the real compiler
callback; native child typing is not a premise of that consumer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinCallNativeTyping
open Core Frontend SourceInference DataPatternValues
open CompatibleExpressionScalarNativeTyping CompatibleExpressionConstructorNativeTyping

theorem result_wellFormed (function : BuiltinFunctionId) (definitions : DataEnvironment) :
    (SourceCoreInteger.builtinResult function).WellFormed definitions := by
  cases function <;> constructor

theorem contracted_native (function : BuiltinFunctionId) (identity contract : Word)
    (definitions : DataEnvironment) (context : Core.Context) :
    HasType context (BuiltinCalls.Protocol.contracted function identity contract)
      (LanguageResult.resultType (CallableContract.functionType
        (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function))) definitions :=
  LanguageResult.success_hasType (CallableContract.wrap_hasType contract
    (TaggedFunction.identified_hasType identity (SourceCoreInteger.builtinClosure_hasType function)))

theorem call_native {definitions : DataEnvironment} {context : Core.Context}
    (function : BuiltinFunctionId) (identity contract unknown : Word)
    {arguments : SourceCoreBasic.LoweredExpr}
    (typed : NativeTyping definitions context arguments)
    (parameter : arguments.type = SourceCoreInteger.builtinParameter function) :
    NativeTyping definitions context
      ⟨SourceCoreInteger.builtinResult function,
        CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
          (BuiltinCalls.Protocol.contracted function identity contract) arguments.expression⟩ := by
  refine ⟨result_wellFormed function definitions, CallableContract.call_hasType [⟨contract, none, none⟩] unknown
    (result_wellFormed function definitions) (contracted_native function identity contract definitions context) ?_⟩
  simpa only [parameter] using typed.2

theorem Head.native {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {definitions : DataEnvironment} {context : Core.Context}
    (head : BuiltinCalls.Typed.Head values source certificate scope id lowered)
    (children : ∀ child code, certificate scope child code → NativeTyping definitions context code) :
    NativeTyping definitions context lowered := by
  cases head with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType sequence nativeTypes =>
    apply call_native function identity contract unknown (packed_native sequence children)
    rw [packed_type, nativeTypes, CompatibleBuiltinMeaning.argumentTypes_pack]

private theorem receipts_of_mapM {error : Type} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {certificate : GenericExpressionMeaning.Certificate}
    (compile : ExpressionId → Except error SourceCoreBasic.LoweredExpr)
    {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
    (accepted : ids.mapM compile = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ code, compile id = .ok code →
      ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code) :
    ListRel (fun id code => ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code) ids codes := by
  induction ids generalizing codes with
  | nil => simp at accepted; subst codes; exact .nil
  | cons id ids ih =>
    cases first : compile id with
    | error reason => simp [List.mapM_cons, first, bind, Except.bind] at accepted
    | ok code =>
      cases rest : ids.mapM compile with
      | error reason => simp [List.mapM_cons, first, rest, bind, Except.bind] at accepted
      | ok tail =>
        simp only [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
        subst codes
        exact .cons (extract id (by simp) code first)
          (ih rest (fun child member => extract child (List.mem_cons_of_mem id member)))

/-- The actual dispatcher checks the packed parameter type and authenticates
the builtin decoration and gate. Only real argument callbacks are consumed. -/
theorem of_functions {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {node : ExpressionNode} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {definitions : DataEnvironment} {context : Core.Context}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin function))
    (owner : id.occurrence.owner = source.owner) (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (children : ∀ child, child ∈ arguments → ∀ code,
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel compilation source scope child reasonAt = .ok code →
      ∃ node, source.lookupExpression? child = some node ∧ NativeTyping definitions context code)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) : NativeTyping definitions context lowered := by
  obtain ⟨calleeNode, calleeType, calleeCode, codes, expression, _, _, reference,
    argumentsAccepted, parameter, resultType, emitted, rfl⟩ :=
    BuiltinCalls.call_of_accepted owner found read form special accepted
  cases reference with
  | @intro index identity calleeExpression _ _ _ _ decorated =>
    rw [profile, ActualCallablePolicy.builtin_decoration native active compilation source calleeNode function
      (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) _ descriptor] at decorated
    cases decorated
    rw [profile, BuiltinCalls.Typed.builtin_call native active compilation source node callee arguments function
      type _ _ descriptor form] at emitted
    cases emitted
    subst type
    have receipts := receipts_of_mapM (scope := scope)
      (certificate := fun _ _ code => NativeTyping definitions context code)
      (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel compilation source scope child reasonAt)
      argumentsAccepted children
    obtain ⟨_, sequence⟩ := DataExpressionSequence.Tree.of_children
      (source := source) (scope := scope)
      (certificate := fun _ _ code => NativeTyping definitions context code) receipts
    exact call_native function identity descriptor.id native.diagnostics.unknown
      (packed_native sequence (fun _ _ typed => typed)) parameter

/-- Scalar source syntax and typing at the real argument callbacks close all
native child obligations under arbitrary administrative and ambient contexts. -/
theorem scalar_of_functions {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel readFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {node : ExpressionNode} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {definitions : DataEnvironment} {sourceContext : SourceSemantics.Context}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin function))
    (owner : id.occurrence.owner = source.owner) (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (ordinary : CompatibleExpressionConditionals.PolicyFor policy compilation readFuel values source scope reasonAt)
    (coercions : ∀ child node, CompatibleExpressionConditionals.Syntax source child →
      source.lookupExpression? child = some node → node.coercions = [])
    (argumentsTyped : ∀ child, child ∈ arguments → ∃ node,
      source.lookupExpression? child = some node ∧ CompatibleExpressionConditionals.Syntax source child ∧
        ExpressionHasType source sourceContext child node.type)
    (scopeWF : ScopeWellFormed values.checked.catalog.definitions scope)
    (administrative : Core.Context) (extension : values.checked.catalog.definitions.Extends definitions)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  apply of_functions native active profile descriptor owner found read form special _ accepted
  intro child member code generated
  obtain ⟨node, found, syntaxTree, typed⟩ := argumentsTyped child member
  exact ⟨node, found, conditionals_native_at scopeWF administrative extension
    (CompatibleExpressionConditionals.tree_of_functions unique declarations ordinary coercions syntaxTree found typed generated)⟩

end Solcore.SourceSemantics.CoreLowering.BuiltinCallNativeTyping
end

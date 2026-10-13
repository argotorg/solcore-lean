import Solcore.SourceSemantics.CoreLowering.SelectedCompilationExpressionSequence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinCallBounds

/-! The real contracted builtin call executes its ordered arguments once.
Its literal callee and both gates are pure; successful primitive application
keeps the reached heap, store and caller records. Child failures retain their
original Source scope and diagnostic. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectBuiltinBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open BuiltinCalls.Protocol
open GenericExpressionMeaning (agree_prefix rename_prefix)
universe u

open CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds (Point)

private theorem values_rep {checked : SourceCoreCompatibleCatalog.Checked} {receiving : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel checked receiving functions)
      mapping world types natives sources payloads) :
    ValuesRep checked receiving functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

private theorem prefixed_typed {definitions : DataEnvironment} {world : StoreTyping}
    {actual : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (function : BuiltinFunctionId) (identity contract : Word) :
    RuntimeEnvironmentHasTypes world (.unit :: contractedValue function identity contract actual :: actual)
      (.unit :: CallableContract.functionType (SourceCoreInteger.builtinParameter function)
        (SourceCoreInteger.builtinResult function) :: actualContext) definitions := by
  have closureTyped := SourceCoreInteger.builtinClosure_hasType (scope := actualContext) (definitions := definitions) function
  cases closureTyped with
  | lambda _ _ body => exact .cons .unit (.cons (.pair (.pair (.inRight .word) (.closure typed body)) .word) typed)

private theorem contracted_rename (function : BuiltinFunctionId) (identity contract : Word) (ξ : Renaming) :
    (contracted function identity contract).rename ξ = contracted function identity contract := by
  cases function <;> rfl

private theorem call_rename (function : BuiltinFunctionId) (identity contract unknown : Word)
    (arguments : Expr) (ξ : Renaming) :
    (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (contracted function identity contract) arguments).rename ξ =
    CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (contracted function identity contract) (arguments.rename ξ) := by
  simp [CallableContract.call, LanguageResult.bind, CallableContract.dispatch, CallableContract.guardResult,
    CallableContract.Gate.reason, LanguageResult.success, LanguageResult.failure,
    contracted_rename, Expr.rename, Renaming.lift]

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
  {ids : List ExpressionId} {function : BuiltinFunctionId} {codes : List SourceCoreBasic.LoweredExpr}
  {identity contract unknown : Word}
  (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
    (SourceCoreInteger.builtinResult function))
  (form : node.form = .call callee ids (.builtinFunction function))
  (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "headCode" => SourceCoreBasic.LoweredExpr.mk (SourceCoreInteger.builtinResult function)
  (CallableContract.call [CallableContract.Gate.mk contract none none] unknown (SourceCoreInteger.builtinResult function)
    (contracted function identity contract) (SourceCoreBasic.LoweredExpr.expression (SourceCoreCalls.packArguments codes)))

include bridge functions observations faults unique metadata form nativeTypes in
theorem preserves {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids function.parameterTypes codes)
    (childMeaning : PreservesBelow bridge context model registry invocation children faults size) :
    PreservesAt bridge context model registry invocation (Point scope id headCode) faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨typing, sourceResult⟩ := CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types
    unique metadata.found form metadata.coercions typed
  have prefixed := prefixed_typed actualTyped function identity contract
  have agreesPrefix : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: contractedValue function identity contract actual :: actual) :=
    agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
  rcases CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.children unique metadata.found form trace with
    ⟨sequenceSize, invocationSize, argumentsHeap, sources, sameSize, sourceTrace, applied⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, payloads, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_values bridge size sequence unique typing
        childMeaning environments heaps locals agreesPrefix prefixed initial admitted sourceTrace within
    have represented := values_rep payloads
    rw [nativeTypes] at represented
    have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
    obtain ⟨value, sameOutcome, sameHeap, _grade, primitive⟩ :=
      CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds.source_value functions observations represented applied
    subst outcome
    subst after
    rw [rename_prefix, rename_prefix] at evaluated
    obtain ⟨actualResult, nativeResult, actualPrimitive, resultRep, completed⟩ := contracted_preserves
      (identity := identity) (contract := contract) (unknown := unknown) inputs evaluated
    have same := actualPrimitive.functional primitive
    subst actualResult
    refine ⟨.inRight .word nativeResult, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, ?_⟩
    · rw [call_rename]; exact completed
    · rw [sourceResult]
      exact .value (CompatibleBuiltinMeaning.result_represents inputs primitive resultRep)
    · refine ⟨post.rows, ?_⟩
      intro value same
      cases same
      exact ⟨sourceResult ▸ primitive.preserves.2, post.at_values.heap⟩
  · subst outcome
    have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_fault bridge size sequence unique typing
        childMeaning environments heaps locals agreesPrefix prefixed initial admitted sourceTrace within
    rw [rename_prefix, rename_prefix] at evaluated
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, ?_⟩
    · rw [call_rename]
      exact CallableContract.call_argument_failure [⟨contract, none, none⟩] unknown
        (contracted_evaluates function identity contract actual store)
        (gates_accept contract unknown .beforeArguments) evaluated
    · exact post.fault

include bridge functions observations faults unique metadata form nativeTypes in
theorem reflects {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids function.parameterTypes codes)
    (childMeaning : ReflectsBelow bridge context model registry invocation children faults size) :
    ReflectsAt bridge context model registry invocation (Point scope id headCode) faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨typing, sourceResult⟩ := CallableIndexedOwnedPreparedStagedBuiltinSourceInversion.source_types
    unique metadata.found form metadata.coercions typed
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.builtinFunction function)) :=
    ⟨node, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have prefixed := prefixed_typed actualTyped function identity contract
  have agreesPrefix : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: contractedValue function identity contract actual :: actual) :=
    agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
  rw [call_rename] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedBuiltinCallBounds.contracted_arguments_sized completed
  have shifted := argumentEvaluation
  rw [← rename_prefix, ← rename_prefix] at shifted
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
    SelectedCompilationExpressionSequence.reflects bridge size sequence unique typing childMeaning
      environments heaps locals agreesPrefix prefixed initial admitted shifted smaller
  cases represented with
  | @values sources values payloads =>
    have represented := values_rep payloads
    rw [nativeTypes] at represented
    have inputs := CompatibleBuiltinMeaning.input_of_values observations represented
    obtain ⟨sourceValue, nativeValue, primitive, resultRep, same, sameStore⟩ :=
      contracted_reflects inputs argumentEvaluation.sound completed.sound
    subst value
    subst finalStore
    have trace := Staging.Recursive.Size.Expression.builtinApplied occurrence sourceTrace
      (Staging.Recursive.Size.Applies.builtin primitive)
    refine ⟨_, _, argumentsHeap, finalMap, finalWorld, trace, ?_, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, ?_⟩
    · rw [sourceResult]
      exact .value (CompatibleBuiltinMeaning.result_represents inputs primitive resultRep)
    · refine ⟨post.rows, ?_⟩
      intro value same
      cases same
      exact ⟨sourceResult ▸ primitive.preserves.2, post.at_values.heap⟩
  | fault matched =>
    have failed := CallableContract.call_argument_failure
      (result := SourceCoreInteger.builtinResult function) [⟨contract, none, none⟩] unknown
      (contracted_evaluates function identity contract actual store)
      (gates_accept contract unknown .beforeArguments) argumentEvaluation.sound
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
    have trace := Staging.Recursive.Size.Expression.builtinArgumentsFault occurrence sourceTrace
    refine ⟨_, _, argumentsHeap, finalMap, finalWorld, trace, .fault matched, finalHeaps,
      maps, worlds, frame, heapMetadata, reached, related, ?_⟩
    exact post.fault

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectBuiltinBounds

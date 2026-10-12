import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorSourceInversion
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionInstantiationLaws

/-! Nominal construction uses the actual metadata header and ordered recursive
children. A reached child failure keeps its original scope and heap; successful
construction retains the same caller state and the exact constructor payload. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CompatibleExpressionConstructors (construct_rename construct_success construct_failure)
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private theorem valuesRep {values : SourceCoreCompatibleValues.Context} {receiving : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
      mapping world types natives sources payloads) :
    ValuesRep values.checked receiving functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "valuesContext" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked

include bridge functions extension faults unique wellFormed runtime covers in
theorem constructor_preserves {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId} {tag : ConstructorId}
    {header : Word} {codes : List SourceCoreBasic.LoweredExpr} {children : GenericExpressionMeaning.Certificate}
    (size : Nat) (childMeaning : PreservesBelow bridge context model registry invocation children faults size)
    (receipt : CompatibleExpressionConstructors.Header valuesContext invocation.source id node instantiation tag header codes)
    (form : node.form = .constructor instantiation ids)
    (admissible : SourceSemantics.DataConstructorInstantiation.Admissible context instantiation)
    (ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution)
    (_count : ids.length = instantiation.payloadTypes.length)
    (_nodes : CompatibleExpressionConstructors.Nodes invocation.source ids instantiation.payloadTypes codes)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids instantiation.payloadTypes codes) :
    PreservesAt bridge context model registry invocation
      (Point scope id ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩)
      faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  have valid := CompatibleSourceInstantiationClosure.constructor_valid admissible runtime.variables_closed ranges
  obtain ⟨_admissible, typing, _sourceType⟩ := CompatibleExpressionConstructors.constructor_source_types
    unique receipt.metadata.found form receipt.metadata.coercions typed
  rcases CallableIndexedOwnedPreparedStagedConstructorSourceInversion.children unique receipt.metadata.found form trace with
    ⟨sequenceSize, sources, sameSize, outcomeEq, sourceTrace⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · subst outcome
    have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, payloads, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_values bridge size sequence unique typing
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace within
    refine ⟨.inRight .word (.constructed tag (.pair (.word header) (packValues values))), finalStore, finalMap, finalWorld,
      ?_, ?_, finalHeaps, maps, worlds, frame, metadata, reached, related, ?_⟩
    · rw [construct_rename]
      exact construct_success tag header evaluated
    · rw [receipt.sourceType]
      exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registryOwner)
        receipt.selected (receipt.sourceType ▸ receipt.metadata.projected) receipt.registered (valuesRep (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) payloads))
    · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame
  · subst outcome
    have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_fault bridge size sequence unique typing
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace within
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ?_⟩
    · rw [construct_rename]
      exact construct_failure tag header evaluated
    · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame

include bridge functions extension faults unique wellFormed runtime covers in
theorem constructor_reflects {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId} {tag : ConstructorId}
    {header : Word} {codes : List SourceCoreBasic.LoweredExpr} {children : GenericExpressionMeaning.Certificate}
    (size : Nat) (childMeaning : ReflectsBelow bridge context model registry invocation children faults size)
    (receipt : CompatibleExpressionConstructors.Header valuesContext invocation.source id node instantiation tag header codes)
    (form : node.form = .constructor instantiation ids)
    (admissible : SourceSemantics.DataConstructorInstantiation.Admissible context instantiation)
    (ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution)
    (_count : ids.length = instantiation.payloadTypes.length)
    (_nodes : CompatibleExpressionConstructors.Nodes invocation.source ids instantiation.payloadTypes codes)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids instantiation.payloadTypes codes) :
    ReflectsAt bridge context model registry invocation
      (Point scope id ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩)
      faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  have valid := CompatibleSourceInstantiationClosure.constructor_valid admissible runtime.variables_closed ranges
  obtain ⟨_admissible, typing, _sourceType⟩ := CompatibleExpressionConstructors.constructor_source_types
    unique receipt.metadata.found form receipt.metadata.coercions typed
  rw [construct_rename] at completed
  obtain ⟨sequenceSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
  obtain ⟨sourceSize, sourceOutcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    CallableIndexedOwnedAdmittedStagedExpressionSequence.reflects bridge size sequence unique typing childMeaning
      environments heaps locals agrees actualTyped initial admitted childEvaluation smaller
  have occurrence : Staging.Recursive.Occurrence invocation child (.constructor instantiation ids) :=
    ⟨node, lookupExpression?_sound receipt.metadata.found, form, receipt.metadata.requirements, receipt.metadata.coercions⟩
  cases represented with
  | @values sources values payloads =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (construct_success tag header childEvaluation.sound)
      have trace := Staging.Recursive.Size.Expression.constructorValue occurrence valid sourceTrace
      refine ⟨_, _, after, finalMap, finalWorld, trace, ?_, finalHeaps,
        maps, worlds, frame, metadata, reached, related, ?_⟩
      · rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registryOwner)
          receipt.selected (receipt.sourceType ▸ receipt.metadata.projected) receipt.registered (valuesRep (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) payloads))
      · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (construct_failure tag header childEvaluation.sound)
      have trace := Staging.Recursive.Size.Expression.constructorFault occurrence sourceTrace
      exact ⟨_, _, after, finalMap, finalWorld, trace, .fault matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related,
        after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorHeadBounds

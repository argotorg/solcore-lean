import Solcore.SourceSemantics.CoreLowering.CellAwareScopeExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionExclusion

/-! Actual builtin references are pure leaves in a heap containing generalized
cells. Their real descriptor and captured runtime environment are retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeBuiltinValueBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeExpressionBounds
universe u

private theorem unchanged {program : Program} {stages : Staging.Recursive.Registry}
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {id : ExpressionId}
    {node : ExpressionNode} {name : String} {function : BuiltinFunctionId} {size : Nat}
    {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinFunction function))
    (empty : node.coercions = [])
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before id outcome after) :
    outcome = .value (.builtin ⟨function⟩) ∧ after = before := by
  have same_node : ∀ {other}, ContainsExpression invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have same_occurrence : ∀ {actual requirements}, Staging.Recursive.Occurrence invocation id actual requirements →
      actual = .reference name (.builtinFunction function) := by
    intro actual requirements occurrence
    obtain ⟨other, contains, same, _requirements, _coercions⟩ := occurrence
    cases same_node contains
    exact same.symm.trans form
  cases trace with
  | atomicValue contains _ _ raw =>
    cases same_node contains
    rw [form] at raw
    cases raw
    exact ⟨rfl, rfl⟩
  | atomicFault contains _ _ raw =>
    cases same_node contains
    rw [form] at raw
    cases raw
  | generalizedLocal contains localForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _ =>
    cases same_node contains
    simp [form] at localForm
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
    exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found empty contains))
  | pair occurrence _ _ | tupleValue occurrence _ _ | constructorValue occurrence _ _
  | unary occurrence _ _ | unaryInvalid occurrence _ _
  | binaryLeftInvalid occurrence _ _ | binaryShortCircuit occurrence _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | notCallable occurrence _ _ | sourceArity occurrence _ _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _
  | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _
  | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _
  | group occurrence _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _ | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _
  | conditional occurrence _ _ | conditionalFault occurrence _ | calleeFault occurrence _
  | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
    cases same_occurrence occurrence

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (included : (CallableIndexedBuiltinValues.model compiled.indexed profile).Includes functions)
  {context : SourceSemantics.Context} {named : SourceCoreGeneralFunctions.Function}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)

private abbrev Certificate : GenericExpressionMeaning.Certificate :=
  fun _ id lowered => Nonempty (CellAwareBuiltinValueCertificates.Header compiled.indexed invocation.source id lowered)

include included in
theorem preserves (unique : NodeOccurrencesUnique invocation.source) (size : Nat) :
    PreservesAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions)
      named stages invocation (Certificate (compiled := compiled) (invocation := invocation)) faults size := by
  intro scope id lowered receipt node found typed mapping world administrative environment canonical actual actualContext
    before store embedding outcome after environments heaps locals agrees actualTyped initial admitted _authority _physical _owner _ownerFrame trace
  obtain ⟨receipt⟩ := receipt
  have same := Option.some.inj (receipt.found.symm.trans found)
  cases same
  obtain ⟨rfl, rfl⟩ := unchanged unique found receipt.form receipt.coercions trace
  let native := BuiltinCalls.Protocol.contractedValue receipt.function receipt.identity receipt.descriptor.id actual
  have related : (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions).Represents
      mapping world receipt.node.type (.builtin ⟨receipt.function⟩) native lowered.type := by
    rw [receipt.sourceType, receipt.nativeType]
    exact .function (included (.builtin receipt.inventory receipt.number receipt.descriptor actualTyped))
  have evaluated : Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
    rw [receipt.rename, receipt.emitted]
    exact BuiltinCalls.Protocol.contracted_evaluates _ _ _ actual store
  refine ⟨.inRight .word native, store, mapping, world, evaluated, .value related,
    heaps, .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _, initial, callerProtocol.refl initial, ?_⟩
  exact ⟨admitted.rows, by
    intro value same
    cases same
    exact ⟨receipt.sourceType.symm ▸ Dynamic.ValueHasType.builtin ⟨receipt.function⟩, admitted.heap⟩⟩

include included in
theorem reflects (size : Nat) :
    ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions)
      named stages invocation (Certificate (compiled := compiled) (invocation := invocation)) faults size := by
  intro scope id lowered receipt node found typed mapping world administrative environment canonical actual actualContext
    before store embedding value finalStore environments heaps locals agrees actualTyped initial admitted _authority _physical _owner _ownerFrame completed
  obtain ⟨receipt⟩ := receipt
  have same := Option.some.inj (receipt.found.symm.trans found)
  cases same
  let native := BuiltinCalls.Protocol.contractedValue receipt.function receipt.identity receipt.descriptor.id actual
  have related : (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions).Represents
      mapping world receipt.node.type (.builtin ⟨receipt.function⟩) native lowered.type := by
    rw [receipt.sourceType, receipt.nativeType]
    exact .function (included (.builtin receipt.inventory receipt.number receipt.descriptor actualTyped))
  have evaluated : Evaluates actual store (lowered.expression.rename embedding) (.inRight .word native) store := by
    rw [receipt.rename, receipt.emitted]
    exact BuiltinCalls.Protocol.contracted_evaluates _ _ _ actual store
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed.sound
  have sourceTrace : Staging.Recursive.Size.Expression program stages (Staging.Recursive.Size.stepSize [])
      invocation context environment before id (.value (.builtin ⟨receipt.function⟩)) before :=
    .atomicValue (lookupExpression?_sound found) (receipt.form.symm ▸ .reference _ _) receipt.coercions
      (by rw [receipt.form, receipt.requirements]; exact .builtinFunction rfl)
  refine ⟨Staging.Recursive.Size.stepSize [], .value (.builtin ⟨receipt.function⟩), before, mapping, world,
    sourceTrace, .value related, heaps, .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _,
    initial, callerProtocol.refl initial, ?_⟩
  exact ⟨admitted.rows, by
    intro value same
    cases same
    exact ⟨receipt.sourceType.symm ▸ Dynamic.ValueHasType.builtin ⟨receipt.function⟩, admitted.heap⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeBuiltinValueBounds

import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLiteralGroupBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxyMeaning
import Solcore.SourceSemantics.Staging.RecursiveAtomicLifting

/-! A proxy leaf keeps its original raw type header, both heaps and the actual
caller. Its compiler receipt supplies all native and Source behavior. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProxyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CompatibleExpressionProxies
universe u

private theorem no_stage
    {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {size : Nat}
    {inner : TypeSystem.Ty} {failedScope call reason}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .proxy inner) (empty : node.coercions = [])
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      before id (.fault (.stage failedScope call reason)) after) : False := by
  have occurrence_form : ∀ {actual requirements},
      Staging.Recursive.Occurrence invocation id actual requirements → actual = .proxy inner := by
    intro actual requirements occurrence
    obtain ⟨actualNode, contains, sameForm, _requirements, _coercions⟩ := occurrence
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    exact sameForm.symm.trans form
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found empty contains)
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _
  | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _
  | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _ | group occurrence _
  | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _ | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _
  | applied occurrence _ _ _ _ _ _ => cases occurrence_form occurrence

variable {values : SourceCoreCompatibleValues.Context} {rawRegistry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry rawRegistry)
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  (unique : NodeOccurrencesUnique invocation.source)
  (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel values.checked rawRegistry functions

include extension unique in
theorem preserves (size : Nat) :
    PreservesAt bridge context model registry invocation
      (Certificate values invocation.source) faults size := by
  intro scope id lowered certificate node found typed
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  cases certificate with
  | @proxy other inner owner header receipt =>
    cases Option.some.inj (receipt.metadata.found.symm.trans found)
    have unchanged : outcome = .value (.proxy inner) ∧ after = before := by
      cases outcome with
      | value value =>
        obtain ⟨same, heap⟩ := receipt.source_outcome unique (.value trace.sound.value_plain)
        exact ⟨congrArg Staging.Recursive.Outcome.value (Dynamic.ExpressionOutcome.value.inj same), heap⟩
      | fault failure =>
        cases failure with
        | semantic reason =>
          obtain ⟨impossible, _⟩ := receipt.source_outcome unique (.fault trace.sound.semanticFault_plain)
          cases impossible
        | stage failedScope call reason =>
          exact False.elim (no_stage unique found receipt.form receipt.metadata.coercions trace)
    obtain ⟨rfl, rfl⟩ := unchanged
    refine ⟨.inRight .word (.constructed ⟨owner, 0⟩ (.word header)), store, mapping, world,
      receipt.native_evaluates actual store ξ, .value (receipt.represents functions extension mapping world),
      heaps, .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, ?_⟩
    exact ⟨admitted.rows, by
      intro result same
      cases same
      exact ⟨by rw [receipt.sourceType]; exact .proxy inner, admitted.heap⟩⟩

include extension in
theorem reflects (size : Nat) :
    ReflectsAt bridge context model registry invocation
      (Certificate values invocation.source) faults size := by
  intro scope id lowered certificate node found typed
    mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  cases certificate with
  | @proxy other inner owner header receipt =>
    cases Option.some.inj (receipt.metadata.found.symm.trans found)
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic (receipt.native_evaluates actual store ξ) completed.sound
    have sourceTrace : Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [])
        invocation context environment before id (.value (.proxy inner)) before :=
      .atomicValue (lookupExpression?_sound found) (by rw [receipt.form]; exact .proxy inner)
        receipt.metadata.coercions (by rw [receipt.form, receipt.metadata.requirements]; exact .proxy rfl)
    refine ⟨Staging.Recursive.Size.stepSize [], .value (.proxy inner), before, mapping, world,
      sourceTrace, .value (receipt.represents functions extension mapping world), heaps,
      .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, ?_⟩
    exact ⟨admitted.rows, by
      intro result same
      cases same
      exact ⟨by rw [receipt.sourceType]; exact .proxy inner, admitted.heap⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProxyBounds

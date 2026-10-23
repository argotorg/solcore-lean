import Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadAdmission
import Solcore.SourceSemantics.CoreLowering.CellAwareReadMeaningEffects
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionBounds

/-! Actual monomorphic reads retain generalized cells elsewhere in the same
Source heap. Descriptor absence is derived only at the selected binding from
its compiler receipt and Source heap typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationReadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CompatibleExpressionReads
open CallableIndexedOwnedFunctionState
open CellAwareInvocationExpressionBounds
universe u

private theorem no_stage
    {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {size : Nat}
    {name : String} {binder : Resolved.LocalId} {failedScope call reason}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (coercions : node.coercions = [])
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      before id (.fault (.stage failedScope call reason)) after) : False := by
  have reference : ∀ {shape requirements}, Staging.Recursive.Occurrence invocation id shape requirements →
      shape = .reference name (.local binder) := by
    intro shape requirements occurrence
    obtain ⟨other, contains, sameForm, _, _⟩ := occurrence
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    exact sameForm.symm.trans form
  cases trace with
  | generalizedLocal contains _ _ _ _ _ _ _ path =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [coercions] at path
      cases path
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found coercions contains))
  | group occurrence _
  | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _
  | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
      cases reference occurrence

/-- Reconstruct only an ordinary readable local, using its actual cell. The
generalized-local alternatives are excluded by that same cell's descriptor. -/
private theorem staged_of_read
    {fuel : Nat} {values : ValuesContext} {invocation : Staging.Recursive.Scope}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel values invocation.source scope id reason code)
    {program : Program} {registry : Staging.Recursive.Registry} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    (read : Dynamic.Heap.Reads before location cell)
    (ordinary : cell.generalized = none)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
      environment before id outcome after) :
    Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [])
      invocation context environment before id
      (match outcome with | .value value => .value value | .fault fault => .fault (.semantic fault)) after := by
  have same_node : ∀ {other}, ContainsExpression invocation.source id other → other = certificate.node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans certificate.metadata.found)
  have same_cell : ∀ {otherLocation otherCell},
      Dynamic.Environment.LooksUp environment certificate.binder otherLocation →
      Dynamic.Heap.Reads before otherLocation otherCell → otherCell = cell := by
    intro otherLocation otherCell otherLookup otherRead
    have sameLocation := otherLookup.functional lookup
    subst otherLocation
    exact otherRead.functional read
  have contains := lookupExpression?_sound certificate.metadata.found
  have atomic : Staging.Recursive.AtomicForm certificate.node.form := by
    rw [certificate.form]
    exact .reference _ _
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro otherContains raw coercions =>
      cases same_node otherContains
      rw [certificate.metadata.coercions] at coercions
      cases coercions
      exact .atomicValue contains atomic certificate.metadata.coercions
        (by simpa only [certificate.metadata.coercions] using raw)
    | generalizedLocal otherContains otherForm _ otherLookup otherRead descriptor _ _ _ =>
      cases same_node otherContains
      rw [certificate.form] at otherForm
      cases otherForm
      cases same_cell otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
    | form otherContains raw =>
      cases same_node otherContains
      exact .atomicFault contains atomic certificate.metadata.coercions
        (by simpa only [certificate.metadata.coercions] using raw)
    | coercion otherContains _ failed =>
      cases same_node otherContains
      rw [certificate.metadata.coercions] at failed
      cases failed
    | generalizedLocalRequirement otherContains otherForm _ otherLookup otherRead descriptor _ _ _
    | generalizedLocalCoercion otherContains otherForm _ otherLookup otherRead descriptor _ _ _ =>
      cases same_node otherContains
      rw [certificate.form] at otherForm
      cases otherForm
      cases same_cell otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  (ordinaryCells : GenericHeap.OrdinaryCells
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {fuel : Nat} {reasonAt : ExpressionId → Word}
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ scope id lowered,
    LoweredRead fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "reads" => LoweredRead fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) invocation.source context reasonAt

include extension ordinaryCells semantic unique in
/-- The accepted local-read compiler discharges preservation internally. A
stage failure at this atomic occurrence is impossible; semantic failures keep
their original token, heap and actual caller state. -/
theorem preserves_local (size : Nat) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation
      (fun scope id lowered => reads scope id lowered ∧
        ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) faults size := by
  intro scope id lowered ⟨receipt, readFault⟩ node found sourceTyped
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted _authority _physical _owner _ownerFrame trace
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  have ordinary := locals.descriptor_empty_of_monomorphic admitted.heap
    binding.declared lookup read certificate.monomorphic
  have plain : ∃ plainOutcome : Dynamic.ExpressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
        environment before id plainOutcome after ∧
      outcome = (match plainOutcome with | .value value => .value value | .fault reason => .fault (.semantic reason)) := by
    cases outcome with
    | value value => exact ⟨.value value, .value trace.sound.value_plain, rfl⟩
    | fault failure => cases failure with
      | semantic reason => exact ⟨.fault reason, .fault trace.sound.semanticFault_plain, rfl⟩
      | stage failedScope call reason =>
        exact False.elim (no_stage unique found (nodeEq ▸ certificate.form) (nodeEq ▸ certificate.metadata.coercions) trace)
  obtain ⟨plainOutcome, plainTrace, outcomeEq⟩ := plain
  obtain ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata, effect⟩ :=
    certificate.scoped_preserves_with_diagnostics functions extension ordinaryCells program context invocation.evidence binding
      environments heaps admitted.heap locals agrees (fun location _ _ => readFault location) unique plainTrace
  simp only [SourceCoreCompatibleValues.Context.initial, nodeEq, typeEq] at represented finalHeaps
  let transport := administrativeTransport headers keys
  let reachedPool := transport.extend (bridge.pool initial) (.refl _) (.refl _) frame metadata
  obtain ⟨reached, _poolEq, related⟩ := bridge.restore initial reachedPool (.refl _) (.refl _)
    frame metadata (transport.related (bridge.pool initial) (.refl _) (.refl _) frame metadata)
  refine ⟨value, finalStore, mapping, world, ?_, ?_, finalHeaps, .refl _, .refl _,
    frame, metadata, effect, reached, related, ?_⟩
  · simpa only [← typeEq] using evaluated
  · cases represented with
    | value payload =>
      rw [outcomeEq]
      exact .value payload
    | fault matched =>
      rw [outcomeEq]
      exact .fault (semantic _ _ matched)
  · have rows := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
      (bridge.pool initial) (bridge.pool reached) admitted.rows frame
    cases outcome with
    | value sourceValue =>
      refine ⟨rows, ?_⟩
      intro value same
      cases same
      have preserved := SelectedCompilationReadAdmission.read_preserved certificate unique lookup read
        ordinary locals admitted.heap sourceTyped trace.sound.value_plain
      exact ⟨preserved.value_typed, preserved.heap_typed⟩
    | fault failure =>
      cases failure with
      | semantic reason => exact ⟨rows, by intro value same; cases same⟩
      | stage origin call reason => exact rows

include extension ordinaryCells semantic unique in
/-- A completed native read reconstructs the original atomic Source outcome
at grade one. Lazy mapping initialization retains its exact written cell and
every caller row at the same final store. -/
theorem reflects_local (size : Nat) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation
      (fun scope id lowered => reads scope id lowered ∧
        ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) faults size := by
  intro scope id lowered ⟨receipt, readFault⟩ node found sourceTyped
    mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted _authority _physical _owner _ownerFrame completed
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  have ordinary := locals.descriptor_empty_of_monomorphic admitted.heap
    binding.declared lookup read certificate.monomorphic
  obtain ⟨outcome, after, sourceTrace, represented, finalHeaps, frame, metadata, effect⟩ :=
    certificate.scoped_reflects_with_diagnostics functions extension ordinaryCells program context invocation.evidence binding
      environments heaps admitted.heap locals agrees (fun location _ _ => readFault location) (by simpa only [← typeEq] using completed.sound)
  simp only [SourceCoreCompatibleValues.Context.initial, nodeEq, typeEq] at represented finalHeaps
  have staged := staged_of_read (registry := registry) certificate unique lookup read ordinary sourceTrace
  let transport := administrativeTransport headers keys
  let reachedPool := transport.extend (bridge.pool initial) (.refl _) (.refl _) frame metadata
  obtain ⟨reached, _poolEq, related⟩ := bridge.restore initial reachedPool (.refl _) (.refl _)
    frame metadata (transport.related (bridge.pool initial) (.refl _) (.refl _) frame metadata)
  refine ⟨Staging.Recursive.Size.stepSize [], _, after, mapping, world, staged, ?_, finalHeaps,
    .refl _, .refl _, frame, metadata, effect, reached, related, ?_⟩
  · cases represented with
    | value payload => exact .value payload
    | fault matched => exact .fault (semantic _ _ matched)
  · have rows := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
      (bridge.pool initial) (bridge.pool reached) admitted.rows frame
    cases outcome with
    | value sourceValue =>
      refine ⟨rows, ?_⟩
      intro value same
      cases same
      have preserved := SelectedCompilationReadAdmission.read_preserved certificate unique lookup read
        ordinary locals admitted.heap sourceTyped staged.sound.value_plain
      exact ⟨preserved.value_typed, preserved.heap_typed⟩
    | fault reason => exact ⟨rows, by intro value same; cases same⟩

include extension ordinaryCells uninitialized semantic unique in
/-- The global diagnostic interface follows by restricting it to the actual read. -/
theorem preserves (size : Nat) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation reads faults size := by
  intro scope id lowered receipt
  exact preserves_local bridge functions extension ordinaryCells semantic unique size
    ⟨receipt, uninitialized scope id lowered receipt⟩

include extension ordinaryCells uninitialized semantic unique in
/-- The global diagnostic interface follows by restricting it to the actual read. -/
theorem reflects (size : Nat) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation reads faults size := by
  intro scope id lowered receipt
  exact reflects_local bridge functions extension ordinaryCells semantic unique size
    ⟨receipt, uninitialized scope id lowered receipt⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationReadBounds

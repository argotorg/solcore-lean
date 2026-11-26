import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementFlows

/-!
# Cell-aware invocations: the preserve flows of the writes to an element

The statement-level preserve flows of a write to one element of a local memory array, as companions of the
reflect flows: the Source's staged trace of an assignment `a[i] = v` or `a[i] op= v`, or of an in-place `~`
`a[i] ~=;`, inverted at one element (`ElementAssignmentSourceInversion.child_and_tail`, `single_fault`,
`single_resolved`, `ElementBitNotSourceInversion.child_and_tail`), each case run on the committed heads, the plain
one for `=` and the compound one otherwise, and the write followed by the remaining statements' preserved run under
the write's binders. Main declarations: `CellAwareInvocationElementAssignmentFlow.preserves` and
`CellAwareInvocationElementBitNotFlow.preserves`.
-/

section
/-! A root of an array's type that holds a value holds an array's reference. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteRoots
open Core Frontend SourceInference GeneralHeap CompatiblePayload

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {registry : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel compiled.indexed.layouts.definitions}
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {environment : Dynamic.Environment} {canonical actual : Environment} {heap : Dynamic.Heap} {store : Store}
  {ξ : Renaming} {root : Resolved.LocalId} {slot : Nat} {rootType : Ty} {location : Dynamic.Location}
  {cell : Dynamic.Cell}

/-- A root of an array's type that holds a value holds an array's reference, as its Core cell stands for it. -/
theorem holds_reference {element : TypeSystem.Ty} {value : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions)
      (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrative scope
      environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) instances) mapping world
      heap store)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slotEq : SourceCoreLocalCell.lookup? scope root = some (slot, rootType))
    (lookup : Dynamic.Environment.LooksUp environment root location)
    (read : Dynamic.Heap.Reads heap location cell) (cellType : cell.type = TypeSystem.Ty.array element)
    (initialValue : Dynamic.RootInitialValue cell (some value)) :
    ∃ element' arrayLocation, value = .arrayRef element' arrayLocation := by
  cases initialValue with
  | initialized =>
    obtain ⟨_, _, _, _, represented⟩ := cell_at environments heaps agrees slotEq lookup read rfl
    cases represented with
    | initialized rootRep =>
      exact array_source rootRep (element := element) (congrArg SourceCoreRawMetadata.runtimeType cellType)
  | emptyMapping => simp [TypeSystem.Ty.array] at cellType

end Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteRoots
end

section
/-! A plain write at one element has no write fault. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ElementAssignmentSourceInversion
open Frontend SourceInference Staging.Recursive

/-- `=` has no invalid operands. -/
theorem equal_operands_valid {selected : Option Dynamic.Value} {right : Dynamic.Value}
    (invalid : Dynamic.AssignmentOperandsInvalid .equal selected right) : False := by
  cases invalid with
  | uninitialized notEqual => exact notEqual rfl
  | compound corresponds _ => cases corresponds

/-- `=` does not panic. -/
theorem equal_operands_no_panic {targetType : TypeSystem.Ty} {selected : Option Dynamic.Value}
    {right : Dynamic.Value} {code : UInt8}
    (panics : Dynamic.AssignmentOperandsPanic targetType .equal selected right code) : False := by
  cases panics with
  | compound corresponds _ => cases corresponds

/-- A plain write at one element has no write fault: `=` has no invalid operands and no panic, and no structural
fault is at an element. -/
theorem plain_writeFault_absurd {target : Dynamic.ResolvedPlace} {right : Dynamic.Value} {heap : Dynamic.Heap}
    {reason : Dynamic.SemanticFault} {position : Nat}
    (failed : ProjectedTarget.WriteFault .equal target right heap reason)
    (single : target.projections = [.element position]) : False := by
  cases failed with
  | operands _ _ _ _ invalid => exact equal_operands_valid invalid
  | panic _ _ _ _ panics => exact equal_operands_no_panic panics
  | structural _ _ _ fault =>
    rw [single] at fault
    cases fault

end Solcore.SourceSemantics.CoreLowering.ElementAssignmentSourceInversion
end

section
/-! An assignment to one element of a local array, preserved: the element target's faults, the right side's
fault, the compound write's fault, or the write, then the remaining statements under the write's binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationElementAssignmentFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
  {expected : TypeSystem.Ty} {type : Ty} {id : StatementId} {node : StatementNode}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {rest : List StatementId} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (sourceEq : invocation.source = bodyIndex.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (found : invocation.source.lookupStatement? id = some node)
  (form : node.form = .assignValue assignment operator rhs)
  (head : CellAwareElementWriteHeads.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope assignment operator rhs)
  {identities : Dynamic.Value → Word → Prop}
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program stages)
  (uninitializedReason : ∀ location, faults (.semantic (.uninitializedLocation location)) head.invalidProjection)

include sourceEq unique found form observations uninitializedReason in
/-- An assignment to one element of a local array, `a[i] = v` or `a[i] op= v`, preserved: from the Source's staged
run, the element target's fault (a root not yet initialized, the index's fault at a root that holds its array, or
`0x32` from the array's length on), the right side's fault, the compound write's fault, or the write, by the plain
head for `=` and the compound head otherwise; the remaining statements' preserved run continues from the write's
binders. The root's own faults are excluded by its writable binder, the index's type fault by the Core type
`.word` of the index's code (`head.keyType`), and a plain write has no write fault. `uninitializedReason` is the
site's token at a root not yet initialized. -/
theorem preserves [RecursiveStageMeaning.FaultTokens faults]
    (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation
      certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages
      invocation faults administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages
      invocation faults administrative scope mode (id :: rest) expected type
      (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.assignment
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have element : Staging.Recursive.ElementPlace assignment.target.projections := ⟨[], head.key, head.single⟩
  -- The Source types: the right side's at its node's, and the index's at its node's.
  have rhsTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨_, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨_, _, indexTyped⟩ := Staging.Recursive.SelectedPreservation.element_place_typed (leading := [])
    (index := head.key) targetTyped head.single
  have keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type :=
    CellAwareArraySourceInversion.typed_type unique head.keyFound indexTyped ▸ indexTyped
  cases ElementAssignmentSourceInversion.child_and_tail unique found form element trace with
  | rootFault failed => exact False.elim (failed.excluded head.writable locals)
  | keysFault _ keyTrace =>
    exact (ElementAssignmentSourceInversion.single_keys_absurd head.single keyTrace).elim
  | targetFault failed =>
    cases ElementAssignmentSourceInversion.single_fault head.single failed with
    | root rootFailed => exact False.elim (rootFailed.excluded head.writable locals)
    | uninitialized lookup read initialValue =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame,
          metadata, effect, reached, related, stable⟩ :=
        CellAwareElementWriteHeads.preserves_uninitialized bridge functions head environments heaps agrees initial
          admitted lookup read initialValue uninitializedReason body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame,
        metadata, effect, reached, related,
        fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
    | @index _ _ _ rootValue _ _ lookup read initialValue indexed =>
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within
      obtain ⟨arrayElement, arrayLocation, rfl⟩ := CellAwareElementWriteRoots.holds_reference environments
        heaps agrees head.slotEq lookup read (CellAwareElementWriteHeads.root_cell_type head locals lookup read)
        initialValue
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame,
          metadata, effect, reached, related, stable⟩ :=
        CellAwareElementWriteHeads.preserves_index_fault bridge functions head environments heaps locals agrees
          actualTyped initial admitted authority physical owner sameLocation budget children lookup read
          initialValue keyTyped indexed (by omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame,
        metadata, effect, reached, related, fault_post bridge reached stable⟩
    | indexType _ _ _ indexed notWord _ =>
      -- The index's Core code is of `.word`, so its represented value is a word.
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within
      obtain ⟨_, _, _, _, _, represented, _⟩ :=
        children _ (by omega) head.keyChild head.keyFound keyTyped environments heaps locals agrees actualTyped
          initial admitted authority physical owner sameLocation indexed
      cases represented with
      | value indexPayload =>
        rw [head.keyType] at indexPayload
        obtain ⟨_, rfl, _⟩ := CompatibleExpressionPrimitives.word_fields indexPayload
        exact (notWord trivial).elim
    | outOfBounds lookup read initialValue indexed arrayRead stored beyond =>
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame,
          metadata, effect, reached, related, stable⟩ :=
        CellAwareElementWriteHeads.preserves_outOfBounds bridge functions head environments heaps locals agrees
          actualTyped initial admitted authority physical owner sameLocation budget children lookup read
          initialValue keyTyped indexed (by omega) arrayRead stored beyond body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame,
        metadata, effect, reached, related,
        fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | rhsFault resolved childTrace =>
    cases ElementAssignmentSourceInversion.single_resolved head.single resolved with
    | intro lookup read initialValue indexed arrayRead arrayValue selection =>
    simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within
    by_cases plain : operator = .equal
    · obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame,
          metadata, effect, reached, related, stable⟩ :=
        CellAwareElementWriteHeads.preserves_plain_rhs_fault bridge functions head environments heaps locals agrees
          actualTyped initial admitted authority physical owner sameLocation budget children plain lookup read
          initialValue keyTyped indexed (by omega) arrayRead arrayValue selection rhsTyped childTrace
          (by omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame,
        metadata, effect, reached, related, fault_post bridge reached stable⟩
    · obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame,
          metadata, effect, reached, related, stable⟩ :=
        CellAwareElementWriteHeads.preserves_compound_rhs_fault bridge functions head environments heaps locals
          agrees actualTyped initial admitted authority physical owner sameLocation budget children plain lookup
          read initialValue keyTyped indexed (by omega) arrayRead arrayValue selection rhsTyped childTrace (by omega)
          body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame,
        metadata, effect, reached, related, fault_post bridge reached stable⟩
  | writeFault resolved childTrace failed =>
    simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within
    by_cases plain : operator = .equal
    · subst plain
      cases ElementAssignmentSourceInversion.single_resolved head.single resolved with
      | intro _ _ _ _ _ _ _ => exact (ElementAssignmentSourceInversion.plain_writeFault_absurd failed rfl).elim
    · obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame,
          metadata, effect, reached, related, stable⟩ :=
        CellAwareElementWriteHeads.preserves_compound_write_fault bridge functions observations head environments
          heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique
          assignmentTyped budget plain children resolved (by omega) childTrace (by omega) failed body
          (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame,
        metadata, effect, reached, related,
        fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | success resolved childTrace write remainingTrace =>
    simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within
    by_cases plain : operator = .equal
    · obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, frame, metadata, effect, count,
          typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
        CellAwareElementWriteHeads.preserves_plain bridge functions head environments heaps locals agrees actualTyped
          initial admitted authority physical owner sameLocation unique assignmentTyped budget plain children
          resolved (by omega) childTrace (by omega) write
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, finalMaps, finalWorlds,
          finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (by omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger suffix reached
          nextAdmitted (authority.transport effect) (physical.transport effect frame) owner sameLocation ready
          remainingTrace
      have native := continuation body (LocalLoop.controlType type) (by
        simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using evaluated)
      exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps, maps.trans finalMaps,
        worlds.trans finalWorlds, frame.trans finalFrame, metadata.trans finalMetadata, effect.trans finalEffect,
        last, protocol.trans related lastRelated, post⟩
    · obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, frame, metadata, effect, count,
          typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
        CellAwareElementWriteHeads.preserves_compound bridge functions observations head environments heaps locals
          agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped budget
          plain children resolved (by omega) childTrace (by omega) write
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, finalMaps, finalWorlds,
          finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (by omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger suffix reached
          nextAdmitted (authority.transport effect) (physical.transport effect frame) owner sameLocation ready
          remainingTrace
      have native := continuation body (LocalLoop.controlType type) (by
        simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using evaluated)
      exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps, maps.trans finalMaps,
        worlds.trans finalWorlds, frame.trans finalFrame, metadata.trans finalMetadata, effect.trans finalEffect,
        last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationElementAssignmentFlow
end

section
/-! An in-place `~` at one element of a local array, preserved: the element target's faults, or the write, then
the remaining statements under the write's binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationElementBitNotFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
  {expected : TypeSystem.Ty} {type : Ty} {id : StatementId} {node : StatementNode}
  {assignment : AssignmentResolution}
  {rest : List StatementId} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (sourceEq : invocation.source = bodyIndex.source)
  (unique : NodeOccurrencesUnique invocation.source)
  (found : invocation.source.lookupStatement? id = some node)
  (form : node.form = .assignBitNot assignment)
  (head : CellAwareElementWriteHeads.BitNotHead (.initial compiled.compatible.checked) invocation.source context
    certificate scope assignment)
  (uninitializedReason : ∀ location, faults (.semantic (.uninitializedLocation location)) head.invalidProjection)

include sourceEq unique found form uninitializedReason in
/-- An in-place `~` at one element of a local array, `a[i] ~=;`, preserved: from the Source's staged run, the
element target's fault (a root not yet initialized, the index's fault at a root that holds its array, or `0x32`
from the array's length on), or the write; the remaining statements' preserved run continues from the write's
eight binders. The root's own faults are excluded by its writable binder, the index's type fault by the Core type
`.word` of the index's code (`head.keyType`), and the operand's fault by `preserves_bitNot_operand_fault`.
`uninitializedReason` is the site's token at a root not yet initialized. -/
theorem preserves [RecursiveStageMeaning.FaultTokens faults]
    (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation
      certificate faults budget)
    (tail : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages
      invocation faults administrative scope mode rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) bodyIndex producer stages
      invocation faults administrative scope mode (id :: rest) expected type
      (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.bit_not unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.bitNot
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have element : Staging.Recursive.ElementPlace assignment.target.projections := ⟨[], head.key, head.single⟩
  -- The index's Source type, at its node's.
  have keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type := by
    cases assignmentTyped with
    | intro targetTyped _ _ =>
      obtain ⟨_, _, indexTyped⟩ := Staging.Recursive.SelectedPreservation.element_place_typed (leading := [])
        (index := head.key) targetTyped head.single
      exact CellAwareArraySourceInversion.typed_type unique head.keyFound indexTyped ▸ indexTyped
  cases ElementBitNotSourceInversion.child_and_tail unique found form element trace with
  | rootFault failed => exact False.elim (failed.excluded head.writable locals)
  | keysFault _ keyTrace =>
    exact (ElementAssignmentSourceInversion.single_keys_absurd head.single keyTrace).elim
  | targetFault failed =>
    cases ElementAssignmentSourceInversion.single_fault head.single failed with
    | root rootFailed => exact False.elim (rootFailed.excluded head.writable locals)
    | uninitialized lookup read initialValue =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame,
          metadata, effect, reached, related, stable⟩ :=
        CellAwareElementWriteHeads.preserves_bitNot_uninitialized bridge functions head environments heaps agrees
          initial admitted lookup read initialValue uninitializedReason body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame,
        metadata, effect, reached, related,
        fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
    | @index _ _ _ rootValue _ _ lookup read initialValue indexed =>
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within
      obtain ⟨arrayElement, arrayLocation, rfl⟩ := CellAwareElementWriteRoots.holds_reference environments
        heaps agrees head.slotEq lookup read
        (CellAwareElementWriteHeads.bitNot_root_cell_type head locals lookup read) initialValue
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame,
          metadata, effect, reached, related, stable⟩ :=
        CellAwareElementWriteHeads.preserves_bitNot_index_fault bridge functions head environments heaps locals
          agrees actualTyped initial admitted authority physical owner sameLocation budget children lookup read
          initialValue keyTyped indexed (by omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame,
        metadata, effect, reached, related, fault_post bridge reached stable⟩
    | indexType _ _ _ indexed notWord _ =>
      -- The index's Core code is of `.word`, so its represented value is a word.
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within
      obtain ⟨_, _, _, _, _, represented, _⟩ :=
        children _ (by omega) head.keyChild head.keyFound keyTyped environments heaps locals agrees actualTyped
          initial admitted authority physical owner sameLocation indexed
      cases represented with
      | value indexPayload =>
        rw [head.keyType] at indexPayload
        obtain ⟨_, rfl, _⟩ := CompatibleExpressionPrimitives.word_fields indexPayload
        exact (notWord trivial).elim
    | outOfBounds lookup read initialValue indexed arrayRead stored beyond =>
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame,
          metadata, effect, reached, related, stable⟩ :=
        CellAwareElementWriteHeads.preserves_bitNot_outOfBounds bridge functions head environments heaps locals
          agrees actualTyped initial admitted authority physical owner sameLocation budget children lookup read
          initialValue keyTyped indexed (by omega) arrayRead stored beyond body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame,
        metadata, effect, reached, related,
        fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | operandFault resolved selected invalid =>
    simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within
    exact (CellAwareElementWriteHeads.preserves_bitNot_operand_fault bridge functions head environments heaps locals
      agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped budget children
      resolved (by omega) selected invalid).elim
  | success resolved write remainingTrace =>
    simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within
    obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, frame, metadata, effect, count,
        typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
      CellAwareElementWriteHeads.preserves_bitNot bridge functions head environments heaps locals agrees actualTyped
        initial admitted authority physical owner sameLocation unique assignmentTyped budget children resolved
        (by omega) write
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, finalMaps, finalWorlds,
        finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail _ (by omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger suffix reached
        nextAdmitted (authority.transport effect) (physical.transport effect frame) owner sameLocation ready
        remainingTrace
    have native := continuation body (LocalLoop.controlType type) (by
      simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
        SourceCoreDataPlaces.shift] using evaluated)
    exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps, maps.trans finalMaps,
      worlds.trans finalWorlds, frame.trans finalFrame, metadata.trans finalMetadata, effect.trans finalEffect,
      last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationElementBitNotFlow
end

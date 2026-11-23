import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementHeads

/-!
# Cell-aware invocations: the heads of a compound write to an element

The compound writes to one element of a local array, `a[i] op= v`, preserved: the prefix to the right side
(the root's check, the index, the bound and the lookup at the index, whose snapshot is the element present
there or the array's default), the right side faulting, the write's faults (represented operands are never
invalid, a panic fails `guard`'s check after the insert, and no structural fault is at an element), and the
write, whose Core run reaches its continuation under the eight binders. Main declarations:
`CellAwareElementWriteHeads.preserves_compound`, `preserves_compound_rhs_fault` and
`preserves_compound_write_fault`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

section
/-! The Core runs: the snapshot of the lookup's option, its typing, and `guard`'s failure after the insert. -/
namespace Solcore.SourceSemantics.CoreLowering.CompatibleElementWrites
open Core Frontend SourceCoreCompatibleDataPlaces

/-- The snapshot of the lookup's option: the entry present at the index, or the array's default. -/
theorem snapshot_evaluates {environment : Environment} {lookupStore : Store} {elementType valueType : Ty}
    {arrayLocation : Location} {position : Word} {length default mapping : Value} (found : Option Value)
    (read : lookupStore.read? arrayLocation = some (.pair length (.pair default mapping))) :
    Evaluates (OrderedMapping.optionValue valueType found :: .word position ::
        .cellRef elementType arrayLocation :: environment) lookupStore
      (.caseE (.var 0) (LanguageResult.success (.inRight .unit (.first (.second (.loadCell (.var 3))))))
        (LanguageResult.success (.inRight .unit (.var 0))))
      (.inRight .word (.inRight .unit (found.getD default))) lookupStore := by
  cases found with
  | none => exact snapshot_absent read
  | some _ => exact snapshot_present

/-- The lookup's option is typed at the option of the entries' type when the snapshot it gives is. -/
theorem optionValue_typed {world : StoreTyping} {definitions : DataEnvironment} {type : Ty} {default : Value} :
    ∀ {found : Option Value}, RuntimeValueHasType world (found.getD default) type definitions →
      RuntimeValueHasType world (OrderedMapping.optionValue type found) (.sum .unit type) definitions
  | none, _ => .inLeft .unit
  | some _, typed => .inRight typed

/-- A compound write or a `~` below the array's length whose `guard` fails: the snapshot, the right side and
`modified`'s leaf, then the insert of the leaf at the index, and `guard`'s check fails before the store. -/
theorem compound_guard_failure {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
    {comparison : SourceCoreCompatibleDataEquality.Prepared checked}
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
    {layout : OrderedMapping.Layout} (keyType : layout.keyType = .word)
    {environment : Environment} {store : Store} {slot : Nat} {storedType outputType cellType : Ty} {invalid : Word}
    {value next index : Expr} {location : Location} {leftType elementType : Ty} {arrayLocation : Location}
    {position length : Word} {rest found snapshot right changed length' default : Value}
    {modifier : ElementModifier} {entries : OrderedMapping.Entries} {reason : Word}
    {after lookupStore rhsStore modifiedStore final : Store}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (full : store.read? location = some (.inRight leftType (.cellRef elementType arrayLocation)))
    (indexed : Evaluates (.cellRef elementType arrayLocation :: environment) store (shift 1 index)
      (.inRight .word (.word position)) after)
    (read : after.read? arrayLocation = some (.pair (.word length) rest)) (within : position < length)
    (lookedUp : Evaluates (.word position :: .cellRef elementType arrayLocation :: environment) after
      (OrderedMapping.lookup layout comparison.expression (.second (.second (.loadCell (.var 1)))) (.var 0))
      (.inRight .word found) lookupStore)
    (snapshotted : Evaluates (found :: .word position :: .cellRef elementType arrayLocation :: environment) lookupStore
      (.caseE (.var 0) (LanguageResult.success (.inRight .unit (.first (.second (.loadCell (.var 3))))))
        (LanguageResult.success (.inRight .unit (.var 0))))
      (.inRight .word snapshot) lookupStore)
    (rhsEvaluated : Evaluates (snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
      lookupStore (shift 4 value) (.inRight .word right) rhsStore)
    (modifiedEvaluated : Evaluates
      (right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment) rhsStore
      (modified modifier.leafType modifier.operator modifier.bitNot (.var 1) (.var 0) modifier.invalidOperand
        modifier.wrap)
      (.inRight .word changed) modifiedStore)
    (current : modifiedStore.read? arrayLocation =
      some (.pair length' (.pair default (OrderedMapping.encode layout entries))))
    (wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word)
    (failed : Evaluates
      (OrderedMapping.encode layout
          (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries) ::
        changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
      (CompatibleMappingComparison.insertStore comparison layout
        (changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
        modifiedStore entries (.word position) changed)
      (SourceCoreDataPlaces.guard outputType modifier.operator
        (.letE (.storeCell (.var 6) (.pair (.first (.loadCell (.var 6)))
            (.pair (.first (.second (.loadCell (.var 6)))) (.var 0))))
          (shift 8 next)))
      (.inLeft outputType (.word reason)) final) :
    Evaluates environment store
      (code slot storedType outputType invalid comparison.expression value next (some modifier) layout index)
      (.inLeft outputType (.word reason)) final := by
  apply LanguageResult.bind_success _ (root_full reference full)
  simp only [arrayElementWrite]
  apply LanguageResult.bind_success _ indexed
  apply Evaluates.ifTrue (within_check read within)
  simp only [elementStore]
  rw [shift_closed comparison, shift_closed comparison]
  apply LanguageResult.bind_success _ lookedUp (LanguageResult.bind_success _ snapshotted
    (LanguageResult.bind_success _ rhsEvaluated (LanguageResult.bind_success _ modifiedEvaluated _)))
  let stack :=
    changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment
  have inserted := OrderedMapping.insert_evaluates (environment := stack)
    (mapping := .second (.second (.loadCell (.var 5)))) (keyExpr := .var 4) (valueExpr := .var 0)
    (keyEqual := comparison.expression) entries (.word position) changed
    (CompatibleMappingComparison.comparator comparison stack modifiedStore) GenericHeap.arrayKeyEqual
    (.second (.second (.loadCell (.var rfl) current))) (.var rfl) (.var rfl)
    (CompatibleEquality.prepared_evaluates_exact comparison stack modifiedStore)
    (CompatibleArrayEvaluation.word_comparisons prepared keyType stack modifiedStore wordKeys position _)
  exact LanguageResult.bind_success _ inserted failed

end Solcore.SourceSemantics.CoreLowering.CompatibleElementWrites
end

section
/-! The insert of an element's value into its array's Core cell without the write: only the insert's
Core-only cells are appended, and the cells stay related. -/
namespace Solcore.SourceSemantics.CoreLowering.CellAwareArrayReads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleArrayEvaluation

private theorem insert_closed_typed {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) (context : Core.Context) :
    HasType context expression type definitions := by
  have extended := typed.rename (mapping := Renaming.id) (target := context) (by intro index type found; cases found)
  simpa using extended

section Inserts
variable {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
  {comparison : SourceCoreCompatibleDataEquality.Prepared checked}
  (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
variable {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel checked registry functions) instances

include prepared in
/-- The insert of a value's entry into an array's Core cell's entries, from any stack whose top is the value and
in which `arrayExpr` loads the array's cell and `keyExpr` gives the position, before any write: the insert
appends only its Core-only cells, and the cells stay related. -/
theorem insert_preserve_at (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    {stack : Environment} {context : Core.Context}
    (stackTyped : RuntimeEnvironmentHasTypes world stack context ambient.definitions)
    {element : TypeSystem.Ty} {location : Dynamic.Location} {cell : Dynamic.Cell}
    {elements : List Dynamic.Value} {position : Word}
    (read : Dynamic.Heap.Reads heap location cell) (current : cell.value = some (.arrayObject element elements))
    {target : Location} {payload : Ty} {identity : DataTypeId}
    (mapped : mapping[location.index]? = some target)
    (typed : world[target]? = some (.product .word (.product payload (.namedData identity))))
    {coreStored : Value} {arrayExpr keyExpr : Expr}
    (arrayLoad : ∀ {current : Store} {value : Value}, current.read? target = some value →
      Evaluates stack current (.loadCell arrayExpr) value current)
    (arrayTyped : HasType context arrayExpr (.cell (.product .word (.product payload (.namedData identity))))
      ambient.definitions)
    (keyEvaluated : ∀ current : Store, Evaluates stack current keyExpr (.word position) current)
    (keyTyped : HasType context keyExpr .word ambient.definitions)
    (storedAt : stack[0]? = some coreStored) (storedTyped : context[0]? = some payload) :
    ∃ length default entries suffix futureWorld,
      store.read? target = some (.pair (.word length) (.pair default
        (OrderedMapping.encode ⟨.word, payload, identity⟩ entries))) ∧
      (∀ key value, (key, value) ∈ entries → ∃ word, key = .word word) ∧
      CompatibleMappingComparison.insertStore comparison ⟨.word, payload, identity⟩ stack store entries
        (.word position) coreStored = store ++ suffix ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld heap (store ++ suffix) ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping (store ++ suffix) := by
  obtain ⟨actualCell, coreValue, sourceRead, coreRead, stands⟩ := heaps.cells mapped
  have sameCell := Dynamic.Heap.Reads.functional read sourceRead
  subst sameCell
  cases stands with
  | optional optionalTyped _ =>
    have impossible := optionalTyped.symm.trans typed
    simp [Core.OptionalCell.cellType] at impossible
  | array cellTyped arrayed =>
    obtain ⟨element', elements', payload', identity', default, entries, cellEq, valueEq, typeEq, contents⟩ :=
      arrayed
    subst cellEq
    simp only [Option.some.injEq, Dynamic.Value.arrayObject.injEq] at current
    obtain ⟨sameElement, sameElements⟩ := current
    subst element' elements'
    subst valueEq
    rw [typeEq] at cellTyped
    have sameType := Option.some.inj (cellTyped.symm.trans typed)
    simp only [Ty.product.injEq, Ty.namedData.injEq, true_and] at sameType
    obtain ⟨samePayload, sameIdentity⟩ := sameType
    subst payload' identity'
    have wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word := by
      intro key value member
      obtain ⟨_, _, same⟩ := contents.keys key value member
      exact ⟨_, same⟩
    have inserted : Evaluates stack store
        (OrderedMapping.insert ⟨.word, payload, identity⟩ comparison.expression
          (.second (.second (.loadCell arrayExpr))) keyExpr (.var 0))
        (.inRight .word (OrderedMapping.encode ⟨.word, payload, identity⟩
          (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) coreStored entries)))
        (CompatibleMappingComparison.insertStore comparison ⟨.word, payload, identity⟩ stack store entries
          (.word position) coreStored) :=
      OrderedMapping.insert_evaluates (environment := stack)
        (mapping := .second (.second (.loadCell arrayExpr))) (keyExpr := keyExpr)
        (valueExpr := .var 0) (keyEqual := comparison.expression) entries (.word position) coreStored
        (CompatibleMappingComparison.comparator comparison stack store) GenericHeap.arrayKeyEqual
        (.second (.second (arrayLoad coreRead))) (keyEvaluated store) (.var storedAt)
        (CompatibleEquality.prepared_evaluates_exact comparison stack store)
        (word_comparisons prepared rfl stack store wordKeys position _)
    have comparisonTyped : HasType context comparison.expression
        (OrderedMapping.Layout.comparisonType ⟨.word, payload, identity⟩) ambient.definitions := by
      have closed := insert_closed_typed (comparison.typed.extend_definitions ambient.basePrefix) context
      rw [(word_comparison prepared).1] at closed
      simpa only [Core.OrderedMapping.Layout.comparisonType, SourceCoreCompatibleDataEquality.comparatorType,
        SourceCoreDataEquality.comparatorType] using closed
    have insertTyped : HasType context
        (OrderedMapping.insert ⟨.word, payload, identity⟩ comparison.expression
          (.second (.second (.loadCell arrayExpr))) keyExpr (.var 0))
        (LanguageResult.resultType (OrderedMapping.Layout.type ⟨.word, payload, identity⟩)) ambient.definitions :=
      OrderedMapping.insert_hasType contents.registered comparisonTyped
        (.second (.second (.loadCell arrayTyped))) keyTyped (.var storedTyped)
    obtain ⟨suffix, appended, _⟩ := CompatibleMappingComparison.helper_store_extension comparison stack store
      (OrderedMapping.Layout.insertParameter ⟨.word, payload, identity⟩)
      (OrderedMapping.Layout.type ⟨.word, payload, identity⟩)
      (OrderedMapping.insertBody ⟨.word, payload, identity⟩)
      (.pair (OrderedMapping.encode ⟨.word, payload, identity⟩ entries)
        (.pair (.pair (.word position) coreStored) (CompatibleMappingComparison.comparator comparison stack store)))
    have appended' : CompatibleMappingComparison.insertStore comparison ⟨.word, payload, identity⟩ stack store
        entries (.word position) coreStored = store ++ suffix := appended
    obtain ⟨futureWorld, worlds, futureHeaps, _, unchanged⟩ :=
      CellMappingHeap.evaluation_preserves_frame heaps stackTyped insertTyped inserted appended'
    rw [appended'] at futureHeaps unchanged
    exact ⟨_, default, entries, suffix, futureWorld, coreRead, wordKeys, appended', futureHeaps, worlds, unchanged⟩

end Inserts

end Solcore.SourceSemantics.CoreLowering.CellAwareArrayReads
end

namespace Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

namespace Head
variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

/-- The Core types of a compound write's eight binders, innermost first: the cell write's unit, the updated
entries, the leaf, the right side, the snapshot, the lookup's option, the index's word and the array's cell. -/
def compoundSlotTypes (head : Head values source context certificate scope assignment operator rhs) :
    Core.Context :=
  [.unit, head.layout.type, head.elementType, head.elementType, .sum .unit head.elementType,
    .sum .unit head.elementType, .word, head.rootType]

/-- A compound write's modifier: the route's, at the element's Core type. -/
theorem modifier_compound (head : Head values source context certificate scope assignment operator rhs)
    (compound : operator ≠ .equal) :
    head.modifier = some ⟨head.elementType,
      assignmentModifier assignment.target.type (head.elementType = .integer) operator, false, head.invalid,
      SourceCoreDataPlaces.placeWrap assignment.target.type operator false⟩ := by
  simp [Head.modifier, CompatibleElementWrites.modifierOf, compound, placeModifier]

end Head

/-- The leaf a compound assignment computes keeps its target's type, from the assignment's typing. -/
theorem compound_leaf_typed {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {node : ExpressionNode} {heap : Dynamic.Heap} {selected right updated : Dynamic.Value}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? rhs = some node)
    (typed : SourceAssignmentHasType source context assignment operator rhs) (compound : operator ≠ .equal)
    (selectedTyped : Dynamic.ValueHasType context heap selected assignment.target.type)
    (rightTyped : Dynamic.ValueHasType context heap right node.type)
    (applied : Dynamic.CompoundAssignmentApplies assignment.target.type operator (some selected) right updated) :
    Dynamic.ValueHasType context heap updated assignment.target.type := by
  have rightAt {type : TypeSystem.Ty} (rhsTyped : ExpressionHasType source context rhs type) :
      Dynamic.ValueHasType context heap right type := by
    obtain ⟨actual, contains, storedType⟩ := rhsTyped.stored_type
    have same : actual = node := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actual
    exact storedType ▸ rightTyped
  cases typed with
  | equal => exact absurd rfl compound
  | wordCompound kind targetTyped rhsTyped _ =>
    have targetEq := targetTyped.type_eq
    rw [targetEq] at selectedTyped ⊢
    exact applied.preserves (.word kind) targetEq (.some selectedTyped) (rightAt rhsTyped)
  | fixedCompound kind targetTyped rhsTyped _ =>
    have targetEq := targetTyped.type_eq
    rw [targetEq] at selectedTyped ⊢
    exact applied.preserves (.fixed kind) targetEq (.some selectedTyped) (rightAt rhsTyped)
  | shiftCompound kind targetTyped targetKind _ _ _ =>
    have targetEq := targetTyped.type_eq
    rw [targetEq] at selectedTyped ⊢
    exact applied.shiftPreserves kind targetKind targetEq (.some selectedTyped)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Heads
variable {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : Head (.initial compiled.compatible.checked) invocation.source context certificate scope assignment operator
    rhs)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context}
  {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions)
    (storageCatalog compiled.compatible.checked.catalog) mapping world administrative scope environment canonical)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
    (payloadModel compiled.compatible.checked registry functions)
    (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
    bodyIndex.owner bodyIndex.active mapping world before store environment)
  (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope
    canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)

local notation "acceptedCells" => GeneralizedLocalDescriptorHeap.cellModel
  (payloadModel compiled.compatible.checked registry functions)
  (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
local notation "acceptedInstances" => GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment

include head locals in
/-- The root's Source cell holds a reference to an array of the target's type, as its writable binder types it. -/
theorem root_cell_type {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root location)
    (read : Dynamic.Heap.Reads before location cell) :
    cell.type = TypeSystem.Ty.array assignment.target.type := by
  obtain ⟨_, staticLookup, _, _, bodyEq⟩ := head.writable.scheme
  obtain ⟨_, _, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
  cases lookup.functional staticLookupRuntime
  cases read.functional staticRead
  exact staticCellType.trans bodyEq

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame in
/-- The prefix of a compound write to one element, to its right side: the root's check, the index and the
bound pass, and the lookup at the index gives the element's snapshot, the entry present there or the array's
default, which represents the Source's snapshot at the target's type; the lookup appends only its Core-only
cells, and the caller's state follows. -/
theorem preserves_snapshot (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {element : TypeSystem.Ty} {arrayLocation : Dynamic.Location}
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root location)
    (read : Dynamic.Heap.Reads before location cell)
    (initialValue : Dynamic.RootInitialValue cell (some (.arrayRef element arrayLocation)))
    (keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type)
    {indexSize : Nat} {position : Word} {targetHeap : Dynamic.Heap} {arrayCell : Dynamic.Cell}
    {elements : List Dynamic.Value} {selected : Dynamic.Value}
    (indexed : Staging.Recursive.Size.Expression program stages indexSize invocation context environment before
      head.key (.value (.word position)) targetHeap)
    (indexBound : indexSize < budget)
    (arrayRead : Dynamic.Heap.Reads targetHeap arrayLocation arrayCell)
    (arrayValue : Dynamic.RootInitialValue arrayCell (some (.arrayObject element elements)))
    (selection : Dynamic.ValueAt elements position.val selected) :
    ∃ rootTarget arrayTarget keyStore lookupStore keyMap lookupWorld length rest found leftCore,
      actual[ξ head.slot]? = some (.cellRef (OptionalCell.cellType head.rootType) rootTarget) ∧
      store.read? rootTarget = some (.inRight .unit
        (.cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget)) ∧
      Evaluates (.cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget ::
          actual) store (shift 1 (head.keyCode.expression.rename ξ)) (.inRight .word (.word position)) keyStore ∧
      keyStore.read? arrayTarget = some (.pair (.word length) rest) ∧ position < length ∧
      Evaluates (.word position ::
          .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
        keyStore
        (OrderedMapping.lookup head.layout head.comparison.expression (.second (.second (.loadCell (.var 1))))
          (.var 0))
        (.inRight .word found) lookupStore ∧
      Evaluates (found :: .word position ::
          .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
        lookupStore
        (.caseE (.var 0) (LanguageResult.success (.inRight .unit (.first (.second (.loadCell (.var 3))))))
          (LanguageResult.success (.inRight .unit (.var 0))))
        (.inRight .word (.inRight .unit leftCore)) lookupStore ∧
      RuntimeValueHasType lookupWorld found (.sum .unit head.elementType) compiled.indexed.layouts.definitions ∧
      ValueRep compiled.compatible.checked registry functions keyMap lookupWorld assignment.target.type selected
        leftCore head.elementType ∧
      keyMap[arrayLocation.index]? = some arrayTarget ∧
      lookupWorld[arrayTarget]? = some (.product .word (.product head.elementType (.namedData head.identity))) ∧
      GenericHeap.CellHeapRepresents acceptedCells keyMap lookupWorld targetHeap lookupStore ∧
      LocationMap.Extends mapping keyMap ∧ WorldExtends world lookupWorld ∧
      AdministrativePreserved mapping store keyMap lookupStore ∧ Dynamic.HeapMetadataExtend before targetHeap ∧
      CellAwareScopeAuthority.Effect acceptedInstances mapping world before store keyMap lookupWorld targetHeap
        lookupStore ∧
      ∃ reached : callerProtocol.State ⟨scope, keyMap, lookupWorld, targetHeap, lookupStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached := by
  have cellType := root_cell_type head locals lookup read
  -- The root's Core cell holds the array's cell reference.
  obtain ⟨rootTarget, _, reference, full, represented⟩ :=
    CellAwareElementWriteRoots.initialized environments heaps agrees head.slotEq lookup read initialValue
  obtain ⟨arrayTarget, payload, identity, rfl, typeEq, mapped, typed, _⟩ := arrayRef_fields represented rfl
  simp only [Core.Ty.cell.injEq, Core.Ty.product.injEq, Core.Ty.namedData.injEq, true_and] at typeEq
  obtain ⟨rfl, rfl⟩ := typeEq
  -- The index's meaning, under the array's binder.
  obtain ⟨_, keyStore, keyMap, keyWorld, keyEval, keyRepresented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata,
      keyEffect, keyReached, keyRelated, keyPost⟩ :=
    meaning indexSize indexBound head.keyChild head.keyFound keyTyped environments heaps locals (agree_prefix agrees _)
      (.cons (.cellRef typed) actualTyped) initial admitted authority physical owner ownerFrame indexed
  rw [rename_prefix] at keyEval
  cases keyRepresented with
  | @value _ _ indexPayload =>
  rw [head.keyType] at indexPayload
  obtain ⟨_, sameWord, rfl⟩ := CompatibleExpressionPrimitives.word_fields indexPayload
  cases sameWord
  -- The lookup at the index: the entry present there or the array's default, which represents the Source's.
  obtain ⟨result, final, lookupWorld, suffix, coreReads, elementRep, lookupHeaps, lookupWorlds, lookupFrame,
      lookupAppend⟩ :=
    CellAwareArrayReads.reads_preserve head.prepared (layout := head.layout) keyHeaps (actualTyped.weaken keyWorlds)
      (.array arrayRead arrayValue.arrayObject_value selection.getElem?_eq)
      (represented.extend (.refl _) keyMaps keyWorlds) (by rw [cellType]) (.array assignment.target.type) rfl
      position.isLt
  rw [CellAwareArrayReads.ofNatModulo_self] at coreReads
  cases coreReads with
  | @array _ arrayTarget length position default entries arrayCoreRead below wordKeys =>
  have lookedUp := CellAwareArrayReads.lookup_evaluates head.prepared (layout := head.layout) rfl
    (environment := actual) (type := .product .word (.product head.elementType (.namedData head.identity)))
    (position := position) arrayCoreRead wordKeys
  have snapshotted := CompatibleElementWrites.snapshot_evaluates (environment := actual)
    (elementType := .product .word (.product head.elementType (.namedData head.identity)))
    (valueType := head.layout.valueType) (position := position)
    (OrderedMapping.lookupEntries GenericHeap.arrayKeyEqual (.word position) entries)
    (CompatibleArrayEvaluation.lookupStore_read (comparison := head.comparison) (layout := head.layout)
      (environment := .word position ::
        .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
      (entries := entries) (key := .word position) arrayCoreRead)
  have snapshotRep := elementRep.extend (.refl _) (.refl _) lookupWorlds
  -- The caller's pool after the lookup's Core-only cells.
  let suffixPool : State headers keys ⟨scope, keyMap, lookupWorld, targetHeap, _, canonical⟩ :=
    (bridge.pool keyReached).extend (.refl _) lookupWorlds lookupFrame (.refl _)
  obtain ⟨lookupReached, _, lookupRelated⟩ := bridge.restore keyReached suffixPool (.refl _) lookupWorlds
    lookupFrame (.refl _) (Relates.of_records_eq rfl)
  have lookupEffect : CellAwareScopeAuthority.Effect acceptedInstances keyMap keyWorld targetHeap keyStore keyMap
      lookupWorld targetHeap (CompatibleMappingComparison.lookupStore head.comparison head.layout
        (.word position :: .cellRef (.product .word (.product head.elementType (.namedData head.identity)))
          arrayTarget :: actual) keyStore entries (.word position)) := by
    rw [lookupAppend]
    exact CellAwareScopeAuthority.Effect.append keyStore suffix (.refl _) (.refl keyMap) lookupWorlds
  exact ⟨rootTarget, arrayTarget, keyStore, _, keyMap, lookupWorld, _, _, _, _, reference, full, keyEval,
    arrayCoreRead, below, lookedUp, snapshotted,
    CompatibleElementWrites.optionValue_typed snapshotRep.runtime_hasType, snapshotRep, keyMaps.lookup mapped,
    lookupWorlds.lookup (keyWorlds.lookup typed), lookupHeaps, keyMaps, keyWorlds.trans lookupWorlds,
    keyFrame.trans lookupFrame, keyMetadata, keyEffect.trans lookupEffect, lookupReached,
    callerProtocol.trans keyRelated lookupRelated, keyPost.at_value.2.heap,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool lookupReached) admitted.rows
      (keyFrame.trans lookupFrame)⟩

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame in
/-- A compound write's right side faulting: the root's check, the index, the bound and the element's
snapshot pass, and the right side's Core run fails as its Source run does, before `modified`. -/
theorem preserves_compound_rhs_fault (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    (compound : operator ≠ .equal)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {element : TypeSystem.Ty} {arrayLocation : Dynamic.Location}
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root location)
    (read : Dynamic.Heap.Reads before location cell)
    (initialValue : Dynamic.RootInitialValue cell (some (.arrayRef element arrayLocation)))
    (keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type)
    {indexSize : Nat} {position : Word} {middle : Dynamic.Heap} {arrayCell : Dynamic.Cell}
    {elements : List Dynamic.Value} {selected : Dynamic.Value}
    (indexed : Staging.Recursive.Size.Expression program stages indexSize invocation context environment before
      head.key (.value (.word position)) middle)
    (indexBound : indexSize < budget)
    (arrayRead : Dynamic.Heap.Reads middle arrayLocation arrayCell)
    (arrayValue : Dynamic.RootInitialValue arrayCell (some (.arrayObject element elements)))
    (selection : Dynamic.ValueAt elements position.val selected)
    (rhsTyped : ExpressionHasType invocation.source context rhs head.node.type)
    {rhsSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (rhsTrace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment middle rhs
      (.fault failure) after)
    (rhsBound : rhsSize < budget) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults failure token ∧
      GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after
        finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  obtain ⟨rootTarget, arrayTarget, keyStore, lookupStore, keyMap, lookupWorld, length, rest, found, leftCore,
      reference, full, keyEval, lengthRead, within, lookedUp, snapshotted, foundTyped, snapshotRep, _, typed,
      lookupHeaps, prefixMaps, prefixWorlds, prefixFrame, prefixMetadata, prefixEffect, prefixReached, prefixRelated,
      prefixAdmitted⟩ :=
    preserves_snapshot bridge functions head environments heaps locals agrees actualTyped initial admitted authority
      physical owner ownerFrame budget meaning lookup read initialValue keyTyped indexed indexBound arrayRead
      arrayValue selection
  obtain ⟨_, finalStore, finalMap, finalWorld, rhsEval, rhsRep, finalHeaps, maps, worlds, frame, metadata, effect,
      reached, related, post⟩ :=
    meaning rhsSize rhsBound head.right head.found rhsTyped (environments.extend prefixMaps prefixWorlds) lookupHeaps
      (locals.mono prefixMetadata)
      (agree_prefix (agree_prefix (agree_prefix (agree_prefix agrees
        (.cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget))
        (.word position)) found) (.inRight .unit leftCore))
      (.cons (.inRight snapshotRep.runtime_hasType) (.cons foundTyped (.cons .word (.cons (.cellRef typed)
        (actualTyped.weaken prefixWorlds)))))
      prefixReached prefixAdmitted (authority.transport prefixEffect) (physical.transport prefixEffect prefixFrame)
      owner ownerFrame rhsTrace
  rw [rename_prefix, rename_prefix, rename_prefix, rename_prefix] at rhsEval
  cases rhsRep with
  | fault matched =>
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, prefixMaps.trans maps,
      prefixWorlds.trans worlds, prefixFrame.trans frame, prefixMetadata.trans metadata, prefixEffect.trans effect,
      reached, callerProtocol.trans prefixRelated related, post.rows⟩
    rw [Head.emit, CompatibleElementWrites.code_rename, Head.modifier_compound head compound]
    exact CompatibleElementWrites.compound_rhs_failure reference full keyEval lengthRead within lookedUp snapshotted
      rhsEval

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique
  assignmentTyped observations in
/-- A compound write's fault after its right side, from the Source's `WriteFault` at one element: represented
operands are never invalid, a panic of the operation fails `guard`'s check with the panic's reason after the
insert, and no structural fault is at an element. -/
theorem preserves_compound_write_fault [RecursiveStageMeaning.FaultTokens faults] (budget : Nat)
    (compound : operator ≠ .equal)
    (meaning : PreservesBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    {targetSize rhsSize : Nat} {target : Dynamic.ResolvedPlace} {right : Dynamic.Value}
    {reason : Dynamic.SemanticFault} {targetHeap after : Dynamic.Heap}
    (targetTrace : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment
      before assignment.target (.resolved target) targetHeap)
    (targetBound : targetSize < budget)
    (trace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment targetHeap rhs
      (.value right) after)
    (rhsBound : rhsSize < budget)
    (failed : Staging.Recursive.ProjectedTarget.WriteFault operator target right after reason)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults (.semantic reason) token ∧
      GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after
        finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  -- The Source types: the right side's at its node's, and the index's at its node's.
  have rhsTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨_, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨_, _, indexTyped⟩ := Staging.Recursive.SelectedPreservation.element_place_typed (leading := [])
    (index := head.key) targetTyped head.single
  have keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type :=
    CellAwareArraySourceInversion.typed_type unique head.keyFound indexTyped ▸ indexTyped
  cases ElementAssignmentSourceInversion.single_resolved head.single targetTrace with
  | @intro indexSize _ cell element arrayLocation position _ _ elements selected lookup read initialValue indexed
      arrayRead arrayValue selection =>
  -- The root, the index, the bound and the element's snapshot.
  obtain ⟨rootTarget, arrayTarget, keyStore, lookupStore, keyMap, lookupWorld, length, rest, found, leftCore,
      reference, full, keyEval, lengthRead, within, lookedUp, snapshotted, foundTyped, snapshotRep, mapped, typed,
      lookupHeaps, prefixMaps, prefixWorlds, prefixFrame, prefixMetadata, prefixEffect, prefixReached, prefixRelated,
      prefixAdmitted⟩ :=
    preserves_snapshot bridge functions head environments heaps locals agrees actualTyped initial admitted authority
      physical owner ownerFrame budget meaning lookup read initialValue keyTyped indexed
      (Nat.lt_trans (Staging.Recursive.Size.child_lt_stepSize (by simp)) targetBound) arrayRead arrayValue selection
  -- The right side's meaning, under the snapshot's, the option's, the index's and the array's binders.
  obtain ⟨_, rhsStore, rhsMap, rhsWorld, rhsEval, rhsRepresented, rhsHeaps, rhsMaps, rhsWorlds, rhsFrame, rhsMetadata,
      rhsEffect, rhsReached, rhsRelated, _⟩ :=
    meaning rhsSize rhsBound head.right head.found rhsTyped (environments.extend prefixMaps prefixWorlds) lookupHeaps
      (locals.mono prefixMetadata)
      (agree_prefix (agree_prefix (agree_prefix (agree_prefix agrees
        (.cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget))
        (.word position)) found) (.inRight .unit leftCore))
      (.cons (.inRight snapshotRep.runtime_hasType) (.cons foundTyped (.cons .word (.cons (.cellRef typed)
        (actualTyped.weaken prefixWorlds)))))
      prefixReached prefixAdmitted (authority.transport prefixEffect) (physical.transport prefixEffect prefixFrame)
      owner ownerFrame trace
  rw [rename_prefix, rename_prefix, rename_prefix, rename_prefix] at rhsEval
  cases rhsRepresented with
  | @value _ coreRight rightPayload =>
  rw [head.rightType] at rightPayload
  -- The Core modifier on the snapshot and the right side.
  obtain ⟨_, changed, modifiedEvaluated, changedTyped, valid, _, agreement⟩ :=
    CompatiblePlaceModifier.assigned_outcome observations head.profile rfl
      (snapshotRep.extend (.refl _) rhsMaps rhsWorlds) head.rightView rightPayload
      (environment := coreRight :: .inRight .unit leftCore :: found :: .word position ::
        .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
      (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore head.invalid
  cases failed with
  | operands _ _ _ _ invalid => exact (valid invalid).elim
  | structural _ _ _ fault => cases fault
  | @panic _ _ _ code currentRead _ currentInitial pathRead panics =>
  have panics : Dynamic.AssignmentOperandsPanic assignment.target.type operator (some selected) right code := panics
  -- The panic fixes `guard`'s failure and its reason.
  cases agreement (leftType := .unit) with
  | applied applies _ _ => exact (DataPlaceModifier.panic_excludes_compound panics applies).elim
  | panicked other otherPanics _ fails =>
  cases CompatiblePlaceModifier.panic_functional panics otherPanics
  -- The insert at the array's latest Core cell, which holds the latest object.
  cases pathRead with
  | element _ _ =>
  have objectValue := currentInitial.arrayObject_value
  obtain ⟨_, default, entries, suffix, futureWorld, storeRead, wordKeys, appended, finalHeaps, futureWorlds,
      storeFrame⟩ :=
    CellAwareArrayReads.insert_preserve_at head.prepared rhsHeaps
      (stack := changed :: coreRight :: .inRight .unit leftCore :: found :: .word position ::
        .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
      (context := head.elementType :: head.elementType :: .sum .unit head.elementType ::
        .sum .unit head.elementType :: .word :: head.rootType :: actualContext)
      (.cons changedTyped (.cons rightPayload.runtime_hasType
        (.cons (.inRight (snapshotRep.runtime_hasType.weaken rhsWorlds)) (.cons (foundTyped.weaken rhsWorlds)
          (.cons .word (.cons (.cellRef (rhsWorlds.lookup typed))
            (actualTyped.weaken (prefixWorlds.trans rhsWorlds))))))))
      currentRead objectValue (rhsMaps.lookup mapped) (rhsWorlds.lookup typed)
      (arrayExpr := .var 5) (keyExpr := .var 4) (position := position) (fun read => .loadCell (.var rfl) read)
      (.var rfl) (fun _ => .var rfl) (.var rfl) rfl rfl
  have appended' : CompatibleMappingComparison.insertStore head.comparison head.layout
      (changed :: coreRight :: .inRight .unit leftCore :: found :: .word position ::
        .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
      rhsStore entries (.word position) changed = rhsStore ++ suffix := appended
  -- The caller's pool after the insert's Core-only cells.
  let suffixPool : State headers keys ⟨scope, rhsMap, futureWorld, after, rhsStore ++ suffix, canonical⟩ :=
    (bridge.pool rhsReached).extend (.refl _) futureWorlds storeFrame (.refl _)
  obtain ⟨returned, _, returnedRelated⟩ := bridge.restore rhsReached suffixPool (.refl _) futureWorlds storeFrame
    (.refl _) (Relates.of_records_eq rfl)
  refine ⟨_, rhsStore ++ suffix, rhsMap, futureWorld, ?_, RecursiveStageMeaning.FaultTokens.panic _, finalHeaps,
    prefixMaps.trans rhsMaps, (prefixWorlds.trans rhsWorlds).trans futureWorlds,
    (prefixFrame.trans rhsFrame).trans storeFrame, prefixMetadata.trans rhsMetadata,
    (prefixEffect.trans rhsEffect).trans (CellAwareScopeAuthority.Effect.append (instances := acceptedInstances)
      rhsStore suffix (.refl _) (.refl rhsMap) futureWorlds),
    returned, callerProtocol.trans (callerProtocol.trans prefixRelated rhsRelated) returnedRelated,
    StableRows.after_administrative (bridge.pool initial) (bridge.pool returned) admitted.rows
      ((prefixFrame.trans rhsFrame).trans storeFrame)⟩
  rw [Head.emit, CompatibleElementWrites.code_rename, Head.modifier_compound head compound, ← appended']
  exact CompatibleElementWrites.compound_guard_failure head.prepared rfl reference full keyEval lengthRead within
    lookedUp snapshotted rhsEval modifiedEvaluated storeRead wordKeys (fails.mpr ⟨rfl, rfl⟩)

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique
  assignmentTyped observations in
/-- A compound write to one element of a local array, `a[i] op= v`, from its staged Source run: the root's
array, the index's meaning, the bound's check, the element's snapshot, the right side's meaning, `modified`'s
leaf as the Source's operation computes it, the insert, `guard`'s passing check and the array's cell taking the
leaf at the index on both sides. The compiled code runs to its continuation under the eight binders. -/
theorem preserves_compound (budget : Nat) (compound : operator ≠ .equal)
    (meaning : PreservesBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    {targetSize rhsSize : Nat} {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value}
    {targetHeap middle after : Dynamic.Heap}
    (targetTrace : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment
      before assignment.target (.resolved target) targetHeap)
    (targetBound : targetSize < budget)
    (trace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment targetHeap rhs
      (.value right) middle)
    (rhsBound : rhsSize < budget)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement =>
        Dynamic.CompoundAssignmentApplies assignment.target.type operator target.selected right replacement)
      middle target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
        (payloadModel compiled.compatible.checked registry functions)
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after
        finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      slots.length = 8 ∧
      RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.compoundSlotTypes ++ actualContext)
        compiled.indexed.layouts.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output {result : Value} {final : Store},
        Evaluates (slots ++ actual) finalStore (shift 8 (next.rename ξ)) result final →
        Evaluates actual store ((head.emit next output).rename ξ) result final := by
  -- The Source types: the right side's at its node's, and the index's at its node's.
  have rhsTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨_, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨_, _, indexTyped⟩ := Staging.Recursive.SelectedPreservation.element_place_typed (leading := [])
    (index := head.key) targetTyped head.single
  have keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type :=
    CellAwareArraySourceInversion.typed_type unique head.keyFound indexTyped ▸ indexTyped
  cases ElementAssignmentSourceInversion.single_resolved head.single targetTrace with
  | @intro indexSize _ cell element arrayLocation position _ _ elements selected lookup read initialValue indexed
      arrayRead arrayValue selection =>
  -- The root's Source cell holds a reference to an array of the target's type.
  have cellType := root_cell_type head locals lookup read
  have rootValue : cell.value = some (.arrayRef element arrayLocation) := by cases initialValue; rfl
  have referenceBefore : Dynamic.ValueHasType context before (.arrayRef element arrayLocation)
      (TypeSystem.Ty.array assignment.target.type) := by
    have cellTyped := (admitted.heap _ read.member).value
    rw [rootValue, cellType] at cellTyped
    cases cellTyped with
    | some typed => exact typed
  -- The root, the index, the bound and the element's snapshot.
  obtain ⟨rootTarget, arrayTarget, keyStore, lookupStore, keyMap, lookupWorld, length, rest, found, leftCore,
      reference, full, keyEval, lengthRead, within, lookedUp, snapshotted, foundTyped, snapshotRep, mapped, typed,
      lookupHeaps, prefixMaps, prefixWorlds, prefixFrame, prefixMetadata, prefixEffect, prefixReached, prefixRelated,
      prefixAdmitted⟩ :=
    preserves_snapshot bridge functions head environments heaps locals agrees actualTyped initial admitted authority
      physical owner ownerFrame budget meaning lookup read initialValue keyTyped indexed
      (Nat.lt_trans (Staging.Recursive.Size.child_lt_stepSize (by simp)) targetBound) arrayRead arrayValue selection
  -- The right side's meaning, under the snapshot's, the option's, the index's and the array's binders.
  obtain ⟨_, rhsStore, rhsMap, rhsWorld, rhsEval, rhsRepresented, rhsHeaps, rhsMaps, rhsWorlds, rhsFrame, rhsMetadata,
      rhsEffect, rhsReached, rhsRelated, rhsPost⟩ :=
    meaning rhsSize rhsBound head.right head.found rhsTyped (environments.extend prefixMaps prefixWorlds) lookupHeaps
      (locals.mono prefixMetadata)
      (agree_prefix (agree_prefix (agree_prefix (agree_prefix agrees
        (.cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget))
        (.word position)) found) (.inRight .unit leftCore))
      (.cons (.inRight snapshotRep.runtime_hasType) (.cons foundTyped (.cons .word (.cons (.cellRef typed)
        (actualTyped.weaken prefixWorlds)))))
      prefixReached prefixAdmitted (authority.transport prefixEffect) (physical.transport prefixEffect prefixFrame)
      owner ownerFrame trace
  rw [rename_prefix, rename_prefix, rename_prefix, rename_prefix] at rhsEval
  cases rhsRepresented with
  | @value _ coreRight rightPayload =>
  rw [head.rightType] at rightPayload
  -- The Source write: the array's cell takes the operation's leaf at the index.
  cases write with
  | intro currentRead _ currentInitial update heapWrite =>
  cases update with
  | element _ child replace =>
  cases child with
  | leaf applied =>
  have objectValue := currentInitial.arrayObject_value
  have referenceMiddle := referenceBefore.mono (prefixMetadata.trans rhsMetadata)
  obtain ⟨sameOther, sameElement⟩ :=
    object_element referenceMiddle rhsPost.at_value.2.heap currentRead objectValue
  subst sameOther
  subst sameElement
  have selectedTyped : Dynamic.ValueHasType context _ selected assignment.target.type :=
    Dynamic.ValueHasType.arrayElement (referenceBefore.mono prefixMetadata) prefixAdmitted.heap arrayRead
      arrayValue.arrayObject_value selection.getElem?_eq
  have updatedTyped := compound_leaf_typed unique head.found assignmentTyped compound
    (selectedTyped.mono rhsMetadata) rhsPost.at_value.1 applied
  -- The Core modifier: the leaf the Source's operation computes, and `guard`'s check passes.
  obtain ⟨changed, changedRep, modifiedEvaluated, _, guarded⟩ :=
    CompatiblePlaceModifier.wide_preserves observations head.profile rfl
      (snapshotRep.extend (.refl _) rhsMaps rhsWorlds) head.rightView rightPayload applied
      (environment := coreRight :: .inRight .unit leftCore :: found :: .word position ::
        .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
      (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore head.invalid
  -- The Core write: the array's cell takes the leaf's entry at the index.
  obtain ⟨length', default, entries, suffix, futureWorld, storeRead, wordKeys, appended, finalHeaps, futureWorlds,
      storeFrame, storeEffect⟩ :=
    CellAwareArrayReads.store_preserve_at head.prepared rhsHeaps
      (stack := changed :: coreRight :: .inRight .unit leftCore :: found :: .word position ::
        .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
      (context := head.elementType :: head.elementType :: .sum .unit head.elementType ::
        .sum .unit head.elementType :: .word :: head.rootType :: actualContext)
      (.cons changedRep.runtime_hasType (.cons rightPayload.runtime_hasType
        (.cons (.inRight (snapshotRep.runtime_hasType.weaken rhsWorlds)) (.cons (foundTyped.weaken rhsWorlds)
          (.cons .word (.cons (.cellRef (rhsWorlds.lookup typed))
            (actualTyped.weaken (prefixWorlds.trans rhsWorlds))))))))
      currentRead objectValue replace heapWrite (rhsMaps.lookup mapped) (rhsWorlds.lookup typed) changedRep rfl
      (arrayExpr := .var 5) (keyExpr := .var 4) (fun read => .loadCell (.var rfl) read) (.var rfl)
      (fun _ => .var rfl) (.var rfl) rfl rfl
  -- The array's Core cell after the write, at its world's type: the updated entries are of the layout's type.
  have finalBound : arrayTarget < (rhsStore ++ suffix).length := by
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp storeRead).1 (Nat.le_add_right _ _)
  obtain ⟨_, cellRead, cellTyped⟩ :=
    finalHeaps.runtime_hasTypes.lookup (futureWorlds.lookup (rhsWorlds.lookup typed))
  have newRead := List.getElem?_set_self (a := Core.Value.pair (.word length') (.pair default
    (OrderedMapping.encode head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position)
      changed entries)))) finalBound
  have cellEq := Option.some.inj (cellRead.symm.trans newRead)
  subst cellEq
  cases cellTyped with
  | pair _ inner =>
  cases inner with
  | pair _ encodeTyped =>
  have appended' : CompatibleMappingComparison.insertStore head.comparison head.layout
      (changed :: coreRight :: .inRight .unit leftCore :: found :: .word position ::
        .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
      rhsStore entries (.word position) changed = rhsStore ++ suffix := appended
  -- The caller's pool after the write.
  let suffixPool : State headers keys ⟨scope, rhsMap, futureWorld, after, _, canonical⟩ :=
    (bridge.pool rhsReached).extend (.refl _) futureWorlds storeFrame (.of_write heapWrite)
  obtain ⟨returned, _, returnedRelated⟩ := bridge.restore rhsReached suffixPool (.refl _) futureWorlds storeFrame
    (.of_write heapWrite) (Relates.of_records_eq rfl)
  refine ⟨_, rhsMap, futureWorld,
    [.unit, OrderedMapping.encode head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual
        (.word position) changed entries), changed, coreRight, .inRight .unit leftCore, found, .word position,
      .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget],
    finalHeaps, prefixMaps.trans rhsMaps, (prefixWorlds.trans rhsWorlds).trans futureWorlds,
    (prefixFrame.trans rhsFrame).trans storeFrame, (prefixMetadata.trans rhsMetadata).trans (.of_write heapWrite),
    (prefixEffect.trans rhsEffect).trans storeEffect, rfl,
    .cons .unit (.cons encodeTyped (.cons (changedRep.runtime_hasType.weaken futureWorlds)
      (.cons (rightPayload.runtime_hasType.weaken futureWorlds)
        (.cons (.inRight ((snapshotRep.runtime_hasType.weaken rhsWorlds).weaken futureWorlds))
          (.cons ((foundTyped.weaken rhsWorlds).weaken futureWorlds) (.cons .word
            (.cons (.cellRef (futureWorlds.lookup (rhsWorlds.lookup typed)))
              (actualTyped.weaken ((prefixWorlds.trans rhsWorlds).trans futureWorlds))))))))),
    ⟨returned, callerProtocol.trans (callerProtocol.trans prefixRelated rhsRelated) returnedRelated,
      referenceMiddle.arrayElementWrite rhsPost.at_value.2.heap currentRead objectValue replace updatedTyped
        heapWrite,
      StableRows.after_administrative (bridge.pool initial) (bridge.pool returned) admitted.rows
        ((prefixFrame.trans rhsFrame).trans storeFrame)⟩, ?_⟩
  -- The compiled code runs to its continuation.
  intro next output result final nextEval
  rw [Head.emit, CompatibleElementWrites.code_rename, Head.modifier_compound head compound]
  exact CompatibleElementWrites.compound_evaluates head.prepared rfl reference full keyEval lengthRead within lookedUp
    snapshotted rhsEval modifiedEvaluated storeRead wordKeys (fun written => guarded.mpr written)
    (by rw [appended']; exact nextEval)

end Heads
end Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteHeads

import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementCompound
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementReflects

/-!
# Cell-aware invocations: the heads of an in-place `~` at an element

An in-place `~` at one element of a local array, `a[i] ~=;`, as a companion of the assignment heads: its
bundle (`CellAwareElementWriteHeads.BitNotHead`), whose code is `elementStore`'s compound path with `~`'s
modifier and the right side `LanguageResult.success .unit`. Preserved: the faults before the operand (a root
not yet initialized, the index's fault at a root that holds its array, and `0x32` from the array's length
on); the operand's fault, which a represented snapshot never has; and the write, whose Core run reaches its
continuation under the eight binders. Reflected: a sized Core run of the code gives the element target's
fault or its write with a strictly smaller run of the continuation (`BitNotResultAt`). Main declarations:
`CellAwareElementWriteHeads.preserves_bitNot`, `preserves_bitNot_operand_fault`,
`preserves_bitNot_uninitialized`, `preserves_bitNot_index_fault`, `preserves_bitNot_outOfBounds` and
`reflects_bitNot_bounded`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

section
/-! The Core runs: the snapshot of the lookup's option, its typing, the unit right side, and a sized run
of the compound path inverted to its continuation. -/
namespace Solcore.SourceSemantics.CoreLowering.CompatibleElementWrites
open Core Frontend SourceCoreCompatibleDataPlaces

/-- The right side of an in-place `~`, `LanguageResult.success .unit`, renamed and under any binders: the
unit, and the store stays. -/
theorem unit_evaluates (ξ : Renaming) (count : Nat) (environment : Environment) (store : Store) :
    Evaluates environment store (shift count ((LanguageResult.success Expr.unit).rename ξ))
      (.inRight .word .unit) store := by
  have closed : ∀ count, shift count (LanguageResult.success Expr.unit) = LanguageResult.success Expr.unit := by
    intro count
    induction count with
    | zero => rfl
    | succ count ih =>
      rw [shift, List.range_succ, List.foldl_append, ← shift, ih]
      simp [LanguageResult.success, Expr.weakenAt]
  rw [show (LanguageResult.success Expr.unit).rename ξ = LanguageResult.success Expr.unit from rfl, closed]
  exact .inRight .unit

private theorem write_at {store : Store} {location : Location} (bound : location < store.length) (value : Value) :
    store.write? location value = some (store.set location value) := by
  simp [Store.write?, bound]

/-- A sized run of a compound write or a `~` below the array's length whose `guard` has no check, inverted:
from the root's array, the index, the bound, the snapshot, the right side, `modified`'s leaf and the insert,
as `compound_evaluates` takes them, the run of `next` under the eight binders is strictly smaller, at the
store whose array's cell has taken the updated entries. -/
theorem compound_continuation {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
    {comparison : SourceCoreCompatibleDataEquality.Prepared checked}
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
    {layout : OrderedMapping.Layout} (keyType : layout.keyType = .word)
    {environment : Environment} {store : Store} {slot : Nat} {storedType outputType cellType : Ty} {invalid : Word}
    {value next index : Expr} {location : Location} {leftType elementType : Ty} {arrayLocation : Location}
    {position length : Word} {rest found snapshot right changed length' default result : Value}
    {modifier : ElementModifier} {entries : OrderedMapping.Entries}
    {after lookupStore rhsStore modifiedStore final : Store} {size : Nat}
    (completed : CoreProof.EvaluationSize size environment store
      (code slot storedType outputType invalid comparison.expression value next (some modifier) layout index)
      result final)
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
    (unguarded : ∀ write, SourceCoreDataPlaces.guard outputType modifier.operator write = write) :
    ∃ smaller, smaller < size ∧ CoreProof.EvaluationSize smaller
      (.unit :: OrderedMapping.encode layout
          (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries) ::
        changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
      ((CompatibleMappingComparison.insertStore comparison layout
          (changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment)
          modifiedStore entries (.word position) changed).set arrayLocation
        (.pair length' (.pair default (OrderedMapping.encode layout
          (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries)))))
      (shift 8 next) result final := by
  simp only [code] at completed
  obtain ⟨first, firstSmaller, completed⟩ := completed.bind_success (root_full reference full)
  simp only [arrayElementWrite] at completed
  obtain ⟨second, secondSmaller, completed⟩ := completed.bind_success indexed
  obtain ⟨third, thirdSmaller, completed⟩ := completed.if_true (within_check read within)
  simp only [elementStore] at completed
  rw [shift_closed comparison, shift_closed comparison] at completed
  obtain ⟨fourth, fourthSmaller, completed⟩ := completed.bind_success lookedUp
  obtain ⟨fifth, fifthSmaller, completed⟩ := completed.bind_success snapshotted
  obtain ⟨sixth, sixthSmaller, completed⟩ := completed.bind_success rhsEvaluated
  obtain ⟨seventh, seventhSmaller, completed⟩ := completed.bind_success modifiedEvaluated
  let stack :=
    changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment
  have inserted := OrderedMapping.insert_evaluates (environment := stack)
    (mapping := .second (.second (.loadCell (.var 5)))) (keyExpr := .var 4) (valueExpr := .var 0)
    (keyEqual := comparison.expression) entries (.word position) changed
    (CompatibleMappingComparison.comparator comparison stack modifiedStore) GenericHeap.arrayKeyEqual
    (.second (.second (.loadCell (.var rfl) current))) (.var rfl) (.var rfl)
    (CompatibleEquality.prepared_evaluates_exact comparison stack modifiedStore)
    (CompatibleArrayEvaluation.word_comparisons prepared keyType stack modifiedStore wordKeys position _)
  obtain ⟨eighth, eighthSmaller, completed⟩ := completed.bind_success inserted
  rw [unguarded] at completed
  have bound : arrayLocation < modifiedStore.length := (List.getElem?_eq_some_iff.mp current).1
  have kept : (CompatibleMappingComparison.insertStore comparison layout stack modifiedStore entries (.word position)
      changed).read? arrayLocation = some (.pair length' (.pair default (OrderedMapping.encode layout entries))) := by
    simp only [CompatibleMappingComparison.insertStore, OrderedMapping.installedStore, WordMapping.installedStore,
      CompatibleMappingComparison.comparisonStore, Store.read?, List.append_assoc] at current ⊢
    rw [List.getElem?_append_left bound]
    exact current
  have keptBound : arrayLocation <
      (CompatibleMappingComparison.insertStore comparison layout stack modifiedStore entries (.word position)
        changed).length :=
    (List.getElem?_eq_some_iff.mp kept).1
  obtain ⟨ninth, ninthSmaller, completed⟩ := completed.let_body (.storeCell (.var rfl) kept
    (.pair (.first (.loadCell (.var rfl) kept)) (.pair (.first (.second (.loadCell (.var rfl) kept))) (.var rfl)))
    (write_at keptBound _))
  exact ⟨ninth, by omega, completed⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleElementWrites
end

namespace Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

/-- An in-place `~` at one element of a local array as the compiler emitted it: the receipt's pieces at the
statement's scope and the index's code under the certificate, as a write's (`Head`), with no right side; the
target is of in-place `~`'s wider profile at its own type, as a projected `~`'s. -/
structure BitNotHead (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (certificate : GenericExpressionMeaning.Certificate)
    (scope : SourceCoreLocalCell.Scope) (assignment : AssignmentResolution) where
  key : ExpressionId
  single : assignment.target.projections = [.element key]
  slot : Nat
  elementType : Ty
  identity : DataTypeId
  slotEq : SourceCoreLocalCell.lookup? scope assignment.target.root =
    some (slot, .cell (.product .word (.product elementType (.namedData identity))))
  writable : WritableLocal context assignment.target.root (TypeSystem.Ty.array assignment.target.type)
  fuel : Nat
  comparison : SourceCoreCompatibleDataEquality.Prepared values.checked
  prepared : SourceCoreCompatibleDataEquality.prepare fuel values.checked (.constructor (.builtin .word)) =
    .ok comparison
  site : SourceCoreElaboration.ErrorSite
  leaf : project values.checked site assignment.target.type = .ok elementType
  keyNode : ExpressionNode
  keyFound : source.lookupExpression? key = some keyNode
  keyCode : SourceCoreBasic.LoweredExpr
  keyChild : certificate scope key keyCode
  keyType : keyCode.type = .word
  /-- The target is of in-place `~`'s wider profile, at its own type. -/
  profile : WideBitNotProfile assignment.target.type
  invalidProjection : Word
  invalid : Word

namespace BitNotHead
variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {assignment : AssignmentResolution}

/-- The array's mapping layout. -/
def layout (head : BitNotHead values source context certificate scope assignment) : OrderedMapping.Layout :=
  ⟨.word, head.elementType, head.identity⟩

/-- The root's Core type: a reference to the array's cell. -/
def rootType (head : BitNotHead values source context certificate scope assignment) : Ty :=
  .cell (.product .word (.product head.elementType (.namedData head.identity)))

/-- The element's modifier: `~`'s, as `lowerElements` gives it without a right side. -/
def modifier (head : BitNotHead values source context certificate scope assignment) : Option ElementModifier :=
  CompatibleElementWrites.modifierOf assignment .equal true head.elementType head.invalid

/-- The code the compiler emitted, before `next`: the right side is `LanguageResult.success .unit`. -/
def emit (head : BitNotHead values source context certificate scope assignment) (next : Expr) (output : Ty) :
    Expr :=
  CompatibleElementWrites.code head.slot head.rootType output head.invalidProjection head.comparison.expression
    (LanguageResult.success .unit) next head.modifier head.layout head.keyCode.expression

/-- `~`'s modifier at the element's Core type: no operator, so `guard` writes at once, and the wrap of
in-place `~` at the target's type. -/
theorem modifier_eq (head : BitNotHead values source context certificate scope assignment) :
    head.modifier =
      some ⟨head.elementType, none, true, head.invalid, SourceCoreDataPlaces.bitNotWrap assignment.target.type⟩ :=
  rfl

/-- The Core types of an in-place `~`'s eight binders, innermost first: the cell write's unit, the updated
entries, the leaf, the right side's unit, the snapshot, the lookup's option, the index's word and the array's
cell. -/
def bitNotSlotTypes (head : BitNotHead values source context certificate scope assignment) : Core.Context :=
  [.unit, head.layout.type, head.elementType, .unit, .sum .unit head.elementType, .sum .unit head.elementType,
    .word, head.rootType]

end BitNotHead

/-- The Source cell at a location the heaps map to a Core cell of an array's type holds an array object, as an
initialized root's value. -/
theorem array_cell_initial {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {ordinary : GenericHeap.PayloadModel catalog projects definitions}
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel ordinary instances) mapping
      world heap store)
    {location : Dynamic.Location} {target : Location} {payload : Ty} {identity : DataTypeId}
    (mapped : mapping[location.index]? = some target)
    (typed : world[target]? = some (.product .word (.product payload (.namedData identity)))) :
    ∃ cell element elements, Dynamic.Heap.Reads heap location cell ∧
      Dynamic.RootInitialValue cell (some (.arrayObject element elements)) := by
  obtain ⟨_, _, sourceRead, _, stands⟩ := heaps.cells mapped
  cases stands with
  | optional optionalTyped _ =>
    have impossible := optionalTyped.symm.trans typed
    simp [Core.OptionalCell.cellType] at impossible
  | array _ arrayed =>
    obtain ⟨element, elements, _, _, _, _, cellEq, _⟩ := arrayed
    subst cellEq
    exact ⟨_, element, elements, sourceRead, .initialized⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- What a sized Core run of an in-place `~` at one element of a local array reflects: the element target's
fault, the run failing with its token; or the target resolved and written as the Source's `~` writes it, the
run of the continuation under the eight binders strictly smaller. -/
inductive BitNotResultAt (size : Nat) (definitions : DataEnvironment) (cells : GenericHeap.CellModel definitions)
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions) (context : SourceSemantics.Context)
    (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (faults : RecursiveStageMeaning.FaultRep) (scope : SourceCoreLocalCell.Scope) (writtenContext : Core.Context)
    (assignment : AssignmentResolution) (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | targetFault {targetSize : Nat} {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (failed : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment before
        assignment.target (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore)
      (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after
        finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      BitNotResultAt size definitions cells instances context stages invocation faults scope writtenContext assignment
        environment canonical actual before store mapping world initial next output value finalStore
  | success {targetSize remainingSize : Nat} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
      {targetHeap after : Dynamic.Heap} {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
      {slots : Environment}
      (resolved : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment
        before assignment.target (.resolved target) targetHeap)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.BitNotAssignmentApplies assignment.target.type target.selected replacement)
        targetHeap target updated after)
      (heaps : GenericHeap.CellHeapRepresents cells finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written)
      (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect instances mapping world before store finalMap finalWorld after written)
      (count : slots.length = 8)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 8 next) value finalStore) :
      BitNotResultAt size definitions cells instances context stages invocation faults scope writtenContext assignment
        environment canonical actual before store mapping world initial next output value finalStore

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
  {faults : RecursiveStageMeaning.FaultRep}
  {assignment : AssignmentResolution}
  (head : BitNotHead (.initial compiled.compatible.checked) invocation.source context certificate scope assignment)
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
  (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)

local notation "acceptedCells" => GeneralizedLocalDescriptorHeap.cellModel
  (payloadModel compiled.compatible.checked registry functions)
  (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
local notation "acceptedInstances" => GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment

include head locals in
/-- The root's Source cell holds a reference to an array of the target's type, as its writable binder types it. -/
theorem bitNot_root_cell_type {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root location)
    (read : Dynamic.Heap.Reads before location cell) :
    cell.type = TypeSystem.Ty.array assignment.target.type := by
  obtain ⟨_, staticLookup, _, _, bodyEq⟩ := head.writable.scheme
  obtain ⟨_, _, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
  cases lookup.functional staticLookupRuntime
  cases read.functional staticRead
  exact staticCellType.trans bodyEq

include environments heaps agrees admitted in
/-- A root not yet initialized: the code fails with the site's reason at the root's check, before the index, and
nothing changes. -/
theorem preserves_bitNot_uninitialized {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root location)
    (read : Dynamic.Heap.Reads before location cell) (initialValue : Dynamic.RootInitialValue cell none)
    (uninitialized : ∀ location, faults (.semantic (.uninitializedLocation location)) head.invalidProjection)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults (.semantic (.uninitializedLocation location)) token ∧
      GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld before finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before before ∧
      CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld before
        finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, before, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  obtain ⟨target, reference, coreRead⟩ :=
    CellAwareElementWriteRoots.uninitialized environments heaps agrees head.slotEq lookup read initialValue
  refine ⟨head.invalidProjection, store, mapping, world, ?_, uninitialized location, heaps, .refl _, .refl _,
    .refl mapping store, .refl _, .refl mapping world before store, initial, callerProtocol.refl _, admitted.rows⟩
  simp only [BitNotHead.emit]
  rw [CompatibleElementWrites.code_rename]
  exact CompatibleElementWrites.root_empty reference coreRead

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame in
/-- The index's fault, at a root that holds its array: the root's check passes, and the index's Core run fails as
its Source run does, before the bound. -/
theorem preserves_bitNot_index_fault (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {element : TypeSystem.Ty} {arrayLocation : Dynamic.Location}
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root location)
    (read : Dynamic.Heap.Reads before location cell)
    (initialValue : Dynamic.RootInitialValue cell (some (.arrayRef element arrayLocation)))
    (keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type)
    {indexSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (indexed : Staging.Recursive.Size.Expression program stages indexSize invocation context environment before
      head.key (.fault failure) after)
    (bound : indexSize < budget) (next : Expr) (output : Ty) :
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
  obtain ⟨target, native, reference, coreRead, represented⟩ :=
    CellAwareElementWriteRoots.initialized environments heaps agrees head.slotEq lookup read initialValue
  obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, resultRep, finalHeaps, maps, worlds, frame, metadata, effect,
      reached, related, post⟩ :=
    meaning indexSize bound head.keyChild head.keyFound keyTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [native])
      (.cons ((payloadModel compiled.compatible.checked registry functions).runtime_hasType represented) actualTyped)
      initial admitted authority physical owner ownerFrame indexed
  cases resultRep with
  | fault matched =>
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata, effect,
      reached, related, post.rows⟩
    simp only [BitNotHead.emit]
    rw [CompatibleElementWrites.code_rename]
    exact CompatibleElementWrites.index_failure reference coreRead
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil, List.cons_append,
        List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame in
/-- `0x32` from the array's length on: the root's check and the index pass, and the bound's check fails on both
sides, before the snapshot. -/
theorem preserves_bitNot_outOfBounds [RecursiveStageMeaning.FaultTokens faults] (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {element : TypeSystem.Ty} {arrayLocation : Dynamic.Location}
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root location)
    (read : Dynamic.Heap.Reads before location cell)
    (initialValue : Dynamic.RootInitialValue cell (some (.arrayRef element arrayLocation)))
    (keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type)
    {indexSize : Nat} {position : Word} {after : Dynamic.Heap} {arrayCell : Dynamic.Cell}
    {elements : List Dynamic.Value}
    (indexed : Staging.Recursive.Size.Expression program stages indexSize invocation context environment before
      head.key (.value (.word position)) after)
    (bound : indexSize < budget)
    (arrayRead : Dynamic.Heap.Reads after arrayLocation arrayCell)
    (stored : arrayCell.value = some (.arrayObject element elements))
    (beyond : elements.length ≤ position.val) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults (.semantic (.panic 0x32)) token ∧
      GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after
        finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  obtain ⟨target, native, reference, coreRead, represented⟩ :=
    CellAwareElementWriteRoots.initialized environments heaps agrees head.slotEq lookup read initialValue
  obtain ⟨arrayTarget, payloadType, identity, rfl, sameType, _, _, _⟩ :=
    CompatiblePayload.arrayRef_fields represented rfl
  obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, resultRep, finalHeaps, maps, worlds, frame, metadata, effect,
      reached, related, post⟩ :=
    meaning indexSize bound head.keyChild head.keyFound keyTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [_])
      (.cons ((payloadModel compiled.compatible.checked registry functions).runtime_hasType represented) actualTyped)
      initial admitted authority physical owner ownerFrame indexed
  cases resultRep with
  | value indexPayload =>
    rw [head.keyType] at indexPayload
    obtain ⟨word, same, rfl⟩ := CompatibleExpressionPrimitives.word_fields indexPayload
    cases same
    have arrayPayload := (payloadModel compiled.compatible.checked registry functions).extend represented maps worlds
    obtain ⟨measured, small⟩ := CellAwareArrayReads.length_preserve finalHeaps (.array arrayRead stored) arrayPayload
      (by rw [sameType]; rfl)
    cases measured with
    | array coreArrayRead =>
      have outside : ¬ position < Word.ofNatModulo elements.length := by
        rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
        omega
      refine ⟨_, finalStore, finalMap, finalWorld, ?_, RecursiveStageMeaning.FaultTokens.panic _, finalHeaps, maps,
        worlds, frame, metadata, effect, reached, related, post.rows⟩
      simp only [BitNotHead.emit]
      rw [CompatibleElementWrites.code_rename]
      exact CompatibleElementWrites.outOfBounds reference coreRead
        (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
          List.cons_append, List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
        coreArrayRead outside

/-- After the index, at a root that holds its array: the lookup at the index gives the element's snapshot, the
entry present there or the array's default, which represents the Source's at the target's type; the lookup
appends only its Core-only cells, and the caller's state follows. -/
theorem bitNot_lookup_preserve {keyMap : LocationMap} {keyWorld : StoreTyping} {targetHeap : Dynamic.Heap}
    {keyStore : Store}
    (keyHeaps : GenericHeap.CellHeapRepresents acceptedCells keyMap keyWorld targetHeap keyStore)
    (keyTyped : RuntimeEnvironmentHasTypes keyWorld actual actualContext compiled.indexed.layouts.definitions)
    (keyReached : callerProtocol.State ⟨scope, keyMap, keyWorld, targetHeap, keyStore, canonical⟩)
    (keyAdmitted : Admission bridge context keyReached)
    {rootType element : TypeSystem.Ty} {arrayLocation : Dynamic.Location} {arrayTarget : Location}
    (rootRep : ValueRep compiled.compatible.checked registry functions keyMap keyWorld rootType
      (.arrayRef element arrayLocation)
      (.cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget) head.rootType)
    (rootView : SourceCoreRawMetadata.runtimeType rootType =
      SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array assignment.target.type))
    {position : Word} {arrayCell : Dynamic.Cell} {elements : List Dynamic.Value} {selected : Dynamic.Value}
    (arrayRead : Dynamic.Heap.Reads targetHeap arrayLocation arrayCell)
    (arrayValue : Dynamic.RootInitialValue arrayCell (some (.arrayObject element elements)))
    (selection : Dynamic.ValueAt elements position.val selected) :
    ∃ lookupStore lookupWorld length rest found leftCore,
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
      GenericHeap.CellHeapRepresents acceptedCells keyMap lookupWorld targetHeap lookupStore ∧
      WorldExtends keyWorld lookupWorld ∧ AdministrativePreserved keyMap keyStore keyMap lookupStore ∧
      CellAwareScopeAuthority.Effect acceptedInstances keyMap keyWorld targetHeap keyStore keyMap lookupWorld
        targetHeap lookupStore ∧
      ∃ reached : callerProtocol.State ⟨scope, keyMap, lookupWorld, targetHeap, lookupStore, canonical⟩,
        callerProtocol.Relates keyReached reached ∧ Admission bridge context reached := by
  obtain ⟨_, _, lookupWorld, suffix, coreReads, elementRep, lookupHeaps, lookupWorlds, lookupFrame, lookupAppend⟩ :=
    CellAwareArrayReads.reads_preserve head.prepared (layout := head.layout) keyHeaps keyTyped
      (.array arrayRead arrayValue.arrayObject_value selection.getElem?_eq) rootRep rootView
      (.array assignment.target.type) rfl position.isLt
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
  exact ⟨_, lookupWorld, _, _, _, _, arrayCoreRead, below, lookedUp, snapshotted,
    CompatibleElementWrites.optionValue_typed snapshotRep.runtime_hasType, snapshotRep, lookupHeaps, lookupWorlds,
    lookupFrame, lookupEffect, lookupReached, lookupRelated, keyAdmitted.heap,
    StableRows.after_administrative (bridge.pool keyReached) (bridge.pool lookupReached) keyAdmitted.rows
      lookupFrame⟩

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame in
/-- The prefix of an in-place `~` at one element, to its right side: the root's check, the index and the
bound pass, and the lookup at the index gives the element's snapshot, the entry present there or the array's
default, which represents the Source's snapshot at the target's type; the lookup appends only its Core-only
cells, and the caller's state follows. -/
theorem preserves_bitNot_snapshot (budget : Nat)
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
  have cellType := bitNot_root_cell_type head locals lookup read
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
  -- The lookup at the index and the element's snapshot.
  obtain ⟨lookupStore, lookupWorld, length, rest, found, leftCore, lengthRead, within, lookedUp, snapshotted,
      foundTyped, snapshotRep, lookupHeaps, lookupWorlds, lookupFrame, lookupEffect, lookupReached, lookupRelated,
      lookupAdmitted⟩ :=
    bitNot_lookup_preserve bridge functions head keyHeaps (actualTyped.weaken keyWorlds) keyReached
      keyPost.at_value.2 (represented.extend (.refl _) keyMaps keyWorlds) (by rw [cellType]) arrayRead arrayValue
      selection
  exact ⟨rootTarget, arrayTarget, keyStore, lookupStore, keyMap, lookupWorld, length, rest, found, leftCore,
    reference, full, keyEval, lengthRead, within, lookedUp, snapshotted, foundTyped, snapshotRep,
    keyMaps.lookup mapped, lookupWorlds.lookup (keyWorlds.lookup typed), lookupHeaps, keyMaps,
    keyWorlds.trans lookupWorlds, keyFrame.trans lookupFrame, keyMetadata, keyEffect.trans lookupEffect,
    lookupReached, callerProtocol.trans keyRelated lookupRelated, lookupAdmitted⟩

include head environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame
  unique assignmentTyped in
/-- The Source's operand fault of an in-place `~` at one element has no run at an accepted head: the
element's snapshot is represented at the target's type, which in-place `~`'s profile admits, so the selected
value is a valid operand of `~`, as at a projected `~` (`CellAwareInvocationProjectedBitNotHeads.operand_valid`). -/
theorem preserves_bitNot_operand_fault (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    {targetSize : Nat} {target : Dynamic.ResolvedPlace} {targetHeap : Dynamic.Heap}
    (targetTrace : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment
      before assignment.target (.resolved target) targetHeap)
    (targetBound : targetSize < budget)
    {value : Dynamic.Value} (selected : target.selected = some value) :
    ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot value := by
  cases assignmentTyped with
  | intro targetTyped _ _ =>
  obtain ⟨_, _, indexTyped⟩ := Staging.Recursive.SelectedPreservation.element_place_typed (leading := [])
    (index := head.key) targetTyped head.single
  have keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type :=
    CellAwareArraySourceInversion.typed_type unique head.keyFound indexTyped ▸ indexTyped
  cases ElementAssignmentSourceInversion.single_resolved head.single targetTrace with
  | @intro indexSize _ cell element arrayLocation position _ _ elements selectedValue lookup read initialValue indexed
      arrayRead arrayValue selection =>
  cases Option.some.inj selected
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, snapshotRep, _⟩ :=
    preserves_bitNot_snapshot bridge functions head environments heaps locals agrees actualTyped initial admitted
      authority physical owner ownerFrame budget meaning lookup read initialValue keyTyped indexed
      (Nat.lt_trans (Staging.Recursive.Size.child_lt_stepSize (by simp)) targetBound) arrayRead arrayValue selection
  obtain ⟨_, _, _, _, _, valid⟩ := CompatiblePlaceNumericBitNotModifier.wide_success head.profile rfl snapshotRep
    (environment := [_]) (rhs := .unit) (.var (index := 0) rfl) none store head.invalid
  exact valid

/-- `~`'s write at one element after its snapshot, from the Source's write at the resolved element: `modified`
gives the leaf the Source's `~` computes at the target's type, and after the insert's Core-only cells the
array's Core cell takes the leaf's entry at the index, as the Source's cell takes the leaf; the cells stay
related, the eight binders are typed, and the caller's state follows, with the heap typed after the write. -/
theorem bitNot_commit_preserve {keyMap : LocationMap} {lookupWorld : StoreTyping} {targetHeap after : Dynamic.Heap}
    {lookupStore : Store}
    (lookupHeaps : GenericHeap.CellHeapRepresents acceptedCells keyMap lookupWorld targetHeap lookupStore)
    (lookupTyped : RuntimeEnvironmentHasTypes lookupWorld actual actualContext compiled.indexed.layouts.definitions)
    (lookupReached : callerProtocol.State ⟨scope, keyMap, lookupWorld, targetHeap, lookupStore, canonical⟩)
    (lookupAdmitted : Admission bridge context lookupReached) (kind : BitNotTargetType assignment.target.type)
    {element : TypeSystem.Ty} {arrayLocation : Dynamic.Location} {arrayTarget : Location}
    (reference : Dynamic.ValueHasType context targetHeap (.arrayRef element arrayLocation)
      (TypeSystem.Ty.array assignment.target.type))
    (mapped : keyMap[arrayLocation.index]? = some arrayTarget)
    (typed : lookupWorld[arrayTarget]? = some (.product .word (.product head.elementType (.namedData head.identity))))
    {position : Word} {arrayCell : Dynamic.Cell} {elements : List Dynamic.Value} {selected : Dynamic.Value}
    (arrayRead : Dynamic.Heap.Reads targetHeap arrayLocation arrayCell)
    (arrayValue : Dynamic.RootInitialValue arrayCell (some (.arrayObject element elements)))
    (selection : Dynamic.ValueAt elements position.val selected) {found leftCore : Value}
    (foundTyped : RuntimeValueHasType lookupWorld found (.sum .unit head.elementType)
      compiled.indexed.layouts.definitions)
    (snapshotRep : ValueRep compiled.compatible.checked registry functions keyMap lookupWorld assignment.target.type
      selected leftCore head.elementType)
    {updated : Dynamic.Value}
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.BitNotAssignmentApplies assignment.target.type (some selected) replacement)
      targetHeap
        { location := arrayLocation, rootType := arrayCell.type, valueType := assignment.target.type,
          projections := [.element position.val], selected := some selected }
        updated after) :
    ∃ changed length default entries suffix futureWorld,
      Evaluates (.unit :: .inRight .unit leftCore :: found :: .word position ::
          .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
        lookupStore
        (modified head.elementType none true (.var 1) (.var 0) head.invalid
          (SourceCoreDataPlaces.bitNotWrap assignment.target.type))
        (.inRight .word changed) lookupStore ∧
      lookupStore.read? arrayTarget =
        some (.pair (.word length) (.pair default (OrderedMapping.encode head.layout entries))) ∧
      (∀ key value, (key, value) ∈ entries → ∃ word, key = .word word) ∧
      CompatibleMappingComparison.insertStore head.comparison head.layout
          (changed :: .unit :: .inRight .unit leftCore :: found :: .word position ::
            .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
          lookupStore entries (.word position) changed = lookupStore ++ suffix ∧
      GenericHeap.CellHeapRepresents acceptedCells keyMap futureWorld after
        ((lookupStore ++ suffix).set arrayTarget (.pair (.word length) (.pair default (OrderedMapping.encode
          head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries))))) ∧
      WorldExtends lookupWorld futureWorld ∧
      AdministrativePreserved keyMap lookupStore keyMap
        ((lookupStore ++ suffix).set arrayTarget (.pair (.word length) (.pair default (OrderedMapping.encode
          head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries))))) ∧
      Dynamic.HeapMetadataExtend targetHeap after ∧
      CellAwareScopeAuthority.Effect acceptedInstances keyMap lookupWorld targetHeap lookupStore keyMap futureWorld
        after ((lookupStore ++ suffix).set arrayTarget (.pair (.word length) (.pair default (OrderedMapping.encode
          head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries))))) ∧
      RuntimeEnvironmentHasTypes futureWorld
        ([.unit, OrderedMapping.encode head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual
            (.word position) changed entries), changed, .unit, .inRight .unit leftCore, found, .word position,
          .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget] ++ actual)
        (head.bitNotSlotTypes ++ actualContext) compiled.indexed.layouts.definitions ∧
      ∃ reached : callerProtocol.State ⟨scope, keyMap, futureWorld, after,
          (lookupStore ++ suffix).set arrayTarget (.pair (.word length) (.pair default (OrderedMapping.encode
            head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries)))),
          canonical⟩,
        callerProtocol.Relates lookupReached reached ∧ Admission bridge context reached := by
  -- The Source write: the array's cell takes `~`'s leaf at the index.
  cases write with
  | intro currentRead _ currentInitial update heapWrite =>
  cases update with
  | element _ child replace =>
  cases child with
  | leaf applied =>
  have objectValue := currentInitial.arrayObject_value
  obtain ⟨sameOther, sameElement⟩ := object_element reference lookupAdmitted.heap currentRead objectValue
  subst sameOther
  subst sameElement
  have selectedTyped : Dynamic.ValueHasType context targetHeap selected assignment.target.type :=
    Dynamic.ValueHasType.arrayElement reference lookupAdmitted.heap arrayRead arrayValue.arrayObject_value
      selection.getElem?_eq
  -- The Core modifier on the snapshot: the leaf the Source's `~` computes at the target's type.
  obtain ⟨_, changed, changedRep, leafApplies, modifiedEvaluated, _⟩ :=
    CompatiblePlaceNumericBitNotModifier.wide_success head.profile rfl snapshotRep
      (environment := .unit :: .inRight .unit leftCore :: found :: .word position ::
        .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
      (rhs := .var 0) (.var (index := 1) rfl) none lookupStore head.invalid
  cases CompatiblePlaceNumericBitNotModifier.assignment_functional leafApplies applied
  have leafTyped := applied.preserves_target kind (.some selectedTyped)
  -- The Core write: the array's cell takes the leaf's entry at the index.
  obtain ⟨length, default, entries, suffix, futureWorld, storeRead, wordKeys, appended, finalHeaps, futureWorlds,
      storeFrame, storeEffect⟩ :=
    CellAwareArrayReads.store_preserve_at head.prepared lookupHeaps
      (stack := changed :: .unit :: .inRight .unit leftCore :: found :: .word position ::
        .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
      (context := head.elementType :: .unit :: .sum .unit head.elementType ::
        .sum .unit head.elementType :: .word :: head.rootType :: actualContext)
      (.cons changedRep.runtime_hasType (.cons .unit (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons foundTyped (.cons .word (.cons (.cellRef typed) lookupTyped))))))
      currentRead objectValue replace heapWrite mapped typed changedRep rfl
      (arrayExpr := .var 5) (keyExpr := .var 4) (fun read => .loadCell (.var rfl) read) (.var rfl)
      (fun _ => .var rfl) (.var rfl) rfl rfl
  -- The array's Core cell after the write, at its world's type: the updated entries are of the layout's type.
  have finalBound : arrayTarget < (lookupStore ++ suffix).length := by
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp storeRead).1 (Nat.le_add_right _ _)
  obtain ⟨_, cellRead, cellTyped⟩ := finalHeaps.runtime_hasTypes.lookup (futureWorlds.lookup typed)
  have newRead := List.getElem?_set_self (a := Core.Value.pair (.word length) (.pair default
    (OrderedMapping.encode head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position)
      changed entries)))) finalBound
  have cellEq := Option.some.inj (cellRead.symm.trans newRead)
  subst cellEq
  cases cellTyped with
  | pair _ inner =>
  cases inner with
  | pair _ encodeTyped =>
  -- The caller's pool after the write.
  let suffixPool : State headers keys ⟨scope, keyMap, futureWorld, after, _, canonical⟩ :=
    (bridge.pool lookupReached).extend (.refl _) futureWorlds storeFrame (.of_write heapWrite)
  obtain ⟨returned, _, returnedRelated⟩ := bridge.restore lookupReached suffixPool (.refl _) futureWorlds storeFrame
    (.of_write heapWrite) (Relates.of_records_eq rfl)
  exact ⟨changed, length, default, entries, suffix, futureWorld, modifiedEvaluated, storeRead, wordKeys, appended,
    finalHeaps, futureWorlds, storeFrame, .of_write heapWrite, storeEffect,
    .cons .unit (.cons encodeTyped (.cons (changedRep.runtime_hasType.weaken futureWorlds) (.cons .unit
      (.cons (.inRight (snapshotRep.runtime_hasType.weaken futureWorlds)) (.cons (foundTyped.weaken futureWorlds)
        (.cons .word (.cons (.cellRef (futureWorlds.lookup typed)) (lookupTyped.weaken futureWorlds)))))))),
    returned, returnedRelated,
    reference.arrayElementWrite lookupAdmitted.heap currentRead objectValue replace leafTyped heapWrite,
    StableRows.after_administrative (bridge.pool lookupReached) (bridge.pool returned) lookupAdmitted.rows
      storeFrame⟩

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique
  assignmentTyped in
/-- An in-place `~` at one element of a local array, `a[i] ~=;`, from its staged Source run: the root's array,
the index's meaning, the bound's check, the element's snapshot, the unit right side, `modified`'s leaf as the
Source's `~` computes it at the target's type, the insert and the array's cell taking the leaf at the index on
both sides; `guard` has no check. The compiled code runs to its continuation under the eight binders. -/
theorem preserves_bitNot (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    {targetSize : Nat} {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value} {targetHeap after : Dynamic.Heap}
    (targetTrace : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment
      before assignment.target (.resolved target) targetHeap)
    (targetBound : targetSize < budget)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.BitNotAssignmentApplies assignment.target.type target.selected replacement)
      targetHeap target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after
        finalStore ∧
      slots.length = 8 ∧
      RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.bitNotSlotTypes ++ actualContext)
        compiled.indexed.layouts.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output {result : Value} {final : Store},
        Evaluates (slots ++ actual) finalStore (shift 8 (next.rename ξ)) result final →
        Evaluates actual store ((head.emit next output).rename ξ) result final := by
  -- The Source types: the target's, of `~`'s target types, and the index's at its node's.
  cases assignmentTyped with
  | intro targetTyped kind _ =>
  have targetEq := targetTyped.type_eq
  subst targetEq
  obtain ⟨_, _, indexTyped⟩ := Staging.Recursive.SelectedPreservation.element_place_typed (leading := [])
    (index := head.key) targetTyped head.single
  have keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type :=
    CellAwareArraySourceInversion.typed_type unique head.keyFound indexTyped ▸ indexTyped
  cases ElementAssignmentSourceInversion.single_resolved head.single targetTrace with
  | @intro indexSize _ cell element arrayLocation position _ _ elements selected lookup read initialValue indexed
      arrayRead arrayValue selection =>
  -- The root's Source cell holds a reference to an array of the target's type.
  have cellType := bitNot_root_cell_type head locals lookup read
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
    preserves_bitNot_snapshot bridge functions head environments heaps locals agrees actualTyped initial admitted
      authority physical owner ownerFrame budget meaning lookup read initialValue keyTyped indexed
      (Nat.lt_trans (Staging.Recursive.Size.child_lt_stepSize (by simp)) targetBound) arrayRead arrayValue selection
  -- `~`'s leaf and the write, on both sides.
  obtain ⟨changed, length', default, entries, suffix, futureWorld, modifiedEvaluated, storeRead, wordKeys, appended,
      finalHeaps, futureWorlds, storeFrame, storeMetadata, storeEffect, slotsTyped, returned, returnedRelated,
      returnedAdmitted⟩ :=
    bitNot_commit_preserve bridge functions head lookupHeaps (actualTyped.weaken prefixWorlds) prefixReached
      prefixAdmitted kind (referenceBefore.mono prefixMetadata) mapped typed arrayRead arrayValue selection foundTyped
      snapshotRep write
  refine ⟨_, keyMap, futureWorld,
    [.unit, OrderedMapping.encode head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual
        (.word position) changed entries), changed, .unit, .inRight .unit leftCore, found, .word position,
      .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget],
    finalHeaps, prefixMaps, prefixWorlds.trans futureWorlds, prefixFrame.trans storeFrame,
    prefixMetadata.trans storeMetadata, prefixEffect.trans storeEffect, rfl, slotsTyped,
    ⟨returned, callerProtocol.trans prefixRelated returnedRelated, returnedAdmitted⟩, ?_⟩
  -- The compiled code runs to its continuation; `guard` has no check.
  intro next output result final nextEval
  rw [BitNotHead.emit, CompatibleElementWrites.code_rename, BitNotHead.modifier_eq]
  exact CompatibleElementWrites.compound_evaluates head.prepared rfl reference full keyEval lengthRead within lookedUp
    snapshotted (CompatibleElementWrites.unit_evaluates ξ 4 _ lookupStore) modifiedEvaluated storeRead wordKeys
    (fun written => written) (by rw [appended]; exact nextEval)

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique
  assignmentTyped in
/-- An in-place `~` at one element of a local array, from a sized Core run of its code: the element target's
fault, at a root not yet initialized, at the index of a root that holds its array, or at `0x32` from the array's
length on, the run failing with the fault's token; or the target resolved and written as the Source's `~` writes
it, the run of the continuation under the eight binders strictly smaller. -/
theorem reflects_bitNot_bounded [RecursiveStageMeaning.FaultTokens faults] (budget : Nat)
    (reflection : ReflectsBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    (uninitialized : ∀ location, faults (.semantic (.uninitializedLocation location)) head.invalidProjection)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store} {size : Nat}
    (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore)
    (bounded : size ≤ budget) :
    BitNotResultAt bridge size _ acceptedCells acceptedInstances context stages invocation faults scope
      (head.bitNotSlotTypes ++ actualContext) assignment environment canonical actual before store mapping world
      initial (next.rename ξ) output value finalStore := by
  -- The Source types: the target's, of `~`'s target types, and the index's at its node's.
  cases assignmentTyped with
  | intro targetTyped kind _ =>
  have targetEq := targetTyped.type_eq
  subst targetEq
  obtain ⟨_, _, indexTyped⟩ := Staging.Recursive.SelectedPreservation.element_place_typed (leading := [])
    (index := head.key) targetTyped head.single
  have keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type :=
    CellAwareArraySourceInversion.typed_type unique head.keyFound indexTyped ▸ indexTyped
  have projectionsEq : assignment.target.projections = [] ++ [.element head.key] := head.single
  -- The root's Source cell, ordinary as its monomorphic binder's, and its Core cell.
  obtain ⟨_, schemeLookup, _, monomorphic, bodyEq⟩ := head.writable.scheme
  obtain ⟨location, cell, lookup, read, cellBody, _⟩ := locals.lookup schemeLookup
  have cellType := cellBody.trans bodyEq
  have ordinary := locals.descriptor_empty_of_monomorphic admitted.heap schemeLookup lookup read monomorphic
  obtain ⟨rootTarget, _, reference, coreRead, represented⟩ :=
    CellAwareElementWriteRoots.cell_at environments heaps agrees head.slotEq lookup read ordinary
  rw [BitNotHead.emit, CompatibleElementWrites.code_rename, BitNotHead.modifier_eq] at completed
  have complete := completed.sound
  cases represented with
  | @uninitialized sourceType _ _ =>
    -- A root not yet initialized: the root's check fails as the Source's target does.
    have rootType : sourceType = TypeSystem.Ty.array assignment.target.type := cellType
    subst rootType
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleElementWrites.root_empty reference coreRead)
    refine .targetFault (.elementUninitialized projectionsEq (.elementRoot rfl lookup read (.uninitialized ?_)) rfl)
      rfl (uninitialized location) heaps (.refl _) (.refl _) (.refl _ _) (.refl _) (.refl _ _ _ _) initial
      (callerProtocol.refl _) admitted.rows
    rintro ⟨_, _, same⟩
    simp [TypeSystem.Ty.array] at same
  | @initialized sourceType _ _ _ rootRep =>
    -- The root holds its array: the root's check passes with the array's cell.
    have rootType : sourceType = TypeSystem.Ty.array assignment.target.type := cellType
    subst rootType
    obtain ⟨element, arrayLocation, rfl⟩ := array_source rootRep (element := assignment.target.type) rfl
    obtain ⟨arrayTarget, payload, identity, rfl, typeEq, mapped, typed, _⟩ := arrayRef_fields rootRep rfl
    simp only [Core.Ty.cell.injEq, Core.Ty.product.injEq, Core.Ty.namedData.injEq, true_and] at typeEq
    obtain ⟨rfl, rfl⟩ := typeEq
    have referenceBefore : Dynamic.ValueHasType context before (.arrayRef element arrayLocation)
        (TypeSystem.Ty.array assignment.target.type) := by
      have cellTyped := (admitted.heap _ read.member).value
      dsimp only at cellTyped
      cases cellTyped with
      | some typed => exact typed
    -- The index's sized run, under the array's binder, reflected.
    obtain ⟨first, firstSmaller, afterRoot⟩ :=
      completed.bind_success (CompatibleElementWrites.root_full reference coreRead)
    simp only [arrayElementWrite] at afterRoot
    obtain ⟨second, keyStore, keyValue, secondSmaller, indexRun⟩ := afterRoot.bind_computation
    have shifted : EvaluationSize second
        (.cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual) store
        (head.keyCode.expression.rename (Renaming.comp (Renaming.insertion 0) ξ)) keyValue keyStore := by
      rw [rename_prefix]
      exact indexRun
    obtain ⟨_, _, keyHeap, keyMap, keyWorld, indexTrace, indexRep, keyHeaps, keyMaps, keyWorlds, keyFrame,
        keyMetadata, keyEffect, keyReached, keyRelated, keyPost⟩ :=
      reflection second (by omega) head.keyChild head.keyFound keyTyped environments heaps locals
        (agree_prefix agrees _) (.cons (.cellRef typed) actualTyped) initial admitted authority physical owner
        ownerFrame shifted
    have indexed := indexRun.sound
    cases indexRep with
    | fault matched =>
      -- The index's fault: the Source's target faults at the index, as the Core run does.
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
        (CompatibleElementWrites.index_failure reference coreRead indexed)
      exact .targetFault (.elementIndexFault projectionsEq (.elementRoot rfl lookup read .initialized)
          (Option.some_ne_none _) indexTrace)
        rfl matched keyHeaps keyMaps keyWorlds keyFrame keyMetadata keyEffect keyReached keyRelated keyPost.rows
    | @value _ _ indexPayload =>
      rw [head.keyType] at indexPayload
      obtain ⟨position, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields indexPayload
      -- The array's Source cell at the index's heap, and its length on both sides.
      have keyAdmitted := keyPost.at_value.2
      have referenceKey := referenceBefore.mono keyMetadata
      obtain ⟨arrayCell, _, elements, arrayRead, arrayValue⟩ :=
        array_cell_initial keyHeaps (keyMaps.lookup mapped) (keyWorlds.lookup typed)
      obtain ⟨sameOther, sameElement⟩ :=
        object_element referenceKey keyAdmitted.heap arrayRead arrayValue.arrayObject_value
      subst sameOther
      subst sameElement
      have arrayPayload := rootRep.extend (.refl _) keyMaps keyWorlds
      obtain ⟨measured, small⟩ :=
        CellAwareArrayReads.length_preserve keyHeaps (.array arrayRead arrayValue.arrayObject_value) arrayPayload rfl
      cases measured with
      | array coreArrayRead =>
      by_cases inside : position.val < elements.length
      · -- Below the array's length: the element's snapshot, `~`'s leaf and the write, on both sides.
        obtain ⟨selected, selection⟩ := valueAt_exists inside
        obtain ⟨lookupStore, lookupWorld, length, rest, found, leftCore, lengthRead, within, lookedUp, snapshotted,
            foundTyped, snapshotRep, lookupHeaps, lookupWorlds, lookupFrame, lookupEffect, lookupReached,
            lookupRelated, lookupAdmitted⟩ :=
          bitNot_lookup_preserve bridge functions head keyHeaps (actualTyped.weaken keyWorlds) keyReached
            keyAdmitted arrayPayload rfl arrayRead arrayValue selection
        obtain ⟨leaf, _, _, leafApplies, _, _⟩ :=
          CompatiblePlaceNumericBitNotModifier.wide_success head.profile rfl snapshotRep
            (environment := [.inRight .unit leftCore]) (rhs := .unit) (.var (index := 0) rfl) none lookupStore
            head.invalid
        obtain ⟨updatedElements, replace⟩ :=
          CellAwareInvocationArrayBounds.replace_exists leaf selection.lt_length
        obtain ⟨finalHeap, heapWrite⟩ := CompatibleExpressionReadCompletion.writes_exists arrayRead
          (.arrayObject assignment.target.type updatedElements)
        have write : Dynamic.ResolvedPlaceWrites
            (fun _ replacement => Dynamic.BitNotAssignmentApplies assignment.target.type (some selected) replacement)
            keyHeap
              { location := arrayLocation, rootType := arrayCell.type, valueType := assignment.target.type,
                projections := [.element position.val], selected := some selected }
            (.arrayObject assignment.target.type updatedElements) finalHeap :=
          .intro arrayRead rfl arrayValue (.element selection (.leaf leafApplies) replace) heapWrite
        obtain ⟨changed, length', default, entries, suffix, futureWorld, modifiedEvaluated, storeRead, wordKeys,
            appended, finalHeaps, futureWorlds, storeFrame, storeMetadata, storeEffect, slotsTyped, returned,
            returnedRelated, returnedAdmitted⟩ :=
          bitNot_commit_preserve bridge functions head lookupHeaps
            ((actualTyped.weaken keyWorlds).weaken lookupWorlds) lookupReached lookupAdmitted kind referenceKey
            (keyMaps.lookup mapped) (lookupWorlds.lookup (keyWorlds.lookup typed)) arrayRead arrayValue selection
            foundTyped snapshotRep write
        obtain ⟨remainingSize, smaller, remaining⟩ := CompatibleElementWrites.compound_continuation head.prepared rfl
          completed reference coreRead indexed lengthRead within lookedUp snapshotted
          (CompatibleElementWrites.unit_evaluates ξ 4 _ lookupStore) modifiedEvaluated storeRead wordKeys
          (fun _ => rfl)
        rw [appended] at remaining
        exact .success (slots := [.unit, OrderedMapping.encode head.layout
            (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries), changed,
            .unit, .inRight .unit leftCore, found, .word position,
            .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget])
          (.elementStep projectionsEq (.elementRoot rfl lookup read .initialized) rfl indexTrace arrayRead arrayValue
            selection)
          write finalHeaps keyMaps ((keyWorlds.trans lookupWorlds).trans futureWorlds)
          ((keyFrame.trans lookupFrame).trans storeFrame) (keyMetadata.trans storeMetadata)
          ((keyEffect.trans lookupEffect).trans storeEffect) rfl slotsTyped returned
          (callerProtocol.trans (callerProtocol.trans keyRelated lookupRelated) returnedRelated) returnedAdmitted
          smaller remaining
      · -- `0x32` from the array's length on: the bound's check fails on both sides.
        have outside : ¬ position < Word.ofNatModulo elements.length := by
          rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
          exact inside
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
          (CompatibleElementWrites.outOfBounds reference coreRead indexed coreArrayRead outside)
        exact .targetFault (.elementOutOfBounds projectionsEq (.elementRoot rfl lookup read .initialized) rfl
            indexTrace arrayRead arrayValue.arrayObject_value (by omega)) rfl
          (RecursiveStageMeaning.FaultTokens.panic _) keyHeaps keyMaps keyWorlds keyFrame keyMetadata keyEffect
          keyReached keyRelated keyPost.rows

end Heads
end Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteHeads

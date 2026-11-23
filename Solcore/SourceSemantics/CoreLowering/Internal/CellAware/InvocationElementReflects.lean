import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementHeads

/-!
# Cell-aware invocations: a plain write to an element, reflected

From an actual Core run of `a[i] = v`'s code, the Source's staged run: the run split at the root's check, the
index, the bound, the right side, the insert and the store (`CompatibleElementWrites.plain_split`,
`plain_store_split`, `plain_tail_split`), and the element's `ResultAt`, with the array's length kept across the
right side as S7's store does. Main declarations: `CellAwareElementWriteHeads.ResultAt` and
`reflects_plain_bounded`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ### The Core run of a plain write to an element, split

A sized run of the code `lowerElements` emits for `a[i] = v`, at its steps: the root's check, the index, the
bound's check, the right side, and the insert, the store and the continuation. These belong beside the code's
runs in `Compatible/ElementWrites.lean`. -/

namespace Solcore.SourceSemantics.CoreLowering.CompatibleElementWrites
open Core Frontend SourceCoreCompatibleDataPlaces CoreProof

/-- A plain write's code, with its binds unfolded up to the element's store. -/
theorem plain_code (slot : Nat) (storedType outputType : Ty) (invalid : Word) (comparison value next : Expr)
    (layout : OrderedMapping.Layout) (index : Expr) :
    code slot storedType outputType invalid comparison value next none layout index =
      .caseE (.caseE (.loadCell (.var slot)) (.inLeft storedType (.word invalid)) (.inRight .word (.var 0)))
        (.inLeft outputType (.var 0))
        (.caseE (shift 1 index) (.inLeft outputType (.var 0))
          (.ifE (Expr.wordLt (.var 0) (.first (.loadCell (.var 1))))
            (elementStore outputType comparison value next none 1 layout)
            (.inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.outOfBounds))))) := rfl

/-- A plain write's element store, with its binds unfolded: the right side, then the insert, the store and the
continuation. -/
theorem plain_store (outputType : Ty) (comparison value next : Expr) (layout : OrderedMapping.Layout) :
    elementStore outputType comparison value next none 1 layout =
      .caseE (shift 2 value) (.inLeft outputType (.var 0))
        (.caseE (OrderedMapping.insert layout (shift 3 comparison) (.second (.second (.loadCell (.var 2))))
            (.var 1) (.var 0))
          (.inLeft outputType (.var 0))
          (.letE (.storeCell (.var 3) (.pair (.first (.loadCell (.var 3)))
              (.pair (.first (.second (.loadCell (.var 3)))) (.var 0))))
            (shift 5 next))) := rfl

/-- A sized run of a plain write's code whose root's cell is `location`, at its steps: the root not yet
initialized, the index's failure, `0x32` from the bound's check, and the element's store below the length, each
step's run below the code's. -/
inductive PlainRun (environment : Environment) (store : Store) (location : Location) (outputType : Ty)
    (invalid : Word) (comparison value next : Expr) (layout : OrderedMapping.Layout) (index : Expr) (size : Nat) :
    Value → Store → Prop where
  | empty {payloadType : Ty} {payload : Value}
      (empty : store.read? location = some (.inLeft payloadType payload)) :
      PlainRun environment store location outputType invalid comparison value next layout index size
        (.inLeft outputType (.word invalid)) store
  | indexFailure {leftType indexType : Ty} {array payload : Value} {indexSize : Nat} {final : Store}
      (full : store.read? location = some (.inRight leftType array))
      (indexed : EvaluationSize indexSize (array :: environment) store (shift 1 index) (.inLeft indexType payload)
        final)
      (indexBound : indexSize < size) :
      PlainRun environment store location outputType invalid comparison value next layout index size
        (.inLeft outputType payload) final
  | outOfBounds {leftType indexType : Ty} {array position : Value} {indexSize : Nat} {indexStore final : Store}
      (full : store.read? location = some (.inRight leftType array))
      (indexed : EvaluationSize indexSize (array :: environment) store (shift 1 index)
        (.inRight indexType position) indexStore)
      (indexBound : indexSize < size)
      (checked : Evaluates (position :: array :: environment) indexStore
        (Expr.wordLt (.var 0) (.first (.loadCell (.var 1)))) (.bool false) final) :
      PlainRun environment store location outputType invalid comparison value next layout index size
        (.inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.outOfBounds))) final
  | inBounds {leftType indexType : Ty} {array position result : Value} {indexSize storeSize : Nat}
      {indexStore checkStore final : Store}
      (full : store.read? location = some (.inRight leftType array))
      (indexed : EvaluationSize indexSize (array :: environment) store (shift 1 index)
        (.inRight indexType position) indexStore)
      (indexBound : indexSize < size)
      (checked : Evaluates (position :: array :: environment) indexStore
        (Expr.wordLt (.var 0) (.first (.loadCell (.var 1)))) (.bool true) checkStore)
      (stored : EvaluationSize storeSize (position :: array :: environment) checkStore
        (elementStore outputType comparison value next none 1 layout) result final)
      (storeBound : storeSize < size) :
      PlainRun environment store location outputType invalid comparison value next layout index size result final

/-- A sized run of a plain write's code, split at its steps (`PlainRun`). -/
theorem plain_split {environment : Environment} {store final : Store} {slot : Nat}
    {storedType outputType cellType : Ty} {invalid : Word} {comparison value next index : Expr}
    {layout : OrderedMapping.Layout} {location : Location} {size : Nat} {result : Value}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (evaluated : EvaluationSize size environment store
      (code slot storedType outputType invalid comparison value next none layout index) result final) :
    PlainRun environment store location outputType invalid comparison value next layout index size result final := by
  rw [plain_code] at evaluated
  cases evaluated with
  | caseLeft scrutinee branch =>
    cases scrutinee with
    | caseLeft loaded failed =>
      cases loaded with
      | loadCell refRun read =>
        cases refRun with
        | var found =>
          rw [reference] at found
          cases found
          cases failed with
          | inLeft word =>
            cases word
            cases branch with
            | inLeft payloadRun =>
              cases payloadRun with
              | var found' =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at found'
                subst found'
                exact .empty read
    | caseRight loaded succeeded => cases succeeded
  | caseRight scrutinee body =>
    cases scrutinee with
    | caseLeft loaded failed => cases failed
    | caseRight loaded succeeded =>
      cases loaded with
      | loadCell refRun read =>
        cases refRun with
        | var found =>
          rw [reference] at found
          cases found
          cases succeeded with
          | inRight payloadRun =>
            cases payloadRun with
            | var found' =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found'
              subst found'
              cases body with
              | caseLeft indexed failed =>
                cases failed with
                | inLeft payloadRun =>
                  cases payloadRun with
                  | var found'' =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at found''
                    subst found''
                    exact .indexFailure read indexed (by omega)
              | caseRight indexed checkedBody =>
                cases checkedBody with
                | ifFalse checked failed =>
                  cases failed with
                  | inLeft word =>
                    cases word
                    exact .outOfBounds read indexed (by omega) checked.sound
                | ifTrue checked stored => exact .inBounds read indexed (by omega) checked.sound stored (by omega)

/-- A sized run of a plain write's element store, at its steps: the right side's failure, or its value and the
rest of the code, the insert, the store and the continuation, each step's run below the store's. -/
inductive PlainStore (environment : Environment) (store : Store) (outputType : Ty) (comparison value next : Expr)
    (layout : OrderedMapping.Layout) (size : Nat) : Value → Store → Prop where
  | rhsFailure {rightType : Ty} {payload : Value} {rhsSize : Nat} {final : Store}
      (failed : EvaluationSize rhsSize environment store (shift 2 value) (.inLeft rightType payload) final)
      (rhsBound : rhsSize < size) :
      PlainStore environment store outputType comparison value next layout size (.inLeft outputType payload) final
  | rhsValue {rightType : Ty} {stored result : Value} {rhsSize tailSize : Nat} {rhsStore final : Store}
      (rhsEvaluated : EvaluationSize rhsSize environment store (shift 2 value) (.inRight rightType stored) rhsStore)
      (rhsBound : rhsSize < size)
      (tail : EvaluationSize tailSize (stored :: environment) rhsStore
        (.caseE (OrderedMapping.insert layout (shift 3 comparison) (.second (.second (.loadCell (.var 2))))
            (.var 1) (.var 0))
          (.inLeft outputType (.var 0))
          (.letE (.storeCell (.var 3) (.pair (.first (.loadCell (.var 3)))
              (.pair (.first (.second (.loadCell (.var 3)))) (.var 0))))
            (shift 5 next)))
        result final)
      (tailBound : tailSize < size) :
      PlainStore environment store outputType comparison value next layout size result final

/-- A sized run of a plain write's element store, split at the right side (`PlainStore`). -/
theorem plain_store_split {environment : Environment} {store final : Store} {outputType : Ty}
    {comparison value next : Expr} {layout : OrderedMapping.Layout} {size : Nat} {result : Value}
    (evaluated : EvaluationSize size environment store (elementStore outputType comparison value next none 1 layout)
      result final) :
    PlainStore environment store outputType comparison value next layout size result final := by
  rw [plain_store] at evaluated
  cases evaluated with
  | caseLeft rhsRun failed =>
    cases failed with
    | inLeft payloadRun =>
      cases payloadRun with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        subst found
        exact .rhsFailure rhsRun (by omega)
  | caseRight rhsRun tail => exact .rhsValue rhsRun (by omega) tail (by omega)

private theorem write_set {store : Store} {location : Location} (bound : location < store.length) (value : Value) :
    store.write? location value = some (store.set location value) := by
  simp [Store.write?, bound]

/-- The rest of a plain write's code after the right side's value: the insert of the value's entry at the
index, then the array's cell takes the entries, keeping its length and default element, and the continuation
runs with the five binders, below the rest's size. -/
theorem plain_tail_split {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
    {comparison : SourceCoreCompatibleDataEquality.Prepared checked}
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
    {layout : OrderedMapping.Layout} (keyType : layout.keyType = .word)
    {environment : Environment} {outputType elementType : Ty} {arrayLocation : Location} {position length : Word}
    {default stored result : Value} {entries : OrderedMapping.Entries} {next : Expr} {tailSize : Nat}
    {rhsStore final : Store}
    (current : rhsStore.read? arrayLocation =
      some (.pair (.word length) (.pair default (OrderedMapping.encode layout entries))))
    (wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word)
    (tail : EvaluationSize tailSize (stored :: .word position :: .cellRef elementType arrayLocation :: environment)
      rhsStore
      (.caseE (OrderedMapping.insert layout (shift 3 comparison.expression) (.second (.second (.loadCell (.var 2))))
          (.var 1) (.var 0))
        (.inLeft outputType (.var 0))
        (.letE (.storeCell (.var 3) (.pair (.first (.loadCell (.var 3)))
            (.pair (.first (.second (.loadCell (.var 3)))) (.var 0))))
          (shift 5 next)))
      result final) :
    ∃ remainingSize, remainingSize < tailSize ∧
      EvaluationSize remainingSize
        (.unit :: OrderedMapping.encode layout
            (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) stored entries) ::
          stored :: .word position :: .cellRef elementType arrayLocation :: environment)
        ((CompatibleMappingComparison.insertStore comparison layout
            (stored :: .word position :: .cellRef elementType arrayLocation :: environment) rhsStore entries
            (.word position) stored).set arrayLocation
          (.pair (.word length) (.pair default (OrderedMapping.encode layout
            (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) stored entries)))))
        (shift 5 next) result final := by
  rw [shift_closed comparison] at tail
  let stack := stored :: .word position :: .cellRef elementType arrayLocation :: environment
  have inserted := OrderedMapping.insert_evaluates (environment := stack)
    (mapping := .second (.second (.loadCell (.var 2)))) (keyExpr := .var 1) (valueExpr := .var 0)
    (keyEqual := comparison.expression) entries (.word position) stored
    (CompatibleMappingComparison.comparator comparison stack rhsStore) GenericHeap.arrayKeyEqual
    (.second (.second (.loadCell (.var rfl) current))) (.var rfl) (.var rfl)
    (CompatibleEquality.prepared_evaluates_exact comparison stack rhsStore)
    (CompatibleArrayEvaluation.word_comparisons prepared keyType stack rhsStore wordKeys position _)
  have bound : arrayLocation < rhsStore.length := (List.getElem?_eq_some_iff.mp current).1
  have kept : (CompatibleMappingComparison.insertStore comparison layout stack rhsStore entries (.word position)
      stored).read? arrayLocation =
        some (.pair (.word length) (.pair default (OrderedMapping.encode layout entries))) := by
    simp only [CompatibleMappingComparison.insertStore, OrderedMapping.installedStore, WordMapping.installedStore,
      CompatibleMappingComparison.comparisonStore, Store.read?, List.append_assoc] at current ⊢
    rw [List.getElem?_append_left bound]
    exact current
  have keptBound : arrayLocation <
      (CompatibleMappingComparison.insertStore comparison layout stack rhsStore entries (.word position)
        stored).length :=
    (List.getElem?_eq_some_iff.mp kept).1
  have storedCell : Evaluates (OrderedMapping.encode layout
        (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) stored entries) :: stack)
      (CompatibleMappingComparison.insertStore comparison layout stack rhsStore entries (.word position) stored)
      (.storeCell (.var 3) (.pair (.first (.loadCell (.var 3))) (.pair (.first (.second (.loadCell (.var 3))))
        (.var 0)))) .unit
      ((CompatibleMappingComparison.insertStore comparison layout stack rhsStore entries (.word position)
          stored).set arrayLocation
        (.pair (.word length) (.pair default (OrderedMapping.encode layout
          (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) stored entries))))) :=
    .storeCell (.var rfl) kept
      (.pair (.first (.loadCell (.var rfl) kept)) (.pair (.first (.second (.loadCell (.var rfl) kept))) (.var rfl)))
      (write_set keptBound _)
  cases tail with
  | caseLeft insertRun _ =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic insertRun.sound inserted
    cases impossible
  | caseRight insertRun body =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic insertRun.sound inserted
    cases same
    cases body with
    | letE storeRun remaining =>
      obtain ⟨same, rfl⟩ := evaluation_deterministic storeRun.sound storedCell
      cases same
      exact ⟨_, by omega, remaining⟩

/-- The bound's check, at an array's cell that holds its length. -/
theorem check_evaluates {environment : Environment} {elementType : Ty} {arrayLocation : Location}
    {position length : Word} {rest : Value} {store : Store}
    (read : store.read? arrayLocation = some (.pair (.word length) rest)) :
    Evaluates (.word position :: .cellRef elementType arrayLocation :: environment) store
      (Expr.wordLt (.var 0) (.first (.loadCell (.var 1)))) (.bool (decide (position < length))) store :=
  CompatibleArrayEvaluation.wordLt_evaluates
    (environment := .word position :: .cellRef elementType arrayLocation :: environment) (store := store)
    (left := .var 0) (right := .first (.loadCell (.var 1))) (weakened := .first (.loadCell (.var 2)))
    (by simp [Expr.weakenAt]) (.var rfl) (.first (.loadCell (.var rfl) read))

/-- A run of the bound's check is its check: whether the index is below the length, and no store change. -/
theorem check_cases {environment : Environment} {elementType : Ty} {arrayLocation : Location}
    {position length : Word} {rest : Value} {store final : Store} {flag : Bool}
    (read : store.read? arrayLocation = some (.pair (.word length) rest))
    (checked : Evaluates (.word position :: .cellRef elementType arrayLocation :: environment) store
      (Expr.wordLt (.var 0) (.first (.loadCell (.var 1)))) (.bool flag) final) :
    flag = decide (position < length) ∧ final = store := by
  obtain ⟨same, rfl⟩ := evaluation_deterministic checked (check_evaluates read)
  cases same
  exact ⟨rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleElementWrites

/-! ### The reflect head of a plain write to an element -/

namespace Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

/-- A writable local's cell: its lookup and read, at the local's type, holding no generalized local, since a
generalized local's scheme quantifies and a writable local's does not. -/
theorem writable_root {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {root : Resolved.LocalId} {type : TypeSystem.Ty}
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context heap) (writable : WritableLocal context root type) :
    ∃ location cell, Dynamic.Environment.LooksUp environment root location ∧
      Dynamic.Heap.Reads heap location cell ∧ cell.type = type ∧ cell.generalized = none := by
  obtain ⟨scheme, staticLookup, _, quantified, bodyEq⟩ := writable.scheme
  obtain ⟨location, cell, lookup, read, cellType, storage⟩ := locals.lookup staticLookup
  refine ⟨location, cell, lookup, read, cellType.trans bodyEq, ?_⟩
  cases storage with
  | ordinary _ empty => exact empty
  | generalized descriptor _ sameScheme =>
    have typed := (heapTyped _ read.member).generalized
    rw [descriptor] at typed
    generalize cell.type = annotation at typed
    cases typed with
    | some closure => exact absurd (by rw [sameScheme]; exact quantified) closure.code.polymorphic

/-- A position below a list's length has an element. -/
theorem valueAt_exists : ∀ {elements : List Dynamic.Value} {position : Nat}, position < elements.length →
    ∃ selected, Dynamic.ValueAt elements position selected
  | [], _, bound => by simp at bound
  | _ :: _, 0, _ => ⟨_, .head⟩
  | _ :: rest, position + 1, bound => by
    obtain ⟨selected, selection⟩ := valueAt_exists (elements := rest) (position := position) (by simpa using bound)
    exact ⟨selected, .tail selection⟩

/-- An array object's Source cell, whose mapped Core cell is at a product type, is an array cell: it holds no
generalized local, so the object is its initial value. -/
theorem array_initial {definitions : DataEnvironment} {model : GenericHeap.CellModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.CellHeapRepresents model mapping world heap store)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {element : TypeSystem.Ty} {elements : List Dynamic.Value}
    {target : Location} {left right : Ty}
    (read : Dynamic.Heap.Reads heap location cell) (stored : cell.value = some (.arrayObject element elements))
    (mapped : mapping[location.index]? = some target) (typed : world[target]? = some (.product left right)) :
    Dynamic.RootInitialValue cell (some (.arrayObject element elements)) := by
  obtain ⟨_, _, sourceRead, _, stands⟩ := heaps.cells mapped
  cases read.functional sourceRead
  cases stands with
  | optional optionalTyped _ =>
    have impossible := optionalTyped.symm.trans typed
    simp [Core.OptionalCell.cellType] at impossible
  | array _ arrayed =>
    obtain ⟨⟨element', elements', cellEq⟩, _⟩ := model.array_shape arrayed
    subst cellEq
    simp only [Option.some.injEq, Dynamic.Value.arrayObject.injEq] at stored
    obtain ⟨rfl, rfl⟩ := stored
    exact .initialized

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Results
variable
  {functions :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}

local notation "acceptedCells" => GeneralizedLocalDescriptorHeap.cellModel
  (payloadModel compiled.compatible.checked registry functions)
  (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
local notation "acceptedInstances" => GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment

/-- What a sized Core run of a plain write to one element of a local array reflects: the Source's element
target faulting at a root not yet initialized (`elementUninitialized`, as the Core's root check fails first), at
the index's fault or at `0x32`, the right side's fault after the target, or the write, with the five binders and
the continuation's run below the code's. -/
inductive ResultAt (size : Nat) (context : SourceSemantics.Context) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (faults : RecursiveStageMeaning.FaultRep) (scope : Scope)
    (writtenContext : Core.Context) (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp)
    (rhs : ExpressionId) (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | uninitialized {targetSize : Nat} {location : Dynamic.Location} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (failed : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment before
        assignment.target (.fault (.semantic (.uninitializedLocation location))) after)
      (same : value = .inLeft output (.word token))
      (matched : faults (.semantic (.uninitializedLocation location)) token)
      (heaps : GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore)
      (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after
        finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs environment
        canonical actual before store mapping world initial next output value finalStore
  | indexFault {targetSize : Nat} {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (failed : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment before
        assignment.target (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore)
      (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after
        finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs environment
        canonical actual before store mapping world initial next output value finalStore
  | outOfBounds {targetSize : Nat} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (failed : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment before
        assignment.target (.fault (.semantic (.panic 0x32))) after)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic (.panic 0x32)) token)
      (heaps : GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore)
      (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after
        finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs environment
        canonical actual before store mapping world initial next output value finalStore
  | rhsFault {targetSize sourceSize : Nat} {target : Dynamic.ResolvedPlace} {targetHeap : Dynamic.Heap}
      {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (resolved : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment
        before assignment.target (.resolved target) targetHeap)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap
        rhs (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore)
      (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after
        finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs environment
        canonical actual before store mapping world initial next output value finalStore
  | success {targetSize sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace}
      {right updated : Dynamic.Value} {targetHeap middle after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (resolved : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment
        before assignment.target (.resolved target) targetHeap)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap
        rhs (.value right) middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement =>
          Dynamic.CompoundAssignmentApplies assignment.target.type operator target.selected right replacement)
        middle target updated after)
      (heaps : GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written)
      (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after
        written)
      (count : slots.length = 5)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext
        compiled.indexed.layouts.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 5 next) value finalStore) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs environment
        canonical actual before store mapping world initial next output value finalStore

end Results

section Heads
variable {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  (functions :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
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

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique
  assignmentTyped in
/-- A plain write to one element of a local array, `a[i] = v`, reflected from the sized Core run of its code: the
root's Source cell, the writable local's, and its Core cell; the index's and the right side's Source runs from their
Core runs below the code's size, at the reached callers; and the Source's element target and write. The array
keeps its length while the right side runs (`KeepsLengths`, from `selectedBodies`, `runtime` and `covers`), so
the Source's write applies at the position the bound's check admitted. A root not yet initialized is
`elementUninitialized`, at the site's reason, as the Core's root check fails before the index. -/
theorem reflects_plain_bounded [RecursiveStageMeaning.FaultTokens faults] (budget : Nat) (plain : operator = .equal)
    (children : ReflectsBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program stages)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (uninitializedReason : ∀ location, faults (.semantic (.uninitializedLocation location)) head.invalidProjection)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store} {size : Nat}
    (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore)
    (bounded : size ≤ budget) :
    ResultAt (attachment := attachment) bridge (functions := functions) (registry := registry) size context stages
      invocation faults scope (head.plainSlotTypes ++ actualContext) assignment operator rhs environment canonical
      actual before store mapping world initial (next.rename ξ) output value finalStore := by
  subst plain
  -- The Source types: the target's and the right side's are one, and the index is typed at its node's.
  have rhsTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨targetTyped, sameType⟩ : SourcePlaceHasType invocation.source context assignment.target head.node.type ∧
      assignment.target.type = head.node.type := by
    cases assignmentTyped with
    | equal targetTyped rhsTyped' _ =>
      have same := CellAwareArraySourceInversion.typed_type unique head.found rhsTyped'
      subst same
      exact ⟨targetTyped, targetTyped.type_eq⟩
    | wordCompound kind _ _ _ => cases kind
    | fixedCompound kind _ _ _ => cases kind
    | shiftCompound kind _ _ _ _ _ => cases kind
  obtain ⟨_, _, indexTyped⟩ := Staging.Recursive.SelectedPreservation.element_place_typed (leading := [])
    (index := head.key) targetTyped head.single
  have keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type :=
    CellAwareArraySourceInversion.typed_type unique head.keyFound indexTyped ▸ indexTyped
  have sameRuntime : SourceCoreRawMetadata.runtimeType assignment.target.type =
      SourceCoreRawMetadata.runtimeType head.node.type := by rw [sameType]
  -- The root's Source cell, the writable local's, and its Core cell at the actual slot's reference.
  obtain ⟨location, cell, lookup, read, cellType, absent⟩ := writable_root locals admitted.heap head.writable
  obtain ⟨target, coreValue, reference, coreRead, represented⟩ :=
    CellAwareElementWriteRoots.cell_at environments heaps agrees head.slotEq lookup read absent
  -- The code's run, split at its steps.
  have modifierNone : head.modifier = none := by simp [Head.modifier, CompatibleElementWrites.modifierOf]
  simp only [Head.emit] at completed
  rw [CompatibleElementWrites.code_rename, modifierNone] at completed
  have split := CompatibleElementWrites.plain_split reference completed
  clear completed
  cases represented with
  | @uninitialized sourceType _ _ =>
    -- The root's Core check fails first: the Source's target faults by `elementUninitialized`.
    have sourceArray : sourceType = TypeSystem.Ty.array assignment.target.type := cellType
    have notMapping : ¬ ∃ keyType valueType, sourceType = TypeSystem.Ty.mapping keyType valueType := by
      rintro ⟨_, _, same⟩
      rw [sourceArray] at same
      simp [TypeSystem.Ty.array] at same
    cases split with
    | empty _ =>
      exact .uninitialized
        (.elementUninitialized (leading := []) (index := head.key) head.single
          (.elementRoot rfl lookup read (.uninitialized notMapping)) rfl)
        rfl (uninitializedReason location) heaps (.refl _) (.refl _) (.refl mapping store) (.refl _)
        (.refl mapping world before store) initial (callerProtocol.refl _) admitted.rows
    | indexFailure full _ _ => cases coreRead.symm.trans full
    | outOfBounds full _ _ _ => cases coreRead.symm.trans full
    | inBounds full _ _ _ _ _ => cases coreRead.symm.trans full
  | @initialized sourceType _ source native rootRep =>
    -- The root holds a reference to its array, whose Core cell its Core cell holds.
    have sourceArray : sourceType = TypeSystem.Ty.array assignment.target.type := cellType
    subst sourceArray
    obtain ⟨element, arrayLocation, rfl⟩ := array_source rootRep (element := assignment.target.type) rfl
    obtain ⟨arrayTarget, payload, identity, rfl, typeEq, mapped, typed, _⟩ := arrayRef_fields rootRep rfl
    simp only [Core.Ty.cell.injEq, Core.Ty.product.injEq, Core.Ty.namedData.injEq, true_and] at typeEq
    obtain ⟨rfl, rfl⟩ := typeEq
    have referenceBefore : Dynamic.ValueHasType context before (.arrayRef element arrayLocation)
        (TypeSystem.Ty.array assignment.target.type) := by
      have cellTyped : Dynamic.OptionalValueHasType context before (some (.arrayRef element arrayLocation))
          (TypeSystem.Ty.array assignment.target.type) := (admitted.heap _ read.member).value
      cases cellTyped with
      | some typed => exact typed
    have rootPayload := fun {futureMap : LocationMap} {futureWorld : StoreTyping}
        (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld) =>
      (payloadModel compiled.compatible.checked registry functions).extend rootRep maps worlds
    -- The index's Source run from its Core run, under the array's binder.
    have reflectKey := fun {indexSize : Nat} {indexValue : Value} {indexStore : Store}
        (indexed : EvaluationSize indexSize
          (.cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
          store (shift 1 (head.keyCode.expression.rename ξ)) indexValue indexStore)
        (indexBound : indexSize < size) =>
      children _ (Nat.lt_of_lt_of_le indexBound bounded) head.keyChild head.keyFound keyTyped environments heaps
        locals (agree_prefix agrees _) (.cons (.cellRef typed) actualTyped) initial admitted authority physical
        owner ownerFrame (by rw [rename_prefix]; exact indexed)
    cases split with
    | empty empty => cases coreRead.symm.trans empty
    | indexFailure full indexed indexBound =>
      -- The index's fault, after the root's check.
      cases coreRead.symm.trans full
      obtain ⟨_, _, _, _, _, keyTrace, keyRep, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, keyEffect,
          keyReached, keyRelated, keyPost⟩ := reflectKey indexed indexBound
      cases keyRep with
      | fault matched =>
        exact .indexFault (.elementIndexFault (leading := []) (index := head.key) head.single
            (.elementRoot rfl lookup read .initialized) keyTrace)
          rfl matched keyHeaps keyMaps keyWorlds keyFrame keyMetadata keyEffect keyReached keyRelated keyPost.rows
    | outOfBounds full indexed indexBound checked =>
      -- `0x32`: the index's word is not below the array's length on either side.
      cases coreRead.symm.trans full
      obtain ⟨_, _, _, _, _, keyTrace, keyRep, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, keyEffect,
          keyReached, keyRelated, keyPost⟩ := reflectKey indexed indexBound
      cases keyRep with
      | value indexPayload =>
        rw [head.keyType] at indexPayload
        obtain ⟨position, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields indexPayload
        obtain ⟨_, counted⟩ := CellAwareArrayReads.length_cases keyHeaps rfl (rootPayload keyMaps keyWorlds) rfl
          (referenceBefore.mono keyMetadata)
        cases counted with
        | @array _ _ arrayCell elements arrayRead stored =>
        obtain ⟨measured, small⟩ := CellAwareArrayReads.length_preserve keyHeaps (.array arrayRead stored)
          (rootPayload keyMaps keyWorlds) rfl
        cases measured with
        | array lengthRead =>
        obtain ⟨flag, rfl⟩ := CompatibleElementWrites.check_cases lengthRead checked
        have beyond : elements.length ≤ position.val := by
          have outside : ¬ position < Word.ofNatModulo elements.length := fun within => by simp [within] at flag
          rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small] at outside
          omega
        exact .outOfBounds (.elementOutOfBounds (leading := []) (index := head.key) head.single
            (.elementRoot rfl lookup read .initialized) rfl keyTrace arrayRead stored beyond)
          rfl (RecursiveStageMeaning.FaultTokens.panic _) keyHeaps keyMaps keyWorlds keyFrame keyMetadata keyEffect
          keyReached keyRelated keyPost.rows
    | @inBounds _ _ _ _ _ _ _ indexStore checkStore _ full indexed indexBound checked stored storeBound =>
      -- Below the length: the target resolves through the array's cell, then the element's store runs.
      cases coreRead.symm.trans full
      obtain ⟨_, _, _, _, _, keyTrace, keyRep, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, keyEffect,
          keyReached, keyRelated, keyPost⟩ := reflectKey indexed indexBound
      cases keyRep with
      | value indexPayload =>
        rw [head.keyType] at indexPayload
        obtain ⟨position, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields indexPayload
        obtain ⟨_, counted⟩ := CellAwareArrayReads.length_cases keyHeaps rfl (rootPayload keyMaps keyWorlds) rfl
          (referenceBefore.mono keyMetadata)
        cases counted with
        | @array _ _ arrayCell elements arrayRead arrayStored =>
        obtain ⟨measured, small⟩ := CellAwareArrayReads.length_preserve keyHeaps (.array arrayRead arrayStored)
          (rootPayload keyMaps keyWorlds) rfl
        cases measured with
        | array lengthRead =>
        obtain ⟨flag, sameStore⟩ := CompatibleElementWrites.check_cases lengthRead checked
        subst checkStore
        have within : position.val < elements.length := by
          have below : position < Word.ofNatModulo elements.length := of_decide_eq_true flag.symm
          rwa [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small] at below
        obtain ⟨selected, selection⟩ := valueAt_exists within
        have arrayInitial :=
          array_initial keyHeaps arrayRead arrayStored (keyMaps.lookup mapped) (keyWorlds.lookup typed)
        have resolved := Staging.Recursive.Size.ElementTarget.elementStep (leading := []) (index := head.key)
          head.single (.elementRoot rfl lookup read .initialized) rfl keyTrace arrayRead arrayInitial selection
        -- The right side's Source run from its Core run, under the index's and the array's binders.
        have reflectRhs := fun {rhsSize : Nat} {rhsValue : Value} {rhsStore : Store}
            (evaluated : EvaluationSize rhsSize (.word position ::
                .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
              indexStore (shift 2 (head.lowered.expression.rename ξ)) rhsValue rhsStore)
            (rhsBound : rhsSize < size) =>
          children _ (Nat.lt_of_lt_of_le rhsBound bounded) head.right head.found rhsTyped
            (environments.extend keyMaps keyWorlds) keyHeaps (locals.mono keyMetadata)
            (agree_prefix (agree_prefix agrees
              (.cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget))
              (.word position))
            (.cons .word (.cons (.cellRef (keyWorlds.lookup typed)) (actualTyped.weaken keyWorlds))) keyReached
            keyPost.at_value.2 (authority.transport keyEffect) (physical.transport keyEffect keyFrame) owner
            ownerFrame (by rw [rename_prefix, rename_prefix]; exact evaluated)
        cases CompatibleElementWrites.plain_store_split stored with
        | rhsFailure failed rhsBound =>
          -- The right side's fault, after the target.
          obtain ⟨_, _, _, _, _, rhsTrace, rhsRep, rhsHeaps, rhsMaps, rhsWorlds, rhsFrame, rhsMetadata, rhsEffect,
              rhsReached, rhsRelated, rhsPost⟩ := reflectRhs failed (by omega)
          cases rhsRep with
          | fault matched =>
            exact .rhsFault resolved rhsTrace rfl matched rhsHeaps (keyMaps.trans rhsMaps)
              (keyWorlds.trans rhsWorlds) (keyFrame.trans rhsFrame) (keyMetadata.trans rhsMetadata)
              (keyEffect.trans rhsEffect) rhsReached (callerProtocol.trans keyRelated rhsRelated) rhsPost.rows
        | @rhsValue _ coreStored _ _ _ rhsStore _ rhsEvaluated rhsBound tail tailBound =>
        -- The write: the right side's value, the array's cell taking it, and the continuation.
        obtain ⟨_, _, _, rhsMap, _, rhsTrace, rhsRep, rhsHeaps, rhsMaps, rhsWorlds, rhsFrame, rhsMetadata,
            rhsEffect, rhsReached, rhsRelated, rhsPost⟩ := reflectRhs rhsEvaluated (by omega)
        cases rhsRep with
        | @value right _ storedPayload =>
        rw [head.rightType] at storedPayload
        -- The array keeps its length while the right side runs, so the index is still below it.
        have preserved := Staging.Recursive.SelectedPreservation.expression selectedBodies runtime covers
          (locals.mono keyMetadata) keyPost.at_value.2.heap rhsTyped rhsTrace
        obtain ⟨kept, current, keptRead, keptStored, keptLength⟩ :=
          preserved.lengths right rfl arrayLocation arrayCell element elements arrayRead arrayStored
        have referenceMiddle := referenceBefore.mono (keyMetadata.trans rhsMetadata)
        obtain ⟨sameElement, _⟩ := object_element referenceMiddle rhsPost.at_value.2.heap keptRead keptStored
        subst sameElement
        have below : position.val < current.length := by rw [keptLength]; exact within
        -- The Source's write: the element at the index takes the right side's value.
        obtain ⟨present, presentAt⟩ := valueAt_exists below
        obtain ⟨replaced, replace⟩ := CellAwareInvocationArrayBounds.replace_exists right below
        obtain ⟨after, heapWrite⟩ :=
          CompatibleExpressionReadCompletion.writes_exists keptRead (.arrayObject assignment.target.type replaced)
        obtain ⟨keptCell, keptRead', keptType, _⟩ := rhsMetadata arrayLocation arrayCell arrayRead
        cases keptRead.functional keptRead'
        have keptInitial := array_initial rhsHeaps keptRead keptStored (rhsMaps.lookup (keyMaps.lookup mapped))
          (rhsWorlds.lookup (keyWorlds.lookup typed))
        -- The Core write: the array's cell takes the right side's value's entry at the index.
        obtain ⟨length, default, entries, suffix, futureWorld, storeRead, wordKeys, appended, finalHeaps,
            futureWorlds, storeFrame, storeEffect⟩ :=
          CellAwareArrayReads.store_preserve_at head.prepared rhsHeaps
            (stack := coreStored :: .word position ::
              .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
            (context := head.elementType :: .word :: head.rootType :: actualContext)
            (.cons storedPayload.runtime_hasType (.cons .word
              (.cons (.cellRef (rhsWorlds.lookup (keyWorlds.lookup typed)))
                (actualTyped.weaken (keyWorlds.trans rhsWorlds)))))
            keptRead keptStored replace heapWrite (rhsMaps.lookup (keyMaps.lookup mapped))
            (rhsWorlds.lookup (keyWorlds.lookup typed)) storedPayload sameRuntime
            (arrayExpr := .var 2) (keyExpr := .var 1) (fun read => .loadCell (.var rfl) read) (.var rfl)
            (fun _ => .var rfl) (.var rfl) rfl rfl
        -- The rest of the code: the insert, the store and the continuation's run.
        obtain ⟨remainingSize, remainingBound, remaining⟩ :=
          CompatibleElementWrites.plain_tail_split (layout := head.layout) head.prepared rfl storeRead wordKeys tail
        have appended' : CompatibleMappingComparison.insertStore head.comparison head.layout
            (coreStored :: .word position ::
              .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
            rhsStore entries (.word position) coreStored = rhsStore ++ suffix := appended
        rw [appended'] at remaining
        -- The array's Core cell after the write, at its world's type.
        have finalBound : arrayTarget < (rhsStore ++ suffix).length := by
          rw [List.length_append]
          exact Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp storeRead).1 (Nat.le_add_right _ _)
        obtain ⟨_, cellRead, cellTyped⟩ := finalHeaps.runtime_hasTypes.lookup
          (futureWorlds.lookup (rhsWorlds.lookup (keyWorlds.lookup typed)))
        have newRead := List.getElem?_set_self (a := Core.Value.pair (.word length) (.pair default
          (OrderedMapping.encode head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position)
            coreStored entries)))) finalBound
        have cellEq := Option.some.inj (cellRead.symm.trans newRead)
        subst cellEq
        cases cellTyped with
        | pair _ inner =>
        cases inner with
        | pair _ encodeTyped =>
        -- The caller's pool after the write.
        let suffixPool : State headers keys ⟨scope, rhsMap, futureWorld, after, _, canonical⟩ :=
          (bridge.pool rhsReached).extend (.refl _) futureWorlds storeFrame (.of_write heapWrite)
        obtain ⟨returned, _, returnedRelated⟩ := bridge.restore rhsReached suffixPool (.refl _) futureWorlds
          storeFrame (.of_write heapWrite) (Relates.of_records_eq rfl)
        exact .success resolved rhsTrace
          (.intro keptRead keptType keptInitial (.element presentAt (.leaf (.primitive
            (Dynamic.CompoundAssignmentApplies.plain_of_profile (.inl rfl)) (.equal _ right))) replace) heapWrite)
          finalHeaps (keyMaps.trans rhsMaps) ((keyWorlds.trans rhsWorlds).trans futureWorlds)
          ((keyFrame.trans rhsFrame).trans storeFrame) ((keyMetadata.trans rhsMetadata).trans (.of_write heapWrite))
          ((keyEffect.trans rhsEffect).trans storeEffect)
          (slots := [.unit, OrderedMapping.encode head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual
              (.word position) coreStored entries), coreStored, .word position,
            .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget]) rfl
          (.cons .unit (.cons encodeTyped (.cons (storedPayload.runtime_hasType.weaken futureWorlds) (.cons .word
            (.cons (.cellRef (futureWorlds.lookup (rhsWorlds.lookup (keyWorlds.lookup typed))))
              (actualTyped.weaken ((keyWorlds.trans rhsWorlds).trans futureWorlds)))))))
          returned (callerProtocol.trans (callerProtocol.trans keyRelated rhsRelated) returnedRelated)
          ⟨referenceMiddle.arrayElementWrite rhsPost.at_value.2.heap keptRead keptStored replace
              (sameType ▸ rhsPost.at_value.1) heapWrite,
            StableRows.after_administrative (bridge.pool initial) (bridge.pool returned) admitted.rows
              ((keyFrame.trans rhsFrame).trans storeFrame)⟩
          (by omega) remaining

end Heads

end Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteHeads

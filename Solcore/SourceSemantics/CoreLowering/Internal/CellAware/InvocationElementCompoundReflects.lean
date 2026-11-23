import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementCompound
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementReflects

/-!
# Cell-aware invocations: a compound write to an element, reflected

From an actual Core run of `a[i] op= v`'s code, the Source's staged run: the run split at the root's
check, the index and the bound (`CompatibleElementWrites.element_split`, for any modifier), then at the
lookup, the snapshot, the right side, `modified`, the insert, `guard` and the store
(`compound_store_split`, `compound_tail_split`, `compound_commit_split`); `guard`'s passing check gives the
write, and its failure the Source's panic. Main declarations: `CellAwareElementWriteHeads.CompoundResultAt`
and `reflects_compound_bounded`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ### The Core run of a compound write to an element, split

A sized run of the code `lowerElements` emits for `a[i] op= v`, at its steps: the root's check, the index, the
bound's check, then the element's store: the lookup at the index and the snapshot, the right side, `modified`,
the insert, `guard`'s check, the store and the continuation under the eight binders. These belong beside the
code's runs in `Compatible/ElementWrites.lean`. -/

namespace Solcore.SourceSemantics.CoreLowering.CompatibleElementWrites
open Core Frontend SourceCoreCompatibleDataPlaces CoreProof

/-- A write's code, with its binds unfolded up to the element's store, whatever its modifier. -/
theorem element_code (slot : Nat) (storedType outputType : Ty) (invalid : Word) (comparison value next : Expr)
    (modifier : Option ElementModifier) (layout : OrderedMapping.Layout) (index : Expr) :
    code slot storedType outputType invalid comparison value next modifier layout index =
      .caseE (.caseE (.loadCell (.var slot)) (.inLeft storedType (.word invalid)) (.inRight .word (.var 0)))
        (.inLeft outputType (.var 0))
        (.caseE (shift 1 index) (.inLeft outputType (.var 0))
          (.ifE (Expr.wordLt (.var 0) (.first (.loadCell (.var 1))))
            (elementStore outputType comparison value next modifier 1 layout)
            (.inLeft outputType (.word (SourceCorePanics.reason SourceCorePanics.outOfBounds))))) := rfl

/-- A sized run of a write's code whose root's cell is `location`, whatever its modifier, at its steps: the root
not yet initialized, the index's failure, `0x32` from the bound's check, and the element's store below the
length, each step's run below the code's. It generalizes `PlainRun`, whose store is the plain one (`none`). -/
inductive ElementRun (environment : Environment) (store : Store) (location : Location) (outputType : Ty)
    (invalid : Word) (comparison value next : Expr) (modifier : Option ElementModifier)
    (layout : OrderedMapping.Layout) (index : Expr) (size : Nat) : Value → Store → Prop where
  | empty {payloadType : Ty} {payload : Value}
      (empty : store.read? location = some (.inLeft payloadType payload)) :
      ElementRun environment store location outputType invalid comparison value next modifier layout index size
        (.inLeft outputType (.word invalid)) store
  | indexFailure {leftType indexType : Ty} {array payload : Value} {indexSize : Nat} {final : Store}
      (full : store.read? location = some (.inRight leftType array))
      (indexed : EvaluationSize indexSize (array :: environment) store (shift 1 index) (.inLeft indexType payload)
        final)
      (indexBound : indexSize < size) :
      ElementRun environment store location outputType invalid comparison value next modifier layout index size
        (.inLeft outputType payload) final
  | outOfBounds {leftType indexType : Ty} {array position : Value} {indexSize : Nat} {indexStore final : Store}
      (full : store.read? location = some (.inRight leftType array))
      (indexed : EvaluationSize indexSize (array :: environment) store (shift 1 index)
        (.inRight indexType position) indexStore)
      (indexBound : indexSize < size)
      (checked : Evaluates (position :: array :: environment) indexStore
        (Expr.wordLt (.var 0) (.first (.loadCell (.var 1)))) (.bool false) final) :
      ElementRun environment store location outputType invalid comparison value next modifier layout index size
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
        (elementStore outputType comparison value next modifier 1 layout) result final)
      (storeBound : storeSize < size) :
      ElementRun environment store location outputType invalid comparison value next modifier layout index size
        result final

/-- A sized run of a write's code, whatever its modifier, split at its steps (`ElementRun`). -/
theorem element_split {environment : Environment} {store final : Store} {slot : Nat}
    {storedType outputType cellType : Ty} {invalid : Word} {comparison value next index : Expr}
    {modifier : Option ElementModifier} {layout : OrderedMapping.Layout} {location : Location} {size : Nat}
    {result : Value}
    (reference : environment[slot]? = some (.cellRef cellType location))
    (evaluated : EvaluationSize size environment store
      (code slot storedType outputType invalid comparison value next modifier layout index) result final) :
    ElementRun environment store location outputType invalid comparison value next modifier layout index size result
      final := by
  rw [element_code] at evaluated
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

/-- A compound write's element store, with its binds unfolded: the lookup at the index, the snapshot, the right
side, `modified`, the insert, then `guard`'s check, the store and the continuation. -/
theorem compound_store (outputType : Ty) (comparison value next : Expr) (modifier : ElementModifier)
    (layout : OrderedMapping.Layout) :
    elementStore outputType comparison value next (some modifier) 1 layout =
      .caseE (OrderedMapping.lookup layout (shift 2 comparison) (.second (.second (.loadCell (.var 1)))) (.var 0))
        (.inLeft outputType (.var 0))
        (.caseE (.caseE (.var 0) (LanguageResult.success (.inRight .unit (.first (.second (.loadCell (.var 3))))))
            (LanguageResult.success (.inRight .unit (.var 0))))
          (.inLeft outputType (.var 0))
          (.caseE (shift 4 value) (.inLeft outputType (.var 0))
            (.caseE (modified modifier.leafType modifier.operator modifier.bitNot (.var 1) (.var 0)
                modifier.invalidOperand modifier.wrap)
              (.inLeft outputType (.var 0))
              (.caseE (OrderedMapping.insert layout (shift 6 comparison) (.second (.second (.loadCell (.var 5))))
                  (.var 4) (.var 0))
                (.inLeft outputType (.var 0))
                (SourceCoreDataPlaces.guard outputType modifier.operator
                  (.letE (.storeCell (.var 6) (.pair (.first (.loadCell (.var 6)))
                      (.pair (.first (.second (.loadCell (.var 6)))) (.var 0))))
                    (shift 8 next))))))) := rfl

/-- A sized run of a compound write's element store past the lookup and the snapshot, at the right side: its
failure, or its value and the rest of the code, `modified`, the insert, `guard`'s check, the store and the
continuation, each step's run below the store's. -/
inductive CompoundStore (environment : Environment) (store : Store) (outputType : Ty)
    (comparison value next : Expr) (modifier : ElementModifier) (layout : OrderedMapping.Layout) (size : Nat) :
    Value → Store → Prop where
  | rhsFailure {rightType : Ty} {payload : Value} {rhsSize : Nat} {final : Store}
      (failed : EvaluationSize rhsSize environment store (shift 4 value) (.inLeft rightType payload) final)
      (rhsBound : rhsSize < size) :
      CompoundStore environment store outputType comparison value next modifier layout size
        (.inLeft outputType payload) final
  | rhsValue {rightType : Ty} {right result : Value} {rhsSize tailSize : Nat} {rhsStore final : Store}
      (rhsEvaluated : EvaluationSize rhsSize environment store (shift 4 value) (.inRight rightType right) rhsStore)
      (rhsBound : rhsSize < size)
      (tail : EvaluationSize tailSize (right :: environment) rhsStore
        (.caseE (modified modifier.leafType modifier.operator modifier.bitNot (.var 1) (.var 0)
            modifier.invalidOperand modifier.wrap)
          (.inLeft outputType (.var 0))
          (.caseE (OrderedMapping.insert layout (shift 6 comparison) (.second (.second (.loadCell (.var 5))))
              (.var 4) (.var 0))
            (.inLeft outputType (.var 0))
            (SourceCoreDataPlaces.guard outputType modifier.operator
              (.letE (.storeCell (.var 6) (.pair (.first (.loadCell (.var 6)))
                  (.pair (.first (.second (.loadCell (.var 6)))) (.var 0))))
                (shift 8 next)))))
        result final)
      (tailBound : tailSize < size) :
      CompoundStore environment store outputType comparison value next modifier layout size result final

/-- A sized run of a compound write's element store, split at the right side (`CompoundStore`): the lookup and
the snapshot run as `lookedUp` and `snapshotted` do, since a run is deterministic. -/
theorem compound_store_split {checked : SourceCoreCompatibleCatalog.Checked}
    {comparison : SourceCoreCompatibleDataEquality.Prepared checked}
    {environment : Environment} {store lookupStore final : Store} {outputType : Ty} {value next : Expr}
    {modifier : ElementModifier} {layout : OrderedMapping.Layout} {size : Nat} {found snapshot result : Value}
    (lookedUp : Evaluates environment store
      (OrderedMapping.lookup layout comparison.expression (.second (.second (.loadCell (.var 1)))) (.var 0))
      (.inRight .word found) lookupStore)
    (snapshotted : Evaluates (found :: environment) lookupStore
      (.caseE (.var 0) (LanguageResult.success (.inRight .unit (.first (.second (.loadCell (.var 3))))))
        (LanguageResult.success (.inRight .unit (.var 0))))
      (.inRight .word snapshot) lookupStore)
    (evaluated : EvaluationSize size environment store
      (elementStore outputType comparison.expression value next (some modifier) 1 layout) result final) :
    CompoundStore (snapshot :: found :: environment) lookupStore outputType comparison.expression value next
      modifier layout size result final := by
  rw [compound_store, shift_closed comparison 2] at evaluated
  cases evaluated with
  | caseLeft lookupRun _ =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic lookupRun.sound lookedUp
    cases impossible
  | caseRight lookupRun body =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic lookupRun.sound lookedUp
    cases same
    cases body with
    | caseLeft snapshotRun _ =>
      obtain ⟨impossible, _⟩ := evaluation_deterministic snapshotRun.sound snapshotted
      cases impossible
    | caseRight snapshotRun rest =>
      obtain ⟨same, rfl⟩ := evaluation_deterministic snapshotRun.sound snapshotted
      cases same
      cases rest with
      | caseLeft rhsRun failed =>
        cases failed with
        | inLeft payloadRun =>
          cases payloadRun with
          | var found' =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found'
            subst found'
            exact .rhsFailure rhsRun (by omega)
      | caseRight rhsRun tail => exact .rhsValue rhsRun (by omega) tail (by omega)

private theorem write_set {store : Store} {location : Location} (bound : location < store.length) (value : Value) :
    store.write? location value = some (store.set location value) := by
  simp [Store.write?, bound]

/-- The insert appends only its Core-only cells: a cell the store holds reads the same after it. -/
theorem insertStore_read {checked : SourceCoreCompatibleCatalog.Checked}
    {comparison : SourceCoreCompatibleDataEquality.Prepared checked} {layout : OrderedMapping.Layout}
    {environment : Environment} {store : Store} {entries : OrderedMapping.Entries} {key stored : Value}
    {location : Location} {value : Value} (read : store.read? location = some value) :
    (CompatibleMappingComparison.insertStore comparison layout environment store entries key stored).read?
      location = some value := by
  have bound : location < store.length := (List.getElem?_eq_some_iff.mp read).1
  simp only [CompatibleMappingComparison.insertStore, OrderedMapping.installedStore, WordMapping.installedStore,
    CompatibleMappingComparison.comparisonStore, Store.read?, List.append_assoc] at read ⊢
  rw [List.getElem?_append_left bound]
  exact read

/-- The rest of a compound write's code after the right side's value: `modified` runs as `modifiedEvaluated`
does, since a run is deterministic, then the insert of its leaf's entry at the index into the array's cell's
entries, and `guard`'s check runs under the seven binders, below the rest's size. The modifier's fields are
separate, so that its leaf type may be given as the element's on either side. -/
theorem compound_tail_split {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
    {comparison : SourceCoreCompatibleDataEquality.Prepared checked}
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
    {layout : OrderedMapping.Layout} (keyType : layout.keyType = .word)
    {environment : Environment} {outputType elementType leafType : Ty} {arrayLocation : Location}
    {position : Word} {operator : Option SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalidOperand : Word}
    {wrap : Option TypeSystem.FixedInteger} {found snapshot right changed length default result : Value}
    {entries : OrderedMapping.Entries} {next : Expr} {tailSize : Nat} {rhsStore modifiedStore final : Store}
    (modifiedEvaluated : Evaluates
      (right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment) rhsStore
      (modified leafType operator bitNot (.var 1) (.var 0) invalidOperand wrap) (.inRight .word changed)
      modifiedStore)
    (current : modifiedStore.read? arrayLocation =
      some (.pair length (.pair default (OrderedMapping.encode layout entries))))
    (wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word)
    (tail : EvaluationSize tailSize
      (right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment) rhsStore
      (.caseE (modified leafType operator bitNot (.var 1) (.var 0) invalidOperand wrap)
        (.inLeft outputType (.var 0))
        (.caseE (OrderedMapping.insert layout (shift 6 comparison.expression) (.second (.second (.loadCell (.var 5))))
            (.var 4) (.var 0))
          (.inLeft outputType (.var 0))
          (SourceCoreDataPlaces.guard outputType operator
            (.letE (.storeCell (.var 6) (.pair (.first (.loadCell (.var 6)))
                (.pair (.first (.second (.loadCell (.var 6)))) (.var 0))))
              (shift 8 next)))))
      result final) :
    ∃ guardSize, guardSize < tailSize ∧
      EvaluationSize guardSize
        (OrderedMapping.encode layout
            (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) changed entries) ::
          changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation ::
            environment)
        (CompatibleMappingComparison.insertStore comparison layout
          (changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation ::
            environment)
          modifiedStore entries (.word position) changed)
        (SourceCoreDataPlaces.guard outputType operator
          (.letE (.storeCell (.var 6) (.pair (.first (.loadCell (.var 6)))
              (.pair (.first (.second (.loadCell (.var 6)))) (.var 0))))
            (shift 8 next)))
        result final := by
  rw [shift_closed comparison] at tail
  let stack :=
    changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation :: environment
  have inserted := OrderedMapping.insert_evaluates (environment := stack)
    (mapping := .second (.second (.loadCell (.var 5)))) (keyExpr := .var 4) (valueExpr := .var 0)
    (keyEqual := comparison.expression) entries (.word position) changed
    (CompatibleMappingComparison.comparator comparison stack modifiedStore) GenericHeap.arrayKeyEqual
    (.second (.second (.loadCell (.var rfl) current))) (.var rfl) (.var rfl)
    (CompatibleEquality.prepared_evaluates_exact comparison stack modifiedStore)
    (CompatibleArrayEvaluation.word_comparisons prepared keyType stack modifiedStore wordKeys position _)
  cases tail with
  | caseLeft modifiedRun _ =>
    obtain ⟨impossible, _⟩ := evaluation_deterministic modifiedRun.sound modifiedEvaluated
    cases impossible
  | caseRight modifiedRun body =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic modifiedRun.sound modifiedEvaluated
    cases same
    cases body with
    | caseLeft insertRun _ =>
      obtain ⟨impossible, _⟩ := evaluation_deterministic insertRun.sound inserted
      cases impossible
    | caseRight insertRun guarded =>
      obtain ⟨same, rfl⟩ := evaluation_deterministic insertRun.sound inserted
      cases same
      exact ⟨_, by omega, guarded⟩

/-- `guard`'s passing check, then the array's cell takes the updated entries, keeping its length and default
element, and the continuation runs under the eight binders, below the check's size. -/
theorem compound_commit_split {environment : Environment} {store final : Store} {outputType elementType : Ty}
    {operator : Option SourceCoreDataPlaces.Modifier} {arrayLocation : Location} {position : Word}
    {updated changed right snapshot found length default mapping result : Value} {next : Expr} {size : Nat}
    (passing : FixedCompoundModifier.CheckPasses operator snapshot right)
    (current : store.read? arrayLocation = some (.pair length (.pair default mapping)))
    (guarded : EvaluationSize size
      (updated :: changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation ::
        environment) store
      (SourceCoreDataPlaces.guard outputType operator
        (.letE (.storeCell (.var 6) (.pair (.first (.loadCell (.var 6)))
            (.pair (.first (.second (.loadCell (.var 6)))) (.var 0))))
          (shift 8 next)))
      result final) :
    ∃ remainingSize, remainingSize < size ∧
      EvaluationSize remainingSize
        (.unit :: updated :: changed :: right :: snapshot :: found :: .word position ::
          .cellRef elementType arrayLocation :: environment)
        (store.set arrayLocation (.pair length (.pair default updated))) (shift 8 next) result final := by
  obtain ⟨child, childBound, written⟩ := DataPlaceGuard.passes_sized passing guarded
  have bound : arrayLocation < store.length := (List.getElem?_eq_some_iff.mp current).1
  have storedCell : Evaluates
      (updated :: changed :: right :: snapshot :: found :: .word position :: .cellRef elementType arrayLocation ::
        environment) store
      (.storeCell (.var 6) (.pair (.first (.loadCell (.var 6))) (.pair (.first (.second (.loadCell (.var 6))))
        (.var 0)))) .unit (store.set arrayLocation (.pair length (.pair default updated))) :=
    .storeCell (.var rfl) current
      (.pair (.first (.loadCell (.var rfl) current)) (.pair (.first (.second (.loadCell (.var rfl) current)))
        (.var rfl)))
      (write_set bound _)
  cases written with
  | letE storeRun remaining =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic storeRun.sound storedCell
    cases same
    exact ⟨_, by omega, remaining⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleElementWrites

/-! ### The reflect head of a compound write to an element -/

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

end Head

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

/-- What a sized Core run of a compound write to one element of a local array reflects, as a plain write's
`ResultAt` does: the Source's element target faulting at a root not yet initialized (`elementUninitialized`, as
the Core's root check fails first), at the index's fault or at `0x32`, the right side's fault after the target;
the write's fault after the right side, at the operation's panic, which `guard`'s check fails with; or the write,
with the eight binders and the continuation's run below the code's. -/
inductive CompoundResultAt (size : Nat) (context : SourceSemantics.Context) (stages : Staging.Recursive.Registry)
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
      CompoundResultAt size context stages invocation faults scope writtenContext assignment operator rhs environment
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
      CompoundResultAt size context stages invocation faults scope writtenContext assignment operator rhs environment
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
      CompoundResultAt size context stages invocation faults scope writtenContext assignment operator rhs environment
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
      CompoundResultAt size context stages invocation faults scope writtenContext assignment operator rhs environment
        canonical actual before store mapping world initial next output value finalStore
  | writeFault {targetSize sourceSize : Nat} {target : Dynamic.ResolvedPlace} {targetHeap : Dynamic.Heap}
      {right : Dynamic.Value} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (resolved : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment
        before assignment.target (.resolved target) targetHeap)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap
        rhs (.value right) after)
      (failed : Staging.Recursive.ProjectedTarget.WriteFault operator target right after reason)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic reason) token)
      (heaps : GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore)
      (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after
        finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      CompoundResultAt size context stages invocation faults scope writtenContext assignment operator rhs environment
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
      (count : slots.length = 8)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext
        compiled.indexed.layouts.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 8 next) value finalStore) :
      CompoundResultAt size context stages invocation faults scope writtenContext assignment operator rhs environment
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

local notation "acceptedInstances" => GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique
  assignmentTyped observations in
/-- A compound write to one element of a local array, `a[i] op= v`, reflected from the sized Core run of its
code: the root's Source cell, the writable local's, and its Core cell; the index's Source run from its Core run;
the lookup at the index, whose snapshot represents the Source's element there; the right side's Source run from
its Core run below the code's size, at the reached callers; then `modified`'s leaf and `guard`'s check, which
pass as the Source's operation applies (`CompoundAssignmentApplies`) or fail with the reason of its panic
(`AssignmentOperandsPanic`), as `CompatiblePlaceModifier.assigned_outcome` relates them. Represented operands are
never invalid, and no structural fault is at an element. The array keeps its length while the right side runs
(`KeepsLengths`), so the Source's write applies at the position the bound's check admitted. A root not yet
initialized is `elementUninitialized`, at the site's reason, as the Core's root check fails before the index. -/
theorem reflects_compound_bounded [RecursiveStageMeaning.FaultTokens faults] (budget : Nat)
    (compound : operator ≠ .equal)
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
    CompoundResultAt (attachment := attachment) bridge (functions := functions) (registry := registry) size context
      stages invocation faults scope (head.compoundSlotTypes ++ actualContext) assignment operator rhs environment
      canonical actual before store mapping world initial (next.rename ξ) output value finalStore := by
  -- The Source types: the right side's at its node's, and the index's at its node's.
  have rhsTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨_, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨_, _, indexTyped⟩ := Staging.Recursive.SelectedPreservation.element_place_typed (leading := [])
    (index := head.key) targetTyped head.single
  have keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type :=
    CellAwareArraySourceInversion.typed_type unique head.keyFound indexTyped ▸ indexTyped
  -- The root's Source cell, the writable local's, and its Core cell at the actual slot's reference.
  obtain ⟨location, cell, lookup, read, cellType, absent⟩ := writable_root locals admitted.heap head.writable
  obtain ⟨target, coreValue, reference, coreRead, represented⟩ :=
    CellAwareElementWriteRoots.cell_at environments heaps agrees head.slotEq lookup read absent
  -- The code's run, split at its steps.
  simp only [Head.emit] at completed
  rw [CompatibleElementWrites.code_rename, Head.modifier_compound head compound] at completed
  have split := CompatibleElementWrites.element_split reference completed
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
      obtain ⟨_, _, targetHeap, keyMap, keyWorld, keyTrace, keyRep, keyHeaps, keyMaps, keyWorlds, keyFrame,
          keyMetadata, keyEffect, keyReached, keyRelated, keyPost⟩ := reflectKey indexed indexBound
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
        -- The lookup at the index: the entry present there or the array's default, which represents the
        -- Source's element; it appends only its Core-only cells.
        obtain ⟨_, _, lookupWorld, suffix, coreReads, elementRep, lookupHeaps, lookupWorlds, lookupFrame,
            lookupAppend⟩ :=
          CellAwareArrayReads.reads_preserve head.prepared (layout := head.layout) keyHeaps
            (actualTyped.weaken keyWorlds) (.array arrayRead arrayStored selection.getElem?_eq)
            (rootPayload keyMaps keyWorlds) rfl (.array assignment.target.type) rfl position.isLt
        rw [CellAwareArrayReads.ofNatModulo_self] at coreReads
        cases coreReads with
        | @array _ _ _ _ default entries arrayCoreRead _ wordKeys =>
        have lookedUp := CellAwareArrayReads.lookup_evaluates head.prepared (layout := head.layout) rfl
          (environment := actual) (type := .product .word (.product head.elementType (.namedData head.identity)))
          (position := position) arrayCoreRead wordKeys
        have lookupRead := CompatibleArrayEvaluation.lookupStore_read (comparison := head.comparison)
          (layout := head.layout)
          (environment := .word position ::
            .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
          (entries := entries) (key := .word position) arrayCoreRead
        generalize OrderedMapping.lookupEntries GenericHeap.arrayKeyEqual (.word position) entries = present
          at lookedUp elementRep
        generalize CompatibleMappingComparison.lookupStore head.comparison head.layout
            (.word position :: .cellRef (.product .word (.product head.elementType (.namedData head.identity)))
              arrayTarget :: actual) indexStore entries (.word position) = lookupStore
          at lookedUp lookupRead lookupHeaps lookupFrame lookupAppend
        have snapshotted := CompatibleElementWrites.snapshot_evaluates (environment := actual)
          (elementType := .product .word (.product head.elementType (.namedData head.identity)))
          (valueType := head.layout.valueType) (position := position) present lookupRead
        have snapshotRep := elementRep.extend (.refl _) (.refl _) lookupWorlds
        have foundTyped := CompatibleElementWrites.optionValue_typed snapshotRep.runtime_hasType
        have lookupEffect : CellAwareScopeAuthority.Effect acceptedInstances keyMap keyWorld targetHeap indexStore
            keyMap lookupWorld targetHeap lookupStore := by
          rw [lookupAppend]
          exact CellAwareScopeAuthority.Effect.append indexStore suffix (.refl _) (.refl keyMap) lookupWorlds
        -- The caller's pool after the lookup's Core-only cells.
        let lookupPool : State headers keys ⟨scope, keyMap, lookupWorld, targetHeap, lookupStore, canonical⟩ :=
          (bridge.pool keyReached).extend (.refl _) lookupWorlds lookupFrame (.refl _)
        obtain ⟨lookupReached, _, lookupRelated⟩ := bridge.restore keyReached lookupPool (.refl _) lookupWorlds
          lookupFrame (.refl _) (Relates.of_records_eq rfl)
        have lookupAdmitted : Admission bridge context lookupReached :=
          ⟨keyPost.at_value.2.heap, StableRows.after_administrative (bridge.pool initial) (bridge.pool lookupReached)
            admitted.rows (keyFrame.trans lookupFrame)⟩
        -- The right side's Source run from its Core run, under the snapshot's, the option's, the index's and the
        -- array's binders.
        have reflectRhs := fun {rhsSize : Nat} {rhsValue : Value} {rhsStore : Store}
            (evaluated : EvaluationSize rhsSize (.inRight .unit (present.getD default) ::
                OrderedMapping.optionValue head.layout.valueType present :: .word position ::
                .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
              lookupStore (shift 4 (head.lowered.expression.rename ξ)) rhsValue rhsStore)
            (rhsBound : rhsSize < size) =>
          children _ (Nat.lt_of_lt_of_le rhsBound bounded) head.right head.found rhsTyped
            (environments.extend keyMaps (keyWorlds.trans lookupWorlds)) lookupHeaps (locals.mono keyMetadata)
            (agree_prefix (agree_prefix (agree_prefix (agree_prefix agrees
              (.cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget))
              (.word position)) (OrderedMapping.optionValue head.layout.valueType present))
              (.inRight .unit (present.getD default)))
            (.cons (.inRight snapshotRep.runtime_hasType) (.cons foundTyped (.cons .word
              (.cons (.cellRef (lookupWorlds.lookup (keyWorlds.lookup typed)))
                (actualTyped.weaken (keyWorlds.trans lookupWorlds))))))
            lookupReached lookupAdmitted (authority.transport (keyEffect.trans lookupEffect))
            (physical.transport (keyEffect.trans lookupEffect) (keyFrame.trans lookupFrame)) owner ownerFrame
            (by rw [rename_prefix, rename_prefix, rename_prefix, rename_prefix]; exact evaluated)
        cases CompatibleElementWrites.compound_store_split lookedUp snapshotted stored with
        | rhsFailure failed rhsBound =>
          -- The right side's fault, after the target.
          obtain ⟨_, _, _, _, _, rhsTrace, rhsRep, rhsHeaps, rhsMaps, rhsWorlds, rhsFrame, rhsMetadata, rhsEffect,
              rhsReached, rhsRelated, rhsPost⟩ := reflectRhs failed (by omega)
          cases rhsRep with
          | fault matched =>
            exact .rhsFault resolved rhsTrace rfl matched rhsHeaps (keyMaps.trans rhsMaps)
              ((keyWorlds.trans lookupWorlds).trans rhsWorlds) ((keyFrame.trans lookupFrame).trans rhsFrame)
              (keyMetadata.trans rhsMetadata) ((keyEffect.trans lookupEffect).trans rhsEffect) rhsReached
              (callerProtocol.trans (callerProtocol.trans keyRelated lookupRelated) rhsRelated) rhsPost.rows
        | @rhsValue _ coreRight _ _ _ rhsStore _ rhsEvaluated rhsBound tail tailBound =>
        -- The right side's value, then `modified`, the insert and `guard`'s check.
        obtain ⟨_, _, middle, rhsMap, _, rhsTrace, rhsRep, rhsHeaps, rhsMaps, rhsWorlds, rhsFrame, rhsMetadata,
            rhsEffect, rhsReached, rhsRelated, rhsPost⟩ := reflectRhs rhsEvaluated (by omega)
        cases rhsRep with
        | @value right _ rightPayload =>
        rw [head.rightType] at rightPayload
        -- The array keeps its length while the right side runs, so the index is still below it.
        have preserved := Staging.Recursive.SelectedPreservation.expression selectedBodies runtime covers
          (locals.mono keyMetadata) keyPost.at_value.2.heap rhsTyped rhsTrace
        obtain ⟨kept, current, keptRead, keptStored, keptLength⟩ :=
          preserved.lengths right rfl arrayLocation arrayCell element elements arrayRead arrayStored
        have referenceMiddle := referenceBefore.mono (keyMetadata.trans rhsMetadata)
        obtain ⟨sameElement, _⟩ := object_element referenceMiddle rhsPost.at_value.2.heap keptRead keptStored
        subst sameElement
        have below : position.val < current.length := by rw [keptLength]; exact within
        obtain ⟨currentElement, currentAt⟩ := valueAt_exists below
        obtain ⟨keptCell, keptRead', keptType, _⟩ := rhsMetadata arrayLocation arrayCell arrayRead
        cases keptRead.functional keptRead'
        have keptInitial := array_initial rhsHeaps keptRead keptStored (rhsMaps.lookup (keyMaps.lookup mapped))
          (rhsWorlds.lookup (lookupWorlds.lookup (keyWorlds.lookup typed)))
        -- The Core modifier on the snapshot and the right side: the operation's leaf, or its panic.
        obtain ⟨replacement, changed, modifiedEvaluated, changedTyped, _, leafUnique, agreement⟩ :=
          CompatiblePlaceModifier.assigned_outcome observations head.profile rfl
            (snapshotRep.extend (.refl _) rhsMaps rhsWorlds) head.rightView rightPayload
            (environment := coreRight :: .inRight .unit (present.getD default) ::
              OrderedMapping.optionValue head.layout.valueType present :: .word position ::
              .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
            (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore head.invalid
        cases agreement (leftType := .unit) with
        | panicked code panics _ fails =>
          -- The insert at the array's latest Core cell, whose cells stay related, and `guard`'s check fails with
          -- the panic's reason: the Source's write faults by the operation's panic.
          obtain ⟨_, _, entries', suffix', futureWorld, storeRead, wordKeys', appended, finalHeaps, futureWorlds,
              storeFrame⟩ :=
            CellAwareArrayReads.insert_preserve_at head.prepared rhsHeaps
              (stack := changed :: coreRight :: .inRight .unit (present.getD default) ::
                OrderedMapping.optionValue head.layout.valueType present :: .word position ::
                .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget ::
                  actual)
              (context := head.elementType :: head.elementType :: .sum .unit head.elementType ::
                .sum .unit head.elementType :: .word :: head.rootType :: actualContext)
              (.cons changedTyped (.cons rightPayload.runtime_hasType
                (.cons (.inRight (snapshotRep.runtime_hasType.weaken rhsWorlds)) (.cons (foundTyped.weaken rhsWorlds)
                  (.cons .word (.cons (.cellRef (rhsWorlds.lookup (lookupWorlds.lookup (keyWorlds.lookup typed))))
                    (actualTyped.weaken ((keyWorlds.trans lookupWorlds).trans rhsWorlds))))))))
              keptRead keptStored (rhsMaps.lookup (keyMaps.lookup mapped))
              (rhsWorlds.lookup (lookupWorlds.lookup (keyWorlds.lookup typed)))
              (arrayExpr := .var 5) (keyExpr := .var 4) (position := position) (fun read => .loadCell (.var rfl) read)
              (.var rfl) (fun _ => .var rfl) (.var rfl) rfl rfl
          obtain ⟨_, _, guarded⟩ := CompatibleElementWrites.compound_tail_split (layout := head.layout)
            head.prepared rfl modifiedEvaluated storeRead wordKeys' tail
          obtain ⟨rfl, rfl⟩ := fails.mp guarded.sound
          have appended' : CompatibleMappingComparison.insertStore head.comparison head.layout
              (changed :: coreRight :: .inRight .unit (present.getD default) ::
                OrderedMapping.optionValue head.layout.valueType present :: .word position ::
                .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget ::
                  actual)
              rhsStore entries' (.word position) changed = rhsStore ++ suffix' := appended
          rw [appended']
          -- The caller's pool after the insert's Core-only cells.
          let insertPool : State headers keys ⟨scope, rhsMap, futureWorld, middle, rhsStore ++ suffix', canonical⟩ :=
            (bridge.pool rhsReached).extend (.refl _) futureWorlds storeFrame (.refl _)
          obtain ⟨returned, _, returnedRelated⟩ := bridge.restore rhsReached insertPool (.refl _) futureWorlds
            storeFrame (.refl _) (Relates.of_records_eq rfl)
          exact .writeFault resolved rhsTrace (.panic keptRead keptType keptInitial (.element currentAt .nil) panics)
            rfl (RecursiveStageMeaning.FaultTokens.panic _) finalHeaps (keyMaps.trans rhsMaps)
            (((keyWorlds.trans lookupWorlds).trans rhsWorlds).trans futureWorlds)
            (((keyFrame.trans lookupFrame).trans rhsFrame).trans storeFrame) (keyMetadata.trans rhsMetadata)
            (((keyEffect.trans lookupEffect).trans rhsEffect).trans
              (CellAwareScopeAuthority.Effect.append (instances := acceptedInstances) rhsStore suffix' (.refl _)
                (.refl rhsMap) futureWorlds))
            returned
            (callerProtocol.trans (callerProtocol.trans (callerProtocol.trans keyRelated lookupRelated) rhsRelated)
              returnedRelated)
            (StableRows.after_administrative (bridge.pool initial) (bridge.pool returned) admitted.rows
              (((keyFrame.trans lookupFrame).trans rhsFrame).trans storeFrame))
        | applied applies passing _ =>
          -- The Source's write: the element at the index takes the operation's leaf.
          obtain ⟨_, changedRep⟩ := leafUnique _ applies
          obtain ⟨replaced, replace⟩ := CellAwareInvocationArrayBounds.replace_exists replacement below
          obtain ⟨after, heapWrite⟩ :=
            CompatibleExpressionReadCompletion.writes_exists keptRead (.arrayObject assignment.target.type replaced)
          have selectedTyped : Dynamic.ValueHasType context targetHeap selected assignment.target.type :=
            Dynamic.ValueHasType.arrayElement (referenceBefore.mono keyMetadata) keyPost.at_value.2.heap arrayRead
              arrayStored selection.getElem?_eq
          have updatedTyped := compound_leaf_typed unique head.found assignmentTyped compound
            (selectedTyped.mono rhsMetadata) rhsPost.at_value.1 applies
          -- The Core write: the insert of the leaf's entry at the index, `guard`'s passing check, and the
          -- array's cell taking the updated entries.
          obtain ⟨length', default', entries', suffix', futureWorld, storeRead, wordKeys', appended, finalHeaps,
              futureWorlds, storeFrame, storeEffect⟩ :=
            CellAwareArrayReads.store_preserve_at head.prepared rhsHeaps
              (stack := changed :: coreRight :: .inRight .unit (present.getD default) ::
                OrderedMapping.optionValue head.layout.valueType present :: .word position ::
                .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget ::
                  actual)
              (context := head.elementType :: head.elementType :: .sum .unit head.elementType ::
                .sum .unit head.elementType :: .word :: head.rootType :: actualContext)
              (.cons changedRep.runtime_hasType (.cons rightPayload.runtime_hasType
                (.cons (.inRight (snapshotRep.runtime_hasType.weaken rhsWorlds)) (.cons (foundTyped.weaken rhsWorlds)
                  (.cons .word (.cons (.cellRef (rhsWorlds.lookup (lookupWorlds.lookup (keyWorlds.lookup typed))))
                    (actualTyped.weaken ((keyWorlds.trans lookupWorlds).trans rhsWorlds))))))))
              keptRead keptStored replace heapWrite (rhsMaps.lookup (keyMaps.lookup mapped))
              (rhsWorlds.lookup (lookupWorlds.lookup (keyWorlds.lookup typed))) changedRep rfl
              (arrayExpr := .var 5) (keyExpr := .var 4) (fun read => .loadCell (.var rfl) read) (.var rfl)
              (fun _ => .var rfl) (.var rfl) rfl rfl
          obtain ⟨_, _, guarded⟩ := CompatibleElementWrites.compound_tail_split (layout := head.layout)
            head.prepared rfl modifiedEvaluated storeRead wordKeys' tail
          obtain ⟨remainingSize, remainingBound, remaining⟩ := CompatibleElementWrites.compound_commit_split passing
            (CompatibleElementWrites.insertStore_read storeRead) guarded
          have appended' : CompatibleMappingComparison.insertStore head.comparison head.layout
              (changed :: coreRight :: .inRight .unit (present.getD default) ::
                OrderedMapping.optionValue head.layout.valueType present :: .word position ::
                .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget ::
                  actual)
              rhsStore entries' (.word position) changed = rhsStore ++ suffix' := appended
          rw [appended'] at remaining
          -- The array's Core cell after the write, at its world's type: the updated entries are of the layout's.
          have finalBound : arrayTarget < (rhsStore ++ suffix').length := by
            rw [List.length_append]
            exact Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp storeRead).1 (Nat.le_add_right _ _)
          obtain ⟨_, cellRead, cellTyped⟩ := finalHeaps.runtime_hasTypes.lookup
            (futureWorlds.lookup (rhsWorlds.lookup (lookupWorlds.lookup (keyWorlds.lookup typed))))
          have newRead := List.getElem?_set_self (a := Core.Value.pair (.word length') (.pair default'
            (OrderedMapping.encode head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual
              (.word position) changed entries')))) finalBound
          have cellEq := Option.some.inj (cellRead.symm.trans newRead)
          subst cellEq
          cases cellTyped with
          | pair _ inner =>
          cases inner with
          | pair _ encodeTyped =>
          -- The caller's pool after the write.
          let writePool : State headers keys ⟨scope, rhsMap, futureWorld, after, _, canonical⟩ :=
            (bridge.pool rhsReached).extend (.refl _) futureWorlds storeFrame (.of_write heapWrite)
          obtain ⟨returned, _, returnedRelated⟩ := bridge.restore rhsReached writePool (.refl _) futureWorlds
            storeFrame (.of_write heapWrite) (Relates.of_records_eq rfl)
          exact .success resolved rhsTrace
            (.intro keptRead keptType keptInitial (.element currentAt (.leaf applies) replace) heapWrite)
            finalHeaps (keyMaps.trans rhsMaps) (((keyWorlds.trans lookupWorlds).trans rhsWorlds).trans futureWorlds)
            (((keyFrame.trans lookupFrame).trans rhsFrame).trans storeFrame)
            ((keyMetadata.trans rhsMetadata).trans (.of_write heapWrite))
            (((keyEffect.trans lookupEffect).trans rhsEffect).trans storeEffect)
            (slots := [.unit, OrderedMapping.encode head.layout (OrderedMapping.insertEntries
                GenericHeap.arrayKeyEqual (.word position) changed entries'), changed, coreRight,
              .inRight .unit (present.getD default), OrderedMapping.optionValue head.layout.valueType present,
              .word position,
              .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget]) rfl
            (.cons .unit (.cons encodeTyped (.cons (changedRep.runtime_hasType.weaken futureWorlds)
              (.cons (rightPayload.runtime_hasType.weaken futureWorlds)
                (.cons (.inRight ((snapshotRep.runtime_hasType.weaken rhsWorlds).weaken futureWorlds))
                  (.cons ((foundTyped.weaken rhsWorlds).weaken futureWorlds) (.cons .word
                    (.cons (.cellRef (futureWorlds.lookup (rhsWorlds.lookup (lookupWorlds.lookup
                        (keyWorlds.lookup typed)))))
                      (actualTyped.weaken (((keyWorlds.trans lookupWorlds).trans rhsWorlds).trans
                        futureWorlds))))))))))
            returned
            (callerProtocol.trans (callerProtocol.trans (callerProtocol.trans keyRelated lookupRelated) rhsRelated)
              returnedRelated)
            ⟨referenceMiddle.arrayElementWrite rhsPost.at_value.2.heap keptRead keptStored replace updatedTyped
                heapWrite,
              StableRows.after_administrative (bridge.pool initial) (bridge.pool returned) admitted.rows
                (((keyFrame.trans lookupFrame).trans rhsFrame).trans storeFrame)⟩
            (by omega) remaining

end Heads

end Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteHeads

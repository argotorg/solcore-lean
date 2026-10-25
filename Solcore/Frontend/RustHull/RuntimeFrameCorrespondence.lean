import Solcore.Frontend.RustHull.AccountRuntime
import Solcore.Frontend.RustHull.StorageCorrespondence
import Solcore.Frontend.RustHull.EffectStateCorrespondence

/-! The actual contract-frame wrapper unpacks runtime references, reads the
final account and exports its snapshot after the assembled Hull body. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution

/-- The real frame compiler supplies both assembly and all checked runtime
references used by the completion snapshot. -/
theorem compileFrame_components {program : Program} {code : CodeBlock}
    {slots : List (String × Core.Ty)} {fuel : Nat} {compiled : Core.Expr}
    (accepted : AccountRuntime.compileFrame program code slots fuel = .ok compiled) :
    ∃ own body cells,
      assemble (program.functions ++ code.functions ++ [AccountRuntime.frameFunction code])
        AccountRuntime.frameEntry (AccountRuntime.frameScope slots) fuel = .ok (own, body) ∧
      AccountRuntime.frameReferences slots = .ok cells ∧
      compiled = AccountRuntime.frameUnpack slots (AccountRuntime.frameCompletion cells body) := by
  unfold AccountRuntime.compileFrame at accepted
  split at accepted
  · simp [fail, Bind.bind, Except.bind] at accepted
  · obtain ⟨pair, assembled, remaining⟩ := lower_bind_eq_ok.mp accepted
    rcases pair with ⟨own, body⟩
    obtain ⟨cells, references, returned⟩ := lower_bind_eq_ok.mp remaining
    cases returned
    exact ⟨own, body, cells, assembled, references, rfl⟩

/-- The exact projection fold used to unpack runtime references, at an explicit
starting index so each step uses the original unchanged argument bundle. -/
def frameBindingCode (total start : Nat) (slots : List (String × Core.Ty)) (body : Core.Expr) : Core.Expr :=
  (slots.zipIdx start).foldr (fun (_, index) next =>
    .letE (projectArgument index total (.var (index + 1))) next) body

theorem frameBindings_evaluate {slots : List (String × Core.Ty)}
    {values allValues : List Core.Value} (length : values.length = slots.length)
    {environment : Core.Environment} {initial final : Core.Store}
    {start : Nat} (argument : environment[start + 1]? = some (bundleValues allValues))
    (selected : ∀ index value, values[index]? = some value → allValues[start + index]? = some value)
    {body : Core.Expr} {result : Core.Value}
    (evaluated : Core.Evaluates (values.reverse ++ environment) initial body result final) :
    Core.Evaluates environment initial (frameBindingCode allValues.length start slots body) result final := by
  induction slots generalizing values start environment with
  | nil =>
      have empty : values = [] := List.eq_nil_of_length_eq_zero length
      subst values
      exact evaluated
  | cons slot rest ih =>
      cases values with
      | nil => simp at length
      | cons value values =>
          have projected : Core.Evaluates environment initial
              (projectArgument start allValues.length (.var (start + 1))) value initial :=
            projectArgument_evaluates (.var argument) (by simpa using selected 0 value rfl)
          simp only [frameBindingCode, List.zipIdx_cons, List.foldr_cons]
          apply Core.Evaluates.letE projected
          apply ih (Nat.succ.inj length) (start := start + 1)
          · simpa only [List.getElem?_cons_succ, Nat.add_assoc] using argument
          · intro index selectedValue found
            simpa only [Nat.add_assoc, Nat.add_comm 1 index] using selected (index + 1) selectedValue found
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using evaluated

/-- Apply the emitted frame lambda and unpack its actual runtime-cell bundle.
No host-created replacement environment is used by the evaluated expression. -/
theorem frameUnpack_evaluates {slots : List (String × Core.Ty)} {values : List Core.Value}
    (length : values.length = slots.length) {environment : Core.Environment}
    {initial allocated final : Core.Store} {argument body : Core.Expr} {result : Core.Value}
    (supplied : Core.Evaluates environment initial argument (bundleValues values) allocated)
    (evaluated : Core.Evaluates (values.reverse ++ .unit :: bundleValues values :: environment)
      allocated body result final) :
    Core.Evaluates environment initial (.apply (AccountRuntime.frameUnpack slots body) argument)
      result final := by
  apply Core.Evaluates.apply .lambda supplied
  apply Core.Evaluates.letE .unit
  have unpacked := frameBindings_evaluate length (start := 0) (allValues := values)
    (by rfl : (Core.Value.unit :: bundleValues values :: environment)[1]? = some (bundleValues values))
    (fun index value found => by simpa only [Nat.zero_add] using found) evaluated
  simpa only [frameBindingCode, length] using unpacked

def CheckedFrameReferences (scope : Scope) (cells : AccountRuntime.References) : Prop :=
  ∀ entry ∈ cells, ∃ binding index,
    scope.lookup (Effects.slotName entry.1) = .ok (binding, index) ∧
    entry.2 = AccountRuntime.raw (.var index)

private theorem effectReference_components {scope : Scope} {name : String} {type : Core.Ty}
    {expression : Core.Expr} (accepted : Effects.reference scope name type = .ok expression) :
    ∃ binding index, scope.lookup (Effects.slotName name) = .ok (binding, index) ∧ expression = .var index := by
  obtain ⟨pair, looked, remaining⟩ := lower_bind_eq_ok.mp accepted
  rcases pair with ⟨binding, index⟩
  obtain ⟨_, _, returned⟩ := lower_bind_eq_ok.mp remaining
  cases returned
  exact ⟨binding, index, looked, rfl⟩

private def frameReferenceStep (scope : Scope) (slot : String × Core.Ty)
    (cells : AccountRuntime.References) : LowerM (ForInStep AccountRuntime.References) := do
  let expression ← Effects.reference scope slot.1 slot.2
  pure (.yield (cells ++ [(slot.1, AccountRuntime.raw expression)]))

private theorem frameReferences_loop {scope : Scope} {slots : List (String × Core.Ty)}
    {initial cells : AccountRuntime.References}
    (accepted : forIn slots initial (frameReferenceStep scope) = .ok cells)
    (checked : CheckedFrameReferences scope initial) :
    CheckedFrameReferences scope cells ∧ cells.map Prod.fst = initial.map Prod.fst ++ slots.map Prod.fst := by
  induction slots generalizing initial with
  | nil =>
      cases accepted
      exact ⟨checked, by simp⟩
  | cons slot rest ih =>
      rcases slot with ⟨name, type⟩
      cases lowered : Effects.reference scope name type with
      | error error =>
          simp [List.forIn_cons, frameReferenceStep, lowered, Bind.bind, Except.bind] at accepted
      | ok expression =>
          simp only [List.forIn_cons, frameReferenceStep, lowered, Bind.bind, Except.bind,
            Pure.pure, Except.pure] at accepted
          have stepChecked : CheckedFrameReferences scope (initial ++ [(name, AccountRuntime.raw expression)]) := by
            intro entry member
            rcases List.mem_append.mp member with old | fresh
            · exact checked entry old
            · have same := List.mem_singleton.mp fresh
              subst entry
              obtain ⟨binding, index, looked, rfl⟩ := effectReference_components lowered
              exact ⟨binding, index, looked, rfl⟩
          obtain ⟨sound, names⟩ := ih accepted stepChecked
          exact ⟨sound, by simpa only [List.map_append, List.map_cons, List.map_nil,
            List.append_assoc, List.singleton_append] using names⟩

/-- Every reference used by the frame comes from the actual successful scope
lookup, and no requested runtime slot is dropped by the compiler's loop. -/
theorem frameReferences_checked {slots : List (String × Core.Ty)} {cells : AccountRuntime.References}
    (accepted : AccountRuntime.frameReferences slots = .ok cells) :
    CheckedFrameReferences (AccountRuntime.frameScope slots) cells ∧
      cells.map Prod.fst = slots.map Prod.fst := by
  have loop : forIn slots [] (frameReferenceStep (AccountRuntime.frameScope slots)) = .ok cells := by
    simp only [AccountRuntime.frameReferences, bind_pure] at accepted
    exact accepted
  obtain ⟨checked, names⟩ := frameReferences_loop loop (by intro entry member; cases member)
  exact ⟨checked, names⟩

/-- A checked runtime reference denotes one actual cell. This relation records
syntax, environment lookup and store contents without assuming an evaluation. -/
def FrameCellObserved (cells : AccountRuntime.References) (environment : Core.Environment)
    (store : Core.Store) (name : String) (value : Core.Value) : Prop :=
  ∃ index location type,
    (∀ depth, AccountRuntime.reference cells name depth = .var (index + depth)) ∧
    environment[index]? = some (.cellRef type location) ∧ store.read? location = some value

/-- Actual frame-reference compilation and the initialized runtime scope
supply the elementary observation used by completion and snapshot execution. -/
theorem FrameCellObserved.of_compilation {slots : List (String × Core.Ty)}
    {cells : AccountRuntime.References} {name : String} {type : Core.Ty}
    (accepted : AccountRuntime.frameReferences slots = .ok cells)
    (member : (name, type) ∈ slots)
    {environment : Core.Environment} {store : Core.Store} {location : Nat} {value : Core.Value}
    (runtime : ∀ binding index,
      (AccountRuntime.frameScope slots).lookup (Effects.slotName name) = .ok (binding, index) →
      environment[index]? = some (.cellRef type location))
    (stored : store.read? location = some value) : FrameCellObserved cells environment store name value := by
  obtain ⟨checked, names⟩ := frameReferences_checked accepted
  have present : name ∈ cells.map Prod.fst := by
    rw [names]
    exact List.mem_map.mpr ⟨(name, type), member, rfl⟩
  obtain ⟨entry, entryMember, named⟩ := List.mem_map.mp present
  have foundEntry : ∃ entry, cells.find? (fun entry => entry.1 == name) = some entry := by
    cases found : cells.find? (fun entry => entry.1 == name) with
    | none =>
        have absent := List.find?_eq_none.mp found entry entryMember
        exact False.elim (absent (by simpa only [beq_iff_eq] using named))
    | some selected => exact ⟨selected, rfl⟩
  obtain ⟨selected, found⟩ := foundEntry
  have selectedMember := List.mem_of_find?_eq_some found
  have same : selected.1 = name := by simpa only [beq_iff_eq] using List.find?_some found
  obtain ⟨binding, index, looked, code⟩ := checked selected selectedMember
  rw [same] at looked
  refine ⟨index, location, type, ?_, runtime binding index looked, stored⟩
  intro depth
  simp only [AccountRuntime.reference, found, Option.map_some, Option.getD_some, code,
    AccountRuntime.raw, Core.Expr.rename]

theorem FrameCellObserved.load {cells : AccountRuntime.References} {environment : Core.Environment}
    {store : Core.Store} {name : String} {value : Core.Value}
    (observed : FrameCellObserved cells environment store name value) (extra : Core.Environment) :
    Core.Evaluates (extra ++ environment) store
      (CodeBuilder.load (AccountRuntime.reference cells name) extra.length) value store := by
  obtain ⟨index, location, type, reference, found, stored⟩ := observed
  unfold CodeBuilder.load
  rw [reference]
  apply Core.Evaluates.loadCell (elementType := type) (location := location) (.var ?_) stored
  simpa only [Nat.add_comm index extra.length, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left] using found

theorem FrameCellObserved.retained {cells : AccountRuntime.References} {environment : Core.Environment}
    {initial final : Core.Store} {name : String} {value : Core.Value}
    (observed : FrameCellObserved cells environment initial name value) (retained : StoreRetains initial final) :
    FrameCellObserved cells environment final name value := by
  obtain ⟨index, location, type, reference, found, stored⟩ := observed
  exact ⟨index, location, type, reference, found, by
    rw [retained.read location (List.getElem?_eq_some_iff.mp stored).1]
    exact stored⟩

def frameSnapshotNames : List String :=
  ["exit", "returnOffset", "returnSize", "memory", "logs", "logSize", "balances", "world"]

def frameSnapshotValue (values : String → Core.Value) (storage : Core.Value) : Core.Value :=
  bundleValues [values "exit", values "returnOffset", values "returnSize", values "memory",
    storage, values "logs", values "logSize", values "balances", values "world"]

theorem frameSnapshot_evaluates {cells : AccountRuntime.References} {environment : Core.Environment}
    {store : Core.Store} {values : String → Core.Value}
    (observed : ∀ name ∈ frameSnapshotNames, FrameCellObserved cells environment store name (values name))
    (extra : Core.Environment) {storage : CodeBuilder.Code} {stored : Core.Value}
    (storageEvaluated : Core.Evaluates (extra ++ environment) store (storage extra.length) stored store) :
    Core.Evaluates (extra ++ environment) store (AccountRuntime.frameSnapshot cells storage extra.length)
      (frameSnapshotValue values stored) store := by
  have exit := (observed "exit" (by simp [frameSnapshotNames])).load extra
  have offset := (observed "returnOffset" (by simp [frameSnapshotNames])).load extra
  have size := (observed "returnSize" (by simp [frameSnapshotNames])).load extra
  have memory := (observed "memory" (by simp [frameSnapshotNames])).load extra
  have logs := (observed "logs" (by simp [frameSnapshotNames])).load extra
  have logSize := (observed "logSize" (by simp [frameSnapshotNames])).load extra
  have balances := (observed "balances" (by simp [frameSnapshotNames])).load extra
  have world := (observed "world" (by simp [frameSnapshotNames])).load extra
  exact .pair exit (.pair offset (.pair size (.pair memory (.pair storageEvaluated
    (.pair logs (.pair logSize (.pair balances world)))))))

def frameCompletionValue (status : Core.Value) (values : String → Core.Value)
    (account : Except Core.Word (AccountState.Account × Nat)) : Core.Value :=
  match account with
  | .ok (account, _) => .pair status (frameSnapshotValue values (Core.WordMapping.encode account.storage))
  | .error reason => .pair (.inLeft .unit (.word reason))
      (frameSnapshotValue values (Core.WordMapping.encode []))

/-- The real completion wrapper reads the final account and exports the final
runtime cells. The account lookup is proved by its concrete source operation;
its helper allocation is retained in the resulting Core store. -/
theorem frameCompletion_evaluates {cells : AccountRuntime.References} {environment : Core.Environment}
    {initial final : Core.Store} {body : Core.Expr} {status : Core.Value}
    (executed : Core.Evaluates environment initial body status final)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (complete : Bool)
    (worldObserved : FrameCellObserved cells environment final "world" (StorageCorrespondence.world accounts))
    (addressObserved : FrameCellObserved cells environment final "address" (.word address))
    (completeObserved : FrameCellObserved cells environment final "worldComplete" (.bool complete))
    {values : String → Core.Value}
    (snapshotObserved : ∀ name ∈ frameSnapshotNames,
      FrameCellObserved cells environment final name (values name)) :
    Core.Evaluates environment initial (AccountRuntime.frameCompletion cells body)
      (frameCompletionValue status values (StorageCorrespondence.get accounts address complete))
      (StorageCorrespondence.getStore accounts address complete (status :: environment) final) := by
  have fetched := StorageCorrespondence.get_evaluates accounts address complete
    (worldObserved.load [status]) (addressObserved.load [status]) (completeObserved.load [status])
  have extension := StorageCorrespondence.getStore_extension accounts address complete (status :: environment) final
  obtain ⟨suffix, _, stored⟩ := extension
  have retained : StoreRetains final
      (StorageCorrespondence.getStore accounts address complete (status :: environment) final) := by
    rw [stored]
    exact StoreRetains.append final suffix
  have finalSnapshot := fun name member => (snapshotObserved name member).retained retained
  simp only [AccountRuntime.frameCompletion, CodeBuilder.bind, AccountRuntime.raw,
    Nat.add_zero]
  rw [show body.rename (fun x => x) = body from Core.Expr.rename_id body]
  apply Core.Evaluates.letE executed
  apply Core.Evaluates.letE fetched
  cases found : StorageCorrespondence.get accounts address complete with
  | error reason =>
      simp only [StorageCorrespondence.getValue, frameCompletionValue]
      apply Core.Evaluates.caseLeft (.var rfl)
      apply Core.Evaluates.pair (.inLeft (.var rfl))
      exact frameSnapshot_evaluates finalSnapshot
        [.word reason, .inLeft AccountState.recordType (.word reason), status] (.construct .unit)
  | ok account =>
      rcases account with ⟨account, identity⟩
      simp only [StorageCorrespondence.getValue, frameCompletionValue]
      apply Core.Evaluates.caseRight (.var rfl)
      apply Core.Evaluates.pair (.var rfl)
      apply frameSnapshot_evaluates finalSnapshot
        [StorageCorrespondence.record account identity,
          .inRight .word (StorageCorrespondence.record account identity), status]
      exact .first (.var rfl)

end Solcore.Frontend.RustHull.Correspondence

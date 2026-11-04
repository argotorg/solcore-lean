import Solcore.Frontend.RustHull.AccountRuntime
import Solcore.Frontend.RustHull.Internal.StorageState
import Solcore.Frontend.RustHull.Internal.MemoryState
import Solcore.Frontend.RustHull.Internal.LoweringFacts

/-!
# Runtime frames

One compiled frame: its closures, memory initialization, completion and frame facts.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeFrameCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeClosureCorrespondence
/-! Runtime frame closures retain the environment at installation even when
called later from a different lexical environment. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution

inductive CapturedClosure : Core.Expr → Core.Environment → Core.Value → Prop where
  | lambda (parameter result : Core.Ty) (body : Core.Expr) (captured : Core.Environment) :
      CapturedClosure (.lambda parameter result body) captured (.closure parameter result body captured)

theorem CapturedClosure.evaluates {expression : Core.Expr} {captured : Core.Environment} {value : Core.Value}
    (related : CapturedClosure expression captured value) (store : Core.Store) :
    Core.Evaluates captured store expression value store := by cases related; exact .lambda

theorem frameUnpack_call_evaluates {slots : List (String × Core.Ty)} {values : List Core.Value}
    (length : values.length = slots.length) {environment captured : Core.Environment}
    {initial argumentsStore allocated final : Core.Store} {function argument body : Core.Expr}
    {closure result : Core.Value}
    (related : CapturedClosure (AccountRuntime.frameUnpack slots body) captured closure)
    (resolved : Core.Evaluates environment initial function closure argumentsStore)
    (supplied : Core.Evaluates environment argumentsStore argument (bundleValues values) allocated)
    (evaluated : Core.Evaluates (values.reverse ++ .unit :: bundleValues values :: captured)
      allocated body result final) :
    Core.Evaluates environment initial (.apply function argument) result final := by
  cases related
  apply Core.Evaluates.apply resolved supplied
  apply Core.Evaluates.letE .unit
  have unpacked := frameBindings_evaluate length (start := 0) (allValues := values)
    (by rfl : (Core.Value.unit :: bundleValues values :: captured)[1]? = some (bundleValues values))
    (fun index value found => by simpa only [Nat.zero_add] using found) evaluated
  simpa only [frameBindingCode, length] using unpacked

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCompletionCorrespondence
/-! Completion of the actual message wrapper preserves account finalization
and forwards the resulting runtime value to public receipts. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

 theorem CodeValue.first {depth : Nat} {environment : Core.Environment} {code : Code}
    {left right : Core.Value} (related : CodeValue depth environment code (.pair left right)) :
    CodeValue depth environment (AccountRuntime.first code) left :=
  fun extra store => .first (related extra store)

 theorem CodeValue.second {depth : Nat} {environment : Core.Environment} {code : Code}
    {left right : Core.Value} (related : CodeValue depth environment code (.pair left right)) :
    CodeValue depth environment (AccountRuntime.second code) right :=
  fun extra store => .second (related extra store)

 theorem StorageCorrespondence.get_complete (accounts : StorageCorrespondence.Accounts) (address : Core.Word) :
    ∃ account identity, StorageCorrespondence.get accounts address true = .ok (account, identity) := by
  unfold StorageCorrespondence.get
  cases StorageCorrespondence.lookup address accounts with
  | none => exact ⟨_, _, rfl⟩
  | some account => exact ⟨account.1, account.2, rfl⟩

 def finalizedSnapshotValue (values : String → Core.Value) (account : AccountState.Account)
    (accounts : StorageCorrespondence.Accounts) (balances : StorageSemantics.Words) : Core.Value :=
  frameSnapshotValue
    (fun name => if name = "balances" then Core.WordMapping.encode balances
      else if name = "world" then StorageCorrespondence.world accounts else values name)
    (Core.WordMapping.encode account.storage)

 theorem messageFinalize_evaluates {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {target result : Code}
    {status oldStorage : Core.Value} {values : String → Core.Value} {address : Core.Word}
    {worldLocation balancesLocation : Nat} {initial : Core.Store}
    (accounts : StorageCorrespondence.Accounts) (balances : StorageSemantics.Words)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (resultValue : CodeValue depth environment result (.pair status (frameSnapshotValue values oldStorage)))
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances)) :
    ∃ account identity final,
      StorageCorrespondence.get (StorageCorrespondence.finalize accounts balances).1 address true = .ok (account, identity) ∧
      Core.Evaluates environment initial (AccountRuntime.finalize shared target result depth)
        (.pair status (finalizedSnapshotValue values account
          (StorageCorrespondence.finalize accounts balances).1 (StorageCorrespondence.finalize accounts balances).2)) final ∧
      final.read? worldLocation = some (StorageCorrespondence.world (StorageCorrespondence.finalize accounts balances).1) ∧
      final.read? balancesLocation = some (Core.WordMapping.encode (StorageCorrespondence.finalize accounts balances).2) ∧
      StorageCorrespondence.FinalizeFrame worldLocation balancesLocation initial final := by
  obtain ⟨completed, finalized, worldUpdated, balancesUpdated, frame⟩ :=
    StorageCorrespondence.finalize_evaluates accounts balances worldLocation balancesLocation
      (.pair (worldReference.evaluates initial) (balancesReference.evaluates initial)) worldFound balancesFound
  obtain ⟨account, identity, found⟩ := StorageCorrespondence.get_complete
    (StorageCorrespondence.finalize accounts balances).1 address
  let finalizedValue := Core.Value.inRight .word .unit
  let fetchedValue := StorageCorrespondence.getValue (.ok (account, identity))
  let getEnvironment := Core.Value.unit :: finalizedValue :: environment
  let final := StorageCorrespondence.getStore (StorageCorrespondence.finalize accounts balances).1
    address true getEnvironment completed
  have fetched := StorageCorrespondence.get_evaluates
    (environment := getEnvironment) (StorageCorrespondence.finalize accounts balances).1 address true
    (.loadCell (worldReference [Core.Value.unit, finalizedValue] completed) worldUpdated)
    (targetValue [Core.Value.unit, finalizedValue] completed) Core.Evaluates.bool
  rw [found] at fetched
  obtain ⟨suffix, _, extension⟩ := StorageCorrespondence.getStore_extension
    (StorageCorrespondence.finalize accounts balances).1 address true getEnvironment completed
  have retained : StoreRetains completed final := by
    rw [show final = completed ++ suffix from extension]
    exact StoreRetains.append _ _
  have worldFinal := retained.read worldLocation (List.getElem?_eq_some_iff.mp worldUpdated).1
  have balancesFinal := retained.read balancesLocation (List.getElem?_eq_some_iff.mp balancesUpdated).1
  rw [worldUpdated] at worldFinal
  rw [balancesUpdated] at balancesFinal
  refine ⟨account, identity, final, found, ?_, worldFinal, balancesFinal, ?_⟩
  · unfold AccountRuntime.finalize CodeBuilder.bind
    apply Core.Evaluates.letE finalized
    apply Core.Evaluates.caseRight (leftType := .word) (payload := .unit) (.var (by simp))
    apply Core.Evaluates.letE fetched
    apply Core.Evaluates.caseRight (leftType := .word) (payload := StorageCorrespondence.record account identity)
      (.var (by simp [StorageCorrespondence.getValue]))
    let extra := [StorageCorrespondence.record account identity, fetchedValue, Core.Value.unit, finalizedValue]
    have evaluated := resultValue extra final
    have projected (index : Nat) (value : Core.Value)
        (selected : [values "exit", values "returnOffset", values "returnSize", values "memory",
          oldStorage, values "logs", values "logSize", values "balances", values "world"][index]? = some value) :=
      projectArgument_evaluates (.second evaluated) selected
    have stored : Core.Evaluates (extra ++ environment) final
        (part 0 9 (fun here => Core.Expr.var (here - (depth + 1 + 1 + 1) - 1)) (depth + 1 + 1 + 1 + 1))
        (Core.WordMapping.encode account.storage) final :=
      projectArgument_evaluates (Core.Evaluates.var (by simp [extra, StorageCorrespondence.record])) (by rfl :
        [Core.WordMapping.encode account.storage, Core.WordMapping.encode account.transient,
          Core.Value.word account.nonce, .word (Core.Word.ofNatModulo identity),
          Core.WordMapping.encode (Memory.packBytes (account.code.getD [])),
          .word (Core.Word.ofNatModulo (account.code.getD []).length),
          .bool account.code.isSome, .bool account.created, .bool account.destroyed][0]? = some _)
    exact .pair (.first evaluated)
      (.pair (projected 0 _ rfl) (.pair (projected 1 _ rfl) (.pair (projected 2 _ rfl)
        (.pair (projected 3 _ rfl) (.pair stored (.pair (projected 5 _ rfl)
          (.pair (projected 6 _ rfl) (.pair
            (.loadCell (balancesReference extra final) balancesFinal)
            (.loadCell (worldReference extra final) worldFinal)))))))))
  · constructor
    · exact Nat.le_trans frame.length_le retained.length_le
    · intro location value differentWorld differentBalances read
      rw [retained.read location (List.getElem?_eq_some_iff.mp
        (frame.preserved location value differentWorld differentBalances read)).1]
      exact frame.preserved location value differentWorld differentBalances read

inductive MessageStatus : Core.Value → Bool → Prop where
  | success : MessageStatus (.inRight .word .unit) true
  | failure (reason : Core.Value) : MessageStatus (.inLeft .unit reason) false

def messageSucceeded (exit : Core.Word) (status : Bool) : Bool :=
  if exit == Core.Word.ofNatModulo 1 then true
  else if exit == Core.Word.ofNatModulo 0 then status else false

theorem messageSuccessful_evaluates {depth : Nat} {environment : Core.Environment}
    {result : Code} {status oldStorage : Core.Value} {values : String → Core.Value}
    {exit : Core.Word} {succeeded : Bool}
    (resultValue : CodeValue depth environment result (.pair status (frameSnapshotValue values oldStorage)))
    (statusRelated : MessageStatus status succeeded) (exitValue : values "exit" = .word exit)
    (store : Core.Store) :
    Core.Evaluates environment store (AccountRuntime.messageSuccessful result depth)
      (.bool (messageSucceeded exit succeeded)) store := by
  have evaluated := resultValue.evaluates store
  have projected := projectArgument_evaluates (.second evaluated)
    (by simpa only [List.getElem?_cons_zero] using congrArg some exitValue :
      [values "exit", values "returnOffset", values "returnSize", values "memory", oldStorage,
       values "logs", values "logSize", values "balances", values "world"][0]? = some (.word exit))
  unfold AccountRuntime.messageSuccessful CodeBuilder.choose messageSucceeded
  cases one : exit == Core.Word.ofNatModulo 1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply Core.Evaluates.ifFalse (.binary projected .word (by simp only [Core.BinaryOp.apply, one]))
    cases zero : exit == Core.Word.ofNatModulo 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact .ifFalse (.binary projected .word (by simp only [Core.BinaryOp.apply, zero])) .bool
    · simp only [↓reduceIte]
      apply Core.Evaluates.ifTrue (.binary projected .word (by simp only [Core.BinaryOp.apply, zero]))
      cases statusRelated
      · exact .caseRight (.first evaluated) .bool
      · exact .caseLeft (.first evaluated) .bool
  · simp only [↓reduceIte]
    exact .ifTrue (.binary projected .word (by simp only [Core.BinaryOp.apply, one])) .bool

theorem completeMessage_failure {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {target deploying result : Code}
    {status oldStorage : Core.Value} {values : String → Core.Value} {exit : Core.Word} {succeeded : Bool}
    (resultValue : CodeValue depth environment result (.pair status (frameSnapshotValue values oldStorage)))
    (statusRelated : MessageStatus status succeeded) (exitValue : values "exit" = .word exit)
    (failed : messageSucceeded exit succeeded = false) (store : Core.Store) :
    Core.Evaluates environment store (AccountRuntime.completeMessage shared images target deploying result depth)
      (.pair status (frameSnapshotValue values oldStorage)) store := by
  have checked := messageSuccessful_evaluates resultValue statusRelated exitValue store
  rw [failed] at checked
  exact .ifFalse checked (resultValue.evaluates store)

theorem completeMessage_success {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {target deploying result : Code}
    {status oldStorage : Core.Value} {values : String → Core.Value} {address exit : Core.Word} {succeeded : Bool}
    {worldLocation balancesLocation : Nat} {initial : Core.Store}
    (accounts : StorageCorrespondence.Accounts) (balances : StorageSemantics.Words)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (resultValue : CodeValue depth environment result (.pair status (frameSnapshotValue values oldStorage)))
    (statusRelated : MessageStatus status succeeded) (exitValue : values "exit" = .word exit)
    (successful : messageSucceeded exit succeeded = true)
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances)) :
    ∃ account identity final,
      StorageCorrespondence.get (StorageCorrespondence.finalize accounts balances).1 address true = .ok (account, identity) ∧
      Core.Evaluates environment initial (AccountRuntime.completeMessage shared images target deploying result depth)
        (.pair status (finalizedSnapshotValue values account
          (StorageCorrespondence.finalize accounts balances).1 (StorageCorrespondence.finalize accounts balances).2)) final ∧
      final.read? worldLocation = some (StorageCorrespondence.world (StorageCorrespondence.finalize accounts balances).1) ∧
      final.read? balancesLocation = some (Core.WordMapping.encode (StorageCorrespondence.finalize accounts balances).2) ∧
      StorageCorrespondence.FinalizeFrame worldLocation balancesLocation initial final := by
  obtain ⟨account, identity, final, found, evaluated, worldFinal, balancesFinal, frame⟩ :=
    messageFinalize_evaluates accounts balances worldReference balancesReference targetValue resultValue worldFound balancesFound
  have checked := messageSuccessful_evaluates resultValue statusRelated exitValue initial
  rw [successful] at checked
  exact ⟨account, identity, final, found,
    .ifTrue checked (.ifFalse (deployingValue.evaluates initial) evaluated), worldFinal, balancesFinal, frame⟩

def completedMessageValue (status : Core.Value) (succeeded : Bool) (exit : Core.Word)
    (values : String → Core.Value) (storage : Core.Value)
    (accounts : StorageCorrespondence.Accounts) (address : Core.Word) (balances : StorageSemantics.Words) : Core.Value :=
  if messageSucceeded exit succeeded then
    match StorageCorrespondence.get (StorageCorrespondence.finalize accounts balances).1 address true with
    | .ok (account, _) => .pair status (finalizedSnapshotValue values account
        (StorageCorrespondence.finalize accounts balances).1 (StorageCorrespondence.finalize accounts balances).2)
    | .error _ => .pair status (frameSnapshotValue values storage)
  else .pair status (frameSnapshotValue values storage)

theorem completeMessage_evaluates {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {images : List (Nat × List UInt8)} {target deploying result : Code}
    {status oldStorage : Core.Value} {values : String → Core.Value} {address exit : Core.Word} {succeeded : Bool}
    {worldLocation balancesLocation : Nat} {initial : Core.Store}
    (accounts : StorageCorrespondence.Accounts) (balances : StorageSemantics.Words)
    (worldReference : CodeValue depth environment (AccountRuntime.reference shared "world")
      (.cellRef AccountState.type worldLocation))
    (balancesReference : CodeValue depth environment (AccountRuntime.reference shared "balances")
      (.cellRef Core.WordMapping.type balancesLocation))
    (targetValue : CodeValue depth environment target (.word address))
    (deployingValue : CodeValue depth environment deploying (.bool false))
    (resultValue : CodeValue depth environment result (.pair status (frameSnapshotValue values oldStorage)))
    (statusRelated : MessageStatus status succeeded) (exitValue : values "exit" = .word exit)
    (worldFound : initial.read? worldLocation = some (StorageCorrespondence.world accounts))
    (balancesFound : initial.read? balancesLocation = some (Core.WordMapping.encode balances)) :
    ∃ final, Core.Evaluates environment initial (AccountRuntime.completeMessage shared images target deploying result depth)
      (completedMessageValue status succeeded exit values oldStorage accounts address balances) final := by
  cases successful : messageSucceeded exit succeeded with
  | false =>
      have evaluated := completeMessage_failure (shared := shared) (images := images) (target := target) (deploying := deploying)
        resultValue statusRelated exitValue successful initial
      exact ⟨initial, by simpa only [completedMessageValue, successful, Bool.false_eq_true, ↓reduceIte] using evaluated⟩
  | true =>
      obtain ⟨account, identity, final, found, evaluated, _, _, _⟩ :=
        completeMessage_success (images := images) accounts balances worldReference balancesReference
          targetValue deployingValue resultValue statusRelated exitValue successful worldFound balancesFound
      exact ⟨final, by simpa only [completedMessageValue, successful, ↓reduceIte, found] using evaluated⟩

/-- Successful public compilation returns the exact object wrapper around
its successfully compiled entry frame. -/
theorem compileObject_components {program : Program} {path : List String} {fuel : Nat}
    {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {expression : Core.Expr}
    (accepted : AccountRuntime.compileObject program path fuel codeBytes catalog = .ok expression) :
    ∃ code compiled others,
      AccountRuntime.compileFrame program code
        (Effects.slots ++ (if codeBytes.isSome || !catalog.isEmpty then Effects.codeSlots else [])) fuel = .ok compiled ∧
      expression = AccountRuntime.objectExpression
        (Effects.slots ++ (if codeBytes.isSome || !catalog.isEmpty then Effects.codeSlots else []))
        compiled others ((codeBytes.toList.map (1, ·)) ++
          (catalog.zipIdx.filterMap fun (definition, index) =>
            if definition.isInit then none else some (index + 2, definition.bytes))) codeBytes catalog := by
  unfold AccountRuntime.compileObject at accepted
  obtain ⟨code, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨compiled, compiledOk, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨others, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨guard, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  cases guard
  cases accepted
  exact ⟨code, compiled, others, compiledOk, rfl⟩

theorem compileObject_empty_catalog {program : Program} {path : List String} {fuel : Nat}
    {codeBytes : Option (List UInt8)} {expression : Core.Expr}
    (accepted : AccountRuntime.compileObject program path fuel codeBytes [] = .ok expression) :
    ∃ code compiled,
      AccountRuntime.compileFrame program code
        (Effects.slots ++ (if codeBytes.isSome then Effects.codeSlots else [])) fuel = .ok compiled ∧
      expression = AccountRuntime.objectExpression
        (Effects.slots ++ (if codeBytes.isSome then Effects.codeSlots else []))
        compiled [] (codeBytes.toList.map (1, ·)) codeBytes [] := by
  unfold AccountRuntime.compileObject at accepted
  obtain ⟨code, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨compiled, compiledOk, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨others, mapped, accepted⟩ := lower_bind_eq_ok.mp accepted
  have empty : others = [] := by simpa using (Except.ok.inj mapped).symm
  subst others
  obtain ⟨_, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  obtain ⟨guard, _, accepted⟩ := lower_bind_eq_ok.mp accepted
  cases guard
  cases accepted
  exact ⟨code, compiled, by simpa using compiledOk, by simp⟩

/-- Applying the exact object expression introduces the real context argument
and executes its emitted runtime body. -/
theorem objectExpression_evaluates {slots : List (String × Core.Ty)} {compiled : Core.Expr}
    {others : List Core.Expr} {images : List (Nat × List UInt8)}
    {codeBytes : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {argument : Core.Expr} {context result : Core.Value} {environment : Core.Environment}
    {initial allocated final : Core.Store}
    (supplied : Core.Evaluates environment initial argument context allocated)
    (evaluated : Core.Evaluates (context :: environment) allocated
      (AccountRuntime.objectRuntime slots compiled others images codeBytes catalog (fun here => .var (here - 0 - 1)) 1)
      result final) :
    Core.Evaluates environment initial
      (.apply (AccountRuntime.objectExpression slots compiled others images codeBytes catalog) argument) result final :=
  .apply .lambda supplied evaluated

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeMemoryInitializationCorrespondence
/-! The actual runtime allocation builders establish the initial cell values
and reference arguments used by compiled Hull frames. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

structure InitializedCell where
  name : String
  type : Core.Ty
  location : Nat
  value : Core.Value

def InitializedCell.reference (cell : InitializedCell) : Core.Value :=
  .cellRef cell.type cell.location

def InitializedCells (cells : List InitializedCell) (store : Core.Store) : Prop :=
  ∀ cell ∈ cells, store.read? cell.location = some cell.value

structure RuntimeReferences (depth : Nat) (environment : Core.Environment)
    (references : AccountRuntime.References) (cells : List InitializedCell) : Prop where
  names : references.map Prod.fst = cells.map InitializedCell.name
  values : CodeValues depth environment (references.map Prod.snd) (cells.map InitializedCell.reference)

theorem RuntimeReferences.prepend {depth : Nat} {environment : Core.Environment}
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells) (extra : Core.Environment) :
    RuntimeReferences (depth + extra.length) (extra ++ environment) references cells :=
  ⟨related.names, related.values.prepend extra⟩

theorem InitializedCells.appendStore {cells : List InitializedCell} {store : Core.Store}
    (initialized : InitializedCells cells store) (suffix : Core.Store) :
    InitializedCells cells (store ++ suffix) := by
  intro cell member
  have found := initialized cell member
  have bound : cell.location < store.length := List.getElem?_eq_some_iff.mp found |>.1
  simpa only [Core.Store.read?, List.getElem?_append_left bound] using found

theorem InitializedCells.cons {cells : List InitializedCell} {store : Core.Store}
    (initialized : InitializedCells cells store) (name : String) (type : Core.Ty) (value : Core.Value) :
    InitializedCells (⟨name, type, store.length, value⟩ :: cells) (store ++ [value]) := by
  intro cell member
  cases member with
  | head => simp [Core.Store.read?]
  | tail _ member => exact initialized.appendStore [value] cell member

theorem sharedInitializers_values {depth : Nat} {environment : Core.Environment}
    {context : Code} {values ambient : List Core.Value} {world complete balances : Core.Value}
    (related : CodeValue depth environment context (bundleValues values))
    (length : values.length = 12) (ambientLength : ambient.length = Ambient.slots.length)
    (worldFound : values[7]? = some world) (completeFound : values[9]? = some complete)
    (balancesFound : values[6]? = some balances) (ambientFound : values[10]? = some (bundleValues ambient)) :
    CodeValues depth environment ((AccountRuntime.sharedInitializers context).map (·.2.2))
      ([world, complete, Core.WordMapping.encode [], .word (Core.Word.ofNatModulo 0), balances] ++ ambient) := by
  have ambientRelated : CodeValue depth environment (part 10 12 context) (bundleValues ambient) := by
    simpa only [length] using related.part ambientFound
  have ambientCodes : CodeValues depth environment
      (Ambient.slots.zipIdx.map (fun entry => part entry.2 Ambient.slots.length (part 10 12 context))) ambient := by
    apply CodeValues.of_getElem? (by simpa only [List.length_map, List.length_zipIdx] using ambientLength.symm)
    intro index code value codeFound valueFound
    simp only [List.getElem?_map, List.getElem?_zipIdx, Option.map_map, Nat.zero_add] at codeFound
    obtain ⟨slot, _, same⟩ := Option.map_eq_some_iff.mp codeFound
    subst code
    simpa only [ambientLength, Function.comp_apply] using ambientRelated.part valueFound
  have heads : CodeValues depth environment
      [part 7 12 context, part 9 12 context, empty, number 0, part 6 12 context]
      [world, complete, Core.WordMapping.encode [], .word (Core.Word.ofNatModulo 0), balances] :=
    .cons (by simpa only [length] using related.part worldFound)
      (.cons (by simpa only [length] using related.part completeFound)
        (.cons (CodeValue.empty depth environment)
          (.cons (CodeValue.number 0 depth environment)
            (.cons (by simpa only [length] using related.part balancesFound) .nil))))
  simpa only [AccountRuntime.sharedInitializers, List.map_append, List.map_cons, List.map_nil,
    List.map_map, Function.comp_def] using heads.append ambientCodes

/-- Every emitted shared allocation is executed before its continuation. The
returned references and stored values include the real allocated locations. -/
theorem allocateSharedSlots_initializes
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {initializers : List (String × Core.Ty × Code)} {initialValues : List Core.Value}
    (inputs : CodeValues depth environment (initializers.map (·.2.2)) initialValues)
    {references : AccountRuntime.References} {cells : List InitializedCell}
    (related : RuntimeReferences depth environment references cells)
    (initialized : InitializedCells cells store) :
    ∃ extra suffix finalReferences finalCells,
      RuntimeReferences (depth + extra.length) (extra ++ environment) finalReferences finalCells ∧
      InitializedCells finalCells (store ++ suffix) ∧
      finalCells.map (fun cell => (cell.name, cell.type, cell.value)) =
        ((initializers.zip initialValues).map (fun (entry, value) => (entry.1, entry.2.1, value))).reverse ++
          cells.map (fun cell => (cell.name, cell.type, cell.value)) ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation finalReferences (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateSharedSlots continuation initializers references depth) result finalStore := by
  induction initializers generalizing depth environment store initialValues references cells with
  | nil =>
      cases inputs
      refine ⟨[], [], references, cells, ?_, ?_, rfl, ?_⟩
      · simpa using related
      · simpa using initialized
      · intro continuation result finalStore evaluated
        simpa [AccountRuntime.allocateSharedSlots] using evaluated
  | cons entry rest ih =>
      rcases entry with ⟨name, type, code⟩
      cases inputs with
      | @cons _ value _ values head tail =>
          let reference : Core.Value := .cellRef type store.length
          let bound : Code := fun here => .var (here - depth - 1)
          let cell : InitializedCell := ⟨name, type, store.length, value⟩
          have earlier := related.prepend [reference]
          have nextRelated : RuntimeReferences (depth + 1) (reference :: environment)
              ((name, bound) :: references) (cell :: cells) := by
            refine ⟨congrArg (name :: ·) related.names, .cons ?_ ?_⟩
            · exact CodeValue.bound depth environment reference
            · simpa using earlier.values
          obtain ⟨extra, suffix, finalReferences, finalCells, finalRelated, finalInitialized, description, evaluated⟩ :=
            ih (by simpa using tail.prepend [reference]) nextRelated (initialized.cons name type value)
          refine ⟨extra ++ [reference], [value] ++ suffix, finalReferences, finalCells, ?_, ?_, ?_, ?_⟩
          · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using finalRelated
          · simpa only [List.append_assoc] using finalInitialized
          · simpa only [List.zip_cons_cons, List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append, cell] using description
          · intro continuation result finalStore completed
            apply Core.Evaluates.letE (.newCell (head.evaluates store))
            apply evaluated continuation result finalStore
            simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using completed

def FrameInitializersReady (depth : Nat) (environment : Core.Environment)
    (frame dispatcher gas code codeSize codeKnown : Code) : Prop :=
  ∀ extra name store, ∃ value, Core.Evaluates (extra ++ environment) store
    (AccountRuntime.frameInitial name frame dispatcher gas code codeSize codeKnown (depth + extra.length)) value store

theorem frameInitializers_ready {depth : Nat} {environment : Core.Environment}
    {frame dispatcher gas code codeSize codeKnown : Code} {values : List Core.Value}
    {gasValue codeValue sizeValue knownValue : Core.Value}
    (frameRelated : CodeValue depth environment frame (bundleValues values))
    (length : values.length = 8)
    (gasRelated : CodeValue depth environment gas gasValue)
    (codeRelated : CodeValue depth environment code codeValue)
    (sizeRelated : CodeValue depth environment codeSize sizeValue)
    (knownRelated : CodeValue depth environment codeKnown knownValue) :
    FrameInitializersReady depth environment frame dispatcher gas code codeSize codeKnown := by
  intro extra name store
  have projected : ∀ index, index < 8 → ∃ value, Core.Evaluates (extra ++ environment) store
      (part index 8 frame (depth + extra.length)) value store := by
    intro index bound
    have existsValue := List.getElem?_eq_getElem (l := values) (i := index) (by omega)
    refine ⟨values[index], ?_⟩
    simpa only [length, part] using projectArgument_evaluates (frameRelated extra store) existsValue
  unfold AccountRuntime.frameInitial
  split <;> first
    | exact ⟨_, .construct .unit⟩
    | exact ⟨_, .word⟩
    | exact ⟨_, .inRight .lambda⟩
    | exact ⟨_, gasRelated extra store⟩
    | exact ⟨_, codeRelated extra store⟩
    | exact ⟨_, sizeRelated extra store⟩
    | exact ⟨_, knownRelated extra store⟩
    | exact projected 0 (by decide)
    | exact projected 1 (by decide)
    | exact projected 2 (by decide)
    | exact projected 3 (by decide)
    | exact projected 4 (by decide)
    | exact projected 6 (by decide)
    | exact projected 7 (by decide)

theorem FrameInitializersReady.prepend {depth : Nat} {environment : Core.Environment}
    {frame dispatcher gas code codeSize codeKnown : Code}
    (ready : FrameInitializersReady depth environment frame dispatcher gas code codeSize codeKnown)
    (earlier : Core.Environment) :
    FrameInitializersReady (depth + earlier.length) (earlier ++ environment) frame dispatcher gas code codeSize codeKnown := by
  intro extra name store
  simpa only [List.append_assoc, List.length_append, Nat.add_assoc, Nat.add_comm earlier.length extra.length]
    using ready (extra ++ earlier) name store

def RuntimeCellReady (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (name : String) (type : Core.Ty) (code : Code) : Prop :=
  ∃ cell : InitializedCell, cell.name = name ∧ cell.type = type ∧
    CodeValue depth environment code cell.reference ∧ store.read? cell.location = some cell.value

theorem RuntimeCellReady.extend {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {name : String} {type : Core.Ty} {code : Code}
    (ready : RuntimeCellReady depth environment store name type code)
    (earlier : Core.Environment) (suffix : Core.Store) :
    RuntimeCellReady (depth + earlier.length) (earlier ++ environment) (store ++ suffix) name type code := by
  obtain ⟨cell, named, typed, related, stored⟩ := ready
  refine ⟨cell, named, typed, related.prepend earlier, ?_⟩
  have bound := (List.getElem?_eq_some_iff.mp stored).1
  simpa only [Core.Store.read?, List.getElem?_append_left bound] using stored

def FrameSharedReady (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (slots : List (String × Core.Ty)) (shared : AccountRuntime.References) : Prop :=
  ∀ slot ∈ slots, ∀ name code, shared.find? (·.1 == slot.1) = some (name, code) →
    RuntimeCellReady depth environment store slot.1 slot.2 code

def FrameCreatorReady (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (slots : List (String × Core.Ty)) (creator : Code) : Prop :=
  ∀ type, ("createHandler", type) ∈ slots → RuntimeCellReady depth environment store "createHandler" type creator

/-- The full frame allocator retains shared locations, reuses the creator cell,
and allocates every other slot before passing the actual reference list on. -/
theorem allocateFrameSlots_initializes
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {slots : List (String × Core.Ty)} {shared : AccountRuntime.References}
    {frame dispatcher creator gas code codeSize codeKnown : Code}
    (initializers : FrameInitializersReady depth environment frame dispatcher gas code codeSize codeKnown)
    (sharedReady : FrameSharedReady depth environment store slots shared)
    (creatorReady : FrameCreatorReady depth environment store slots creator)
    {previous : List Code} {previousCells : List InitializedCell}
    (previousRelated : CodeValues depth environment previous (previousCells.map InitializedCell.reference))
    (previousStored : InitializedCells previousCells store) :
    ∃ extra suffix references cells,
      CodeValues (depth + extra.length) (extra ++ environment) references
        ((previousCells.reverse ++ cells).map InitializedCell.reference) ∧
      InitializedCells (previousCells.reverse ++ cells) (store ++ suffix) ∧
      cells.map (fun cell => (cell.name, cell.type)) = slots ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation references (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateFrameSlots shared frame dispatcher creator gas code codeSize codeKnown
            continuation slots previous depth) result finalStore := by
  induction slots generalizing depth environment store previous previousCells with
  | nil =>
      refine ⟨[], [], previous.reverse, [], ?_, ?_, rfl, ?_⟩
      · simpa only [List.length_nil, Nat.add_zero, List.nil_append, List.append_nil, List.map_reverse]
          using previousRelated.reverse
      · intro cell member
        simpa only [List.append_nil] using previousStored cell (by simpa using member)
      · intro continuation result finalStore evaluated
        simpa only [List.length_nil, Nat.add_zero, List.nil_append, List.append_nil,
          AccountRuntime.allocateFrameSlots] using evaluated
  | cons slot rest ih =>
      rcases slot with ⟨name, type⟩
      have sharedTail : FrameSharedReady depth environment store rest shared := by
        intro slot member
        exact sharedReady slot (.tail _ member)
      have creatorTail : FrameCreatorReady depth environment store rest creator := by
        intro type member
        exact creatorReady type (.tail _ member)
      cases found : shared.find? (·.1 == name) with
      | some entry =>
          rcases entry with ⟨foundName, reference⟩
          obtain ⟨cell, named, typed, related, stored⟩ := sharedReady (name, type) (.head _) foundName reference found
          have storedCons : InitializedCells (cell :: previousCells) store := by
            intro selected member
            cases member with
            | head => exact stored
            | tail _ member => exact previousStored selected member
          obtain ⟨extra, suffix, references, cells, related', stored', signature, evaluated⟩ :=
            ih initializers sharedTail creatorTail (.cons related previousRelated) storedCons
          refine ⟨extra, suffix, references, cell :: cells, ?_, ?_, ?_, ?_⟩
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using related'
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using stored'
          · simp only [List.map_cons, named, typed, signature]
          · intro continuation result finalStore completed
            simpa only [AccountRuntime.allocateFrameSlots, found] using evaluated continuation result finalStore completed
      | none =>
          by_cases isCreator : name == "createHandler"
          · have named : name = "createHandler" := by simpa only [beq_iff_eq] using isCreator
            subst name
            obtain ⟨cell, named, typed, related, stored⟩ := creatorReady type (.head _)
            have storedCons : InitializedCells (cell :: previousCells) store := by
              intro selected member
              cases member with
              | head => exact stored
              | tail _ member => exact previousStored selected member
            obtain ⟨extra, suffix, references, cells, related', stored', signature, evaluated⟩ :=
              ih initializers sharedTail creatorTail (.cons related previousRelated) storedCons
            refine ⟨extra, suffix, references, cell :: cells, ?_, ?_, ?_, ?_⟩
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using related'
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using stored'
            · simp only [List.map_cons, named, typed, signature]
            · intro continuation result finalStore completed
              simpa only [AccountRuntime.allocateFrameSlots, found, beq_self_eq_true, ↓reduceIte]
                using evaluated continuation result finalStore completed
          · obtain ⟨value, initialized⟩ := initializers [] name store
            have initialized' : Core.Evaluates environment store
                (AccountRuntime.frameInitial name frame dispatcher gas code codeSize codeKnown depth) value store := by
              simpa using initialized
            let reference : Core.Value := .cellRef type store.length
            let cell : InitializedCell := ⟨name, type, store.length, value⟩
            have sharedTail' : FrameSharedReady (depth + 1) (reference :: environment) (store ++ [value]) rest shared := by
              intro slot member foundName foundCode found'
              simpa using (sharedTail slot member foundName foundCode found').extend [reference] [value]
            have creatorTail' : FrameCreatorReady (depth + 1) (reference :: environment) (store ++ [value]) rest creator := by
              intro type member
              simpa using (creatorTail type member).extend [reference] [value]
            have relatedCons : CodeValues (depth + 1) (reference :: environment)
                ((fun here => .var (here - depth - 1)) :: previous) ((cell :: previousCells).map InitializedCell.reference) :=
              .cons (CodeValue.bound depth environment reference) (by simpa using previousRelated.prepend [reference])
            obtain ⟨extra, suffix, references, cells, related', stored', signature, evaluated⟩ :=
              ih (by simpa using initializers.prepend [reference]) sharedTail' creatorTail'
                relatedCons (previousStored.cons name type value)
            refine ⟨extra ++ [reference], [value] ++ suffix, references, cell :: cells, ?_, ?_, ?_, ?_⟩
            · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1, List.reverse_cons] using related'
            · simpa [List.append_assoc, List.reverse_cons] using stored'
            · exact congrArg ((name, type) :: ·) signature
            · intro continuation result finalStore completed
              simp only [AccountRuntime.allocateFrameSlots, found, isCreator]
              apply Core.Evaluates.letE (.newCell initialized')
              apply evaluated continuation result finalStore
              simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using completed

def initialMemoryCell (store : Core.Store) : InitializedCell :=
  ⟨"memory", Core.WordMapping.type, store.length, Core.WordMapping.encode []⟩

def initialSizeCell (store : Core.Store) : InitializedCell :=
  ⟨"memorySize", .word, store.length + 1, .word (Core.Word.ofNatModulo 0)⟩

/-- The runtime's first two frame cells establish empty memory and size zero.
The remaining real allocations preserve those cells and supply every actual
frame argument to the continuation. -/
theorem allocateFrame_memory_initializes
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {slots : List (String × Core.Ty)} {shared : AccountRuntime.References}
    {frame dispatcher creator gas code codeSize codeKnown : Code}
    (initializers : FrameInitializersReady depth environment frame dispatcher gas code codeSize codeKnown)
    (sharedReady : FrameSharedReady depth environment store slots shared)
    (creatorReady : FrameCreatorReady depth environment store slots creator)
    (memoryAbsent : shared.find? (·.1 == "memory") = none)
    (sizeAbsent : shared.find? (·.1 == "memorySize") = none) :
    ∃ extra suffix references cells,
      CodeValues (depth + extra.length) (extra ++ environment) references
        ((initialMemoryCell store :: initialSizeCell store :: cells).map InitializedCell.reference) ∧
      InitializedCells (initialMemoryCell store :: initialSizeCell store :: cells) (store ++ suffix) ∧
      cells.map (fun cell => (cell.name, cell.type)) = slots ∧
      MemoryCorrespondence.StateRel store.length (store.length + 1) ⟨[], Core.Word.ofNatModulo 0⟩ (store ++ suffix) ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation references (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateFrame (("memory", Core.WordMapping.type) :: ("memorySize", .word) :: slots)
            shared frame dispatcher creator gas code codeSize codeKnown continuation depth) result finalStore := by
  let memoryValue := Core.WordMapping.encode []
  let sizeValue := Core.Value.word (Core.Word.ofNatModulo 0)
  let memoryReference := (initialMemoryCell store).reference
  let sizeReference := (initialSizeCell store).reference
  let previous : List Code :=
    [fun here => .var (here - (depth + 1) - 1), fun here => .var (here - depth - 1)]
  have sharedReady' : FrameSharedReady (depth + 2) (sizeReference :: memoryReference :: environment)
      (store ++ [memoryValue, sizeValue]) slots shared := by
    intro slot member name code found
    simpa using (sharedReady slot member name code found).extend [sizeReference, memoryReference] [memoryValue, sizeValue]
  have creatorReady' : FrameCreatorReady (depth + 2) (sizeReference :: memoryReference :: environment)
      (store ++ [memoryValue, sizeValue]) slots creator := by
    intro type member
    simpa using (creatorReady type member).extend [sizeReference, memoryReference] [memoryValue, sizeValue]
  have previousRelated : CodeValues (depth + 2) (sizeReference :: memoryReference :: environment) previous
      ([initialSizeCell store, initialMemoryCell store].map InitializedCell.reference) := by
    refine .cons ?_ (.cons ?_ .nil)
    · simpa [Nat.add_assoc] using CodeValue.bound (depth + 1) (memoryReference :: environment) sizeReference
    · simpa [Nat.add_assoc] using (CodeValue.bound depth environment memoryReference).prepend [sizeReference]
  have previousStored : InitializedCells [initialSizeCell store, initialMemoryCell store]
      (store ++ [memoryValue, sizeValue]) := by
    intro cell member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [initialSizeCell, initialMemoryCell, Core.Store.read?,
      memoryValue, sizeValue]
  obtain ⟨extra, suffix, references, cells, related, stored, signature, evaluated⟩ :=
    allocateFrameSlots_initializes
      (by simpa using initializers.prepend [sizeReference, memoryReference]) sharedReady' creatorReady'
      previousRelated previousStored
  have initialized : InitializedCells (initialMemoryCell store :: initialSizeCell store :: cells)
      (store ++ ([memoryValue, sizeValue] ++ suffix)) := by
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.append_assoc, List.cons_append] using stored
  refine ⟨extra ++ [sizeReference, memoryReference], [memoryValue, sizeValue] ++ suffix, references, cells,
    ?_, initialized, signature, ?_, ?_⟩
  · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 2, List.reverse_cons] using related
  · exact ⟨by omega, initialized _ (.head _), initialized _ (.tail _ (.head _))⟩
  · intro continuation result finalStore completed
    simp only [AccountRuntime.allocateFrame, AccountRuntime.allocateFrameSlots, memoryAbsent, sizeAbsent]
    apply Core.Evaluates.letE (.newCell (.construct .unit))
    apply Core.Evaluates.letE (.newCell .word)
    have continued := evaluated continuation result finalStore
      (by simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 2] using completed)
    simpa [previous, memoryReference, sizeReference, initialMemoryCell, initialSizeCell,
      InitializedCell.reference, Core.Store.allocate, Nat.add_assoc, memoryValue, sizeValue, Core.WordMapping.encode] using continued

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeFrameInitializationFacts
/-! Frame initialization records the values and disjoint locations needed by
public execution, as well as evaluating the actual allocation builders. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

def FrameInitializersValid (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (frame dispatcher gas code codeSize codeKnown : Code) (shared : AccountRuntime.References) (property : InitializedCell → Prop) : Prop :=
  ∀ extra suffix name type, shared.find? (·.1 == name) = none → ∃ value, Core.Evaluates (extra ++ environment) (store ++ suffix)
    (AccountRuntime.frameInitial name frame dispatcher gas code codeSize codeKnown (depth + extra.length))
      value (store ++ suffix) ∧ property ⟨name, type, (store ++ suffix).length, value⟩

theorem FrameInitializersValid.extend {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {frame dispatcher gas code codeSize codeKnown : Code} {shared : AccountRuntime.References} {property : InitializedCell → Prop}
    (valid : FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared property)
    (earlier : Core.Environment) (suffix : Core.Store) :
    FrameInitializersValid (depth + earlier.length) (earlier ++ environment) (store ++ suffix)
      frame dispatcher gas code codeSize codeKnown shared property := by
  intro extra later name type absent
  simpa only [List.append_assoc, List.length_append, Nat.add_assoc, Nat.add_comm earlier.length extra.length]
    using valid (extra ++ earlier) (suffix ++ later) name type absent

def RuntimeCellValid (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (name : String) (type : Core.Ty) (code : Code) (property : InitializedCell → Prop) : Prop :=
  ∃ cell : InitializedCell, cell.name = name ∧ cell.type = type ∧
    CodeValue depth environment code cell.reference ∧ store.read? cell.location = some cell.value ∧ property cell

theorem RuntimeCellValid.extend {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {name : String} {type : Core.Ty} {code : Code} {property : InitializedCell → Prop}
    (valid : RuntimeCellValid depth environment store name type code property)
    (earlier : Core.Environment) (suffix : Core.Store) :
    RuntimeCellValid (depth + earlier.length) (earlier ++ environment) (store ++ suffix) name type code property := by
  obtain ⟨cell, named, typed, related, stored, property⟩ := valid
  refine ⟨cell, named, typed, related.prepend earlier, ?_, property⟩
  have bound := (List.getElem?_eq_some_iff.mp stored).1
  simpa only [Core.Store.read?, List.getElem?_append_left bound] using stored

def FrameSharedValid (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (slots : List (String × Core.Ty)) (shared : AccountRuntime.References) (property : InitializedCell → Prop) : Prop :=
  ∀ slot ∈ slots, ∀ name code, shared.find? (·.1 == slot.1) = some (name, code) →
    RuntimeCellValid depth environment store slot.1 slot.2 code property

def FrameCreatorValid (depth : Nat) (environment : Core.Environment) (store : Core.Store)
    (slots : List (String × Core.Ty)) (creator : Code) (property : InitializedCell → Prop) : Prop :=
  ∀ type, ("createHandler", type) ∈ slots → RuntimeCellValid depth environment store "createHandler" type creator property

theorem allocateFrameSlots_validates
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {slots : List (String × Core.Ty)} {shared : AccountRuntime.References}
    {frame dispatcher creator gas code codeSize codeKnown : Code}
    {property : InitializedCell → Prop}
    (initializers : FrameInitializersValid depth environment store frame dispatcher gas code codeSize codeKnown shared property)
    (sharedReady : FrameSharedValid depth environment store slots shared property)
    (creatorReady : FrameCreatorValid depth environment store slots creator property)
    {previous : List Code} {previousCells : List InitializedCell}
    (previousRelated : CodeValues depth environment previous (previousCells.map InitializedCell.reference))
    (previousStored : InitializedCells previousCells store)
    (previousValid : ∀ cell ∈ previousCells, property cell) :
    ∃ extra suffix references cells,
      CodeValues (depth + extra.length) (extra ++ environment) references
        ((previousCells.reverse ++ cells).map InitializedCell.reference) ∧
      InitializedCells (previousCells.reverse ++ cells) (store ++ suffix) ∧
      cells.map (fun cell => (cell.name, cell.type)) = slots ∧
      (∀ cell ∈ previousCells.reverse ++ cells, property cell) ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation references (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateFrameSlots shared frame dispatcher creator gas code codeSize codeKnown
            continuation slots previous depth) result finalStore := by
  induction slots generalizing depth environment store previous previousCells with
  | nil =>
      refine ⟨[], [], previous.reverse, [], ?_, ?_, rfl, ?_, ?_⟩
      · simpa only [List.length_nil, Nat.add_zero, List.nil_append, List.append_nil, List.map_reverse]
          using previousRelated.reverse
      · intro cell member
        simpa only [List.append_nil] using previousStored cell (by simpa using member)
      · intro cell member
        exact previousValid cell (by simpa using member)
      · intro continuation result finalStore evaluated
        simpa only [List.length_nil, Nat.add_zero, List.nil_append, List.append_nil,
          AccountRuntime.allocateFrameSlots] using evaluated
  | cons slot rest ih =>
      rcases slot with ⟨name, type⟩
      have sharedTail : FrameSharedValid depth environment store rest shared property := by
        intro slot member
        exact sharedReady slot (.tail _ member)
      have creatorTail : FrameCreatorValid depth environment store rest creator property := by
        intro type member
        exact creatorReady type (.tail _ member)
      cases found : shared.find? (·.1 == name) with
      | some entry =>
          rcases entry with ⟨foundName, reference⟩
          obtain ⟨cell, named, typed, related, stored, valid⟩ := sharedReady (name, type) (.head _) foundName reference found
          have storedCons : InitializedCells (cell :: previousCells) store := by
            intro selected member
            cases member with
            | head => exact stored
            | tail _ member => exact previousStored selected member
          obtain ⟨extra, suffix, references, cells, related', stored', signature, valid', evaluated⟩ :=
            ih initializers sharedTail creatorTail (.cons related previousRelated) storedCons
                (by intro selected member; cases member with
                    | head => exact valid
                    | tail _ member => exact previousValid selected member)
          refine ⟨extra, suffix, references, cell :: cells, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using related'
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using stored'
          · simp only [List.map_cons, named, typed, signature]
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valid'
          · intro continuation result finalStore completed
            simpa only [AccountRuntime.allocateFrameSlots, found] using evaluated continuation result finalStore completed
      | none =>
          by_cases isCreator : name == "createHandler"
          · have named : name = "createHandler" := by simpa only [beq_iff_eq] using isCreator
            subst name
            obtain ⟨cell, named, typed, related, stored, valid⟩ := creatorReady type (.head _)
            have storedCons : InitializedCells (cell :: previousCells) store := by
              intro selected member
              cases member with
              | head => exact stored
              | tail _ member => exact previousStored selected member
            obtain ⟨extra, suffix, references, cells, related', stored', signature, valid', evaluated⟩ :=
              ih initializers sharedTail creatorTail (.cons related previousRelated) storedCons
                (by intro selected member; cases member with
                    | head => exact valid
                    | tail _ member => exact previousValid selected member)
            refine ⟨extra, suffix, references, cell :: cells, ?_, ?_, ?_, ?_, ?_⟩
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using related'
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using stored'
            · simp only [List.map_cons, named, typed, signature]
            · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valid'
            · intro continuation result finalStore completed
              simpa only [AccountRuntime.allocateFrameSlots, found, beq_self_eq_true, ↓reduceIte]
                using evaluated continuation result finalStore completed
          · obtain ⟨value, initialized, valid⟩ := initializers [] [] name type found
            have initialized' : Core.Evaluates environment store
                (AccountRuntime.frameInitial name frame dispatcher gas code codeSize codeKnown depth) value store := by
              simpa using initialized
            let reference : Core.Value := .cellRef type store.length
            let cell : InitializedCell := ⟨name, type, store.length, value⟩
            have sharedTail' : FrameSharedValid (depth + 1) (reference :: environment) (store ++ [value]) rest shared property := by
              intro slot member foundName foundCode found'
              simpa using (sharedTail slot member foundName foundCode found').extend [reference] [value]
            have creatorTail' : FrameCreatorValid (depth + 1) (reference :: environment) (store ++ [value]) rest creator property := by
              intro type member
              simpa using (creatorTail type member).extend [reference] [value]
            have relatedCons : CodeValues (depth + 1) (reference :: environment)
                ((fun here => .var (here - depth - 1)) :: previous) ((cell :: previousCells).map InitializedCell.reference) :=
              .cons (CodeValue.bound depth environment reference) (by simpa using previousRelated.prepend [reference])
            obtain ⟨extra, suffix, references, cells, related', stored', signature, valid', evaluated⟩ :=
              ih (by simpa using initializers.extend [reference] [value]) sharedTail' creatorTail'
                relatedCons (previousStored.cons name type value)
                (by intro selected member; cases member with
                    | head => simpa only [List.append_nil] using valid
                    | tail _ member => exact previousValid selected member)
            refine ⟨extra ++ [reference], [value] ++ suffix, references, cell :: cells, ?_, ?_, ?_, ?_, ?_⟩
            · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1, List.reverse_cons] using related'
            · simpa [List.append_assoc, List.reverse_cons] using stored'
            · exact congrArg ((name, type) :: ·) signature
            · simpa [List.append_assoc, List.reverse_cons] using valid'
            · intro continuation result finalStore completed
              simp only [AccountRuntime.allocateFrameSlots, found, isCreator]
              apply Core.Evaluates.letE (.newCell initialized')
              apply evaluated continuation result finalStore
              simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using completed

theorem allocateFrame_memory_validates
    {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {slots : List (String × Core.Ty)} {shared : AccountRuntime.References}
    {frame dispatcher creator gas code codeSize codeKnown : Code}
    {property : InitializedCell → Prop}
    (initializers : FrameInitializersValid depth environment
      (store ++ [Core.WordMapping.encode [], .word (Core.Word.ofNatModulo 0)])
      frame dispatcher gas code codeSize codeKnown shared property)
    (sharedReady : FrameSharedValid depth environment store slots shared property)
    (creatorReady : FrameCreatorValid depth environment store slots creator property)
    (memoryAbsent : shared.find? (·.1 == "memory") = none)
    (sizeAbsent : shared.find? (·.1 == "memorySize") = none)
    (memoryValid : property (initialMemoryCell store)) (sizeValid : property (initialSizeCell store)) :
    ∃ extra suffix references cells,
      CodeValues (depth + extra.length) (extra ++ environment) references
        ((initialMemoryCell store :: initialSizeCell store :: cells).map InitializedCell.reference) ∧
      InitializedCells (initialMemoryCell store :: initialSizeCell store :: cells) (store ++ suffix) ∧
      cells.map (fun cell => (cell.name, cell.type)) = slots ∧
      (∀ cell ∈ initialMemoryCell store :: initialSizeCell store :: cells, property cell) ∧
      MemoryCorrespondence.StateRel store.length (store.length + 1) ⟨[], Core.Word.ofNatModulo 0⟩ (store ++ suffix) ∧
      ∀ continuation result finalStore,
        Core.Evaluates (extra ++ environment) (store ++ suffix)
          (continuation references (depth + extra.length)) result finalStore →
        Core.Evaluates environment store
          (AccountRuntime.allocateFrame (("memory", Core.WordMapping.type) :: ("memorySize", .word) :: slots)
            shared frame dispatcher creator gas code codeSize codeKnown continuation depth) result finalStore := by
  let memoryValue := Core.WordMapping.encode []
  let sizeValue := Core.Value.word (Core.Word.ofNatModulo 0)
  let memoryReference := (initialMemoryCell store).reference
  let sizeReference := (initialSizeCell store).reference
  let previous : List Code :=
    [fun here => .var (here - (depth + 1) - 1), fun here => .var (here - depth - 1)]
  have sharedReady' : FrameSharedValid (depth + 2) (sizeReference :: memoryReference :: environment)
      (store ++ [memoryValue, sizeValue]) slots shared property := by
    intro slot member name code found
    simpa using (sharedReady slot member name code found).extend [sizeReference, memoryReference] [memoryValue, sizeValue]
  have creatorReady' : FrameCreatorValid (depth + 2) (sizeReference :: memoryReference :: environment)
      (store ++ [memoryValue, sizeValue]) slots creator property := by
    intro type member
    simpa using (creatorReady type member).extend [sizeReference, memoryReference] [memoryValue, sizeValue]
  have previousRelated : CodeValues (depth + 2) (sizeReference :: memoryReference :: environment) previous
      ([initialSizeCell store, initialMemoryCell store].map InitializedCell.reference) := by
    refine .cons ?_ (.cons ?_ .nil)
    · simpa [Nat.add_assoc] using CodeValue.bound (depth + 1) (memoryReference :: environment) sizeReference
    · simpa [Nat.add_assoc] using (CodeValue.bound depth environment memoryReference).prepend [sizeReference]
  have previousStored : InitializedCells [initialSizeCell store, initialMemoryCell store]
      (store ++ [memoryValue, sizeValue]) := by
    intro cell member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [initialSizeCell, initialMemoryCell, Core.Store.read?,
      memoryValue, sizeValue]
  obtain ⟨extra, suffix, references, cells, related, stored, signature, valid, evaluated⟩ :=
    allocateFrameSlots_validates
      (by simpa using initializers.extend [sizeReference, memoryReference] []) sharedReady' creatorReady'
      previousRelated previousStored
      (by intro cell member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact sizeValid
          · exact memoryValid)
  have initialized : InitializedCells (initialMemoryCell store :: initialSizeCell store :: cells)
      (store ++ ([memoryValue, sizeValue] ++ suffix)) := by
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.append_assoc, List.cons_append] using stored
  refine ⟨extra ++ [sizeReference, memoryReference], [memoryValue, sizeValue] ++ suffix, references, cells,
    ?_, initialized, signature, ?_, ?_, ?_⟩
  · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 2, List.reverse_cons] using related
  · simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.append_assoc, List.cons_append] using valid
  · exact ⟨by omega, initialized _ (.head _), initialized _ (.tail _ (.head _))⟩
  · intro continuation result finalStore completed
    simp only [AccountRuntime.allocateFrame, AccountRuntime.allocateFrameSlots, memoryAbsent, sizeAbsent]
    apply Core.Evaluates.letE (.newCell (.construct .unit))
    apply Core.Evaluates.letE (.newCell .word)
    have continued := evaluated continuation result finalStore
      (by simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 2] using completed)
    simpa [previous, memoryReference, sizeReference, initialMemoryCell, initialSizeCell,
      InitializedCell.reference, Core.Store.allocate, Nat.add_assoc, memoryValue, sizeValue, Core.WordMapping.encode] using continued

end Solcore.Frontend.RustHull.Correspondence
end

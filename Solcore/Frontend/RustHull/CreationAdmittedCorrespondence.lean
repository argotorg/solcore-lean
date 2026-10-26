import Solcore.Frontend.RustHull.CreationAddressCorrespondence
import Solcore.Frontend.RustHull.CreationHandlerCorrespondence
import Solcore.Frontend.RustHull.AccountCallSharedCorrespondence
import Solcore.Frontend.RustHull.MemoryCopyCorrespondence
import Solcore.Frontend.RustHull.CreationSemantics

/-! The installed create handler completes admitted attempts that run no init
frame. The actual dispatcher derives the address, advances the creator nonce,
loads its checkpoint and examines the target: a nonzero nonce or code size is a
collision that returns zero, and an address absent from a complete world
receives a new account, the endowment and the empty runtime image. An unknown
target and an endowment overflow fail with reasons 7 and 12; the protection
then runs the checkpoint's restoration, so only the nonce advance remains.
Catalog code links survive every outcome. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationCorrespondence
open Core Correspondence ScalarExecution CodeBuilder AccountCallCorrespondence

theorem bundle_evaluates {environment : Environment} {store : Store} :
    ∀ {expressions : List Core.Expr} {values : List Value}, expressions.length = values.length →
      (∀ (index : Nat) (expression : Core.Expr) (value : Value), expressions[index]? = some expression →
        values[index]? = some value → Evaluates environment store expression value store) →
      Evaluates environment store (bundle expressions) (bundleValues values) store
  | [], [], _, _ => .unit
  | [expression], [value], _, each => each 0 expression value rfl rfl
  | expression :: next :: rest, value :: nextValue :: restValues, same, each =>
      .pair (each 0 expression value rfl rfl)
        (bundle_evaluates (expressions := next :: rest) (values := nextValue :: restValues)
          (by simpa using same) (fun index => each (index + 1)))
  | [], _ :: _, same, _ => by simp at same
  | _ :: _, [], same, _ => by simp at same
  | [_], _ :: _ :: _, same, _ => by simp at same
  | _ :: _ :: _, [_], same, _ => by simp at same

/-- `AccountState.replace` over an evaluated nine-field record. -/
theorem replace_evaluates {environment : Environment} {store : Store} {recordExpr valueExpr : Core.Expr}
    {fields : List Value} {value : Value} (index : Nat) (nine : fields.length = 9)
    (recordEvaluated : Evaluates environment store recordExpr (bundleValues fields) store)
    (valueEvaluated : Evaluates environment store valueExpr value store) :
    Evaluates environment store (AccountState.replace recordExpr index valueExpr)
      (bundleValues (fields.set index value)) store := by
  unfold AccountState.replace
  apply bundle_evaluates (by simp [nine])
  intro item expression result expressionFound valueFound
  have itemSmall : item < 9 := by
    have := (List.getElem?_eq_some_iff.mp expressionFound).1
    simpa using this
  simp only [List.getElem?_map, List.getElem?_range itemSmall, Option.map_some, Option.some.injEq] at expressionFound
  subst expressionFound
  by_cases same : item = index
  · subst same
    rw [List.getElem?_set_self (by omega), Option.some.injEq] at valueFound
    subst valueFound
    simpa using valueEvaluated
  · rw [List.getElem?_set_ne (Ne.symm same)] at valueFound
    have different : (item == index) = false := beq_eq_false_iff_ne.mpr same
    simp only [different, Bool.false_eq_true, ↓reduceIte, AccountState.field]
    rw [← nine]
    exact projectArgument_evaluates recordEvaluated valueFound

def fields (account : AccountState.Account) (identity : Nat) : List Value :=
  [WordMapping.encode account.storage, WordMapping.encode account.transient,
    .word account.nonce, .word (Word.ofNatModulo identity),
    WordMapping.encode (Memory.packBytes (account.code.getD [])),
    .word (Word.ofNatModulo (account.code.getD []).length),
    .bool account.code.isSome, .bool account.created, .bool account.destroyed]

theorem fields_record (account : AccountState.Account) (identity : Nat) :
    bundleValues (fields account identity) = StorageCorrespondence.record account identity := rfl

theorem fields_length (account : AccountState.Account) (identity : Nat) : (fields account identity).length = 9 := rfl

/-- The address scheme a request selects. -/
def Request.scheme (request : Request) : CreationAddressSemantics.Scheme :=
  if request.create2 then .create2 request.salt else .create

theorem deriveAddress_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {creatorCode nonceCode requestCode : Code} {creator nonce target : Word} {request : Request}
    (creatorValue : CodeValue depth environment creatorCode (.word creator))
    (nonceValue : CodeValue depth environment nonceCode (.word nonce))
    (requested : CodeValue depth environment requestCode (requestValue request))
    (bounded : request.initLength.val ≤ 49152)
    (derived : CreationAddressSemantics.Derived creator nonce request.initCode request.initLength
      request.scheme target) :
    ∃ next, Evaluates environment store (CreationImplementation.deriveAddress creatorCode nonceCode requestCode depth)
      (.inRight .word (.word target)) next ∧ StoreRetains store next := by
  unfold CreationImplementation.deriveAddress
  have flag : Evaluates environment store (part 3 8 requestCode depth) (.bool request.create2) store :=
    (requested.part (index := 3) rfl).evaluates store
  cases create2 : request.create2 with
  | false =>
      rw [create2] at flag
      simp only [Request.scheme, create2, Bool.false_eq_true, ↓reduceIte] at derived
      cases derived with
      | create hashed =>
          obtain ⟨final, evaluated, retained⟩ := CreationAddressCorrespondence.createAddress_evaluates
            (.pair (creatorValue.evaluates store) (nonceValue.evaluates store)) hashed
          exact ⟨final, .ifFalse flag evaluated, retained⟩
  | true =>
      rw [create2] at flag
      simp only [Request.scheme, create2, ↓reduceIte] at derived
      cases derived with
      | create2 initHashed hashed =>
          let initRef := Value.cellRef WordMapping.type store.length
          let sizeRef := Value.cellRef .word (store.length + 1)
          let allocated : Store := store ++ [WordMapping.encode request.initCode, .word (Word.ofNatModulo 0)]
          have initRelated : MemoryCorrespondence.StateRel store.length (store.length + 1)
              ⟨request.initCode, Word.ofNatModulo 0⟩ allocated := by
            refine ⟨by omega, ?_, ?_⟩ <;> simp [allocated, Store.read?]
          have memoryValue := (CodeValue.bound depth environment initRef).prepend [sizeRef]
          have sizeValue := CodeValue.bound (depth + 1) (initRef :: environment) sizeRef
          have argumentsEvaluated := Evaluates.pair (memoryValue.evaluates allocated)
            (.pair (sizeValue.evaluates allocated) (.pair ((creatorValue.prepend [sizeRef, initRef]).evaluates allocated)
              (.pair (((requested.part (index := 2) rfl).prepend [sizeRef, initRef]).evaluates allocated)
                (.pair (Evaluates.word (value := Word.ofNatModulo 0))
                  (((requested.part (index := 7) rfl).prepend [sizeRef, initRef]).evaluates allocated)))))
          obtain ⟨final, evaluated, frame⟩ := CreationAddressCorrespondence.create2Address_evaluates
            argumentsEvaluated initRelated bounded initHashed hashed
          refine ⟨final, .ifTrue flag ?_, CreationAddressCorrespondence.scratch_retains frame⟩
          apply Evaluates.letE (bodyStore := store ++ [WordMapping.encode request.initCode])
          · exact .newCell ((requested.part (index := 6) rfl).evaluates store)
          · apply Evaluates.letE (bodyStore := allocated)
            · simpa only [allocated, List.length_append, List.length_cons, List.length_nil, List.append_assoc,
                List.cons_append, List.nil_append, CodeBuilder.allocate, CodeBuilder.number, CodeBuilder.constant] using
                (Evaluates.newCell (elementType := .word) (environment := initRef :: environment)
                  (initialStore := store ++ [WordMapping.encode request.initCode]) Evaluates.word
                  (initialValue := .word (Word.ofNatModulo 0)))
            · exact evaluated

theorem putStore_extension (accounts : StorageCorrespondence.Accounts) (address : Word) (account : AccountState.Account)
    (identity : Nat) (environment : Environment) (store : Store) :
    ∃ suffix, StorageCorrespondence.putStore accounts address account identity environment store = store ++ suffix :=
  ⟨_, rfl⟩

/-- Writes that change one cell and append helper cells. -/
structure Overwrites (location : Nat) (initial final : Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ other value, other ≠ location → initial.read? other = some value → final.read? other = some value

theorem Overwrites.append (location : Nat) (store suffix : Store) : Overwrites location store (store ++ suffix) :=
  ⟨by simp, fun _ _ _ found => StorageCorrespondence.appended_read found _⟩

theorem Overwrites.set {location : Nat} {initial final : Store} (overwrites : Overwrites location initial final)
    (value : Value) : Overwrites location initial (final.set location value) :=
  ⟨by simpa using overwrites.length_le, fun other old different found => by
    change (final.set location value)[other]? = some old
    rw [List.getElem?_set_ne (Ne.symm different)]
    exact overwrites.read other old different found⟩

theorem Overwrites.trans {location : Nat} {initial middle final : Store}
    (first : Overwrites location initial middle) (second : Overwrites location middle final) :
    Overwrites location initial final :=
  ⟨Nat.le_trans first.length_le second.length_le, fun other value different found =>
    second.read other value different (first.read other value different found)⟩

theorem Overwrites.ofRetains {location : Nat} {initial final : Store} (retained : StoreRetains initial final) :
    Overwrites location initial final :=
  ⟨retained.length_le, fun other _ _ found =>
    (retained.read other (List.getElem?_eq_some_iff.mp found).1).trans found⟩

/-- The actual nonce write: read the account, replace field 2, store the world. -/
theorem writeNonce_evaluates {environment : Environment} {initial store : Store}
    {worldReference addressExpr completeExpr valueExpr : Core.Expr}
    (accounts : StorageCorrespondence.Accounts) (location : Nat) (address : Word) (complete : Bool) (nonce : Word)
    (arguments : Evaluates environment initial (bundle [worldReference, addressExpr, completeExpr, valueExpr])
      (bundleValues [.cellRef AccountState.type location, .word address, .bool complete, .word nonce]) store)
    (found : store.read? location = some (StorageCorrespondence.world accounts))
    {account : AccountState.Account} {identity : Nat}
    (obtained : StorageCorrespondence.get accounts address complete = .ok (account, identity)) :
    ∃ next, Evaluates environment initial (AccountState.writeField worldReference addressExpr completeExpr 2 valueExpr)
        (.inRight .word .unit) next ∧
      next.read? location = some (StorageCorrespondence.world
        (StorageCorrespondence.put address {account with nonce := nonce} identity accounts)) ∧
      Overwrites location store next := by
  let argumentValue := bundleValues [.cellRef AccountState.type location, .word address, .bool complete, .word nonce]
  have fetched := StorageCorrespondence.get_evaluates
    (environment := argumentValue :: environment)
    (initial := store) (worldStore := store) (addressStore := store) (final := store)
    (worldExpr := .loadCell (.first (.var 0)))
    (addressExpr := .first (.second (.var 0)))
    (completeExpr := .first (.second (.second (.var 0)))) accounts address complete
    (.loadCell (.first (.var rfl)) found)
    (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
  rw [obtained] at fetched
  let fetchedStore := StorageCorrespondence.getStore accounts address complete (argumentValue :: environment) store
  obtain ⟨fetchedSuffix, _, fetchedSame⟩ := StorageCorrespondence.getStore_extension accounts address complete
    (argumentValue :: environment) store
  have current : fetchedStore.read? location = some (StorageCorrespondence.world accounts) := by
    change (StorageCorrespondence.getStore accounts address complete (argumentValue :: environment) store).read? location = _
    rw [fetchedSame]
    exact StorageCorrespondence.appended_read found _
  let updatedAccount : AccountState.Account := {account with nonce := nonce}
  have updated := StorageCorrespondence.put_evaluates
    (environment := StorageCorrespondence.record account identity :: argumentValue :: environment)
    (initial := fetchedStore) (mappingStore := fetchedStore) (addressStore := fetchedStore) (final := fetchedStore)
    (mapping := .loadCell (projectArgument 0 4 (.var 1)))
    (addressExpr := projectArgument 1 4 (.var 1))
    (accountExpr := AccountState.replace (.var 0) 2 (projectArgument 3 4 (.var 1)))
    accounts address updatedAccount identity
    (.loadCell (.first (.var rfl)) current) (.first (.second (.var rfl)))
    (replace_evaluates (fields := fields account identity) 2 rfl (.var rfl) (.second (.second (.second (.var rfl)))))
  let putStore := StorageCorrespondence.putStore accounts address updatedAccount identity
    (StorageCorrespondence.record account identity :: argumentValue :: environment) fetchedStore
  obtain ⟨putSuffix, putSame⟩ := putStore_extension accounts address updatedAccount identity
    (StorageCorrespondence.record account identity :: argumentValue :: environment) fetchedStore
  have latest : putStore.read? location = some (StorageCorrespondence.world accounts) := by
    change (StorageCorrespondence.putStore accounts address updatedAccount identity _ fetchedStore).read? location = _
    rw [putSame]
    exact StorageCorrespondence.appended_read current _
  have overwrites : Overwrites location store putStore := by
    change Overwrites location store (StorageCorrespondence.putStore accounts address updatedAccount identity _ fetchedStore)
    rw [putSame]
    change Overwrites location store ((StorageCorrespondence.getStore accounts address complete _ store) ++ putSuffix)
    rw [fetchedSame, List.append_assoc]
    exact Overwrites.append location store _
  refine ⟨putStore.set location (StorageCorrespondence.world (StorageCorrespondence.put address updatedAccount identity accounts)),
    ?_, ?_, overwrites.set _⟩
  · unfold AccountState.writeField CodeBuilder.bind CodeBuilder.constant
    apply Evaluates.letE arguments
    apply LanguageResult.bind_success .unit fetched
    apply LanguageResult.bind_success .unit updated
    exact .inRight (.storeCell (.first (.var rfl)) latest (.var rfl)
      (Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp latest).1, rfl⟩))
  · have bound := (List.getElem?_eq_some_iff.mp latest).1
    change (putStore.set location _)[location]? = _
    rw [List.getElem?_set_self bound]

/-- The restoration code of the checkpoint, storing the four loaded values. -/
def restoreCode (world balances logs logSize : Code) (depth : Nat) : Code :=
  bind (CodeBuilder.store logSize (fun here => .var (here - (depth + 3) - 1))) fun _ =>
  bind (CodeBuilder.store logs (fun here => .var (here - (depth + 2) - 1))) fun _ =>
  bind (CodeBuilder.store balances (fun here => .var (here - (depth + 1) - 1))) fun _ =>
  bind (CodeBuilder.store world (fun here => .var (here - depth - 1))) fun _ => CodeBuilder.unit

/-- The checkpoint loads the four shared cells in order; its restoration code
is only reached by a failure. -/
theorem checkpoint_evaluates {depth : Nat} {environment : Environment} {store final : Store}
    {world balances logs logSize : Code} {continuation : Code → Code}
    {worldValue balancesValue logsValue logSizeValue result : Value}
    {worldType balancesType logsType logSizeType : Core.Ty}
    {worldLocation balancesLocation logsLocation logSizeLocation : Nat}
    (worldCode : CodeValue depth environment world (.cellRef worldType worldLocation))
    (balancesCode : CodeValue depth environment balances (.cellRef balancesType balancesLocation))
    (logsCode : CodeValue depth environment logs (.cellRef logsType logsLocation))
    (logSizeCode : CodeValue depth environment logSize (.cellRef logSizeType logSizeLocation))
    (worldRead : store.read? worldLocation = some worldValue)
    (balancesRead : store.read? balancesLocation = some balancesValue)
    (logsRead : store.read? logsLocation = some logsValue)
    (logSizeRead : store.read? logSizeLocation = some logSizeValue)
    (continued : Evaluates (logSizeValue :: logsValue :: balancesValue :: worldValue :: environment) store
      (continuation (restoreCode world balances logs logSize depth) (depth + 4)) result final) :
    Evaluates environment store
      (CreationImplementation.checkpoint [world, balances, logs, logSize] continuation depth) result final := by
  simp only [CreationImplementation.checkpoint, CreationImplementation.checkpoint.capture, CodeBuilder.bind, CodeBuilder.load]
  apply Evaluates.letE (.loadCell (worldCode.evaluates store) worldRead)
  apply Evaluates.letE (.loadCell ((balancesCode.prepend [worldValue]).evaluates store) balancesRead)
  apply Evaluates.letE (.loadCell ((logsCode.prepend [balancesValue, worldValue]).evaluates store) logsRead)
  apply Evaluates.letE (.loadCell ((logSizeCode.prepend [logsValue, balancesValue, worldValue]).evaluates store) logSizeRead)
  exact continued

/-- The restoration stores the four values loaded by the checkpoint. -/
theorem restoreCode_evaluates {checkpoint depth : Nat} {environment : Environment} {store : Store}
    {world balances logs logSize : Code} {worldType balancesType logsType logSizeType : Core.Ty}
    {worldLocation balancesLocation logsLocation logSizeLocation : Nat}
    {worldValue balancesValue logsValue logSizeValue : Value}
    (worldCode : CodeValue depth environment world (.cellRef worldType worldLocation))
    (balancesCode : CodeValue depth environment balances (.cellRef balancesType balancesLocation))
    (logsCode : CodeValue depth environment logs (.cellRef logsType logsLocation))
    (logSizeCode : CodeValue depth environment logSize (.cellRef logSizeType logSizeLocation))
    (savedWorld : CodeValue depth environment (fun here => .var (here - checkpoint - 1)) worldValue)
    (savedBalances : CodeValue depth environment (fun here => .var (here - (checkpoint + 1) - 1)) balancesValue)
    (savedLogs : CodeValue depth environment (fun here => .var (here - (checkpoint + 2) - 1)) logsValue)
    (savedLogSize : CodeValue depth environment (fun here => .var (here - (checkpoint + 3) - 1)) logSizeValue)
    (worldBound : worldLocation < store.length) (balancesBound : balancesLocation < store.length)
    (logsBound : logsLocation < store.length) (logSizeBound : logSizeLocation < store.length) :
    Evaluates environment store (restoreCode world balances logs logSize checkpoint depth) .unit
      ((((store.set logSizeLocation logSizeValue).set logsLocation logsValue).set balancesLocation balancesValue).set
        worldLocation worldValue) := by
  have logsBound' : logsLocation < (store.set logSizeLocation logSizeValue).length := by
    simpa only [List.length_set] using logsBound
  have balancesBound' : balancesLocation <
      ((store.set logSizeLocation logSizeValue).set logsLocation logsValue).length := by
    simpa only [List.length_set] using balancesBound
  have worldBound' : worldLocation <
      (((store.set logSizeLocation logSizeValue).set logsLocation logsValue).set balancesLocation balancesValue).length := by
    simpa only [List.length_set] using worldBound
  unfold restoreCode
  apply Evaluates.letE (.storeCell (logSizeCode.evaluates store) (List.getElem?_eq_getElem logSizeBound)
    (savedLogSize.evaluates store) (Store.write?_eq_some_iff.mpr ⟨logSizeBound, rfl⟩))
  apply Evaluates.letE (.storeCell ((logsCode.prepend [.unit]).evaluates _) (List.getElem?_eq_getElem logsBound')
    ((savedLogs.prepend [.unit]).evaluates _) (Store.write?_eq_some_iff.mpr ⟨logsBound', rfl⟩))
  apply Evaluates.letE (.storeCell ((balancesCode.prepend [.unit, .unit]).evaluates _)
    (List.getElem?_eq_getElem balancesBound') ((savedBalances.prepend [.unit, .unit]).evaluates _)
    (Store.write?_eq_some_iff.mpr ⟨balancesBound', rfl⟩))
  apply Evaluates.letE (.storeCell ((worldCode.prepend [.unit, .unit, .unit]).evaluates _)
    (List.getElem?_eq_getElem worldBound') ((savedWorld.prepend [.unit, .unit, .unit]).evaluates _)
    (Store.write?_eq_some_iff.mpr ⟨worldBound', rfl⟩))
  exact .unit

/-- A successful attempt passes through the protection unchanged. -/
theorem protect_succeeded {depth : Nat} {environment : Environment} {store final : Store}
    {restore attempt : Code} {payload : Value}
    (attempted : Evaluates environment store (attempt depth) (.inRight .word payload) final) :
    Evaluates environment store (CreationImplementation.protect restore attempt depth) (.inRight .word payload) final :=
  .caseRight attempted (.inRight (.var rfl))

/-- A failed attempt restores the checkpoint and keeps its reason. -/
theorem protect_failed {depth : Nat} {environment : Environment} {store current final : Store}
    {restore attempt : Code} {reason : Word} {failedType : Core.Ty}
    (attempted : Evaluates environment store (attempt depth) (.inLeft failedType (.word reason)) current)
    (restored : Evaluates (.word reason :: environment) current (restore (depth + 1)) .unit final) :
    Evaluates environment store (CreationImplementation.protect restore attempt depth)
      (.inLeft Creation.responseType (.word reason)) final :=
  .caseLeft attempted (.letE restored
    (.inLeft (((CodeValue.bound depth environment (.word reason)).prepend [.unit]).evaluates final)))

/-- The endowment moves from the creator to a different new account, using the
creator balance already read by the funds check. -/
theorem transfer_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {balancesCode creatorCode targetCode valueCode creatorBalanceCode : Code}
    {location : Nat} {creator target value : Word} {balances next : StorageSemantics.Words}
    (reference : CodeValue depth environment balancesCode (.cellRef WordMapping.type location))
    (creatorValue : CodeValue depth environment creatorCode (.word creator))
    (targetValue : CodeValue depth environment targetCode (.word target))
    (valueValue : CodeValue depth environment valueCode (.word value))
    (creatorBalanceValue : CodeValue depth environment creatorBalanceCode
      (.word (StorageSemantics.readWord creator balances)))
    (balancesRead : store.read? location = some (WordMapping.encode balances))
    (different : creator ≠ target)
    (transferred : AccountCallSemantics.transfer creator target value balances = .ok next) :
    ∃ final, Evaluates environment store
        (CreationImplementation.transfer balancesCode creatorCode targetCode valueCode creatorBalanceCode depth)
        (.inRight .word .unit) final ∧
      final.read? location = some (WordMapping.encode next) ∧ Overwrites location store final := by
  unfold CreationImplementation.transfer
  by_cases zero : value == Word.zero
  · simp only [AccountCallSemantics.transfer, zero, ↓reduceIte, Except.ok.injEq] at transferred
    subst transferred
    refine ⟨store, ?_, balancesRead, .ofRetains (.refl _)⟩
    exact .ifTrue (.binary (valueValue.evaluates store) .word
      (by change some (Value.bool (value == Word.zero)) = some (Value.bool _); simp only [zero])) (.inRight .unit)
  have zeroFalse : (value == Word.zero) = false := Bool.eq_false_iff.mpr zero
  have sameFalse : (creator == target) = false := beq_eq_false_iff_ne.mpr different
  let creatorBalance := StorageSemantics.readWord creator balances
  let targetBalance := StorageSemantics.readWord target balances
  by_cases overflow : targetBalance > Word.maximum.sub value
  · simp only [AccountCallSemantics.transfer, zeroFalse, sameFalse, Bool.false_eq_true, ↓reduceIte] at transferred
    rw [if_pos overflow] at transferred
    cases transferred
  simp only [AccountCallSemantics.transfer, zeroFalse, sameFalse, Bool.false_eq_true, ↓reduceIte] at transferred
  rw [if_neg overflow, Except.ok.injEq] at transferred
  subst transferred
  obtain ⟨first, targetLooked, firstRetained⟩ := lookup_preserves
    (.loadCell (reference.evaluates store) balancesRead) (targetValue.evaluates store)
  have targetBound := CodeValue.bound depth environment (.word targetBalance)
  let firstEnv : Environment := [.word targetBalance]
  have overflowTest : Evaluates (firstEnv ++ environment) first
      (binary .wordGt (fun here => .var (here - depth - 1))
        (binary .wordSub (number (wordModulus - 1)) valueCode) (depth + 1))
      (.bool (decide (targetBalance > Word.maximum.sub value))) first :=
    .binary (targetBound.evaluates first) (.binary .word ((valueValue.prepend firstEnv).evaluates first) rfl) rfl
  let debited := StorageSemantics.writeWord creator (creatorBalance.sub value) balances
  obtain ⟨second, debitEvaluated, secondRetained⟩ := AccountCallCorrespondence.insert_preserves
    (entries := balances) (key := creator) (value := creatorBalance.sub value)
    (.loadCell ((reference.prepend firstEnv).evaluates first) (AccountCallCorrespondence.retained_read firstRetained balancesRead))
    ((creatorValue.prepend firstEnv).evaluates first)
    (.binary (op := .wordSub) ((creatorBalanceValue.prepend firstEnv).evaluates first)
      ((valueValue.prepend firstEnv).evaluates first) rfl)
  let secondEnv : Environment := WordMapping.encode debited :: firstEnv
  have debitBound := CodeValue.bound (depth + 1) (firstEnv ++ environment) (WordMapping.encode debited)
  obtain ⟨third, creditEvaluated, thirdRetained⟩ := AccountCallCorrespondence.insert_preserves
    (entries := debited) (key := target) (value := targetBalance.add value)
    (debitBound.evaluates second) ((targetValue.prepend secondEnv).evaluates second)
    (.binary (op := .wordAdd) ((targetBound.prepend [WordMapping.encode debited]).evaluates second)
      ((valueValue.prepend secondEnv).evaluates second) rfl)
  let credited := StorageSemantics.writeWord target (targetBalance.add value) debited
  let thirdEnv : Environment := WordMapping.encode credited :: secondEnv
  have creditBound := CodeValue.bound (depth + 2) (secondEnv ++ environment) (WordMapping.encode credited)
  have retainedAll := (firstRetained.trans secondRetained).trans thirdRetained
  have readable := AccountCallCorrespondence.retained_read retainedAll balancesRead
  have bound := (List.getElem?_eq_some_iff.mp readable).1
  refine ⟨third.set location (WordMapping.encode credited), ?_, ?_, (Overwrites.ofRetains retainedAll).set _⟩
  · apply Evaluates.ifFalse (.binary (valueValue.evaluates store) .word
      (by change some (Value.bool (value == Word.zero)) = some (Value.bool _); simp only [zero]))
    apply LanguageResult.bind_success .unit targetLooked
    apply Evaluates.ifFalse (by simpa only [overflow, decide_false, firstEnv, List.cons_append, List.nil_append] using overflowTest)
    apply LanguageResult.bind_success .unit debitEvaluated
    apply LanguageResult.bind_success .unit creditEvaluated
    exact .inRight (.storeCell ((reference.prepend thirdEnv).evaluates third) readable (creditBound.evaluates third)
      (Store.write?_eq_some_iff.mpr ⟨bound, rfl⟩))
  · change (third.set location _)[location]? = _
    rw [List.getElem?_set_self bound]

/-- An endowment that would overflow the target balance is failure 12 and
changes no balance. -/
theorem transfer_overflow {depth : Nat} {environment : Environment} {store : Store}
    {balancesCode creatorCode targetCode valueCode creatorBalanceCode : Code}
    {location : Nat} {creator target value : Word} {balances : StorageSemantics.Words}
    (reference : CodeValue depth environment balancesCode (.cellRef WordMapping.type location))
    (targetValue : CodeValue depth environment targetCode (.word target))
    (valueValue : CodeValue depth environment valueCode (.word value))
    (balancesRead : store.read? location = some (WordMapping.encode balances))
    (overflowed : AccountCallSemantics.transfer creator target value balances = .error (Word.ofNatModulo 12)) :
    ∃ final, Evaluates environment store
        (CreationImplementation.transfer balancesCode creatorCode targetCode valueCode creatorBalanceCode depth)
        (.inLeft .unit (.word (Word.ofNatModulo 12))) final ∧ StoreRetains store final := by
  unfold CreationImplementation.transfer
  by_cases zero : value == Word.zero
  · simp only [AccountCallSemantics.transfer, zero, ↓reduceIte] at overflowed
    cases overflowed
  have zeroFalse : (value == Word.zero) = false := Bool.eq_false_iff.mpr zero
  let targetBalance := StorageSemantics.readWord target balances
  have overflow : targetBalance > Word.maximum.sub value := by
    by_cases same : creator == target
    · simp only [AccountCallSemantics.transfer, zeroFalse, same, Bool.false_eq_true, ↓reduceIte] at overflowed
      cases overflowed
    by_cases fits : targetBalance > Word.maximum.sub value
    · exact fits
    simp only [AccountCallSemantics.transfer, zeroFalse, same, Bool.false_eq_true, ↓reduceIte] at overflowed
    rw [if_neg fits] at overflowed
    cases overflowed
  obtain ⟨first, targetLooked, firstRetained⟩ := lookup_preserves
    (.loadCell (reference.evaluates store) balancesRead) (targetValue.evaluates store)
  have targetBound := CodeValue.bound depth environment (.word targetBalance)
  let firstEnv : Environment := [.word targetBalance]
  have overflowTest : Evaluates (firstEnv ++ environment) first
      (binary .wordGt (fun here => .var (here - depth - 1))
        (binary .wordSub (number (wordModulus - 1)) valueCode) (depth + 1))
      (.bool (decide (targetBalance > Word.maximum.sub value))) first :=
    .binary (targetBound.evaluates first) (.binary .word ((valueValue.prepend firstEnv).evaluates first) rfl) rfl
  refine ⟨first, ?_, firstRetained⟩
  apply Evaluates.ifFalse (.binary (valueValue.evaluates store) .word
    (by change some (Value.bool (value == Word.zero)) = some (Value.bool _); simp only [zeroFalse]))
  apply LanguageResult.bind_success .unit targetLooked
  exact .ifTrue (by simpa only [overflow, decide_true, firstEnv, List.cons_append, List.nil_append] using overflowTest)
    (.inLeft .word)

/-- Writes that change only the listed cells and append helper cells. -/
structure Rewrites (changed : List Nat) (initial final : Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ other value, other ∉ changed → initial.read? other = some value → final.read? other = some value

theorem Rewrites.trans {changed : List Nat} {initial middle final : Store}
    (first : Rewrites changed initial middle) (second : Rewrites changed middle final) : Rewrites changed initial final :=
  ⟨Nat.le_trans first.length_le second.length_le, fun other value outside found =>
    second.read other value outside (first.read other value outside found)⟩

theorem Rewrites.ofOverwrites {changed : List Nat} {location : Nat} {initial final : Store}
    (overwrites : Overwrites location initial final) (member : location ∈ changed) : Rewrites changed initial final :=
  ⟨overwrites.length_le, fun other value outside found =>
    overwrites.read other value (fun same => outside (same ▸ member)) found⟩

theorem put_put (address : Word) (account other : AccountState.Account) (identity otherIdentity : Nat) :
    ∀ accounts : StorageCorrespondence.Accounts,
      StorageCorrespondence.put address account identity (StorageCorrespondence.put address other otherIdentity accounts) =
        StorageCorrespondence.put address account identity accounts
  | [] => by simp [StorageCorrespondence.put]
  | (head, headIdentity) :: rest => by
      by_cases same : address = head.address
      · simp [StorageCorrespondence.put, same]
      · have different : (address == head.address) = false := beq_eq_false_iff_ne.mpr same
        simp only [StorageCorrespondence.put, different, Bool.false_eq_true, ↓reduceIte]
        rw [put_put address account other identity otherIdentity rest]

/-- With empty init code no init frame runs: the new account receives the
endowment, its empty runtime image installs with identity zero, and the
attempt returns the address with empty revert data. -/
theorem deployment_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {runInit : Code → Code → Code} {identify : Code → Code} {shared : AccountRuntime.References}
    {locations : SharedLocations} {world balances creator value creatorBalance request target restore : Code}
    {accounts : StorageCorrespondence.Accounts} {before after : StorageSemantics.Words}
    {creatorWord valueWord targetWord : Word} {requested : Request}
    (references : SharedReferences depth environment shared locations)
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type locations.world))
    (balancesCode : CodeValue depth environment balances (.cellRef WordMapping.type locations.balances))
    (creatorValue : CodeValue depth environment creator (.word creatorWord))
    (valueValue : CodeValue depth environment value (.word valueWord))
    (creatorBalanceValue : CodeValue depth environment creatorBalance
      (.word (StorageSemantics.readWord creatorWord before)))
    (requestCode : CodeValue depth environment request (requestValue requested))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (worldRead : store.read? locations.world = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? locations.balances = some (WordMapping.encode before))
    (completeRead : store.read? locations.complete = some (.bool true))
    (distinct : locations.all.Nodup)
    (different : creatorWord ≠ targetWord)
    (emptyInit : requested.initLength = Word.zero)
    (transferred : AccountCallSemantics.transfer creatorWord targetWord valueWord before = .ok after) :
    ∃ final, Evaluates environment store
        (CreationImplementation.deployment runInit (CreationImplementation.installWith identify shared)
          world balances creator value creatorBalance request target restore depth)
        (.inRight .word (bundleValues [.word targetWord, WordMapping.encode [], .word (Word.ofNatModulo 0)])) final ∧
      final.read? locations.world = some (StorageCorrespondence.world
        (StorageCorrespondence.put targetWord (CreationSemantics.createdAccount targetWord) 0 accounts)) ∧
      final.read? locations.balances = some (WordMapping.encode after) ∧
      Rewrites [locations.world, locations.balances] store final := by
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at distinct
  obtain ⟨⟨worldLogs, worldSize, worldBalances, worldComplete⟩, ⟨logsSize, logsBalances, logsComplete⟩,
    ⟨sizeBalances, sizeComplete⟩, balancesComplete⟩ := distinct
  let created := CreationSemantics.createdAccount targetWord
  -- the new account record
  have createdRecord (env : Environment) (current : Store) : Evaluates env current
      (AccountState.replace (AccountState.replace AccountState.defaultRecord 2 (.word (Word.ofNatModulo 1))) 7 (.bool true))
      (StorageCorrespondence.record created 0) current :=
    replace_evaluates (fields := (fields {address := targetWord} 0).set 2 (.word (Word.ofNatModulo 1))) 7 rfl
      (replace_evaluates (fields := fields {address := targetWord} 0) 2 rfl
        (StorageCorrespondence.default_evaluates targetWord env current) .word) .bool
  have inserted := StorageCorrespondence.put_evaluates (environment := environment)
    (initial := store) (mappingStore := store) (addressStore := store) (final := store)
    accounts targetWord created 0 (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store)
    (createdRecord _ _)
  let created1 := StorageCorrespondence.put targetWord created 0 accounts
  let insertedValue := StorageCorrespondence.world created1
  let store1 := StorageCorrespondence.putStore accounts targetWord created 0 environment store
  obtain ⟨suffix1, same1⟩ := putStore_extension accounts targetWord created 0 environment store
  have keep1 {location : Nat} {old : Value} (found : store.read? location = some old) : store1.read? location = some old := by
    change (StorageCorrespondence.putStore accounts targetWord created 0 environment store).read? location = _
    rw [same1]
    exact StorageCorrespondence.appended_read found _
  have bound1 := (List.getElem?_eq_some_iff.mp (keep1 worldRead)).1
  let store2 : Store := store1.set locations.world insertedValue
  have stored : Evaluates (insertedValue :: environment) store1
      (CodeBuilder.store world (fun here => .var (here - depth - 1)) (depth + 1)) .unit store2 :=
    .storeCell ((worldCode.prepend [insertedValue]).evaluates store1) (keep1 worldRead)
      ((CodeValue.bound depth environment insertedValue).evaluates store1) (Store.write?_eq_some_iff.mpr ⟨bound1, rfl⟩)
  have keep2 {location : Nat} {old : Value} (different : location ≠ locations.world)
      (found : store.read? location = some old) : store2.read? location = some old := by
    change (store1.set locations.world insertedValue)[location]? = _
    rw [List.getElem?_set_ne (Ne.symm different)]
    exact keep1 found
  have worldRead2 : store2.read? locations.world = some insertedValue := by
    change (store1.set locations.world insertedValue)[locations.world]? = _
    rw [List.getElem?_set_self bound1]
  have frame2 : Rewrites [locations.world, locations.balances] store store2 := by
    refine ⟨?_, fun other old outside found => keep2 (fun same => outside (by simp [same])) found⟩
    change store.length ≤ (store1.set _ _).length
    rw [List.length_set]
    change store.length ≤ (StorageCorrespondence.putStore accounts targetWord created 0 environment store).length
    rw [same1]; simp
  -- the endowment
  let E2 : Environment := .unit :: insertedValue :: environment
  obtain ⟨store3, transferEvaluated, balancesRead3, transferFrame⟩ := transfer_evaluates
    (balancesCode.prepend [.unit, insertedValue]) (creatorValue.prepend [.unit, insertedValue])
    (targetValue.prepend [.unit, insertedValue]) (valueValue.prepend [.unit, insertedValue])
    (creatorBalanceValue.prepend [.unit, insertedValue]) (keep2 (Ne.symm worldBalances) balancesRead) different
    transferred
  have keep3 {location : Nat} {old : Value} (different : location ≠ locations.balances)
      (found : store2.read? location = some old) : store3.read? location = some old :=
    transferFrame.read location old different found
  -- empty init code returns an empty successful response
  let E3 : Environment := .unit :: E2
  let childValue : Value := bundleValues [.bool true, WordMapping.encode [], .word (Word.ofNatModulo 0)]
  have lengthTest : Evaluates E3 store3 (binary .wordEq (part 7 8 request) (number 0) (depth + 3)) (.bool true) store3 :=
    .binary (((requestCode.part (index := 7) rfl).prepend [.unit, .unit, insertedValue]).evaluates store3) .word
      (by simp [BinaryOp.apply, emptyInit]; rfl)
  have childEvaluated : Evaluates E3 store3
      (choose (binary .wordEq (part 7 8 request) (number 0))
        (success (packet [CodeBuilder.boolean true, empty, number 0])) (runInit target request) (depth + 3))
      (.inRight .word childValue) store3 :=
    .ifTrue lengthTest (.inRight (.pair .bool (.pair (.construct .unit) .word)))
  let E4 : Environment := childValue :: E3
  have childCode := CodeValue.bound (depth + 3) E3 childValue
  have successTest : Evaluates E4 store3 (part 0 3 (fun here => .var (here - (depth + 3) - 1)) (depth + 4))
      (.bool true) store3 := (childCode.part (index := 0) rfl).evaluates store3
  have sizeTest : Evaluates E4 store3 (binary .wordGt (part 2 3 (fun here => .var (here - (depth + 3) - 1)))
      (number 24576) (depth + 4)) (.bool false) store3 :=
    .binary ((childCode.part (index := 2) rfl).evaluates store3) .word (by simp [BinaryOp.apply]; decide)
  obtain ⟨suffix5, firstRead⟩ := MemoryCopyCorrespondence.readMemoryByte_evaluates (environment := E4) (store := store3)
    [] (Word.ofNatModulo 0) ((childCode.part (index := 1) rfl).evaluates store3) .word
  rw [CreationBytes.readByte_empty] at firstRead
  let store5 : Store := store3 ++ suffix5
  let E5 : Environment := .word Word.zero :: E4
  have childCode5 := childCode.prepend [.word Word.zero]
  have prefixTest : Evaluates E5 store5
      (choose (binary .wordGt (part 2 3 (fun here => .var (here - (depth + 3) - 1))) (number 0))
        (binary .wordEq (fun here => .var (here - (depth + 4) - 1)) (number 0xef)) (CodeBuilder.boolean false) (depth + 5))
      (.bool false) store5 :=
    .ifFalse (.binary ((childCode5.part (index := 2) rfl).evaluates store5) .word (by simp [BinaryOp.apply])) .bool
  have keep5 {location : Nat} {old : Value} (found : store3.read? location = some old) : store5.read? location = some old :=
    StorageCorrespondence.appended_read found _
  -- installation of the empty runtime image
  have identityEvaluated : Evaluates E5 store5
      (choose (binary .wordEq (part 2 3 (fun here => .var (here - (depth + 3) - 1))) (number 0))
        (success (number 0)) (identify (fun here => .var (here - (depth + 3) - 1))) (depth + 5))
      (.inRight .word (.word (Word.ofNatModulo 0))) store5 :=
    .ifTrue (.binary ((childCode5.part (index := 2) rfl).evaluates store5) .word (by simp [BinaryOp.apply])) (.inRight .word)
  let E6 : Environment := .word (Word.ofNatModulo 0) :: E5
  let extra6 : Environment := [.word (Word.ofNatModulo 0), .word Word.zero, childValue, .unit, .unit, insertedValue]
  have references6 := references.prepend extra6
  have worldRead5 : store5.read? locations.world = some insertedValue :=
    keep5 (keep3 (Ne.symm (Ne.symm worldBalances)) worldRead2)
  have completeRead5 : store5.read? locations.complete = some (.bool true) :=
    keep5 (keep3 (Ne.symm balancesComplete.1) (keep2 (Ne.symm worldComplete) completeRead))
  have found : StorageCorrespondence.get created1 targetWord true = .ok (created, 0) := by
    simp only [StorageCorrespondence.get, created1, CatalogWorldCorrespondence.lookup_put_same]
    rfl
  have recordEvaluated := StorageCorrespondence.get_evaluates (environment := E6) (initial := store5)
    (worldStore := store5) (addressStore := store5) (final := store5) created1 targetWord true
    (.loadCell (references6.world.evaluates store5) worldRead5) ((targetValue.prepend extra6).evaluates store5)
    (.loadCell (references6.complete.evaluates store5) completeRead5)
  rw [found] at recordEvaluated
  let store6 := StorageCorrespondence.getStore created1 targetWord true E6 store5
  obtain ⟨suffix6, _, same6⟩ := StorageCorrespondence.getStore_extension created1 targetWord true E6 store5
  have keep6 {location : Nat} {old : Value} (found : store5.read? location = some old) : store6.read? location = some old := by
    change (StorageCorrespondence.getStore created1 targetWord true E6 store5).read? location = _
    rw [same6]
    exact StorageCorrespondence.appended_read found _
  let recordValue := StorageCorrespondence.record created 0
  let E7 : Environment := recordValue :: E6
  have childCode7 := childCode.prepend [recordValue, .word (Word.ofNatModulo 0), .word Word.zero]
  have recordCode := CodeValue.bound (depth + 6) E6 recordValue
  have identityCode := (CodeValue.bound (depth + 5) E5 (.word (Word.ofNatModulo 0))).prepend [recordValue]
  have updatedEvaluated := replace_evaluates (fields := (((fields created 0).set 3 (.word (Word.ofNatModulo 0))).set 4
        (WordMapping.encode [])).set 5 (.word (Word.ofNatModulo 0))) 6 rfl
      (replace_evaluates (fields := ((fields created 0).set 3 (.word (Word.ofNatModulo 0))).set 4 (WordMapping.encode [])) 5 rfl
        (replace_evaluates (fields := (fields created 0).set 3 (.word (Word.ofNatModulo 0))) 4 rfl
          (replace_evaluates (fields := fields created 0) 3 rfl (recordCode.evaluates store6) (identityCode.evaluates store6))
          ((childCode7.part (index := 1) rfl).evaluates store6))
        ((childCode7.part (index := 2) rfl).evaluates store6)) (Evaluates.bool (value := true))
  have putEvaluated := StorageCorrespondence.put_evaluates (environment := E7) (initial := store6)
    (mappingStore := store6) (addressStore := store6) (final := store6) created1 targetWord created 0
    (.loadCell ((references6.world.prepend [recordValue]).evaluates store6) (keep6 worldRead5))
    ((targetValue.prepend (recordValue :: extra6)).evaluates store6) (by exact updatedEvaluated)
  rw [put_put] at putEvaluated
  let store7 := StorageCorrespondence.putStore created1 targetWord created 0 E7 store6
  obtain ⟨suffix7, same7⟩ := putStore_extension created1 targetWord created 0 E7 store6
  have keep7 {location : Nat} {old : Value} (found : store6.read? location = some old) : store7.read? location = some old := by
    change (StorageCorrespondence.putStore created1 targetWord created 0 E7 store6).read? location = _
    rw [same7]
    exact StorageCorrespondence.appended_read found _
  have worldRead7 := keep7 (keep6 worldRead5)
  have bound7 := (List.getElem?_eq_some_iff.mp worldRead7).1
  let store8 : Store := store7.set locations.world insertedValue
  have installEvaluated : Evaluates E5 store5
      (CreationImplementation.installWith identify shared target (fun here => .var (here - (depth + 3) - 1)) (depth + 5))
      (.inRight .word .unit) store8 := by
    unfold CreationImplementation.installWith
    apply LanguageResult.bind_success _ identityEvaluated
    apply LanguageResult.bind_success _ recordEvaluated
    dsimp only
    apply LanguageResult.bind_success _ putEvaluated
    exact .inRight (.storeCell ((references6.world.prepend [insertedValue, recordValue]).evaluates store7) worldRead7
      ((CodeValue.bound (depth + 7) E7 insertedValue).evaluates store7) (Store.write?_eq_some_iff.mpr ⟨bound7, rfl⟩))
  have responseEvaluated : Evaluates (.unit :: E5) store8
      (CreationImplementation.response target empty (number 0) (depth + 6))
      (.inRight .word (bundleValues [.word targetWord, WordMapping.encode [], .word (Word.ofNatModulo 0)])) store8 :=
    .inRight (.pair ((targetValue.prepend (.unit :: .word Word.zero :: childValue :: .unit :: .unit :: [insertedValue])).evaluates store8)
      (.pair (.construct .unit) .word))
  refine ⟨store8, ?_, ?_, ?_, ?_⟩
  · unfold CreationImplementation.deployment
    apply LanguageResult.bind_success _ inserted
    apply Evaluates.letE stored
    apply LanguageResult.bind_success _ transferEvaluated
    apply LanguageResult.bind_success _ childEvaluated
    apply Evaluates.ifTrue successTest
    apply Evaluates.ifFalse sizeTest
    apply LanguageResult.bind_success _ firstRead
    apply Evaluates.ifFalse prefixTest
    apply LanguageResult.bind_success _ installEvaluated
    exact responseEvaluated
  · change (store7.set locations.world insertedValue)[locations.world]? = _
    rw [List.getElem?_set_self bound7]
  · change (store7.set locations.world insertedValue)[locations.balances]? = _
    rw [List.getElem?_set_ne worldBalances]
    exact keep7 (keep6 (keep5 balancesRead3))
  · have appended : Rewrites [locations.world, locations.balances] store3 store7 := by
      refine ⟨?_, fun other old _ found => keep7 (keep6 (keep5 found))⟩
      change store3.length ≤ (StorageCorrespondence.putStore created1 targetWord created 0 E7 store6).length
      rw [same7]
      change store3.length ≤ ((StorageCorrespondence.getStore created1 targetWord true E6 store5) ++ suffix7).length
      rw [same6]
      simp [store5]
    have written : Rewrites [locations.world, locations.balances] store7 store8 := by
      refine ⟨by simp [store8], fun other old outside found => ?_⟩
      change (store7.set locations.world insertedValue)[other]? = _
      rw [List.getElem?_set_ne (fun same => outside (by simp [same]))]
      exact found
    exact ((frame2.trans (Rewrites.ofOverwrites transferFrame (by simp))).trans appended).trans written

/-- Rewriting an account with the identity it already has keeps every code
link when its code is unchanged. -/
theorem links_put_same {anchors : List CatalogWorldCorrespondence.Anchor} {accounts : StorageCorrespondence.Accounts}
    (linked : CatalogWorldCorrespondence.Links anchors accounts) {address : Word} {complete : Bool}
    {account updated : AccountState.Account} {identity : Nat}
    (obtained : StorageCorrespondence.get accounts address complete = .ok (account, identity))
    (code : updated.code = account.code) :
    CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.put address updated identity accounts) := by
  intro anchor member
  obtain ⟨selected, selectedAt, selectedCode⟩ := linked anchor member
  by_cases same : address = anchor.address
  · subst address
    have original : StorageCorrespondence.get accounts anchor.address complete = .ok (selected, anchor.identity) := by
      simp only [StorageCorrespondence.get, selectedAt]
    have equal := Except.ok.inj (obtained.symm.trans original)
    cases equal
    exact ⟨_, CatalogWorldCorrespondence.lookup_put_same accounts anchor.address _ anchor.identity,
      by simpa [code] using selectedCode⟩
  · exact ⟨selected, (CatalogWorldCorrespondence.lookup_put_other same accounts _ identity).trans selectedAt, selectedCode⟩

/-- A new account at an address without a record breaks no code link. -/
theorem links_put_absent {anchors : List CatalogWorldCorrespondence.Anchor} {accounts : StorageCorrespondence.Accounts}
    (linked : CatalogWorldCorrespondence.Links anchors accounts) {address : Word}
    (absent : StorageCorrespondence.lookup address accounts = none) (account : AccountState.Account) (identity : Nat) :
    CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.put address account identity accounts) := by
  intro anchor member
  obtain ⟨selected, selectedAt, selectedCode⟩ := linked anchor member
  have different : address ≠ anchor.address := by
    intro same
    rw [same, selectedAt] at absent
    cases absent
  exact ⟨selected, (CatalogWorldCorrespondence.lookup_put_other different accounts _ identity).trans selectedAt, selectedCode⟩

private theorem refused_evaluates (depth : Nat) (environment : Environment) (store : Store) :
    Evaluates environment store (CreationImplementation.refused depth) refusedValue store :=
  .inRight (.pair .word (.pair (.construct .unit) .word))

/-- A target with a nonzero nonce or code size is a collision. -/
theorem attempt_collision {depth : Nat} {environment : Environment} {store : Store}
    {runInit installRuntime : Code → Code → Code}
    {world balances complete creator value creatorBalance request target restore : Code}
    {location : Nat} {accounts : StorageCorrespondence.Accounts} {targetWord : Word} {completeFlag : Bool}
    {existing : AccountState.Account} {identity : Nat}
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type location))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (completeValue : CodeValue depth environment complete (.bool completeFlag))
    (worldRead : store.read? location = some (StorageCorrespondence.world accounts))
    (obtained : StorageCorrespondence.get accounts targetWord completeFlag = .ok (existing, identity))
    (used : existing.nonce ≠ Word.zero ∨
      AccountObservationSemantics.codeSize (existing.code.getD []) ≠ Word.zero) :
    ∃ final, Evaluates environment store
        (CreationImplementation.attempt runInit installRuntime world balances complete creator value creatorBalance
          request target restore depth) refusedValue final ∧ StoreRetains store final := by
  have fetched := StorageCorrespondence.get_evaluates (environment := environment) (initial := store)
    (worldStore := store) (addressStore := store) (final := store) accounts targetWord completeFlag
    (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store) (completeValue.evaluates store)
  rw [obtained] at fetched
  let fetchedStore := StorageCorrespondence.getStore accounts targetWord completeFlag environment store
  let recordValue := StorageCorrespondence.record existing identity
  have recordCode := CodeValue.bound depth environment recordValue
  have nonceTest : Evaluates (recordValue :: environment) fetchedStore
      (binary .wordGt (part 2 9 (fun here => .var (here - depth - 1))) (number 0) (depth + 1))
      (.bool (decide (existing.nonce > Word.ofNatModulo 0))) fetchedStore :=
    .binary ((recordCode.part (index := 2) rfl).evaluates fetchedStore) .word rfl
  have sizeTest : Evaluates (recordValue :: environment) fetchedStore
      (binary .wordGt (part 5 9 (fun here => .var (here - depth - 1))) (number 0) (depth + 1))
      (.bool (decide (AccountObservationSemantics.codeSize (existing.code.getD []) > Word.ofNatModulo 0))) fetchedStore :=
    .binary ((recordCode.part (index := 5) rfl).evaluates fetchedStore) .word rfl
  refine ⟨fetchedStore, ?_, StoreRetains.append _ _⟩
  unfold CreationImplementation.attempt
  apply LanguageResult.bind_success _ fetched
  by_cases nonceUsed : existing.nonce ≠ Word.zero
  · have positive : existing.nonce > Word.ofNatModulo 0 := by
      rw [GT.gt, Fin.lt_def]
      exact Nat.pos_of_ne_zero (fun zero => nonceUsed (Fin.ext zero))
    exact .ifTrue (by simpa only [positive, decide_true] using nonceTest) (refused_evaluates _ _ _)
  · have sizeUsed := used.resolve_left nonceUsed
    have notPositive : ¬existing.nonce > Word.ofNatModulo 0 := by
      rw [GT.gt, Fin.lt_def]
      exact fun lt => nonceUsed (fun zero => by rw [zero] at lt; exact Nat.lt_irrefl _ lt)
    have positive : AccountObservationSemantics.codeSize (existing.code.getD []) > Word.ofNatModulo 0 := by
      rw [GT.gt, Fin.lt_def]
      exact Nat.pos_of_ne_zero (fun zero => sizeUsed (Fin.ext zero))
    exact .ifFalse (by simpa only [notPositive, decide_false] using nonceTest)
      (.ifTrue (by simpa only [positive, decide_true] using sizeTest) (refused_evaluates _ _ _))

theorem Rewrites.append (changed : List Nat) (store suffix : Store) : Rewrites changed store (store ++ suffix) :=
  ⟨by simp, fun _ _ _ found => StorageCorrespondence.appended_read found _⟩

/-- A target absent from a complete world reads as a fresh record and receives
the new account. -/
theorem attempt_deployed {depth : Nat} {environment : Environment} {store : Store}
    {runInit : Code → Code → Code} {identify : Code → Code} {shared : AccountRuntime.References}
    {locations : SharedLocations}
    {world balances complete creator value creatorBalance request target restore : Code}
    {accounts : StorageCorrespondence.Accounts} {before after : StorageSemantics.Words}
    {creatorWord valueWord targetWord : Word} {requested : Request}
    (references : SharedReferences depth environment shared locations)
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type locations.world))
    (balancesCode : CodeValue depth environment balances (.cellRef WordMapping.type locations.balances))
    (completeValue : CodeValue depth environment complete (.bool true))
    (creatorValue : CodeValue depth environment creator (.word creatorWord))
    (valueValue : CodeValue depth environment value (.word valueWord))
    (creatorBalanceValue : CodeValue depth environment creatorBalance
      (.word (StorageSemantics.readWord creatorWord before)))
    (requestCode : CodeValue depth environment request (requestValue requested))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (worldRead : store.read? locations.world = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? locations.balances = some (WordMapping.encode before))
    (completeRead : store.read? locations.complete = some (.bool true))
    (distinct : locations.all.Nodup)
    (absent : StorageCorrespondence.lookup targetWord accounts = none)
    (different : creatorWord ≠ targetWord)
    (emptyInit : requested.initLength = Word.zero)
    (transferred : AccountCallSemantics.transfer creatorWord targetWord valueWord before = .ok after) :
    ∃ final, Evaluates environment store
        (CreationImplementation.attempt runInit (CreationImplementation.installWith identify shared)
          world balances complete creator value creatorBalance request target restore depth)
        (.inRight .word (bundleValues [.word targetWord, WordMapping.encode [], .word (Word.ofNatModulo 0)])) final ∧
      final.read? locations.world = some (StorageCorrespondence.world
        (StorageCorrespondence.put targetWord (CreationSemantics.createdAccount targetWord) 0 accounts)) ∧
      final.read? locations.balances = some (WordMapping.encode after) ∧
      Rewrites [locations.world, locations.balances] store final := by
  have fetched := StorageCorrespondence.get_evaluates (environment := environment) (initial := store)
    (worldStore := store) (addressStore := store) (final := store) accounts targetWord true
    (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store) (completeValue.evaluates store)
  have obtained : StorageCorrespondence.get accounts targetWord true = .ok ({address := targetWord}, 0) := by
    simp only [StorageCorrespondence.get, absent, ↓reduceIte]
  rw [obtained] at fetched
  let fetchedStore := StorageCorrespondence.getStore accounts targetWord true environment store
  obtain ⟨suffix, _, same⟩ := StorageCorrespondence.getStore_extension accounts targetWord true environment store
  have keep {location : Nat} {old : Value} (found : store.read? location = some old) :
      fetchedStore.read? location = some old := by
    change (StorageCorrespondence.getStore accounts targetWord true environment store).read? location = _
    rw [same]
    exact StorageCorrespondence.appended_read found _
  let recordValue := StorageCorrespondence.record {address := targetWord} 0
  have recordCode := CodeValue.bound depth environment recordValue
  obtain ⟨final, deployed, worldFinal, balancesFinal, frame⟩ := deployment_evaluates (runInit := runInit)
    (identify := identify) (restore := restore) (references.prepend [recordValue])
    (worldCode.prepend [recordValue]) (balancesCode.prepend [recordValue]) (creatorValue.prepend [recordValue])
    (valueValue.prepend [recordValue]) (creatorBalanceValue.prepend [recordValue]) (requestCode.prepend [recordValue])
    (targetValue.prepend [recordValue]) (keep worldRead) (keep balancesRead) (keep completeRead) distinct different
    emptyInit transferred
  refine ⟨final, ?_, worldFinal, balancesFinal, ?_⟩
  · unfold CreationImplementation.attempt
    apply LanguageResult.bind_success _ fetched
    apply Evaluates.ifFalse (.binary ((recordCode.part (index := 2) rfl).evaluates fetchedStore) .word
      (by simp [BinaryOp.apply]; decide))
    apply Evaluates.ifFalse (.binary ((recordCode.part (index := 5) rfl).evaluates fetchedStore) .word
      (by simp [BinaryOp.apply]))
    exact .ifTrue ((recordCode.part (index := 6) rfl).evaluates fetchedStore) deployed
  · have appended : Rewrites [locations.world, locations.balances] store fetchedStore := by
      change Rewrites _ store (StorageCorrespondence.getStore accounts targetWord true environment store)
      rw [same]
      exact Rewrites.append _ _ _
    exact appended.trans frame

/-- The shared world after the creator nonce advances. -/
def advancedWorld (state : AccountCallSemantics.Shared) (creator : Word) (account : AccountState.Account) :
    StorageSemantics.World :=
  StorageSemantics.put creator {account with nonce := account.nonce.add (Word.ofNatModulo 1)} state.world

/-- The response of a deployment: the new address and no revert bytes. -/
def deployedValue (target : Word) : Value :=
  .inRight .word (bundleValues [.word target, WordMapping.encode [], .word (Word.ofNatModulo 0)])

/-- Admitted attempts that the dispatcher completes without an init frame:
a collision, a deployment of empty init code at an address absent from a
complete world, and the two faults after the nonce advance, an unknown target
(failure 7) and an endowment overflow (failure 12). The faults restore the
checkpoint, so only the nonce advance remains. -/
inductive Admitting (state : AccountCallSemantics.Shared) (request : Request) :
    Value → AccountCallSemantics.Shared → Prop where
  | collision {account existing : AccountState.Account} {target : Word}
      (funded : ¬request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
      (found : StorageSemantics.get state.world (request.creator.bitAnd addressMask) state.complete = .ok account)
      (belowLimit : ¬account.nonce > Word.ofNatModulo (2 ^ 64 - 2))
      (bounded : request.initLength.val ≤ 49152)
      (derived : CreationAddressSemantics.Derived (request.creator.bitAnd addressMask) account.nonce
        request.initCode request.initLength request.scheme target)
      (occupied : StorageSemantics.lookup target (advancedWorld state (request.creator.bitAnd addressMask) account) =
        some existing)
      (used : existing.nonce ≠ Word.zero ∨
        AccountObservationSemantics.codeSize (existing.code.getD []) ≠ Word.zero) :
      Admitting state request refusedValue
        {state with world := advancedWorld state (request.creator.bitAnd addressMask) account}
  | deployed {account : AccountState.Account} {target : Word} {balances : StorageSemantics.Words}
      (funded : ¬request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
      (found : StorageSemantics.get state.world (request.creator.bitAnd addressMask) state.complete = .ok account)
      (belowLimit : ¬account.nonce > Word.ofNatModulo (2 ^ 64 - 2))
      (bounded : request.initLength.val ≤ 49152)
      (derived : CreationAddressSemantics.Derived (request.creator.bitAnd addressMask) account.nonce
        request.initCode request.initLength request.scheme target)
      (absent : StorageSemantics.lookup target (advancedWorld state (request.creator.bitAnd addressMask) account) = none)
      (complete : state.complete = true)
      (emptyInit : request.initLength = Word.zero)
      (transferred : AccountCallSemantics.transfer (request.creator.bitAnd addressMask) target request.value
        state.balances = .ok balances) :
      Admitting state request (deployedValue target)
        {state with
          world := (StorageSemantics.put target (CreationSemantics.createdAccount target)
            (advancedWorld state (request.creator.bitAnd addressMask) account))
          balances := balances}
  | unknown {account : AccountState.Account} {target : Word}
      (funded : ¬request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
      (found : StorageSemantics.get state.world (request.creator.bitAnd addressMask) state.complete = .ok account)
      (belowLimit : ¬account.nonce > Word.ofNatModulo (2 ^ 64 - 2))
      (bounded : request.initLength.val ≤ 49152)
      (derived : CreationAddressSemantics.Derived (request.creator.bitAnd addressMask) account.nonce
        request.initCode request.initLength request.scheme target)
      (unknown : CreationSemantics.Unknown (advancedWorld state (request.creator.bitAnd addressMask) account) target
        state.complete) :
      Admitting state request (.inLeft Creation.responseType (.word (Word.ofNatModulo 7)))
        {state with world := advancedWorld state (request.creator.bitAnd addressMask) account}
  | overflow {account : AccountState.Account} {target : Word}
      (funded : ¬request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
      (found : StorageSemantics.get state.world (request.creator.bitAnd addressMask) state.complete = .ok account)
      (belowLimit : ¬account.nonce > Word.ofNatModulo (2 ^ 64 - 2))
      (bounded : request.initLength.val ≤ 49152)
      (derived : CreationAddressSemantics.Derived (request.creator.bitAnd addressMask) account.nonce
        request.initCode request.initLength request.scheme target)
      (absent : StorageSemantics.lookup target (advancedWorld state (request.creator.bitAnd addressMask) account) = none)
      (complete : state.complete = true)
      (overflowed : AccountCallSemantics.transfer (request.creator.bitAnd addressMask) target request.value
        state.balances = .error (Word.ofNatModulo 12)) :
      Admitting state request (.inLeft Creation.responseType (.word (Word.ofNatModulo 12)))
        {state with world := advancedWorld state (request.creator.bitAnd addressMask) account}

theorem Rewrites.ofRetains {changed : List Nat} {initial final : Store} (retained : StoreRetains initial final) :
    Rewrites changed initial final :=
  ⟨retained.length_le, fun other _ _ found => (retained.read other (List.getElem?_eq_some_iff.mp found).1).trans found⟩

/-- An endowment overflow after the new record is inserted is failure 12; the
world keeps the inserted record until the checkpoint is restored. -/
theorem deployment_overflow {depth : Nat} {environment : Environment} {store : Store}
    {runInit installRuntime : Code → Code → Code}
    {locations : SharedLocations} {world balances creator value creatorBalance request target restore : Code}
    {accounts : StorageCorrespondence.Accounts} {before : StorageSemantics.Words}
    {creatorWord valueWord targetWord : Word}
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type locations.world))
    (balancesCode : CodeValue depth environment balances (.cellRef WordMapping.type locations.balances))
    (valueValue : CodeValue depth environment value (.word valueWord))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (worldRead : store.read? locations.world = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? locations.balances = some (WordMapping.encode before))
    (worldBalances : locations.world ≠ locations.balances)
    (overflowed : AccountCallSemantics.transfer creatorWord targetWord valueWord before = .error (Word.ofNatModulo 12)) :
    ∃ final, Evaluates environment store
        (CreationImplementation.deployment runInit installRuntime world balances creator value creatorBalance request
          target restore depth)
        (.inLeft Creation.responseType (.word (Word.ofNatModulo 12))) final ∧
      Rewrites [locations.world] store final := by
  let created := CreationSemantics.createdAccount targetWord
  have createdRecord (env : Environment) (current : Store) : Evaluates env current
      (AccountState.replace (AccountState.replace AccountState.defaultRecord 2 (.word (Word.ofNatModulo 1))) 7 (.bool true))
      (StorageCorrespondence.record created 0) current :=
    replace_evaluates (fields := (fields {address := targetWord} 0).set 2 (.word (Word.ofNatModulo 1))) 7 rfl
      (replace_evaluates (fields := fields {address := targetWord} 0) 2 rfl
        (StorageCorrespondence.default_evaluates targetWord env current) .word) .bool
  have inserted := StorageCorrespondence.put_evaluates (environment := environment)
    (initial := store) (mappingStore := store) (addressStore := store) (final := store)
    accounts targetWord created 0 (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store)
    (createdRecord _ _)
  let insertedValue := StorageCorrespondence.world (StorageCorrespondence.put targetWord created 0 accounts)
  let store1 := StorageCorrespondence.putStore accounts targetWord created 0 environment store
  obtain ⟨suffix1, same1⟩ := putStore_extension accounts targetWord created 0 environment store
  have keep1 {location : Nat} {old : Value} (found : store.read? location = some old) : store1.read? location = some old := by
    change (StorageCorrespondence.putStore accounts targetWord created 0 environment store).read? location = _
    rw [same1]
    exact StorageCorrespondence.appended_read found _
  have bound1 := (List.getElem?_eq_some_iff.mp (keep1 worldRead)).1
  let store2 : Store := store1.set locations.world insertedValue
  have stored : Evaluates (insertedValue :: environment) store1
      (CodeBuilder.store world (fun here => .var (here - depth - 1)) (depth + 1)) .unit store2 :=
    .storeCell ((worldCode.prepend [insertedValue]).evaluates store1) (keep1 worldRead)
      ((CodeValue.bound depth environment insertedValue).evaluates store1) (Store.write?_eq_some_iff.mpr ⟨bound1, rfl⟩)
  have balancesRead2 : store2.read? locations.balances = some (WordMapping.encode before) := by
    change (store1.set locations.world insertedValue)[locations.balances]? = _
    rw [List.getElem?_set_ne worldBalances]
    exact keep1 balancesRead
  have frame2 : Rewrites [locations.world] store store2 := by
    refine ⟨?_, fun other old outside found => ?_⟩
    · change store.length ≤ (store1.set _ _).length
      rw [List.length_set]
      change store.length ≤ (StorageCorrespondence.putStore accounts targetWord created 0 environment store).length
      rw [same1]; simp
    · change (store1.set locations.world insertedValue)[other]? = _
      rw [List.getElem?_set_ne (fun same => outside (by simp [same]))]
      exact keep1 found
  obtain ⟨store3, failed, retained⟩ := transfer_overflow (creatorCode := creator) (creatorBalanceCode := creatorBalance)
    (balancesCode.prepend [.unit, insertedValue]) (targetValue.prepend [.unit, insertedValue])
    (valueValue.prepend [.unit, insertedValue]) balancesRead2 overflowed
  refine ⟨store3, ?_, frame2.trans (Rewrites.ofRetains retained)⟩
  unfold CreationImplementation.deployment
  apply LanguageResult.bind_success _ inserted
  apply Evaluates.letE stored
  exact LanguageResult.bind_failure _ failed

/-- A target absent from an incomplete world is failure 7. -/
theorem attempt_absent {depth : Nat} {environment : Environment} {store : Store}
    {runInit installRuntime : Code → Code → Code}
    {world balances complete creator value creatorBalance request target restore : Code}
    {location : Nat} {accounts : StorageCorrespondence.Accounts} {targetWord : Word}
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type location))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (completeValue : CodeValue depth environment complete (.bool false))
    (worldRead : store.read? location = some (StorageCorrespondence.world accounts))
    (absent : StorageCorrespondence.lookup targetWord accounts = none) :
    ∃ final, Evaluates environment store
        (CreationImplementation.attempt runInit installRuntime world balances complete creator value creatorBalance
          request target restore depth) (.inLeft Creation.responseType (.word (Word.ofNatModulo 7))) final ∧
      StoreRetains store final := by
  have fetched := StorageCorrespondence.get_evaluates (environment := environment) (initial := store)
    (worldStore := store) (addressStore := store) (final := store) accounts targetWord false
    (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store) (completeValue.evaluates store)
  have obtained : StorageCorrespondence.get accounts targetWord false = .error (Word.ofNatModulo 7) := by
    simp only [StorageCorrespondence.get, absent, Bool.false_eq_true, ↓reduceIte]
  rw [obtained] at fetched
  refine ⟨StorageCorrespondence.getStore accounts targetWord false environment store, ?_, StoreRetains.append _ _⟩
  unfold CreationImplementation.attempt
  exact LanguageResult.bind_failure _ fetched

/-- A record with a zero nonce and unknown code is failure 7. -/
theorem attempt_unknownCode {depth : Nat} {environment : Environment} {store : Store}
    {runInit installRuntime : Code → Code → Code}
    {world balances complete creator value creatorBalance request target restore : Code}
    {location : Nat} {accounts : StorageCorrespondence.Accounts} {targetWord : Word} {completeFlag : Bool}
    {existing : AccountState.Account} {identity : Nat}
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type location))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (completeValue : CodeValue depth environment complete (.bool completeFlag))
    (worldRead : store.read? location = some (StorageCorrespondence.world accounts))
    (obtained : StorageCorrespondence.get accounts targetWord completeFlag = .ok (existing, identity))
    (zero : existing.nonce = Word.zero) (unknown : existing.code = none) :
    ∃ final, Evaluates environment store
        (CreationImplementation.attempt runInit installRuntime world balances complete creator value creatorBalance
          request target restore depth) (.inLeft Creation.responseType (.word (Word.ofNatModulo 7))) final ∧
      StoreRetains store final := by
  have fetched := StorageCorrespondence.get_evaluates (environment := environment) (initial := store)
    (worldStore := store) (addressStore := store) (final := store) accounts targetWord completeFlag
    (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store) (completeValue.evaluates store)
  rw [obtained] at fetched
  let fetchedStore := StorageCorrespondence.getStore accounts targetWord completeFlag environment store
  let recordValue := StorageCorrespondence.record existing identity
  have recordCode := CodeValue.bound depth environment recordValue
  have nonceZero : ¬existing.nonce > Word.ofNatModulo 0 := by rw [zero]; decide
  have sizeZero : ¬Word.ofNatModulo (existing.code.getD []).length > Word.ofNatModulo 0 := by rw [unknown]; decide
  refine ⟨fetchedStore, ?_, StoreRetains.append _ _⟩
  unfold CreationImplementation.attempt
  apply LanguageResult.bind_success _ fetched
  apply Evaluates.ifFalse (.binary ((recordCode.part (index := 2) rfl).evaluates fetchedStore) .word
    (by simp only [BinaryOp.apply, nonceZero, decide_false]))
  apply Evaluates.ifFalse (.binary ((recordCode.part (index := 5) rfl).evaluates fetchedStore) .word
    (by simp only [BinaryOp.apply, sizeZero, decide_false]))
  exact .ifFalse ((recordCode.part (index := 6) (value := .bool false) (by simp [unknown])).evaluates
    fetchedStore) (.inLeft .word)

/-- A target absent from a complete world whose endowment would overflow is
failure 12 after the new record is inserted. -/
theorem attempt_overflow {depth : Nat} {environment : Environment} {store : Store}
    {runInit installRuntime : Code → Code → Code} {locations : SharedLocations}
    {world balances complete creator value creatorBalance request target restore : Code}
    {accounts : StorageCorrespondence.Accounts} {before : StorageSemantics.Words}
    {creatorWord valueWord targetWord : Word}
    (worldCode : CodeValue depth environment world (.cellRef AccountState.type locations.world))
    (balancesCode : CodeValue depth environment balances (.cellRef WordMapping.type locations.balances))
    (completeValue : CodeValue depth environment complete (.bool true))
    (valueValue : CodeValue depth environment value (.word valueWord))
    (targetValue : CodeValue depth environment target (.word targetWord))
    (worldRead : store.read? locations.world = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? locations.balances = some (WordMapping.encode before))
    (worldBalances : locations.world ≠ locations.balances)
    (absent : StorageCorrespondence.lookup targetWord accounts = none)
    (overflowed : AccountCallSemantics.transfer creatorWord targetWord valueWord before = .error (Word.ofNatModulo 12)) :
    ∃ final, Evaluates environment store
        (CreationImplementation.attempt runInit installRuntime world balances complete creator value creatorBalance
          request target restore depth) (.inLeft Creation.responseType (.word (Word.ofNatModulo 12))) final ∧
      Rewrites [locations.world] store final := by
  have fetched := StorageCorrespondence.get_evaluates (environment := environment) (initial := store)
    (worldStore := store) (addressStore := store) (final := store) accounts targetWord true
    (.loadCell (worldCode.evaluates store) worldRead) (targetValue.evaluates store) (completeValue.evaluates store)
  have obtained : StorageCorrespondence.get accounts targetWord true = .ok ({address := targetWord}, 0) := by
    simp only [StorageCorrespondence.get, absent, ↓reduceIte]
  rw [obtained] at fetched
  let fetchedStore := StorageCorrespondence.getStore accounts targetWord true environment store
  obtain ⟨suffix, _, same⟩ := StorageCorrespondence.getStore_extension accounts targetWord true environment store
  have keep {location : Nat} {old : Value} (found : store.read? location = some old) :
      fetchedStore.read? location = some old := by
    change (StorageCorrespondence.getStore accounts targetWord true environment store).read? location = _
    rw [same]
    exact StorageCorrespondence.appended_read found _
  let recordValue := StorageCorrespondence.record {address := targetWord} 0
  have recordCode := CodeValue.bound depth environment recordValue
  obtain ⟨final, failed, frame⟩ := deployment_overflow (runInit := runInit) (installRuntime := installRuntime)
    (creator := creator) (creatorBalance := creatorBalance) (request := request) (restore := restore)
    (worldCode.prepend [recordValue]) (balancesCode.prepend [recordValue]) (valueValue.prepend [recordValue])
    (targetValue.prepend [recordValue]) (keep worldRead) (keep balancesRead) worldBalances overflowed
  refine ⟨final, ?_, ?_⟩
  · unfold CreationImplementation.attempt
    apply LanguageResult.bind_success _ fetched
    apply Evaluates.ifFalse (.binary ((recordCode.part (index := 2) rfl).evaluates fetchedStore) .word
      (by simp [BinaryOp.apply]; decide))
    apply Evaluates.ifFalse (.binary ((recordCode.part (index := 5) rfl).evaluates fetchedStore) .word
      (by simp [BinaryOp.apply]))
    exact .ifTrue ((recordCode.part (index := 6) rfl).evaluates fetchedStore) failed
  · have appended : Rewrites [locations.world] store fetchedStore := by
      change Rewrites _ store (StorageCorrespondence.getStore accounts targetWord true environment store)
      rw [same]
      exact Rewrites.append _ _ _
    exact appended.trans frame

theorem Rewrites.set_member {changed : List Nat} {initial current : Store} {location : Nat} {value : Value}
    (rewrites : Rewrites changed initial current) (member : location ∈ changed) :
    Rewrites changed initial (current.set location value) :=
  ⟨by simpa only [List.length_set] using rewrites.length_le, fun other old outside found => by
    change (current.set location value)[other]? = _
    rw [List.getElem?_set_ne (fun same : location = other => outside (same ▸ member))]
    exact rewrites.read other old outside found⟩

/-- Restoring a cell to its initial value keeps the frame. -/
theorem Rewrites.set_same {changed : List Nat} {initial current : Store} {location : Nat} {value : Value}
    (rewrites : Rewrites changed initial current) (found : initial.read? location = some value) :
    Rewrites changed initial (current.set location value) := by
  refine ⟨by simpa only [List.length_set] using rewrites.length_le, fun other old outside foundOther => ?_⟩
  change (current.set location value)[other]? = _
  by_cases same : location = other
  · subst same
    have bound : location < current.length :=
      Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp found).1 rewrites.length_le
    rw [List.getElem?_set_self bound]
    exact found.symm.trans foundOther
  · rw [List.getElem?_set_ne same]
    exact rewrites.read other old outside foundOther

theorem source_get {accounts : StorageCorrespondence.Accounts} {world : StorageSemantics.World}
    (same : accounts.map Prod.fst = world) {address : Word} {complete : Bool} {account : AccountState.Account}
    (found : StorageSemantics.get world address complete = .ok account) :
    ∃ identity, StorageCorrespondence.get accounts address complete = .ok (account, identity) := by
  have sourced := StorageCorrespondence.get_source accounts address complete
  rw [same, found] at sourced
  cases obtained : StorageCorrespondence.get accounts address complete with
  | error reason => simp [obtained, Except.map] at sourced
  | ok entry =>
      simp only [obtained, Except.map, Except.ok.injEq] at sourced
      exact ⟨entry.2, by rw [← sourced]⟩

/-- The admitted remainder up to the protected attempt on the target: the
address, the nonce advance and the checkpoint. The protected attempt is
evaluated after the nonce write. -/
theorem admitted_prefix {depth : Nat} {environment : Environment} {store : Store}
    {runInit installRuntime : Code → Code → Code} {args creatorBalance creatorRecord : Code}
    {locations : SharedLocations} {accounts : StorageCorrespondence.Accounts} {account : AccountState.Account}
    {identity : Nat} {target : Word} {complete : Bool} {balances : StorageSemantics.Words}
    {logs : MemorySemantics.Entries} {logSize : Word} {request : Request} {result : Value}
    {property : Store → Prop}
    (argsCode : CodeValue depth environment args (bundleValues [.cellRef AccountState.type locations.world,
      .cellRef WordMapping.type locations.balances, .cellRef WordMapping.type locations.logs,
      .cellRef .word locations.logSize, .bool complete, requestValue request]))
    (recordCode : CodeValue depth environment creatorRecord (StorageCorrespondence.record account identity))
    (distinct : locations.all.Nodup)
    (worldRead : store.read? locations.world = some (StorageCorrespondence.world accounts))
    (balancesRead : store.read? locations.balances = some (WordMapping.encode balances))
    (logsRead : store.read? locations.logs = some (WordMapping.encode logs))
    (logSizeRead : store.read? locations.logSize = some (.word logSize))
    (obtained : StorageCorrespondence.get accounts (request.creator.bitAnd addressMask) complete = .ok (account, identity))
    (bounded : request.initLength.val ≤ 49152)
    (derived : CreationAddressSemantics.Derived (request.creator.bitAnd addressMask) account.nonce
      request.initCode request.initLength request.scheme target)
    (attempted : ∀ current, Overwrites locations.world store current →
      current.read? locations.world = some (StorageCorrespondence.world (StorageCorrespondence.put
        (request.creator.bitAnd addressMask) {account with nonce := account.nonce.add (Word.ofNatModulo 1)} identity accounts)) →
      ∃ final, Evaluates ([.word logSize, WordMapping.encode logs, WordMapping.encode balances,
          StorageCorrespondence.world (StorageCorrespondence.put (request.creator.bitAnd addressMask)
            {account with nonce := account.nonce.add (Word.ofNatModulo 1)} identity accounts),
          .unit, .word target] ++ environment) current
        (CreationImplementation.protect
          (restoreCode (part 0 6 args) (part 1 6 args) (part 2 6 args) (part 3 6 args) (depth + 2))
          (CreationImplementation.attempt runInit installRuntime (part 0 6 args) (part 1 6 args) (part 4 6 args)
            (address (part 0 8 (part 5 6 args))) (part 1 8 (part 5 6 args)) creatorBalance (part 5 6 args)
            (fun here => .var (here - depth - 1))
            (restoreCode (part 0 6 args) (part 1 6 args) (part 2 6 args) (part 3 6 args) (depth + 2))) (depth + 6))
        result final ∧ property final) :
    ∃ final, Evaluates environment store
      (CreationImplementation.admitted runInit installRuntime args creatorBalance creatorRecord depth)
      result final ∧ property final := by
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at distinct
  obtain ⟨⟨worldLogs, worldSize, worldBalances, _⟩, _, _, _⟩ := distinct
  have requestCode := argsCode.part (index := 5) rfl
  have creatorCode : CodeValue depth environment (address (part 0 8 (part 5 6 args)))
      (.word (request.creator.bitAnd addressMask)) :=
    CreationAddressCorrespondence.binary_code (op := .wordAnd) (requestCode.part (index := 0) rfl)
      (CodeValue.number (2 ^ 160 - 1) depth environment) rfl
  have nonceCode := recordCode.part (index := 2) rfl
  obtain ⟨store4, derivedEvaluated, derivedRetained⟩ := deriveAddress_evaluates creatorCode nonceCode requestCode
    bounded derived
  have keep4 {location : Nat} {old : Value} (found : store.read? location = some old) :
      store4.read? location = some old :=
    (derivedRetained.read location (List.getElem?_eq_some_iff.mp found).1).trans found
  have argumentsEvaluated : Evaluates (.word target :: environment) store4
      (bundle [part 0 6 args (depth + 1), address (part 0 8 (part 5 6 args)) (depth + 1), part 4 6 args (depth + 1),
        binary .wordAdd (part 2 9 creatorRecord) (number 1) (depth + 1)])
      (bundleValues [.cellRef AccountState.type locations.world, .word (request.creator.bitAnd addressMask),
        .bool complete, .word (account.nonce.add (Word.ofNatModulo 1))]) store4 :=
    .pair (((argsCode.part (index := 0) rfl).prepend [.word target]).evaluates store4)
      (.pair ((creatorCode.prepend [.word target]).evaluates store4)
        (.pair (((argsCode.part (index := 4) rfl).prepend [.word target]).evaluates store4)
          (.binary ((nonceCode.prepend [.word target]).evaluates store4) .word rfl)))
  obtain ⟨store5, nonceEvaluated, worldRead5, overwrites5⟩ := writeNonce_evaluates accounts locations.world _ complete _
    argumentsEvaluated (keep4 worldRead) obtained
  have keep5 {location : Nat} {old : Value} (different : location ≠ locations.world)
      (found : store.read? location = some old) : store5.read? location = some old :=
    overwrites5.read location old different (keep4 found)
  obtain ⟨final, attemptEvaluated, property⟩ := attempted store5
    ((Overwrites.ofRetains derivedRetained).trans overwrites5) worldRead5
  refine ⟨final, ?_, property⟩
  unfold CreationImplementation.admitted
  apply LanguageResult.bind_success _ derivedEvaluated
  apply LanguageResult.bind_success _ nonceEvaluated
  apply checkpoint_evaluates (((argsCode.part (index := 0) rfl).prepend [.unit, .word target]))
    (((argsCode.part (index := 1) rfl).prepend [.unit, .word target]))
    (((argsCode.part (index := 2) rfl).prepend [.unit, .word target]))
    (((argsCode.part (index := 3) rfl).prepend [.unit, .word target])) worldRead5
    (keep5 (Ne.symm worldBalances) balancesRead) (keep5 (Ne.symm worldLogs) logsRead) (keep5 (Ne.symm worldSize) logSizeRead)
  exact attemptEvaluated

/-- The six dispatcher arguments as the handler packs them. -/
def argumentsValue (locations : SharedLocations) (complete : Bool) (request : Request) : Value :=
  bundleValues [.cellRef AccountState.type locations.world,
    .cellRef WordMapping.type locations.balances, .cellRef WordMapping.type locations.logs,
    .cellRef .word locations.logSize, .bool complete, requestValue request]

/-- The environment of the attempt on the target, after the checkpoint loads. -/
def attemptEnvironment (environment : Environment) (locations : SharedLocations) (state : AccountCallSemantics.Shared)
    (request : Request) (account : AccountState.Account) (identity : Nat) (target : Word)
    (advanced : StorageCorrespondence.Accounts) : Environment :=
  [.word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances,
    StorageCorrespondence.world advanced, .unit, .word target,
    StorageCorrespondence.record account identity,
    .word (StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances),
    argumentsValue locations state.complete request] ++ environment

/-- The accounts after the creator nonce advances. -/
def advancedAccounts (accounts : StorageCorrespondence.Accounts) (creator : Word) (account : AccountState.Account)
    (identity : Nat) : StorageCorrespondence.Accounts :=
  StorageCorrespondence.put creator {account with nonce := account.nonce.add (Word.ofNatModulo 1)} identity accounts

/-- The checkpoint restoration seen by the attempt of a dispatcher whose
arguments are bound at `depth`. -/
def attemptRestore (depth : Nat) : Code :=
  restoreCode (part 0 6 (fun here => .var (here - depth - 1))) (part 1 6 (fun here => .var (here - depth - 1)))
    (part 2 6 (fun here => .var (here - depth - 1))) (part 3 6 (fun here => .var (here - depth - 1))) (depth + 5)

/-- A failed attempt inside the dispatcher restores the four checkpointed
cells: the world keeps the nonce advance, and balances and logs return to their
values before the attempt. -/
theorem attempt_restored {depth : Nat} {environment : Environment} {store current failed : Store}
    {locations : SharedLocations} {state : AccountCallSemantics.Shared} {request : Request}
    {account : AccountState.Account} {identity : Nat} {target : Word} {advanced : StorageCorrespondence.Accounts}
    {attempt : Code} {reason : Word} {failedType : Core.Ty}
    (related : SharedStateRel locations state store)
    (attempted : Evaluates (attemptEnvironment environment locations state request account identity target advanced)
      current (attempt (depth + 9)) (.inLeft failedType (.word reason)) failed)
    (rewrites : Rewrites [locations.world, locations.balances] store failed) :
    ∃ final, Evaluates (attemptEnvironment environment locations state request account identity target advanced)
        current (CreationImplementation.protect (attemptRestore depth) attempt (depth + 9))
        (.inLeft Creation.responseType (.word reason)) final ∧
      final.read? locations.world = some (StorageCorrespondence.world advanced) ∧
      final.read? locations.balances = some (WordMapping.encode state.balances) ∧
      final.read? locations.logs = some (WordMapping.encode state.logs) ∧
      final.read? locations.logSize = some (.word state.logSize) ∧
      Rewrites [locations.world, locations.balances] store final := by
  have distinct := related.distinct
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at distinct
  obtain ⟨⟨worldLogs, worldSize, worldBalances, _⟩, ⟨logsSize, logsBalances, _⟩, ⟨sizeBalances, _⟩, _⟩ := distinct
  obtain ⟨_, _, worldRead⟩ := related.world
  have bound {location : Nat} {value : Value} (found : store.read? location = some value) :
      location < failed.length :=
    Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp found).1 rewrites.length_le
  let argsValue := argumentsValue locations state.complete request
  let creatorBalance : Value := .word (StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
  let below : Environment := [.unit, .word target, StorageCorrespondence.record account identity, creatorBalance,
    argsValue] ++ environment
  have args := (CodeValue.bound depth environment argsValue).prepend [.word reason, .word state.logSize,
    WordMapping.encode state.logs, WordMapping.encode state.balances, StorageCorrespondence.world advanced, .unit,
    .word target, StorageCorrespondence.record account identity, creatorBalance]
  have savedWorld := (CodeValue.bound (depth + 5) below (StorageCorrespondence.world advanced)).prepend
    [.word reason, .word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances]
  have savedBalances := (CodeValue.bound (depth + 6) (StorageCorrespondence.world advanced :: below)
    (WordMapping.encode state.balances)).prepend [.word reason, .word state.logSize, WordMapping.encode state.logs]
  have savedLogs := (CodeValue.bound (depth + 7)
    (WordMapping.encode state.balances :: StorageCorrespondence.world advanced :: below)
    (WordMapping.encode state.logs)).prepend [.word reason, .word state.logSize]
  have savedLogSize := (CodeValue.bound (depth + 8)
    (WordMapping.encode state.logs :: WordMapping.encode state.balances :: StorageCorrespondence.world advanced :: below)
    (.word state.logSize)).prepend [.word reason]
  have restored := restoreCode_evaluates (checkpoint := depth + 5) (args.part (index := 0) rfl)
    (args.part (index := 1) rfl) (args.part (index := 2) rfl) (args.part (index := 3) rfl)
    savedWorld savedBalances savedLogs savedLogSize (bound worldRead) (bound related.balances) (bound related.logs)
    (bound related.logSize)
  refine ⟨_, protect_failed attempted restored, ?_, ?_, ?_, ?_,
    (((rewrites.set_same related.logSize).set_same related.logs).set_member (by simp)).set_member (by simp)⟩
  · change (List.set _ locations.world _)[locations.world]? = _
    rw [List.getElem?_set_self (by simp only [List.length_set]; exact bound worldRead)]
  · change (List.set _ locations.world _)[locations.balances]? = _
    rw [List.getElem?_set_ne worldBalances, List.getElem?_set_self (by simp only [List.length_set]; exact bound related.balances)]
  · change (List.set _ locations.world _)[locations.logs]? = _
    rw [List.getElem?_set_ne worldLogs, List.getElem?_set_ne (Ne.symm logsBalances),
      List.getElem?_set_self (by simp only [List.length_set]; exact bound related.logs)]
  · change (List.set _ locations.world _)[locations.logSize]? = _
    rw [List.getElem?_set_ne worldSize, List.getElem?_set_ne (Ne.symm sizeBalances), List.getElem?_set_ne logsSize,
      List.getElem?_set_self (bound related.logSize)]

/-- The funds and nonce checks pass, the creator record is read and the
admitted remainder runs; the protected attempt on the target is supplied. -/
theorem dispatchWith_admit {depth : Nat} {environment : Environment} {store : Store}
    {shared : AccountRuntime.References} {locations : SharedLocations}
    {requestCode : Code} {request : Request} {state : AccountCallSemantics.Shared}
    {runInit : Code → Code → Code} {identify : Code → Code}
    {accounts : StorageCorrespondence.Accounts} {account : AccountState.Account} {target : Word}
    {result : Value} {property : Store → Prop}
    (references : SharedReferences depth environment shared locations)
    (requestRelated : CodeValue depth environment requestCode (requestValue request))
    (related : SharedStateRel locations state store)
    (worldSame : accounts.map Prod.fst = state.world)
    (worldRead : store.read? locations.world = some (StorageCorrespondence.world accounts))
    (funded : ¬request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
    (found : StorageSemantics.get state.world (request.creator.bitAnd addressMask) state.complete = .ok account)
    (belowLimit : ¬account.nonce > Word.ofNatModulo (2 ^ 64 - 2))
    (bounded : request.initLength.val ≤ 49152)
    (derived : CreationAddressSemantics.Derived (request.creator.bitAnd addressMask) account.nonce
      request.initCode request.initLength request.scheme target)
    (attempted : ∀ identity,
      StorageCorrespondence.get accounts (request.creator.bitAnd addressMask) state.complete = .ok (account, identity) →
      ∀ current, Overwrites locations.world store current →
      current.read? locations.world = some (StorageCorrespondence.world
        (advancedAccounts accounts (request.creator.bitAnd addressMask) account identity)) →
      ∃ final, Evaluates (attemptEnvironment environment locations state request account identity target
          (advancedAccounts accounts (request.creator.bitAnd addressMask) account identity)) current
        (CreationImplementation.protect (attemptRestore depth)
          (CreationImplementation.attempt runInit (CreationImplementation.installWith identify shared)
            (part 0 6 (fun here => .var (here - depth - 1))) (part 1 6 (fun here => .var (here - depth - 1)))
            (part 4 6 (fun here => .var (here - depth - 1)))
            (address (part 0 8 (part 5 6 (fun here => .var (here - depth - 1)))))
            (part 1 8 (part 5 6 (fun here => .var (here - depth - 1)))) (fun here => .var (here - (depth + 1) - 1))
            (part 5 6 (fun here => .var (here - depth - 1))) (fun here => .var (here - (depth + 3) - 1))
            (attemptRestore depth))
          (depth + 9))
        result final ∧ property final) :
    ∃ final, Evaluates environment store
      (CreationImplementation.dispatchWith (AccountRuntime.reference shared "world")
        (AccountRuntime.reference shared "balances") (AccountRuntime.reference shared "logs")
        (AccountRuntime.reference shared "logSize") (load (AccountRuntime.reference shared "worldComplete"))
        requestCode (CreationImplementation.admitted runInit (CreationImplementation.installWith identify shared)) depth)
        result final ∧ property final := by
  let argsValue := argumentsValue locations state.complete request
  have packed : Evaluates environment store
      (packet [AccountRuntime.reference shared "world", AccountRuntime.reference shared "balances",
        AccountRuntime.reference shared "logs", AccountRuntime.reference shared "logSize",
        load (AccountRuntime.reference shared "worldComplete"), requestCode] depth) argsValue store :=
    .pair (references.world.evaluates store) (.pair (references.balances.evaluates store)
      (.pair (references.logs.evaluates store) (.pair (references.logSize.evaluates store)
        (.pair (.loadCell (references.complete.evaluates store) related.complete) (requestRelated.evaluates store)))))
  have argsCode := CodeValue.bound depth environment argsValue
  have requestCode' : CodeValue (depth + 1) (argsValue :: environment)
      (part 5 6 (fun here => .var (here - depth - 1))) (requestValue request) :=
    argsCode.part (index := 5) rfl
  let key := request.creator.bitAnd addressMask
  have keyEvaluated : Evaluates (argsValue :: environment) store
      (address (part 0 8 (part 5 6 (fun here => .var (here - depth - 1)))) (depth + 1)) (.word key) store :=
    .binary ((requestCode'.part (index := 0) rfl).evaluates store) .word rfl
  obtain ⟨looked, lookedEvaluated, lookedRetained⟩ := lookup_preserves
    (.loadCell ((argsCode.part (index := 1) rfl).evaluates store) related.balances) keyEvaluated
  let balance := StorageSemantics.readWord key state.balances
  have valueEvaluated : Evaluates (.word balance :: argsValue :: environment) looked
      (part 1 8 (part 5 6 (fun here => .var (here - depth - 1))) (depth + 1 + 1)) (.word request.value) looked :=
    ((requestCode'.part (index := 1) rfl).prepend [.word balance]).evaluates looked
  have balanceCode := CodeValue.bound (depth + 1) (argsValue :: environment) (.word balance)
  have keepLooked {location : Nat} {old : Value} (found : store.read? location = some old) :
      looked.read? location = some old :=
    (lookedRetained.read location (List.getElem?_eq_some_iff.mp found).1).trans found
  obtain ⟨identity, got⟩ := source_get worldSame found
  let recordValue := StorageCorrespondence.record account identity
  have worldLoaded : Evaluates (.word balance :: argsValue :: environment) looked
      (load (part 0 6 (fun here => .var (here - depth - 1))) (depth + 1 + 1))
      (StorageCorrespondence.world accounts) looked :=
    .loadCell (((argsCode.part (index := 0) rfl).prepend [.word balance]).evaluates looked) (keepLooked worldRead)
  have creatorEvaluated : Evaluates (.word balance :: argsValue :: environment) looked
      (address (part 0 8 (part 5 6 (fun here => .var (here - depth - 1)))) (depth + 1 + 1)) (.word key) looked :=
    .binary (((requestCode'.part (index := 0) rfl).prepend [.word balance]).evaluates looked) .word rfl
  have completeEvaluated : Evaluates (.word balance :: argsValue :: environment) looked
      (part 4 6 (fun here => .var (here - depth - 1)) (depth + 1 + 1)) (.bool state.complete) looked :=
    ((argsCode.part (index := 4) rfl).prepend [.word balance]).evaluates looked
  have recordRead := StorageCorrespondence.get_evaluates accounts key state.complete
    worldLoaded creatorEvaluated completeEvaluated
  rw [got] at recordRead
  let recordStore := StorageCorrespondence.getStore accounts key state.complete
    (.word balance :: argsValue :: environment) looked
  have recordRetained : StoreRetains looked recordStore := StoreRetains.append _ _
  have retained := lookedRetained.trans recordRetained
  have keepRecord {location : Nat} {old : Value} (found : store.read? location = some old) :
      recordStore.read? location = some old :=
    (retained.read location (List.getElem?_eq_some_iff.mp found).1).trans found
  have recordCode := CodeValue.bound (depth + 2) (.word balance :: argsValue :: environment) recordValue
  obtain ⟨final, admittedEvaluated, holds⟩ := admitted_prefix (property := property)
    (argsCode.prepend [recordValue, .word balance]) recordCode related.distinct (keepRecord worldRead)
    (keepRecord related.balances) (keepRecord related.logs) (keepRecord related.logSize) got bounded derived
    (fun current overwrites read => attempted identity got current
      ((Overwrites.ofRetains retained).trans overwrites) read)
  refine ⟨final, ?_, holds⟩
  unfold CreationImplementation.dispatchWith
  apply Evaluates.letE packed
  apply LanguageResult.bind_success Creation.responseType lookedEvaluated
  apply Evaluates.ifFalse (.binary valueEvaluated (balanceCode.evaluates looked)
    (by simp [BinaryOp.apply, balance, key, funded]))
  apply LanguageResult.bind_success Creation.responseType recordRead
  apply Evaluates.ifFalse (.binary ((recordCode.part (index := 2) rfl).evaluates recordStore) .word
    (by simp [BinaryOp.apply, belowLimit]))
  exact admittedEvaluated

theorem Rewrites.mono {changed wider : List Nat} {initial final : Store} (rewrites : Rewrites changed initial final)
    (included : ∀ location ∈ changed, location ∈ wider) : Rewrites wider initial final :=
  ⟨rewrites.length_le, fun other value outside found =>
    rewrites.read other value (fun member => outside (included other member)) found⟩

theorem advanced_source {accounts : StorageCorrespondence.Accounts} {state : AccountCallSemantics.Shared}
    (worldSame : accounts.map Prod.fst = state.world) (creator : Word) (account : AccountState.Account) (identity : Nat) :
    (advancedAccounts accounts creator account identity).map Prod.fst = advancedWorld state creator account := by
  unfold advancedAccounts advancedWorld
  rw [StorageCorrespondence.put_source, worldSame]

/-- Applying the dispatcher to an admitted attempt without an init frame
publishes its account and balance changes. Logs and other cells are kept. -/
theorem dispatchWith_admitted {depth : Nat} {environment : Environment} {store : Store}
    {shared : AccountRuntime.References} {locations : SharedLocations}
    {anchors : List CatalogWorldCorrespondence.Anchor}
    {requestCode : Code} {request : Request} {state next : AccountCallSemantics.Shared} {response : Value}
    {runInit : Code → Code → Code} {identify : Code → Code}
    (references : SharedReferences depth environment shared locations)
    (requestRelated : CodeValue depth environment requestCode (requestValue request))
    (related : LinkedSharedStateRel anchors locations state store)
    (admitting : Admitting state request response next) :
    ∃ final, Evaluates environment store
      (CreationImplementation.dispatchWith (AccountRuntime.reference shared "world")
        (AccountRuntime.reference shared "balances") (AccountRuntime.reference shared "logs")
        (AccountRuntime.reference shared "logSize") (load (AccountRuntime.reference shared "worldComplete"))
        requestCode (CreationImplementation.admitted runInit (CreationImplementation.installWith identify shared)) depth)
        response final ∧
      LinkedSharedStateRel anchors locations next final ∧ Rewrites [locations.world, locations.balances] store final := by
  obtain ⟨accounts, worldSame, links, worldRead⟩ := related.linked
  have sharedRelated := related.shared
  have distinct := sharedRelated.distinct
  simp only [SharedLocations.all, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at distinct
  obtain ⟨⟨worldLogs, worldSize, worldBalances, worldComplete⟩, ⟨logsSize, logsBalances, logsComplete⟩,
    ⟨sizeBalances, sizeComplete⟩, balancesComplete⟩ := distinct
  let key := request.creator.bitAnd addressMask
  let argsValue := argumentsValue locations state.complete request
  have argsCode := CodeValue.bound depth environment argsValue
  have identityOf {account : AccountState.Account} {identity other : Nat}
      (first : StorageCorrespondence.get accounts key state.complete = .ok (account, identity))
      (second : StorageCorrespondence.get accounts key state.complete = .ok (account, other)) : identity = other := by
    have equal := Except.ok.inj (first.symm.trans second)
    exact (Prod.mk.inj equal).2
  cases admitting with
  | collision funded found belowLimit bounded derived occupied used =>
      rename_i account existing target
      obtain ⟨identity, got⟩ := source_get worldSame found
      let advanced := advancedAccounts accounts key account identity
      have advancedSame := advanced_source worldSame key account identity
      obtain ⟨final, evaluated, worldFinal, rewrites⟩ := dispatchWith_admit (runInit := runInit) (identify := identify)
        (property := fun final => final.read? locations.world = some (StorageCorrespondence.world advanced) ∧
          Rewrites [locations.world] store final)
        references requestRelated sharedRelated worldSame worldRead funded found belowLimit bounded derived
        (fun other gotOther current overwrites read => by
          have same := identityOf got gotOther
          subst same
          obtain ⟨identityE, lookedUp⟩ := CatalogWorldCorrespondence.lookup_of_source
            (accounts := advanced) (by rw [advancedSame]; exact occupied)
          have obtainedE : StorageCorrespondence.get advanced target state.complete = .ok (existing, identityE) := by
            simp only [StorageCorrespondence.get, lookedUp]
          let extra : Environment := [.word state.logSize, WordMapping.encode state.logs,
            WordMapping.encode state.balances, StorageCorrespondence.world advanced, .unit, .word target,
            StorageCorrespondence.record account identity, .word (StorageSemantics.readWord key state.balances)]
          have args9 := argsCode.prepend extra
          have target9 := (CodeValue.bound (depth + 3) ([StorageCorrespondence.record account identity,
            .word (StorageSemantics.readWord key state.balances)] ++ argsValue :: environment) (.word target)).prepend
            [.word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances,
              StorageCorrespondence.world advanced, .unit]
          obtain ⟨final, evaluated, retained⟩ := attempt_collision (runInit := runInit)
            (installRuntime := CreationImplementation.installWith identify shared)
            (args9.part (index := 0) rfl) target9 (args9.part (index := 4) rfl) read obtainedE used
          exact ⟨final, protect_succeeded evaluated,
            (retained.read locations.world (List.getElem?_eq_some_iff.mp read).1).trans read,
            (Rewrites.ofOverwrites overwrites (by simp)).trans (Rewrites.ofRetains retained)⟩)
      refine ⟨final, evaluated, ⟨⟨⟨advanced, advancedSame, worldFinal⟩, ?_, ?_, ?_, ?_, sharedRelated.distinct⟩,
        ⟨advanced, advancedSame, links_put_same links got rfl, worldFinal⟩⟩, rewrites.mono (by simp)⟩
      · exact rewrites.read _ _ (by simp [Ne.symm worldLogs]) sharedRelated.logs
      · exact rewrites.read _ _ (by simp [Ne.symm worldSize]) sharedRelated.logSize
      · exact rewrites.read _ _ (by simp [Ne.symm worldBalances]) sharedRelated.balances
      · exact rewrites.read _ _ (by simp [Ne.symm worldComplete]) sharedRelated.complete
  | deployed funded found belowLimit bounded derived absent complete emptyInit transferred =>
      rename_i account target balances
      obtain ⟨identity, got⟩ := source_get worldSame found
      let advanced := advancedAccounts accounts key account identity
      have advancedSame := advanced_source worldSame key account identity
      have absentAdvanced : StorageCorrespondence.lookup target advanced = none := by
        have sourced := StorageCorrespondence.lookup_source advanced target
        rw [advancedSame, absent] at sourced
        cases lookedUp : StorageCorrespondence.lookup target advanced with
        | none => rfl
        | some entry => simp [lookedUp] at sourced
      have different : key ≠ target := by
        intro same
        have present := CatalogWorldCorrespondence.lookup_put_same accounts key
          {account with nonce := account.nonce.add (Word.ofNatModulo 1)} identity
        change StorageCorrespondence.lookup target (StorageCorrespondence.put key _ identity accounts) = none at absentAdvanced
        rw [← same, present] at absentAdvanced
        cases absentAdvanced
      let deployedAccounts := StorageCorrespondence.put target (CreationSemantics.createdAccount target) 0 advanced
      obtain ⟨final, evaluated, worldFinal, balancesFinal, rewrites⟩ := dispatchWith_admit (runInit := runInit)
        (identify := identify)
        (property := fun final => final.read? locations.world = some (StorageCorrespondence.world deployedAccounts) ∧
          final.read? locations.balances = some (WordMapping.encode balances) ∧
          Rewrites [locations.world, locations.balances] store final)
        references requestRelated sharedRelated worldSame worldRead funded found belowLimit bounded derived
        (fun other gotOther current overwrites read => by
          have same := identityOf got gotOther
          subst same
          let extra : Environment := [.word state.logSize, WordMapping.encode state.logs,
            WordMapping.encode state.balances, StorageCorrespondence.world advanced, .unit, .word target,
            StorageCorrespondence.record account identity, .word (StorageSemantics.readWord key state.balances)]
          have args9 := argsCode.prepend extra
          have target9 := (CodeValue.bound (depth + 3) ([StorageCorrespondence.record account identity,
            .word (StorageSemantics.readWord key state.balances)] ++ argsValue :: environment) (.word target)).prepend
            [.word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances,
              StorageCorrespondence.world advanced, .unit]
          have balance9 := (CodeValue.bound (depth + 1) (argsValue :: environment)
            (.word (StorageSemantics.readWord key state.balances))).prepend
            [.word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances,
              StorageCorrespondence.world advanced, .unit, .word target, StorageCorrespondence.record account identity]
          have request9 := args9.part (index := 5) rfl
          have creator9 := CreationAddressCorrespondence.binary_code (op := .wordAnd) (request9.part (index := 0) rfl)
            (CodeValue.number (2 ^ 160 - 1) _ _) rfl
          have complete9 := args9.part (index := 4) rfl
          rw [complete] at complete9
          have balancesRead := overwrites.read _ _ (Ne.symm worldBalances) sharedRelated.balances
          have completeRead := overwrites.read _ _ (Ne.symm worldComplete) sharedRelated.complete
          rw [complete] at completeRead
          obtain ⟨final, evaluated, worldFinal, balancesFinal, rewrites⟩ := attempt_deployed (runInit := runInit)
            (identify := identify) (restore := restoreCode (part 0 6 (fun here => .var (here - depth - 1)))
              (part 1 6 (fun here => .var (here - depth - 1))) (part 2 6 (fun here => .var (here - depth - 1)))
              (part 3 6 (fun here => .var (here - depth - 1))) (depth + 5))
            (references.prepend (extra ++ [argsValue])) (args9.part (index := 0) rfl) (args9.part (index := 1) rfl)
            complete9 creator9 (request9.part (index := 1) rfl) balance9 request9 target9 read balancesRead completeRead
            sharedRelated.distinct absentAdvanced different emptyInit transferred
          exact ⟨final, protect_succeeded evaluated, worldFinal, balancesFinal,
            (Rewrites.ofOverwrites overwrites (by simp)).trans rewrites⟩)
      refine ⟨final, evaluated, ⟨⟨⟨deployedAccounts, ?_, worldFinal⟩, ?_, ?_, balancesFinal, ?_, sharedRelated.distinct⟩,
        ⟨deployedAccounts, ?_, links_put_absent (accounts := advanced)
          (links_put_same (updated := {account with nonce := account.nonce.add (Word.ofNatModulo 1)}) links got rfl)
          absentAdvanced _ 0, worldFinal⟩⟩, rewrites⟩
      · rw [StorageCorrespondence.put_source, advancedSame]
      · exact rewrites.read _ _ (by simp [Ne.symm worldLogs, logsBalances]) sharedRelated.logs
      · exact rewrites.read _ _ (by simp [Ne.symm worldSize, sizeBalances]) sharedRelated.logSize
      · exact rewrites.read _ _ (by simp [Ne.symm worldComplete, Ne.symm balancesComplete.1]) sharedRelated.complete
      · rw [StorageCorrespondence.put_source, advancedSame]
  | unknown funded found belowLimit bounded derived unknown =>
      rename_i account target
      obtain ⟨identity, got⟩ := source_get worldSame found
      let advanced := advancedAccounts accounts key account identity
      have advancedSame := advanced_source worldSame key account identity
      obtain ⟨final, evaluated, worldFinal, balancesFinal, logsFinal, logSizeFinal, rewrites⟩ := dispatchWith_admit
        (runInit := runInit) (identify := identify)
        (property := fun final => final.read? locations.world = some (StorageCorrespondence.world advanced) ∧
          final.read? locations.balances = some (WordMapping.encode state.balances) ∧
          final.read? locations.logs = some (WordMapping.encode state.logs) ∧
          final.read? locations.logSize = some (.word state.logSize) ∧
          Rewrites [locations.world, locations.balances] store final)
        references requestRelated sharedRelated worldSame worldRead funded found belowLimit bounded derived
        (fun other gotOther current overwrites read => by
          have same := identityOf got gotOther
          subst same
          let extra : Environment := [.word state.logSize, WordMapping.encode state.logs,
            WordMapping.encode state.balances, StorageCorrespondence.world advanced, .unit, .word target,
            StorageCorrespondence.record account identity, .word (StorageSemantics.readWord key state.balances)]
          have args9 := argsCode.prepend extra
          have target9 := (CodeValue.bound (depth + 3) ([StorageCorrespondence.record account identity,
            .word (StorageSemantics.readWord key state.balances)] ++ argsValue :: environment) (.word target)).prepend
            [.word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances,
              StorageCorrespondence.world advanced, .unit]
          cases unknown with
          | absent absent incomplete =>
              have absentAdvanced : StorageCorrespondence.lookup target advanced = none := by
                have sourced := StorageCorrespondence.lookup_source advanced target
                rw [advancedSame, absent] at sourced
                cases lookedUp : StorageCorrespondence.lookup target advanced with
                | none => rfl
                | some entry => simp [lookedUp] at sourced
              have complete9 := args9.part (index := 4) rfl
              rw [incomplete] at complete9
              obtain ⟨failed, attempted, retained⟩ := attempt_absent (runInit := runInit)
                (installRuntime := CreationImplementation.installWith identify shared)
                (args9.part (index := 0) rfl) target9 complete9 read absentAdvanced
              exact attempt_restored sharedRelated attempted
                ((Rewrites.ofOverwrites overwrites (by simp)).trans (Rewrites.ofRetains retained))
          | unknownCode occupied zero unknownCode =>
              rename_i existing
              obtain ⟨identityE, lookedUp⟩ := CatalogWorldCorrespondence.lookup_of_source
                (accounts := advanced) (by rw [advancedSame]; exact occupied)
              have obtainedE : StorageCorrespondence.get advanced target state.complete = .ok (existing, identityE) := by
                simp only [StorageCorrespondence.get, lookedUp]
              obtain ⟨failed, attempted, retained⟩ := attempt_unknownCode (runInit := runInit)
                (installRuntime := CreationImplementation.installWith identify shared)
                (args9.part (index := 0) rfl) target9 (args9.part (index := 4) rfl) read obtainedE zero unknownCode
              exact attempt_restored sharedRelated attempted
                ((Rewrites.ofOverwrites overwrites (by simp)).trans (Rewrites.ofRetains retained)))
      refine ⟨final, evaluated, ⟨⟨⟨advanced, advancedSame, worldFinal⟩, logsFinal, logSizeFinal, balancesFinal, ?_,
        sharedRelated.distinct⟩, ⟨advanced, advancedSame, links_put_same links got rfl, worldFinal⟩⟩, rewrites⟩
      exact rewrites.read _ _ (by simp [Ne.symm worldComplete, Ne.symm balancesComplete.1]) sharedRelated.complete
  | overflow funded found belowLimit bounded derived absent complete overflowed =>
      rename_i account target
      obtain ⟨identity, got⟩ := source_get worldSame found
      let advanced := advancedAccounts accounts key account identity
      have advancedSame := advanced_source worldSame key account identity
      have absentAdvanced : StorageCorrespondence.lookup target advanced = none := by
        have sourced := StorageCorrespondence.lookup_source advanced target
        rw [advancedSame, absent] at sourced
        cases lookedUp : StorageCorrespondence.lookup target advanced with
        | none => rfl
        | some entry => simp [lookedUp] at sourced
      obtain ⟨final, evaluated, worldFinal, balancesFinal, logsFinal, logSizeFinal, rewrites⟩ := dispatchWith_admit
        (runInit := runInit) (identify := identify)
        (property := fun final => final.read? locations.world = some (StorageCorrespondence.world advanced) ∧
          final.read? locations.balances = some (WordMapping.encode state.balances) ∧
          final.read? locations.logs = some (WordMapping.encode state.logs) ∧
          final.read? locations.logSize = some (.word state.logSize) ∧
          Rewrites [locations.world, locations.balances] store final)
        references requestRelated sharedRelated worldSame worldRead funded found belowLimit bounded derived
        (fun other gotOther current overwrites read => by
          have same := identityOf got gotOther
          subst same
          let extra : Environment := [.word state.logSize, WordMapping.encode state.logs,
            WordMapping.encode state.balances, StorageCorrespondence.world advanced, .unit, .word target,
            StorageCorrespondence.record account identity, .word (StorageSemantics.readWord key state.balances)]
          have args9 := argsCode.prepend extra
          have target9 := (CodeValue.bound (depth + 3) ([StorageCorrespondence.record account identity,
            .word (StorageSemantics.readWord key state.balances)] ++ argsValue :: environment) (.word target)).prepend
            [.word state.logSize, WordMapping.encode state.logs, WordMapping.encode state.balances,
              StorageCorrespondence.world advanced, .unit]
          have request9 := args9.part (index := 5) rfl
          have complete9 := args9.part (index := 4) rfl
          rw [complete] at complete9
          have balancesRead := overwrites.read _ _ (Ne.symm worldBalances) sharedRelated.balances
          obtain ⟨failed, attempted, frame⟩ := attempt_overflow (runInit := runInit)
            (installRuntime := CreationImplementation.installWith identify shared)
            (args9.part (index := 0) rfl) (args9.part (index := 1) rfl) complete9 (request9.part (index := 1) rfl)
            target9 read balancesRead worldBalances absentAdvanced overflowed
          exact attempt_restored sharedRelated attempted
            ((Rewrites.ofOverwrites overwrites (by simp)).trans (frame.mono (by simp))))
      refine ⟨final, evaluated, ⟨⟨⟨advanced, advancedSame, worldFinal⟩, logsFinal, logSizeFinal, balancesFinal, ?_,
        sharedRelated.distinct⟩, ⟨advanced, advancedSame, links_put_same links got rfl, worldFinal⟩⟩, rewrites⟩
      exact rewrites.read _ _ (by simp [Ne.symm worldComplete, Ne.symm balancesComplete.1]) sharedRelated.complete

/-- Applying the actual installed closure to an admitted attempt without an
init frame returns its response and publishes its shared changes. -/
theorem HandlerClosure.apply_admitted {locations : SharedLocations} {value : Value}
    (closure : HandlerClosure locations value) {request : Request} {state next : AccountCallSemantics.Shared}
    {response : Value} {anchors : List CatalogWorldCorrespondence.Anchor}
    {environment : Environment} {before middle initial : Store} {function argument : Core.Expr}
    (related : LinkedSharedStateRel anchors locations state initial) (admitting : Admitting state request response next)
    (resolved : Evaluates environment before function value middle)
    (supplied : Evaluates environment middle argument (requestValue request) initial) :
    ∃ final, Evaluates environment before (.apply function argument) response final ∧
      LinkedSharedStateRel anchors locations next final ∧ Rewrites [locations.world, locations.balances] initial final := by
  rcases closure with ⟨depth, captured, shared, runInit, identify, capturedClosure, references⟩
  cases capturedClosure
  obtain ⟨final, evaluated, nextRelated, rewrites⟩ := dispatchWith_admitted (runInit := runInit) (identify := identify)
    (references.prepend [requestValue request]) (CodeValue.bound depth captured (requestValue request)) related admitting
  exact ⟨final, .apply resolved supplied evaluated, nextRelated, rewrites⟩

end Solcore.Frontend.RustHull.CreationCorrespondence

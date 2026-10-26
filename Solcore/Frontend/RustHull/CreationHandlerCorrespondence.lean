import Solcore.Frontend.RustHull.CreationImplementation
import Solcore.Frontend.RustHull.AccountCallCheckpointCorrespondence

/-! The create handler installed by the object initializer refuses an attempt
whose endowment exceeds the creator's balance, or whose creator nonce is
exhausted, before it derives an address. The closure records the actual
captured shared references and runtime installation; init selection and the
identification of a nonempty runtime image stay abstract. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationCorrespondence
open Core Correspondence ScalarExecution CodeBuilder AccountCallCorrespondence

def addressMask : Word := Word.ofNatModulo (2 ^ 160 - 1)

theorem mask_idempotent (address : Word) :
    (address.bitAnd addressMask).bitAnd addressMask = address.bitAnd addressMask := by
  apply Fin.ext
  simp [Word.bitAnd, Nat.and_assoc]

/-- A creation request as the creating frame passes it to the create handler. -/
structure Request where
  creator : Word
  value : Word
  salt : Word
  create2 : Bool
  depth : Word
  gas : Word
  initCode : MemorySemantics.Entries
  initLength : Word

def requestValue (request : Request) : Value :=
  bundleValues [.word request.creator, .word request.value, .word request.salt, .bool request.create2,
    .word request.depth, .word request.gas, WordMapping.encode request.initCode, .word request.initLength]

/-- The successful callback result of a refused attempt: no address and no
revert bytes. -/
def refusedValue : Value :=
  .inRight .word (bundleValues [.word Word.zero, WordMapping.encode [], .word Word.zero])

/-- The installed create handler and its captured shared references. -/
structure HandlerClosure (locations : SharedLocations) (value : Value) where
  depth : Nat
  captured : Environment
  shared : AccountRuntime.References
  runInit : Code → Code → Code
  identify : Code → Code
  closure : CapturedClosure
    (lambda Creation.requestType (LanguageResult.resultType Creation.responseType) (fun request =>
      CreationRuntime.dispatch (AccountRuntime.reference shared "world")
        (AccountRuntime.reference shared "balances") (AccountRuntime.reference shared "logs")
        (AccountRuntime.reference shared "logSize") (load (AccountRuntime.reference shared "worldComplete"))
        request runInit (CreationImplementation.installWith identify shared)) depth) captured value
  references : SharedReferences depth captured shared locations

/-- The dispatcher's two refusals, read from the shared account state. -/
inductive Refusing (state : AccountCallSemantics.Shared) (request : Request) : Prop where
  | underfunded
      (shortfall : request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
  | exhausted {account : AccountState.Account}
      (funded : ¬request.value > StorageSemantics.readWord (request.creator.bitAnd addressMask) state.balances)
      (found : StorageSemantics.get state.world (request.creator.bitAnd addressMask) state.complete = .ok account)
      (limit : account.nonce > Word.ofNatModulo (2 ^ 64 - 2))

private theorem refused_evaluates (depth : Nat) (environment : Environment) (store : Store) :
    Evaluates environment store (CreationImplementation.refused depth) refusedValue store :=
  .inRight (.pair .word (.pair (.construct .unit) .word))

theorem dispatchWith_refused {depth : Nat} {environment : Environment} {store : Store}
    {shared : AccountRuntime.References} {locations : SharedLocations}
    {requestCode : Code} {request : Request} {state : AccountCallSemantics.Shared}
    (rest : Code → Code → Code → Code)
    (references : SharedReferences depth environment shared locations)
    (requestRelated : CodeValue depth environment requestCode (requestValue request))
    (related : SharedStateRel locations state store)
    (refusing : Refusing state request) :
    ∃ final, Evaluates environment store
      (CreationImplementation.dispatchWith (AccountRuntime.reference shared "world")
        (AccountRuntime.reference shared "balances") (AccountRuntime.reference shared "logs")
        (AccountRuntime.reference shared "logSize") (load (AccountRuntime.reference shared "worldComplete"))
        requestCode rest depth) refusedValue final ∧ StoreRetains store final := by
  obtain ⟨accounts, worldSame, worldRead⟩ := related.world
  let argsValue := bundleValues [.cellRef AccountState.type locations.world,
    .cellRef WordMapping.type locations.balances, .cellRef WordMapping.type locations.logs,
    .cellRef .word locations.logSize, .bool state.complete, requestValue request]
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
  have afterBalance := argsCode.prepend [.word balance]
  have valueEvaluated : Evaluates (.word balance :: argsValue :: environment) looked
      (part 1 8 (part 5 6 (fun here => .var (here - depth - 1))) (depth + 1 + 1)) (.word request.value) looked :=
    ((requestCode'.part (index := 1) rfl).prepend [.word balance]).evaluates looked
  have balanceEvaluated : Evaluates (.word balance :: argsValue :: environment) looked
      ((fun here => Expr.var (here - (depth + 1) - 1)) (depth + 1 + 1)) (.word balance) looked :=
    (CodeValue.bound (depth + 1) (argsValue :: environment) (.word balance)).evaluates looked
  unfold CreationImplementation.dispatchWith
  cases refusing with
  | underfunded shortfall =>
      refine ⟨looked, .letE packed ?_, lookedRetained⟩
      apply LanguageResult.bind_success Creation.responseType lookedEvaluated
      exact .ifTrue (.binary valueEvaluated balanceEvaluated (by simp [BinaryOp.apply, balance, key, shortfall]))
        (refused_evaluates _ _ _)
  | exhausted funded found limit =>
      have sourced := StorageCorrespondence.get_source accounts key state.complete
      rw [worldSame, found] at sourced
      obtain ⟨⟨account, identity⟩, got, same⟩ : ∃ entry, StorageCorrespondence.get accounts key state.complete = .ok entry ∧
          entry.1 = _ := by
        cases got : StorageCorrespondence.get accounts key state.complete with
        | error reason => simp [got, Except.map] at sourced
        | ok entry =>
            simp only [got, Except.map, Except.ok.injEq] at sourced
            exact ⟨entry, rfl, sourced⟩
      cases same
      let recordValue := StorageCorrespondence.record account identity
      have worldLoaded : Evaluates (.word balance :: argsValue :: environment) looked
          (load (part 0 6 (fun here => .var (here - depth - 1))) (depth + 1 + 1))
          (StorageCorrespondence.world accounts) looked :=
        .loadCell (((argsCode.part (index := 0) rfl).prepend [.word balance]).evaluates looked)
          ((lookedRetained.read _ (List.getElem?_eq_some_iff.mp worldRead).1).trans worldRead)
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
      have nonceEvaluated : Evaluates (recordValue :: .word balance :: argsValue :: environment) recordStore
          (part 2 9 (fun here => .var (here - (depth + 1 + 1) - 1)) (depth + 1 + 1 + 1)) (.word account.nonce) recordStore :=
        ((CodeValue.bound (depth + 1 + 1) (.word balance :: argsValue :: environment) recordValue).part
          (index := 2) rfl).evaluates recordStore
      refine ⟨recordStore, .letE packed ?_, lookedRetained.trans recordRetained⟩
      apply LanguageResult.bind_success Creation.responseType lookedEvaluated
      apply Evaluates.ifFalse (.binary valueEvaluated balanceEvaluated (by simp [BinaryOp.apply, balance, key, funded]))
      apply LanguageResult.bind_success Creation.responseType recordRead
      exact .ifTrue (.binary nonceEvaluated .word (by simp [BinaryOp.apply, limit])) (refused_evaluates _ _ _)

/-- Applying the actual installed closure to a refusing request returns the
refused response. Only helper cells are appended; no existing cell changes. -/
theorem HandlerClosure.apply_refused {locations : SharedLocations} {value : Value}
    (closure : HandlerClosure locations value) {request : Request} {state : AccountCallSemantics.Shared}
    {environment : Environment} {before middle initial : Store} {function argument : Core.Expr}
    (related : SharedStateRel locations state initial) (refusing : Refusing state request)
    (resolved : Evaluates environment before function value middle)
    (supplied : Evaluates environment middle argument (requestValue request) initial) :
    ∃ final, Evaluates environment before (.apply function argument) refusedValue final ∧
      StoreRetains initial final := by
  rcases closure with ⟨depth, captured, shared, runInit, identify, capturedClosure, references⟩
  cases capturedClosure
  obtain ⟨final, evaluated, retained⟩ := dispatchWith_refused
    (CreationImplementation.admitted runInit (CreationImplementation.installWith identify shared))
    (references.prepend [requestValue request]) (CodeValue.bound depth captured (requestValue request))
    related refusing
  exact ⟨final, .apply resolved supplied evaluated, retained⟩

end Solcore.Frontend.RustHull.CreationCorrespondence

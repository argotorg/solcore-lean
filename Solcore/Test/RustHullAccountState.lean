import Solcore.Frontend.RustHull.AccountState
import Solcore.Core.Machine

/-! Core execution tests for the shared world and transaction finalization. -/
set_option autoImplicit false
namespace Tests.RustHullAccountState
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def bytes (values : List Nat) : List UInt8 := values.map UInt8.ofNat
private def entries (values : List (Nat × Nat)) : WordMapping.Entries :=
  values.map fun (key, value) => (word key, word value)
private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false
private def values : List Value → Value
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (values rest)
private def mapping : Value → Except String WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor == WordMapping.nilConstructor then pure [] else .error "wrong empty balance mapping"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor == WordMapping.consConstructor do throw "wrong balance mapping constructor"
      pure ((key, value) :: (← mapping tail))
  | _ => .error "invalid balance mapping"
private def sequence (result : Ty) (action next : Expr) : Expr :=
  LanguageResult.bind result action (next.weakenAt 0)

private def initial : List AccountState.Account := [
  {address := word 0xaaa, storage := entries [(0, 1)], transient := entries [(0, 2)],
    nonce := word 5, code := some (bytes [0x60, 0xfe]), destroyed := true},
  {address := word 0xbbb, storage := entries [(0, 7)], transient := entries [(0, 8)],
    nonce := word 3, code := none, created := true},
  {address := word 0xccc, storage := entries [(0, 9)], transient := entries [(0, 10)],
    nonce := word 4, code := some (bytes [0]), created := true, destroyed := true},
  {address := word 0xddd}]
private def balances : WordMapping.Entries := entries [(0xaaa, 9), (0xbbb, 11), (0xccc, 123), (0xeee, 17)]

/-- Bodies see the balance reference at zero and world reference at one. -/
private def program (result : Ty) (body : Expr) (accounts := initial) (ledger := balances) : Program := {
  dataDefinitions := AccountState.definitions
  resultType := .product (LanguageResult.resultType result) (.product AccountState.type WordMapping.type)
  body := .letE (.newCell AccountState.type (AccountState.literal (accounts.map (·, 17))))
    (.letE (.newCell WordMapping.type (WordMapping.literal ledger))
      (.letE body (.pair (.var 0) (.pair (.loadCell (.var 2)) (.loadCell (.var 1))))))
}

private structure Snapshot where
  status : Value
  world : Value
  accounts : List AccountState.Account
  balances : WordMapping.Entries

private def snapshot (label : String) (value : Value) : IO Snapshot := do
  let .pair status (.pair world balanceValue) := value
    | throw (IO.userError s!"{label}: invalid snapshot shape")
  pure ⟨status, world, ← get (AccountState.decode world), ← get (mapping balanceValue)⟩

private def execute (label : String) (compiled : Program) : IO Snapshot := do
  require compiled.check s!"{label}: generated Core is ill-typed"
  match compiled.runStateful 3000000 with
  | .done value _ => snapshot label value
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def account (snapshot : Snapshot) (address : Nat) : IO AccountState.Account :=
  match snapshot.accounts.find? (·.address == word address) with
  | some account => pure account
  | none => throw (IO.userError s!"missing account {address}")

private def storageTests : IO Unit := do
  let action := sequence .word
    (AccountState.writeStorage (.var 1) (number 0xaaa) (.bool false) (number 0) (number 101))
    (sequence .word
      (AccountState.writeStorage (.var 1) (number 0xbbb) (.bool false) (number 0) (number 202) true)
      (sequence .word
        (AccountState.writeStorage (.var 1) (number 0xaaa) (.bool false) (number 1) (number 303) true)
        (sequence .word
          (AccountState.writeField (.var 1) (number 0xaaa) (.bool false) 2 (number 12))
          (AccountState.readStorage (.var 1) (number 0xaaa) (.bool false) (number 0)))))
  let actual ← execute "world storage helpers" (program .word action)
  require (actual.status == .inRight .word (scalar 101)) "persistent read did not observe write"
  let a ← account actual 0xaaa
  let b ← account actual 0xbbb
  require (a.storage == entries [(0, 101)] && a.transient == entries [(0, 2), (1, 303)] && a.nonce == word 12)
    "first account fields or updates were lost"
  require (b.storage == entries [(0, 7)] && b.transient == entries [(0, 202)] && b.nonce == word 3)
    "storage crossed account or persistent/transient boundaries"
  require (actual.balances == balances) "storage helper changed balances"
  let read ← execute "transient read" (program .word
    (AccountState.readStorage (.var 1) (number 0xbbb) (.bool false) (number 0) true))
  require (read.status == .inRight .word (scalar 8)) "transient read used persistent storage"
  let absent ← execute "incomplete world rejects unknown account" (program .word
    (AccountState.readStorage (.var 1) (number 0x999) (.bool false) (number 0)))
  require (absent.status == .inLeft .word (scalar 7) && absent.accounts.length == initial.length)
    "unknown account silently became empty"
  let absentWrite ← execute "incomplete world rejects unknown write" (program .unit
    (AccountState.writeStorage (.var 1) (number 0x999) (.bool false) (number 0) (number 42)))
  require (absentWrite.status == .inLeft .unit (scalar 7) && absentWrite.accounts.length == initial.length)
    "failed write inserted an unknown account"
  let created ← execute "complete world materializes empty account" (program .word
    (sequence .word
      (AccountState.writeStorage (.var 1) (number 0x999) (.bool true) (number 0) (number 42))
      (AccountState.readStorage (.var 1) (number 0x999) (.bool true) (number 0))))
  let fresh ← account created 0x999
  require (created.status == .inRight .word (scalar 42) && fresh.storage == entries [(0, 42)] &&
    fresh.nonce == word 0 && fresh.code == some []) "default account was not initialized consistently"

private def finalizeTests : IO Unit := do
  let finalizer := AccountState.finalize (.var 1) (.var 0)
  let compiled := program .unit finalizer
  let actual ← execute "transaction finalization" compiled
  require (actual.status == .inRight .word .unit) "finalization failed"
  require (actual.accounts.map (·.address.val) == [0xaaa, 0xbbb, 0xddd])
    "finalization removed an existing account, kept a destroyed new account, or reordered entries"
  for account in actual.accounts do
    require (account.transient.isEmpty && !account.created && !account.destroyed)
      "finalization retained transaction-local state"
  let old ← account actual 0xaaa
  require (old.storage == entries [(0, 1)] && old.nonce == word 5 && old.code == some (bytes [0x60, 0xfe]))
    "existing selfdestruct erased persistent state"
  let new ← account actual 0xbbb
  require (new.storage == entries [(0, 7)] && new.nonce == word 3 && new.code == none)
    "surviving new account lost persistent state or unknown-code status"
  require (actual.balances == entries [(0xaaa, 9), (0xbbb, 11), (0xccc, 0), (0xeee, 17)])
    "finalization did not burn a later credit to a removed account or changed other balances"
  let .constructed _ (.pair (.pair _ (.pair _ (.pair _ (.pair _ (.pair identity _))))) _) := actual.world
    | throw (IO.userError "finalizer produced an invalid record")
  require (identity == scalar 17) "finalization changed the internal code identity"
  let repeated ← execute "idempotent transaction finalization"
    (program .unit (sequence .unit finalizer finalizer))
  require (actual.world == repeated.world && actual.balances == repeated.balances)
    "repeated finalization changed the committed state"
  let empty ← execute "empty world finalization" (program .unit finalizer [] balances)
  require (empty.accounts.isEmpty && empty.balances == balances) "empty finalization changed the ledger"
  match compiled.runStateful 100 with
  | .outOfFuel checkpoint =>
      match runStateful 3000000 checkpoint with
      | .done value _ =>
          let resumed ← snapshot "resumed finalizer" value
          require (resumed.world == actual.world && resumed.balances == actual.balances &&
            resumed.status == actual.status) "resumption changed finalization"
      | other => throw (IO.userError s!"resumed finalizer failed: {reprStr other}")
  | other => throw (IO.userError s!"finalizer did not suspend: {reprStr other}")

private def record (code : Value := WordMapping.encode []) (size : Nat := 0)
    (known : Bool := true) : Value := values [WordMapping.encode (entries [(0, 8)]), WordMapping.encode [],
      scalar 7, scalar 99, code, scalar size, .bool known, .bool false, .bool true]
private def world (record : Value) : Value := OrderedMapping.encode AccountState.layout [(scalar 0xaaa, record)]

private def decoderTests : IO Unit := do
  let packed := WordMapping.encode (entries [(0, 0x1234 * 256 ^ 30), (0, 0xff * 256 ^ 31), (7, 123)])
  let [decoded] ← get (AccountState.decode (world (record packed 33)) 33)
    | throw (IO.userError "decoder lost account")
  require (decoded.address == word 0xaaa && decoded.storage == entries [(0, 8)] && decoded.nonce == word 7 &&
    decoded.code == some (bytes [0x12, 0x34] ++ List.replicate 31 0) && decoded.destroyed)
    "decoder changed fields, byte order, first-match lookup or zero padding"
  let [unknown] ← get (AccountState.decode (world (record packed 33 false)) 33)
    | throw (IO.userError "decoder lost unknown-code account")
  require unknown.code.isNone "decoder trusted an unknown code image"
  require (AccountState.decode (world (record packed 33)) 32 |> rejected) "decoder ignored code bound"
  require (AccountState.decode (world (record packed 33 false)) 32 |> rejected) "unknown code bypassed code bound"
  require (AccountState.decode (WordMapping.encode []) |> rejected) "decoder accepted wrong world data identity"
  require (AccountState.decode (.constructed AccountState.layout.consConstructor .unit) |> rejected)
    "decoder accepted malformed world constructor"
  require (AccountState.decode (world .unit) |> rejected) "decoder accepted truncated account record"
  require (AccountState.decode (world (record .unit)) |> rejected) "decoder accepted malformed code mapping"
  let malformed := values [WordMapping.encode [], WordMapping.encode [], scalar 0, .bool false,
    WordMapping.encode [], scalar 0, .bool true, .bool false, .bool false]
  require (AccountState.decode (world malformed) |> rejected) "decoder accepted malformed code identity"
  let badStorage := values [WordMapping.encode [], .unit, scalar 0, scalar 0,
    WordMapping.encode [], scalar 0, .bool true, .bool false, .bool false]
  require (AccountState.decode (world badStorage) |> rejected) "decoder accepted malformed transient mapping"
  require (AccountState.decode (.constructed AccountState.layout.consConstructor
    (.pair (.pair (scalar 1) (record)) .unit)) |> rejected) "decoder accepted malformed world tail"

def run : IO Unit := do
  storageTests
  finalizeTests
  decoderTests

end Tests.RustHullAccountState

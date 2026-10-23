import Solcore.Frontend.RustHull.CreationRuntime
import Solcore.Core.Machine

set_option autoImplicit false
namespace Tests.RustHullCreationRuntime
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program
open CodeBuilder

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def scalar (value : Nat) : Value := .word (word value)
private def bytes (values : List Nat) : List UInt8 := values.map UInt8.ofNat
private def entries (values : List (Nat × Nat)) : WordMapping.Entries :=
  values.map fun (key, value) => (word key, word value)
private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def mapping : Value → Except String WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor == WordMapping.nilConstructor then pure [] else .error "wrong mapping constructor"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor == WordMapping.consConstructor do throw "wrong mapping constructor"
      pure ((key, value) :: (← mapping tail))
  | _ => .error "invalid mapping"

-- Independently obtained with `cast compute-address 0x...aaaa --nonce 7`.
private def createdAddress : Nat := 0x21e44f0740e8cf48922d40250130b7fa7d305f15
private def initialLogs := entries [(0, 9)]
private structure Scenario where
  creator : Nat := 0xaaaa
  nonce : Nat := 7
  balance : Nat := 100
  value : Nat := 17
  target : Nat := createdAddress
  targetBalance : Nat := 5
  targetNonce : Nat := 0
  targetCode : Option (List UInt8) := some []
  create2 : Bool := false
  init : List UInt8 := bytes [0]
  output : List UInt8 := bytes [0x60, 0, 0xfe]
  outputLength : Nat := 3
  childOk : Bool := true
  childError : Option Nat := none
  installError : Option Nat := none

private def accounts (scenario : Scenario) : List AccountState.Account := [
  {address := word scenario.creator, nonce := word scenario.nonce, code := some (bytes [0x60])},
  {address := word scenario.target, storage := entries [(1, 99)], transient := entries [(2, 88)],
    nonce := word scenario.targetNonce, code := scenario.targetCode}]
private def ledger (scenario : Scenario) : WordMapping.Entries :=
  entries [(scenario.creator, scenario.balance), (scenario.target, scenario.targetBalance)]

private def program (scenario : Scenario) : Program := {
  dataDefinitions := AccountState.definitions
  resultType := bundleType [LanguageResult.resultType Creation.responseType, AccountState.type,
    WordMapping.type, WordMapping.type, .word]
  body := (bind (allocate AccountState.type (constant (AccountState.literal ((accounts scenario).map (·, 0))))) fun world =>
    bind (allocate WordMapping.type (constant (WordMapping.literal (ledger scenario)))) fun balances =>
    bind (allocate WordMapping.type (constant (WordMapping.literal initialLogs))) fun logs =>
    bind (allocate .word (number 1)) fun logSize =>
    let runInit (target request : Code) : Code :=
      bindResult Calls.responseType (fun depth => AccountState.writeStorage (world depth) (target depth)
        (.bool true) (.word (word 1)) (.word (word 42))) fun _ =>
      bindResult Calls.responseType (fun depth => AccountState.writeStorage (world depth) (target depth)
        (.bool true) (.word (word 3)) (part 1 8 request depth)) fun _ =>
      bind (store logs (constant (WordMapping.literal (entries [(0, 77)])))) fun _ =>
      bind (store logSize (number 2)) fun _ =>
      match scenario.childError with
      | some reason => failure Calls.responseType (number reason)
      | none => success (packet [boolean scenario.childOk,
          constant (WordMapping.literal (Memory.packBytes scenario.output)), number scenario.outputLength])
    let install (target child : Code) : Code :=
      bindResult .unit (fun depth => AccountState.writeField (world depth) (target depth) (.bool true) 3
        (.word (word 73))) fun _ =>
      match scenario.installError with
      | some reason => failure .unit (number reason)
      | none =>
          bindResult .unit (fun depth => AccountState.writeField (world depth) (target depth) (.bool true) 4
            (part 1 3 child depth)) fun _ =>
          fun depth => AccountState.writeField (world depth) (target depth) (.bool true) 5
            (part 2 3 child depth)
    let request := packet [number scenario.creator, number scenario.value, number 0, boolean scenario.create2,
      number 1, number 100000, constant (WordMapping.literal (Memory.packBytes scenario.init)),
      number scenario.init.length]
    bind (CreationRuntime.dispatch world balances logs logSize (boolean true) request runInit install) fun result =>
    packet [result, load world, load balances, load logs, load logSize]) 0
}

private structure Snapshot where
  status : Value
  world : Value
  accounts : List AccountState.Account
  balances : WordMapping.Entries
  logs : WordMapping.Entries
  logSize : Nat

private def snapshot (value : Value) : IO Snapshot := do
  let .pair status (.pair world (.pair balances (.pair logs (.word logSize)))) := value
    | throw (IO.userError "invalid creation snapshot")
  pure ⟨status, world, ← get (AccountState.decode world), ← get (mapping balances),
    ← get (mapping logs), logSize.val⟩
private def execute (label : String) (scenario : Scenario) : IO Snapshot := do
  let compiled := program scenario
  match inferDetailed [] [] compiled.body compiled.dataDefinitions with
  | .error error => throw (IO.userError s!"{label}: ill-typed Core: {reprStr error}")
  | .ok actual => require (actual == compiled.resultType) s!"{label}: wrong result type"
  match compiled.runStateful 10000000 with
  | .done value _ => snapshot value
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def account (snapshot : Snapshot) (address : Nat) : IO AccountState.Account :=
  match snapshot.accounts.find? (·.address == word address) with
  | some value => pure value
  | none => throw (IO.userError s!"missing account {address}")
private def returned (label : String) (snapshot : Snapshot) (address : Nat)
    (data : List UInt8 := []) : IO Unit := do
  let .inRight _ (.pair (.word actualAddress) (.pair actualData (.word length))) := snapshot.status
    | throw (IO.userError s!"{label}: did not return a creation response: {reprStr snapshot.status}")
  let actualData ← get (mapping actualData)
  let actualBytes := (List.range length.val).map fun index =>
    UInt8.ofNat (Memory.lookupByte actualData (word index)).val
  require (actualAddress == word address && actualBytes == data)
    s!"{label}: wrong creation address or return data"
private def rolledBack (label : String) (snapshot : Snapshot) (scenario : Scenario) (nonce : Nat) : IO Unit := do
  let creator ← account snapshot scenario.creator
  let target ← account snapshot scenario.target
  require (creator.nonce == word nonce) s!"{label}: creator nonce did not follow the checkpoint rule"
  require (target.storage == entries [(1, 99)] && target.transient == entries [(2, 88)] &&
    target.nonce == word scenario.targetNonce && target.code == scenario.targetCode && !target.created)
    s!"{label}: target state escaped rollback"
  require (snapshot.balances == ledger scenario && snapshot.logs == initialLogs && snapshot.logSize == 1)
    s!"{label}: balance or log state escaped rollback"

private def successTests : IO Unit := do
  let scenario : Scenario := {}
  let actual ← execute "successful creation" scenario
  returned "successful creation" actual createdAddress
  let creator ← account actual scenario.creator
  let target ← account actual scenario.target
  require (creator.nonce == word 8 && target.nonce == word 1 && target.created && !target.destroyed)
    "successful creation nonce or lifecycle flags"
  require (target.storage == entries [(1, 42), (3, 17)] && target.transient.isEmpty &&
    target.code == some scenario.output) "constructor state or deployed bytes were not installed"
  require (actual.balances == entries [(scenario.creator, 83), (scenario.target, 22)])
    "creation did not preserve prefunding or transfer value"
  require (actual.logs == entries [(0, 77)] && actual.logSize == 2) "successful constructor logs were lost"
  let emptyScenario : Scenario := {init := [], childError := some 77}
  let empty ← execute "empty init skips constructor" emptyScenario
  returned "empty init" empty createdAddress
  let target ← account empty emptyScenario.target
  require (target.storage.isEmpty && target.code == some [] && target.nonce == word 1 && target.created)
    "empty init did not create an empty account"
  require (empty.logs == initialLogs && empty.logSize == 1) "empty init ran the constructor callback"
  let create2 : Scenario := {
    creator := 0
    nonce := 0
    value := 0
    create2 := true
    target := 0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38
    output := []
    outputLength := 0
  }
  let actual ← execute "CREATE2 EIP-1014 address" create2
  returned "CREATE2" actual create2.target
  require ((← account actual 0).nonce == word 1) "CREATE2 did not increment creator nonce"
  let boundary : Scenario := {output := bytes [0x60], outputLength := 24576}
  let actual ← execute "maximum deployed code length" boundary
  returned "maximum deployed code length" actual createdAddress
  let target ← account actual boundary.target
  require (target.code.map List.length == some 24576) "maximum deployed code length was rejected"

private def failureTests : IO Unit := do
  for (label, scenario) in [
    ("insufficient balance", {value := 101 : Scenario}),
    ("nonce exhausted", {nonce := 2 ^ 64 - 1 : Scenario}),
    ("nonce outside protocol range", {nonce := 2 ^ 64 : Scenario})] do
    let actual ← execute label scenario
    returned label actual 0
    rolledBack label actual scenario scenario.nonce
  for (label, scenario) in [
    ("nonce collision", {targetNonce := 1 : Scenario}),
    ("code collision", {targetCode := some (bytes [0x60]) : Scenario}),
    ("oversized deployed code", {outputLength := 24577 : Scenario}),
    ("reserved deployed code prefix", {output := bytes [0xef], outputLength := 1 : Scenario})] do
    let actual ← execute label scenario
    returned label actual 0
    rolledBack label actual scenario 8
  let reverting : Scenario := {childOk := false, output := bytes [0xde, 0xad], outputLength := 2}
  let actual ← execute "constructor revert" reverting
  returned "constructor revert" actual 0 reverting.output
  rolledBack "constructor revert" actual reverting 8
  for (label, reason, scenario) in [
    ("constructor language failure", 77, {childError := some 77 : Scenario}),
    ("installation failure", 88, {installError := some 88 : Scenario}),
    ("balance overflow", 12, {targetBalance := wordModulus - 1, value := 1 : Scenario}),
    ("unknown target code", 7, {targetCode := none : Scenario})] do
    let actual ← execute label scenario
    require (actual.status == .inLeft Creation.responseType (scalar reason))
      s!"{label}: language failure was not propagated"
    rolledBack label actual scenario 8

def run : IO Unit := do
  successTests
  failureTests
  let compiled := program {}
  match compiled.runStateful 1000 with
  | .outOfFuel checkpoint =>
      match runStateful 10000000 checkpoint with
      | .done value _ =>
          let actual ← snapshot value
          returned "creation resumes" actual createdAddress
          require ((← account actual 0xaaaa).nonce == word 8) "resumed creation incremented nonce twice"
      | other => throw (IO.userError s!"resumed creation: {reprStr other}")
  | other => throw (IO.userError s!"creation did not suspend: {reprStr other}")

end Tests.RustHullCreationRuntime

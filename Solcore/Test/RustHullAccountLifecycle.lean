import Solcore.Frontend.RustHull.AccountLifecycle
import Solcore.Core.Machine

set_option autoImplicit false
namespace Tests.RustHullAccountLifecycle
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def packet : List Value → Value
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)
private def ok : Value := .inRight .word .unit
private def failure (reason : Nat) : Value := .inLeft .unit (scalar reason)
private def entries (values : List (Nat × Nat)) : WordMapping.Entries :=
  values.map fun (key, value) => (word key, word value)

private def current (created : Bool) : AccountState.Account := {
  address := word 0xabc, nonce := word 7,
  storage := entries [(1, 42)], transient := entries [(2, 33)],
  code := some [0x60, 0x00, 0x55], created}
private def neighbor : AccountState.Account := {
  address := word 0x123, nonce := word 8, storage := entries [(4, 99)],
  code := some [0x61, 0x22, 0x33]}
private def recordValue (account : AccountState.Account) (identity : Nat) : Value :=
  packet [WordMapping.encode account.storage, WordMapping.encode account.transient,
    .word account.nonce, scalar identity, WordMapping.encode (Memory.packBytes (account.code.getD [])),
    scalar (account.code.getD []).length, .bool account.code.isSome, .bool account.created, .bool account.destroyed]
private def worldValue (accounts : List (AccountState.Account × Nat)) : Value :=
  OrderedMapping.encode AccountState.layout (accounts.map fun (account, identity) =>
    (.word (word (account.address.val % 2 ^ 160)), recordValue account identity))

private def destroy (beneficiary : Nat) (address : Nat := 0xabc) (complete : Bool := false) : Expr :=
  AccountLifecycle.destroy (.var 1) (.var 0) (number address) (number beneficiary) (.bool complete)

/-- The result includes an actual post-update Core account read. -/
private def program (accounts : List (AccountState.Account × Nat)) (balances : WordMapping.Entries)
    (body : Expr) (address : Nat := 0xabc) (complete : Bool := false) : Program := {
  dataDefinitions := AccountLifecycle.definitions,
  resultType := .product (LanguageResult.resultType .unit) (LanguageResult.resultType AccountState.recordType),
  body := .letE (.newCell AccountState.type (AccountState.literal accounts))
    (.letE (.newCell WordMapping.type (WordMapping.literal balances))
      (.letE body (.pair (.var 0) (AccountState.get (.loadCell (.var 2))
        (number (address % 2 ^ 160)) (.bool complete)))))}

private def check (label : String) (compiled : Program) (status observed : Value)
    (accounts : List (AccountState.Account × Nat)) (balances : WordMapping.Entries) : IO Unit := do
  require compiled.check s!"{label}: lifecycle Core is ill-typed"
  match compiled.runStateful 200000 with
  | .done actual store =>
      require (actual == .pair status observed) s!"{label}: incorrect post-update observations {reprStr actual}"
      require (store[0]? == some (worldValue accounts)) s!"{label}: unexpected world mutation"
      require (store[1]? == some (WordMapping.encode balances)) s!"{label}: unexpected balance mutation"
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def observed (account : AccountState.Account) (identity : Nat := 4) : Value :=
  .inRight .word (recordValue account identity)

private def transferTests : IO Unit := do
  for created in [false, true] do
    let account := current created
    let pending := {account with destroyed := created}
    let catalog := [(account, 4), (neighbor, 9)]
    let after := [(pending, 4), (neighbor, 9)]
    let initial := entries [(0xabc, 20), (0xdef, 3), (0x123, 8)]
    let balances := entries [(0xabc, 0), (0xdef, 23), (0x123, 8)]
    check s!"transfer all balance created={created}"
      (program catalog initial (destroy 0xdef)) ok (observed pending) after balances
    check s!"canonical addresses created={created}"
      (program catalog initial (destroy (2 ^ 200 + 0xdef) (2 ^ 200 + 0xabc)))
      ok (observed pending) after balances
    check s!"recipient need not have a world record created={created}"
      (program catalog (entries [(0xabc, 20)]) (destroy 0xdef))
      ok (observed pending) after (entries [(0xabc, 0), (0xdef, 20)])
    check s!"zero balance retains ledger keys created={created}"
      (program catalog (entries [(0x123, 8)]) (destroy 0xdef))
      ok (observed pending) after (entries [(0x123, 8)])
    check s!"maximum transfer remains representable created={created}"
      (program catalog (entries [(0xabc, wordModulus - 1)]) (destroy 0xdef))
      ok (observed pending) after (entries [(0xabc, 0), (0xdef, wordModulus - 1)])
    let overflow := entries [(0xabc, 20), (0xdef, wordModulus - 20)]
    check s!"overflow precedes all public mutation created={created}"
      (program catalog overflow (destroy 0xdef)) (failure 12) (observed account) catalog overflow

private def selfTests : IO Unit := do
  for created in [false, true] do
    let account := current created
    let pending := {account with destroyed := created}
    let catalog := [(account, 4), (neighbor, 9)]
    let balances := entries [(0xabc, 20), (0xdef, 3)]
    let expected := if created then entries [(0xabc, 0), (0xdef, 3)] else balances
    check s!"self beneficiary created={created}"
      (program catalog balances (destroy 0xabc)) ok (observed pending)
      [(pending, 4), (neighbor, 9)] expected
    check s!"self beneficiary high-bit alias created={created}"
      (program catalog balances (destroy (2 ^ 200 + 0xabc))) ok (observed pending)
      [(pending, 4), (neighbor, 9)] expected

private def sequence (action next : Expr) : Expr :=
  LanguageResult.bind .unit action (next.weakenAt 0)

private def credit (amount : Nat) : Expr :=
  LanguageResult.bind .unit (WordMapping.insert (.loadCell (.var 0)) (number 0xabc) (number amount))
    (LanguageResult.success (.storeCell (.var 1) (.var 0)))

private def repeatedTests : IO Unit := do
  for created in [false, true] do
    let account := current created
    let pending := {account with destroyed := created}
    let catalog := [(account, 4), (neighbor, 9)]
    let after := [(pending, 4), (neighbor, 9)]
    let initial := entries [(0xabc, 20), (0xdef, 3)]
    let repeated := sequence (destroy 0xdef) (sequence (credit 7) (destroy 0x123))
    check s!"repeated destruction transfers newly received funds created={created}"
      (program catalog initial repeated) ok (observed pending) after
      (entries [(0xabc, 0), (0xdef, 23), (0x123, 7)])
    let repeatedSelf := sequence (destroy 0xdef) (sequence (credit 7) (destroy 0xabc))
    check s!"repeated destruction to self created={created}"
      (program catalog initial repeatedSelf) ok (observed pending) after
      (entries [(0xabc, if created then 0 else 7), (0xdef, 23)])
    check s!"repeated zero-balance destruction created={created}"
      (program catalog initial (sequence (destroy 0xdef) (destroy 0x123)))
      ok (observed pending) after (entries [(0xabc, 0), (0xdef, 23)])
  let account := {current true with destroyed := true}
  let catalog := [(account, 4), (neighbor, 9)]
  check "already pending account retains code, nonce and storage while receiving more funds"
    (program catalog (entries [(0xabc, 9), (0xdef, 2)]) (destroy 0xdef))
    ok (observed account) catalog (entries [(0xabc, 0), (0xdef, 11)])

private def missingTests : IO Unit := do
  let balances := entries [(0xabc, 20)]
  let catalog := [(neighbor, 9)]
  check "unknown current account fails without mutation"
    (program catalog balances (destroy 0xdef)) (failure 7)
    (.inLeft AccountState.recordType (scalar 7)) catalog balances
  let defaultAccount : AccountState.Account := {address := word 0xabc}
  check "complete world supplies empty current record"
    (program catalog balances (destroy 0xdef 0xabc true) 0xabc true) ok (observed defaultAccount 0)
    catalog (entries [(0xabc, 0), (0xdef, 20)])

private def resumeChunks : Nat → State → IO StatefulRunResult
  | 0, _ => throw (IO.userError "lifecycle resume budget exhausted")
  | attempts + 1, state => match runStateful 31 state with
      | .outOfFuel state => resumeChunks attempts state
      | result => pure result

private def onceAndResumeTests : IO Unit := do
  let account := current true
  let catalog := [(account, 4), (neighbor, 9)]
  let pending := {account with destroyed := true}
  let initial := entries [(0xabc, 20), (0xdef, 3)]
  let body := sequence (destroy 0xdef) (sequence (credit 7) (destroy 0x123))
  let compiled := program catalog initial body
  match compiled.runStateful 1 with
  | .outOfFuel checkpoint => match ← resumeChunks 10000 checkpoint with
      | .done actual store =>
          require (actual == .pair ok (observed pending)) "resumption changed account observations"
          require (store[0]? == some (worldValue [(pending, 4), (neighbor, 9)]))
            "resumption changed pending destruction"
          require (store[1]? == some (WordMapping.encode (entries [(0xabc, 0), (0xdef, 23), (0x123, 7)])))
            "resumption duplicated or lost a balance transfer"
      | other => throw (IO.userError s!"lifecycle resume: {reprStr other}")
  | _ => throw (IO.userError "lifecycle fixture did not suspend")
  let tick (value : Expr) := Expr.letE
    (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (number 1))) (value.weakenAt 0)
  let once : Program := {
    resultType := .product (LanguageResult.resultType .unit) .word,
    dataDefinitions := AccountLifecycle.definitions,
    body := .letE (.newCell AccountState.type (AccountState.literal catalog))
      (.letE (.newCell WordMapping.type (WordMapping.literal initial))
        (.letE (.newCell .word (number 0))
          (.letE (AccountLifecycle.destroy (tick (.var 2)) (tick (.var 1))
            (tick (number 0xabc)) (tick (number 0xdef)) (tick (.bool false)))
            (.pair (.var 0) (.loadCell (.var 1))))))}
  require once.check "argument-once lifecycle Core is ill-typed"
  match once.runStateful 200000 with
  | .done value _ => require (value == .pair ok (scalar 5)) "lifecycle repeated an input expression"
  | other => throw (IO.userError s!"lifecycle argument evaluation: {reprStr other}")

def run : IO Unit := do
  transferTests
  selfTests
  repeatedTests
  missingTests
  onceAndResumeTests
  IO.println "Rust Hull account lifecycle tests passed"

end Tests.RustHullAccountLifecycle

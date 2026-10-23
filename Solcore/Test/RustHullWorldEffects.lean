import Solcore.Frontend.RustHull.Effects
import Solcore.Core.Machine

set_option autoImplicit false
namespace Tests.RustHullWorldEffects
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def number (n : Nat) : Solcore.Core.Expr := .word (Word.ofNatModulo n)
private def scalar (n : Nat) : Value := .word (Word.ofNatModulo n)
private def require (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)
private def slots := Effects.slots ++ Effects.codeSlots
private def scope : Scope := slots.reverse.map fun (name, type) =>
  ⟨some (Effects.slotName name), type, false⟩
private def account : AccountState.Account := {
  address := Word.ofNatModulo 0xaaa, nonce := Word.ofNatModulo 1,
  code := some [0x60, 0], created := true}
private def ambient : Ambient.Context := {
  origin := some (Word.ofNatModulo 0xbbb), number := some (Word.ofNatModulo 300),
  blockHashes := some [(Word.ofNatModulo 44, Word.ofNatModulo 123)],
  blobHashes := some [Word.ofNatModulo 42]}
private structure Settings where
  isStatic : Bool := false
  gas : Bool := true
  known : Bool := true
  mode : String := ""

private def callback (settings : Settings) (name : String) : Solcore.Core.Expr :=
  let expected := if name == "delegateCallHandler" then
    [(0, 0xccc), (1, 0xbbb), (2, 17), (4, 9), (5, 123)] else
    [(0, 0xccc), (1, 0xaaa), (2, 18), (4, 9), (5, 2423)]
  let rejected := LanguageResult.failure Calls.responseType (number 99)
  let success := LanguageResult.success (Calls.response (.bool true) WordMapping.empty (number 0))
  let checked := expected.foldr (fun (index, value) body =>
    .ifE (.binary .wordEq (Calls.requestField index (.var 0)) (number value)) body rejected) success
  .lambda Calls.requestType (LanguageResult.resultType Calls.responseType)
    (.ifE (.bool (settings.mode == name))
      (.ifE (Calls.requestField 3 (.var 0)) checked rejected) rejected)

private def creationCallback (settings : Settings) : Solcore.Core.Expr :=
  let expected := [(0, 0xaaa), (1, 9), (2, if settings.mode == "create2" then 77 else 0),
    (4, 9), (5, 222), (7, 0)]
  let rejected := LanguageResult.failure Creation.responseType (number 99)
  let success := LanguageResult.success (Creation.response (number 0x1234) WordMapping.empty (number 0))
  let checked := expected.foldr (fun (index, value) body =>
    .ifE (.binary .wordEq (Creation.requestField index (.var 0)) (number value)) body rejected) success
  let flag := Creation.requestField 3 (.var 0)
  .lambda Creation.requestType (LanguageResult.resultType Creation.responseType)
    (if settings.mode == "create2" then .ifE flag checked rejected else .ifE flag rejected checked)

private def initial (settings : Settings) (name : String) (type : Solcore.Core.Ty) : Solcore.Core.Expr :=
  match Ambient.slots.zipIdx.find? (fun entry => entry.1.1 == name) with
  | some (_, index) => Ambient.initialValue index (Ambient.contextExpression ambient)
  | none => match name with
    | "world" => AccountState.literal [(account, 1)]
    | "worldComplete" => .bool true
    | "balances" => WordMapping.literal [(Word.ofNatModulo 0xaaa, Word.ofNatModulo 100)]
    | "address" => number 0xaaa
    | "caller" => number 0xbbb
    | "callvalue" => number 17
    | "callDepth" => number 8
    | "isStatic" => .bool settings.isStatic
    | "availableGas" => if settings.gas then .inRight .unit (number 222) else .inLeft .word .unit
    | "codeKnown" => .bool settings.known
    | "code" => WordMapping.literal (Memory.packBytes [0x60, 0])
    | "codeSize" => number 2
    | "callHandler" | "callCodeHandler" | "delegateCallHandler" => .inRight .unit (callback settings name)
    | "createHandler" => .inRight .unit (creationCallback settings)
    | _ => match type with
      | .word => number 0
      | .bool => .bool false
      | .namedData _ => WordMapping.empty
      | _ => .unit

private def lower (name : String) (args : List Nat) : IO Lowered :=
  match Effects.lowerBuiltin scope name (args.map number) with
  | .ok value => pure value
  | .error error => throw (IO.userError error.message)

private def check (label : String) (lowered : Lowered) (settings : Settings)
    (expected : Value) (exit : Nat := 0) : IO Unit := do
  let compiled : Program := {
    resultType := LanguageResult.resultType lowered.type
    dataDefinitions := AccountState.definitions
    body := slots.foldr (fun (name, type) body =>
      .letE (.newCell type (initial settings name type)) body) lowered.expression
  }
  require compiled.check s!"{label}: ill-typed Core"
  match compiled.runStateful 3000000 with
  | .done value store =>
      require (value == expected) s!"{label}: expected {reprStr expected}, got {reprStr value}"
      let index := (slots.findIdx? (fun entry => entry.1 == "exit")).getD slots.length
      require (store[index]? == some (scalar exit)) s!"{label}: unexpected exit status"
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def success (n : Nat) : Value := .inRight .word (scalar n)
private def failure (type : Solcore.Core.Ty) (n : Nat) : Value := .inLeft type (scalar n)

def run : IO Unit := do
  for (writeName, readName) in [("sstore", "sload"), ("tstore", "tload")] do
    let write ← lower writeName [7, 99]
    let read ← lower readName [7]
    check writeName ⟨.word, LocalSequence.discard .word write.expression read.expression⟩ {} (success 99)
    check (writeName ++ " static") write {isStatic := true} (failure .unit (wordModulus - 1)) 3
  for (name, args, result) in [("origin", [], 0xbbb), ("blockhash", [44], 123),
      ("blobhash", [0], 42), ("extcodesize", [0xaaa], 2)] do
    check name (← lower name args) {} (success result)
  check "callcode" (← lower "callcode" [123, 0xccc, 18, 0, 0, 0, 0])
    {isStatic := true, mode := "callCodeHandler"} (success 1)
  check "delegatecall" (← lower "delegatecall" [123, 0xccc, 0, 0, 0, 0])
    {isStatic := true, mode := "delegateCallHandler"} (success 1)
  check "static nonzero call" (← lower "call" [123, 0xccc, 18, 0, 0, 0, 0])
    {isStatic := true} (failure .word (wordModulus - 1)) 3
  check "callcode stipend overflow" (← lower "callcode" [wordModulus - 1, 0xccc, 18, 0, 0, 0, 0])
    {isStatic := true} (failure .word 13)
  for (name, args) in [("create", [9, 0, 0]), ("create2", [9, 0, 0, 77])] do
    let effect ← lower name args
    check name effect {mode := name} (success 0x1234)
    check (name ++ " missing gas") effect {gas := false} (failure .word 9)
    check (name ++ " static") effect {gas := false, isStatic := true} (failure .word (wordModulus - 1)) 3
  check "oversized initcode" (← lower "create" [9, 0, 49153])
    {gas := false} (failure .word (wordModulus - 1)) 3
  for (name, args, type) in [("codesize", [], Solcore.Core.Ty.word),
      ("codecopy", [0, 0, 0], Solcore.Core.Ty.unit), ("datacopy", [0, 0, 0], Solcore.Core.Ty.unit)] do
    check name (← lower name args) {known := false} (failure type 15)
  check "selfdestruct" (← lower "selfdestruct" [0xdef]) {} (failure .unit (wordModulus - 1)) 1
  check "static selfdestruct" (← lower "selfdestruct" [0xdef])
    {isStatic := true} (failure .unit (wordModulus - 1)) 3
  IO.println "Rust Hull world effects tests passed"
end Tests.RustHullWorldEffects

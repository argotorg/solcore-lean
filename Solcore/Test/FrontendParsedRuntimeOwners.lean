import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionEntry
import Solcore.Frontend.LocalNameRenaming

/-! Caller-owned declaration identities change input IDs, not the prepared
Core or runtime values. Compare complete parsed entries at identical fuel. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-owner.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  assertTrue lexed.diagnostics.isEmpty s!"{content}: lexer diagnostics"
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      assertTrue (next.atEnd && next.diagnostics.isEmpty) s!"{content}: incomplete or diagnosed declaration"
      return source
  | .reject _ _ => throw (IO.userError s!"{content}: expected a complete declaration")
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def firstOwner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"First", by decide⟩], by decide⟩⟩, 3⟩
private def secondOwner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Second", by decide⟩], by decide⟩⟩, 9⟩
private def types : TypeNameTable :=
  [(["Bool"], .bool), (["Word"], .word), (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def seven : Core.Word := ⟨7, by decide⟩
private def nine : Core.Word := ⟨9, by decide⟩
private def store : Core.Store := [.word nine, .bool false]
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def wordArg (value : Core.Word) : TypedRuntimeArgument := ⟨.word, .word value, .word⟩
private def closure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩

private def checkAccepted (content : String) (arguments : List TypedRuntimeArgument)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (initialStore : Core.Store := store) : IO Unit := do
  let source ← parsed content
  let some original := prepareRuntimeFunction? types firstOwner source arguments
    | throw (IO.userError s!"{content}: original entry rejected")
  assertTrue (decide (original.core = core ∧ original.returnType = type))
    s!"{content}: wrong original Core/type"
  for owner in [firstOwner, secondOwner] do
    let some prepared := prepareRuntimeFunction? types owner source arguments
      | throw (IO.userError s!"{content}: changing the owner rejected a valid entry")
    assertTrue (decide (prepared.core = original.core ∧ prepared.returnType = original.returnType))
      s!"{content}: owner changed exact Core/type"
    assertTrue (decide (prepared.inputs.environment.values = arguments.reverse.map (·.value)))
      s!"{content}: owner changed actual runtime values or row order"
    assertTrue (decide (prepared.inputs.context.values = arguments.reverse.map (·.type)))
      s!"{content}: owner changed context types or row order"
    let expectedIds := (List.range arguments.length).reverse.map fun index => (⟨owner, index⟩ : Resolved.LocalId)
    assertTrue (decide (prepared.inputs.ids = expectedIds)) s!"{content}: incorrect owner-relative identities"
    -- This concrete table contains only firstOwner IDs; this is not a global ID map law.
    assertTrue (decide (prepared.inputs.names = LocalNameTable.mapIds
      (fun id => ⟨owner, id.binderIndex⟩) original.inputs.names)) s!"{content}: wrong name-table relabeling"
    if owner == secondOwner && !arguments.isEmpty then
      assertTrue (decide (prepared.inputs.ids ≠ original.inputs.ids))
        s!"{content}: distinct owners should change nonempty identity tables"
    for fuel in [0, 1, 2, 3, 4, 5, 6, 8, cost - 1, cost, cost + 5] do
      assertTrue (decide (runRuntimeFunction? types owner source arguments fuel initialStore =
        runRuntimeFunction? types firstOwner source arguments fuel initialStore))
        s!"{content}: owner changed a full same-fuel result or suspended state"
    assertTrue (decide (runRuntimeFunction? types owner source arguments 0 initialStore =
      some (type, .outOfFuel (Core.State.initial core original.inputs.environment.values initialStore))))
      s!"{content}: wrong exact zero-fuel state"
    for fuel in [0, cost - 1] do
      match runRuntimeFunction? types owner source arguments fuel initialStore with
      | some (actualType, .outOfFuel _) =>
          assertTrue (decide (actualType = type)) s!"{content}: exhaustion changed type"
      | _ => throw (IO.userError s!"{content}: expected exhaustion below cost")
    for fuel in [cost, cost + 5] do
      assertTrue (decide (runRuntimeFunction? types owner source arguments fuel initialStore =
        some (type, .done value initialStore))) s!"{content}: wrong value, cost, or preserved store"

def frontendParsedRuntimeOwnerTests : IO Unit := do
  checkAccepted "function unit() { return; }" [] .unit .unit .unit 1
  checkAccepted "function literal() returns (Word) { return 7; }" [] (.word seven) .word (.word seven) 1
  for left in [false, true] do
    for right in [false, true] do
      checkAccepted "function first(x: Bool, y: Bool) returns (Bool) { return x; }"
        [boolArg left, boolArg right] (.var 1) .bool (.bool left) 1
      checkAccepted "function last(x: Bool, y: Bool) returns (Bool) { return y; }"
        [boolArg left, boolArg right] (.var 0) .bool (.bool right) 1
  for choice in [false, true] do
    let arguments := [boolArg choice, wordArg seven, wordArg nine]
    checkAccepted "function choose(c: Bool, t: Word, f: Word) returns (Word) { return c ? ~t : f; }"
      arguments (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word
      (.word (if choice then seven.bitNot else nine)) (if choice then 6 else 4)
    checkAccepted "function bits(c: Bool, t: Word, f: Word) returns (Word) { return t ^ f; }"
      arguments (.binary .wordXor (.var 1) (.var 0)) .word (.word (seven.bitXor nine)) 5
  checkAccepted "function cell(x: Cell) returns (Cell) { return x; }"
    [⟨.cell .word, .cellRef .word 40, .cellRef⟩] (.var 0) (.cell .word) (.cellRef .word 40) 1 []
  checkAccepted "function closure(x: Fn) returns (Fn) { return x; }"
    [closure] (.var 0) closure.type closure.value 1
  for choice in [false, true] do
    let arguments := [boolArg choice, wordArg seven, wordArg nine]
    for content in [
        "function missing(c: Bool, t: Word, f: Word) returns (Word) { return c ? t : missing; }",
        "function branches(c: Bool, t: Word, f: Word) returns (Word) { return c ? t : c; }",
        "function mismatch(c: Bool, t: Word, f: Word) returns (Bool) { return t; }",
        "function duplicate(c: Bool, t: Word, c: Word) returns (Word) { return t; }",
        "function generic<T>(c: Bool, t: Word, f: Word) returns (Word) { return t; }",
        "function empty(c: Bool, t: Word, f: Word) returns () { return; }"] do
      let source ← parsed content
      for owner in [firstOwner, secondOwner] do
        assertTrue (prepareRuntimeFunction? types owner source arguments).isNone
          s!"{content}: owner bypassed whole preparation"
        for fuel in [0, 1, 4, 6, 20] do
          assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone
            s!"{content}: invalid whole declaration ran after owner change"

end Tests

import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionStoreProperties

/-! Fully parsed restricted entries retain values and exact fuel boundaries
across unrelated stores. Every concrete result still carries its own store;
supplied references and closures are returned, never dereferenced or called. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "store-independence.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"StoreIndependent", by decide⟩], by decide⟩⟩, 18⟩
private def types : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def word (value : Nat) := Core.Word.ofNatModulo value
private def wordArg (value : Nat) : TypedRuntimeArgument := ⟨.word, .word (word value), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def cellArg (address : Nat) : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word address, .cellRef⟩
private def identityClosure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
private def constantClosure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.bool false) [], .closure .nil .bool⟩
private def stores : List Core.Store :=
  [[], [.word (word 7), .bool false], [.bool true, .word (word 99), .cellRef .word 40]]

private def accepted (content : String) (parameterTypes : List Core.Ty)
    (expectedCore : Core.Expr) (returnType : Core.Ty) : IO (Syntax.FunctionDecl × CompiledRuntimeFunction) := do
  let some declaration ← parsed? content | throw (IO.userError s!"{content}: incomplete declaration")
  let some compiled := compileRuntimeFunction? types owner declaration
    | throw (IO.userError s!"{content}: compilation failed")
  assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = returnType ∧
    compiled.inputs.context.values = parameterTypes.reverse)) "wrong exact static compilation"
  assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some returnType))
    "actual open Core failed typing"
  return (declaration, compiled)

private def runCase (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (initialStore : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) :=
  runRuntimeFunction? types owner declaration arguments fuel initialStore

/-- Only the type, terminal value, and exhaustion kind are compared between
stores. Neither suspended states nor complete stateful results are identified. -/
private def sameObservation (left right : Option (Core.Ty × Core.StatefulRunResult)) : Bool :=
  match left, right with
  | some (leftType, .done leftValue _), some (rightType, .done rightValue _) =>
      decide (leftType = rightType ∧ leftValue = rightValue)
  | some (leftType, .outOfFuel _), some (rightType, .outOfFuel _) => decide (leftType = rightType)
  | none, none => true
  | _, _ => false

private def completed (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) (value : Core.Value) (cost : Nat) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) = compiled.inputs.context.values.reverse))
    "completion case did not pass the exact argument guard"
  for fuel in List.range (cost + 3) do
    let reference := runCase declaration arguments fuel []
    for initialStore in stores do
      let observed := runCase declaration arguments fuel initialStore
      let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore
      assertTrue (decide (observed = some (compiled.returnType, Core.runStateful fuel initial)))
        s!"runtime entry changed its actual compiled execution at fuel {fuel}"
      assertTrue (sameObservation reference observed) s!"store changed the observation at fuel {fuel}"
      assertTrue (match observed with
        | some (type, .done result finalStore) =>
            decide (cost ≤ fuel ∧ type = compiled.returnType ∧ result = value ∧ finalStore = initialStore)
        | some (type, .outOfFuel suspended) =>
            decide (fuel < cost ∧ type = compiled.returnType ∧ suspended.store = initialStore)
        | _ => false) s!"wrong value, per-store preservation, or exact cost at fuel {fuel}"
      if fuel = 0 then
        assertTrue (decide (observed = some (compiled.returnType, .outOfFuel initial)))
          "zero fuel lost the actual store or arguments"

private def rejectedArguments (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ compiled.inputs.context.values.reverse))
    "rejection case accidentally satisfied the exact argument guard"
  for initialStore in stores do
    assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone
      "mismatched arguments prepared independently of the store"
    for fuel in List.range 20 do
      assertTrue (runCase declaration arguments fuel initialStore).isNone
        "a replacement store bypassed the argument guard"

def frontendParsedStoreIndependenceTests : IO Unit := do
  assertTrue (decide (stores.length = 3 ∧ stores[0]! ≠ stores[1]! ∧
    stores[0]! ≠ stores[2]! ∧ stores[1]! ≠ stores[2]!)) "store fixtures must be distinct"
  let (bare, bareCompiled) ← accepted "function bare() { return; }" [] .unit .unit
  completed bare bareCompiled [] .unit 1
  rejectedArguments bare bareCompiled [boolArg false]
  let (arithmetic, arithmeticCompiled) ← accepted
    "function arithmetic(x: Word, y: Word) returns (Word) { return x * y > y ? x - y : x; }"
    [.word, .word] (.ifE (.binary .wordGt (.binary .wordMul (.var 1) (.var 0)) (.var 0))
      (.binary .wordSub (.var 1) (.var 0)) (.var 1)) .word
  for left in [0, 1, 7, 2 ^ 256 - 1] do
    for right in [0, 1, 9] do
      let selected := decide ((word left).mul (word right) > word right)
      completed arithmetic arithmeticCompiled [wordArg left, wordArg right]
        (.word (if selected then (word left).sub (word right) else word left)) (if selected then 16 else 12)
  let (branch, branchCompiled) ← accepted
    "function branch(c: Bool, x: Word, y: Word) returns (Word) { return c ? x * y : x; }"
    [.bool, .word, .word] (.ifE (.var 2) (.binary .wordMul (.var 1) (.var 0)) (.var 1)) .word
  for choice in [false, true] do
    completed branch branchCompiled [boolArg choice, wordArg 7, wordArg 9]
      (.word (word (if choice then 63 else 7))) (if choice then 8 else 4)
  for arguments in [[], [boolArg false, wordArg 7], [wordArg 7, boolArg true, wordArg 9],
      [boolArg true, wordArg 7, boolArg false], [boolArg true, wordArg 7, wordArg 9, wordArg 1]] do
    rejectedArguments branch branchCompiled arguments
  let (short, shortCompiled) ← accepted
    "function short(c: Bool) returns (Bool) { return c && !c; }"
    [.bool] (.ifE (.var 0) (.unary .boolNot (.var 0)) (.bool false)) .bool
  for choice in [false, true] do
    completed short shortCompiled [boolArg choice] (.bool false) (if choice then 6 else 4)
  for (typeName, type, supplied) in
      [("Cell", Core.Ty.cell .word, [cellArg 0, cellArg 40, cellArg 91]),
       ("Fn", Core.Ty.function .bool .bool, [identityClosure, constantClosure])] do
    let (declaration, compiled) ← accepted
      (s!"function identity(x: {typeName}) returns ({typeName})" ++ " { return ((x)); }")
      [type] (.var 0) type
    for argument in supplied do
      completed declaration compiled [argument] argument.value 1
    rejectedArguments declaration compiled []
    rejectedArguments declaration compiled [wordArg 7]
  let (nominal, nominalCompiled) ← accepted
    "function nominal(x: Opaque) returns (Opaque) { return x; }"
    [.namedData ⟨91⟩] (.var 0) (.namedData ⟨91⟩)
  for arguments in [[], [boolArg false], [wordArg 0], [cellArg 0], [identityClosure]] do
    rejectedArguments nominal nominalCompiled arguments
  for content in ["function invalid(c: Bool) returns (Bool) { return c || missing; }",
      "function invalid(c: Bool) returns (Bool) { return c && missing; }",
      "function invalid(c: Bool, x: Word) returns (Word) { return c ? x : missing; }",
      "function invalid(c: Bool, x: Word) returns (Word) { return c ? x : c; }",
      "function invalid(x: Word) returns (Word) { return x > 0; }",
      "function duplicate(x: Bool, x: Bool) { return; }", "function empty() {}"] do
    let some declaration ← parsed? content | throw (IO.userError "whole-rejection fixture failed parsing")
    assertTrue (compileRuntimeFunction? types owner declaration).isNone "invalid whole declaration compiled"
    for arguments in [[], [boolArg false], [boolArg true], [wordArg 7],
        [boolArg false, wordArg 7], [boolArg true, wordArg 7], [boolArg false, boolArg true]] do
      assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone
        "a skipped invalid branch bypassed whole preparation"
      for initialStore in stores do
        for fuel in [0, 1, 4, 6, 20] do
          assertTrue (runCase declaration arguments fuel initialStore).isNone
            "a replacement store bypassed whole declaration rejection"
  for content in ["", "function incomplete()", "function f() { return;",
      "function f() { return; } trailing", "function f() { return; } /*"] do
    assertTrue (← parsed? content).isNone "incomplete input entered store observation tests"

end Tests

import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunction

/-! A cached result from complete source compilation determines full runtime
states for many actual argument lists, including exact guard rejection. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "compiled-execution.sol"⟩, content }
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

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Cached", by decide⟩], by decide⟩⟩, 7⟩
private def types : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["U"], .unit),
    (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def word (value : Nat) := Core.Word.ofNatModulo value
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def wordArg (value : Nat) : TypedRuntimeArgument := ⟨.word, .word (word value), .word⟩
private def cellArg (address : Nat) : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word address, .cellRef⟩
private def identityClosure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
private def constantClosure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.bool false) [], .closure .nil .bool⟩
private def store : Core.Store := [.bool false, .word (word 91)]

/-- Use the cached compilation, not another body/preparation lookup, on the
expected side. The actual side is the unchanged public runtime endpoint. -/
private def compareFuels (declaration : Syntax.FunctionDecl) (cached : Option CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) (fuels : List Nat) (initialStore : Core.Store) : IO Unit := do
  for fuel in fuels do
    let expected := cached.bind fun compiled =>
      if arguments.map (·.type) = compiled.inputs.context.values.reverse then
        some (compiled.returnType, Core.runStateful fuel
          (Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore))
      else none
    assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel initialStore = expected))
      s!"{declaration.value.signature.name.value}: cached compilation changed the full result at fuel {fuel}"

private def accepted (content : String) (parameterTypes : List Core.Ty)
    (expectedCore : Core.Expr) (returnType : Core.Ty) : IO (Syntax.FunctionDecl × CompiledRuntimeFunction) := do
  let some declaration ← parsed? content | throw (IO.userError s!"{content}: incomplete declaration")
  let some compiled := compileRuntimeFunction? types owner declaration
    | throw (IO.userError s!"{content}: compilation failed")
  assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = returnType ∧
    compiled.inputs.context.values = parameterTypes.reverse)) s!"{content}: wrong exact static output"
  assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some returnType))
    s!"{content}: actual open Core is not typed"
  return (declaration, compiled)

private def completed (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) (expected : Core.Value) (cost : Nat)
    (initialStore : Core.Store := store) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) = compiled.inputs.context.values.reverse))
    "completion case did not pass the ordered argument guard"
  compareFuels declaration (some compiled) arguments (List.range (cost + 3)) initialStore
  let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore
  assertTrue (decide (runRuntimeFunction? types owner declaration arguments 0 initialStore =
    some (compiled.returnType, .outOfFuel initial))) "wrong exact zero-fuel state"
  assertTrue (match runRuntimeFunction? types owner declaration arguments (cost - 1) initialStore with
    | some (_, .outOfFuel _) => true | _ => false) "completed below the independent expected cost"
  for fuel in [cost, cost + 2] do
    assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel initialStore =
      some (compiled.returnType, .done expected initialStore))) "wrong value, store, or exact completion boundary"

private def mismatched (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ compiled.inputs.context.values.reverse))
    "mismatch fixture accidentally satisfied the ordered type guard"
  compareFuels declaration (some compiled) arguments (List.range 20) store
  assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone
    "mismatched arguments were prepared"

def frontendParsedCompiledExecutionTests : IO Unit := do
  let (bare, bareCompiled) ← accepted "function bare() { return; }" [] .unit .unit
  completed bare bareCompiled [] .unit 1
  mismatched bare bareCompiled [boolArg false]
  for index in List.range 3 do
    let name := ["x", "y", "z"][index]!
    let (declaration, compiled) ← accepted
      ("function position(x: Bool, y: Bool, z: Bool) returns (Bool) { return " ++ name ++ "; }")
      [.bool, .bool, .bool] (.var (2 - index)) .bool
    for x in [false, true] do
      for y in [false, true] do
        for z in [false, true] do
          completed declaration compiled [boolArg x, boolArg y, boolArg z] (.bool ([x, y, z][index]!)) 1
    for arguments in [[], [boolArg false], [boolArg false, boolArg true],
        [boolArg false, boolArg true, boolArg false, boolArg true],
        [wordArg 7, boolArg false, boolArg true]] do
      mismatched declaration compiled arguments
  let (subtract, subtractCompiled) ← accepted
    "function difference(x: Word, y: Word) returns (Word) { return x - y; }"
    [.word, .word] (.binary .wordSub (.var 1) (.var 0)) .word
  for left in [0, 7, 9] do
    for right in [0, 7, 9] do
      let arguments := [wordArg left, wordArg right]
      completed subtract subtractCompiled arguments (.word ((word left).sub (word right))) 5
      assertTrue (decide (runRuntimeFunction? types owner subtract arguments 4 store =
        some (.word, .outOfFuel ⟨.ret (.word (word right)),
          [.binaryApply .wordSub (.word (word left))], store⟩))) "cached subtraction reversed the pending operands"
  let (branch, branchCompiled) ← accepted
    "function branch(c: Bool, x: Word, y: Word) returns (Word) { return c ? x * y : x; }"
    [.bool, .word, .word] (.ifE (.var 2) (.binary .wordMul (.var 1) (.var 0)) (.var 1)) .word
  for choice in [false, true] do
    completed branch branchCompiled [boolArg choice, wordArg 7, wordArg 9]
      (.word (word (if choice then 63 else 7))) (if choice then 8 else 4)
  for arguments in [[wordArg 7, boolArg true, wordArg 9], [boolArg true, boolArg false, wordArg 9],
      [boolArg true, wordArg 7], [boolArg true, wordArg 7, wordArg 9, wordArg 1]] do
    mismatched branch branchCompiled arguments
  let (short, shortCompiled) ← accepted
    "function short(c: Bool) returns (Bool) { return c && !c; }"
    [.bool] (.ifE (.var 0) (.unary .boolNot (.var 0)) (.bool false)) .bool
  for choice in [false, true] do
    completed short shortCompiled [boolArg choice] (.bool false) (if choice then 6 else 4)
  assertTrue (decide (runRuntimeFunction? types owner short [boolArg false] 5 store =
    some (.bool, .done (.bool false) store))) "false short-circuit path did not finish at five"
  assertTrue (match runRuntimeFunction? types owner short [boolArg true] 5 store with
    | some (.bool, .outOfFuel _) => true | _ => false) "equal argument types erased the selected path's extra cost"
  let (cell, cellCompiled) ← accepted
    "function cell(c: Bool, x: Cell, y: Cell) returns (Cell) { return c ? x : y; }"
    [.bool, .cell .word, .cell .word] (.ifE (.var 2) (.var 1) (.var 0)) (.cell .word)
  let (closure, closureCompiled) ← accepted
    "function closure(c: Bool, x: Fn, y: Fn) returns (Fn) { return c ? x : y; }"
    [.bool, .function .bool .bool, .function .bool .bool] (.ifE (.var 2) (.var 1) (.var 0)) (.function .bool .bool)
  for choice in [false, true] do
    completed cell cellCompiled [boolArg choice, cellArg 40, cellArg 91]
      (if choice then (cellArg 40).value else (cellArg 91).value) 4 []
    completed closure closureCompiled [boolArg choice, identityClosure, constantClosure]
      (if choice then identityClosure.value else constantClosure.value) 4
  let (nominal, nominalCompiled) ← accepted
    "function nominal(x: Opaque) returns (Opaque) { return x; }"
    [.namedData ⟨91⟩] (.var 0) (.namedData ⟨91⟩)
  for arguments in [[], [boolArg false], [wordArg 0], [cellArg 0], [identityClosure]] do
    mismatched nominal nominalCompiled arguments
  for content in ["function wrong(x: Word) returns (Word) { return x > 0; }",
      "function unknown(x: Missing) { return; }", "function duplicate(x: Bool, x: Bool) { return; }",
      "function empty() {}", "function invalid(c: Bool) returns (Bool) { return c || missing; }"] do
    let some declaration ← parsed? content | throw (IO.userError "whole-rejection fixture did not parse")
    let cached := compileRuntimeFunction? types owner declaration
    assertTrue cached.isNone "invalid whole declaration compiled"
    for arguments in [[], [boolArg false], [boolArg true], [wordArg 7], [boolArg false, boolArg true]] do
      compareFuels declaration cached arguments [0, 1, 4, 5, 20] store
  for content in ["", "function f()", "function f() { return;", "function f() { return; } trailing"] do
    assertTrue (← parsed? content).isNone "malformed or partially consumed declaration entered compiled tests"

end Tests

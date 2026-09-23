import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunction

/-! Full canonical declarations compile before any arguments are supplied.
Matching actual arguments then use the unchanged checked runtime endpoint. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed? (content : String) (location : Syntax.Parser.FunctionLocation := .module) :
    IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-function-compilation.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Compilation", by decide⟩], by decide⟩⟩, 4⟩
private def types : TypeNameTable :=
  [(["Bool"], .bool), (["Word"], .word), (["U"], .unit), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def seven : Core.Word := ⟨7, by decide⟩
private def nine : Core.Word := ⟨9, by decide⟩
private def store : Core.Store := [.word nine, .bool false]
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def wordArg (value : Core.Word) : TypedRuntimeArgument := ⟨.word, .word value, .word⟩
private def cellArg : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
private def closureArg : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩

private def sameCompiled : Option CompiledRuntimeFunction → Option CompiledRuntimeFunction → Bool
  | none, none => true
  | some left, some right =>
      decide (left.inputs.bindings.map (fun row => (row.name, row.id, row.type)) =
        right.inputs.bindings.map (fun row => (row.name, row.id, row.type))) &&
      decide (left.core = right.core) && decide (left.returnType = right.returnType)
  | _, _ => false

private def checkCompiled (table : TypeNameTable) (declaration : Syntax.FunctionDecl)
    (expectedTypes : List Core.Ty) (expectedCore : Core.Expr) (expectedType : Core.Ty) :
    IO CompiledRuntimeFunction := do
  let some compiled := compileRuntimeFunction? table owner declaration
    | throw (IO.userError "value-free compilation failed")
  assertTrue (decide (compiled.core = expectedCore)) "compiler did not keep the exact elaborated Core"
  assertTrue (decide (compiled.returnType = expectedType)) "compiler changed the return contract"
  assertTrue (decide (compiled.inputs.context.values = expectedTypes.reverse)) "wrong static parameter types"
  assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some expectedType))
    "compiled open Core did not type-check in its parameter context"
  let names ← declaration.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name _ := parameter.value | throw (IO.userError "unexpected parameter profile")
    pure name.value
  assertTrue (decide (names.length = expectedTypes.length)) "wrong expected parameter count"
  assertTrue (decide (compiled.inputs.names = (names.zipIdx.map fun (name, index) =>
    (name, (⟨owner, index⟩ : Resolved.LocalId))).reverse)) "wrong compiled name/identity table"
  return compiled

private def checkRun (table : TypeNameTable) (declaration : Syntax.FunctionDecl)
    (compiled : CompiledRuntimeFunction) (arguments : List TypedRuntimeArgument)
    (value : Core.Value) (cost : Nat) (initialStore : Core.Store := store) : IO Unit := do
  let prepared := prepareRuntimeFunction? table owner declaration arguments
  assertTrue (sameCompiled (prepared.map PreparedRuntimeFunction.toCompiled) (some compiled))
    "matching actual arguments changed the compiled projection"
  let actualValues := arguments.reverse.map (·.value)
  for fuel in [0, 1, cost - 1, cost, cost + 5] do
    assertTrue (decide (runRuntimeFunction? table owner declaration arguments fuel initialStore =
      some (compiled.returnType, Core.runStateful fuel (Core.State.initial compiled.core actualValues initialStore))))
      "checked entry did not run the actual compiled Core with actual argument values"
  assertTrue (decide (runRuntimeFunction? table owner declaration arguments 0 initialStore =
    some (compiled.returnType, .outOfFuel (Core.State.initial compiled.core actualValues initialStore))))
    "zero-fuel state changed through compilation"
  match runRuntimeFunction? table owner declaration arguments (cost - 1) initialStore with
  | some (_, .outOfFuel _) => pure ()
  | _ => throw (IO.userError "entry completed below its exact cost")
  for fuel in [cost, cost + 5] do
    assertTrue (decide (runRuntimeFunction? table owner declaration arguments fuel initialStore =
      some (compiled.returnType, .done value initialStore))) "wrong result, store, or exact fuel boundary"

private def checkAccepted (content : String) (expectedTypes : List Core.Ty)
    (core : Core.Expr) (type : Core.Ty) : IO (Syntax.FunctionDecl × CompiledRuntimeFunction) := do
  let some declaration ← parsed? content | throw (IO.userError s!"{content}: expected complete declaration")
  let compiled ← checkCompiled types declaration expectedTypes core type
  return (declaration, compiled)

def frontendParsedFunctionCompilationTests : IO Unit := do
  let (bare, bareCompiled) ← checkAccepted "function bare() { return; }" [] .unit .unit
  checkRun types bare bareCompiled [] .unit 1
  let (literal, literalCompiled) ← checkAccepted "function literal() returns (Word) { return 7; }"
    [] (.word seven) .word
  checkRun types literal literalCompiled [] (.word seven) 1
  let _ ← checkAccepted "function opaque(x: Opaque) returns (Opaque) { return x; }"
    [.namedData ⟨91⟩] (.var 0) (.namedData ⟨91⟩)
  let _ ← checkAccepted "function choice(c: Bool, x: Opaque, y: Opaque) returns (Opaque) { return c ? x : y; }"
    [.bool, .namedData ⟨91⟩, .namedData ⟨91⟩] (.ifE (.var 2) (.var 1) (.var 0)) (.namedData ⟨91⟩)
  let _ ← checkAccepted "function unused(x: Opaque) { return; }" [.namedData ⟨91⟩] .unit .unit
  let (first, firstCompiled) ← checkAccepted "function first(x: Bool, y: Bool) returns (Bool) { return x; }"
    [.bool, .bool] (.var 1) .bool
  for left in [false, true] do
    for right in [false, true] do
      checkRun types first firstCompiled [boolArg left, boolArg right] (.bool left) 1
  let (branch, branchCompiled) ← checkAccepted
    "function branch(c: Bool, t: Word, f: Word) returns (Word) { return c ? ~t : f; }"
    [.bool, .word, .word] (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word
  for choice in [false, true] do
    checkRun types branch branchCompiled [boolArg choice, wordArg seven, wordArg nine]
      (.word (if choice then seven.bitNot else nine)) (if choice then 6 else 4)
  let (cell, cellCompiled) ← checkAccepted "function cell(x: Cell) returns (Cell) { return x; }"
    [.cell .word] (.var 0) (.cell .word)
  checkRun types cell cellCompiled [cellArg] cellArg.value 1 []
  let (closure, closureCompiled) ← checkAccepted "function closure(x: Fn) returns (Fn) { return x; }"
    [.function .bool .bool] (.var 0) (.function .bool .bool)
  checkRun types closure closureCompiled [closureArg] closureArg.value 1
  let some alias ← parsed? "function alias(x: Word) returns (Word) { return x; }"
    | throw (IO.userError "alias declaration did not parse")
  let aliasCompiled ← checkCompiled [(["Word"], .bool)] alias [.bool] (.var 0) .bool
  checkRun [(["Word"], .bool)] alias aliasCompiled [boolArg true] (.bool true) 1
  for arguments in [[], [boolArg true], [boolArg true, boolArg false, boolArg true],
      [wordArg seven, boolArg true], [boolArg true, wordArg seven]] do
    assertTrue (prepareRuntimeFunction? types owner first arguments).isNone
      "static success bypassed argument arity/type checking"
  for arguments in [[wordArg seven, boolArg true, wordArg nine],
      [boolArg true, boolArg false, wordArg nine]] do
    assertTrue (prepareRuntimeFunction? types owner branch arguments).isNone
      "static success bypassed ordered argument types"
  for content in ["function bad() returns (Bool) { return 7; }", "function absent() { return 7; }",
      "function empty() returns () { return; }", "function many() returns (Word, Bool) { return 7; }",
      "function generic<T>() { return; }", "function constrained() where Word: Eq { return; }",
      "function duplicate(x: Bool, x: Bool) returns (Bool) { return x; }",
      "function staged(comptime x: Bool) returns (Bool) { return x; }",
      "function unknown(x: Unknown) { return; }", "function emptyBody() {}",
      "function repeated() { return; return; }", "function tail() returns (Word) { 7 }",
      "function missing(c: Bool, x: Word) returns (Word) { return c ? x : missing; }",
      "function types(c: Bool, x: Word) returns (Word) { return c ? x : c; }"] do
    let some declaration ← parsed? content | throw (IO.userError s!"{content}: rejection case should parse")
    assertTrue (compileRuntimeFunction? types owner declaration).isNone "invalid whole contract compiled"
    for arguments in [[], [boolArg false, wordArg seven], [boolArg true, wordArg nine]] do
      assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone
        "runtime preparation bypassed compile rejection"
  for content in ["function publicOnly() public { return; }", "function payableOnly() payable { return; }"] do
    let some declaration ← parsed? content .contract | throw (IO.userError "contract modifier case did not parse")
    assertTrue (compileRuntimeFunction? types owner declaration).isNone "unsupported modifier compiled"
  for content in ["", "function f()", "function f() { return;", "function f() { return 7 }",
      "function f() { return; } trailing", "function f() public { return; }"] do
    assertTrue (← parsed? content).isNone "malformed, diagnosed, or incompletely consumed source accepted"

end Tests

import Solcore.Syntax.Parser.Function
import Solcore.Frontend.ReturnBodyFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionExecutionFactorization

/-! A source-computed budget is shared by actual typed argument cases. The
budget is sufficient, not exact; rejected sources still do not execute. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "fuel-bounds.sol"⟩, content }
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
  ⟨⟨.main, ⟨[⟨"SourceBudget", by decide⟩], by decide⟩⟩, 20⟩
private def types : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def word (value : Nat) := Core.Word.ofNatModulo value
private def wordArg (value : Nat) : TypedRuntimeArgument := ⟨.word, .word (word value), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def stores : List Core.Store := [[], [.word (word 7), .bool false, .cellRef .word 40]]

private def accepted (content : String) (parameterTypes : List Core.Ty)
    (expectedCore : Core.Expr) (returnType : Core.Ty) (expectedBound : Nat) :
    IO (Syntax.FunctionDecl × CompiledRuntimeFunction) := do
  let some declaration ← parsed? content | throw (IO.userError s!"{content}: incomplete declaration")
  let bound := returnBodyFuelBound declaration.value.body
  assertTrue (bound == expectedBound) s!"{content}: wrong source-only fuel bound {bound}"
  match declaration.value.body.value with
  | [⟨_, .returnStmt (some source)⟩] =>
      assertTrue (localExpressionFuelBound source == bound) "return wrapper charged extra fuel"
  | [⟨_, .returnStmt none⟩] => assertTrue (bound == 1) "bare return must cost one"
  | _ => throw (IO.userError "accepted fixture is not a singleton return")
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

private def completed (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) (value : Core.Value) (cost : Nat) : IO Unit := do
  let bound := returnBodyFuelBound declaration.value.body
  assertTrue (decide (0 < cost ∧ cost ≤ bound)) "path cost exceeded its source bound"
  assertTrue (decide (arguments.map (·.type) = compiled.inputs.context.values.reverse))
    "completion case did not pass the exact argument guard"
  for initialStore in stores do
    let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore
    for fuel in List.range (bound + 3) do
      let observed := runCase declaration arguments fuel initialStore
      assertTrue (decide (observed = some (compiled.returnType, Core.runStateful fuel initial)))
        s!"runtime entry changed its actual compiled execution at fuel {fuel}"
      assertTrue (match observed with
        | some (type, .done result finalStore) =>
            decide (cost ≤ fuel ∧ type = compiled.returnType ∧ result = value ∧ finalStore = initialStore)
        | some (type, .outOfFuel suspended) =>
            decide (fuel < cost ∧ type = compiled.returnType ∧ suspended.store = initialStore)
        | _ => false) s!"wrong value, unchanged store, or exact path cost at fuel {fuel}"
      if bound ≤ fuel then
        assertTrue (decide (observed = some (compiled.returnType, .done value initialStore)))
          "source budget was insufficient for an actual matching argument case"
    if cost < bound then
      assertTrue (decide (runCase declaration arguments (bound - 1) initialStore =
        some (compiled.returnType, .done value initialStore))) "conservative budget became an exact cost"

private def rejectedArguments (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) : IO Unit := do
  let bound := returnBodyFuelBound declaration.value.body
  assertTrue (decide (arguments.map (·.type) ≠ compiled.inputs.context.values.reverse))
    "rejection case accidentally satisfied the exact argument guard"
  assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone
    "source bound bypassed preparation's actual argument guard"
  for initialStore in stores do
    for fuel in [0, bound, bound + 10] do
      assertTrue (runCase declaration arguments fuel initialStore).isNone
        "increasing the source budget bypassed the argument guard"

private def strictOperations :
    List (String × Core.BinaryOp × (Core.Word → Core.Word → Core.Word)) :=
  [("+", .wordAdd, Core.Word.add), ("-", .wordSub, Core.Word.sub),
    ("*", .wordMul, Core.Word.mul), ("&", .wordAnd, Core.Word.bitAnd),
    ("|", .wordOr, Core.Word.bitOr), ("^", .wordXor, Core.Word.bitXor)]

def frontendParsedFuelBoundTests : IO Unit := do
  let (bare, bareCompiled) ← accepted "function bare() { return; }" [] .unit .unit 1
  completed bare bareCompiled [] .unit 1
  rejectedArguments bare bareCompiled [boolArg false]
  for spelling in ["7", "0007", "0x0007", "(((7)))", "/* text adds no Core steps */ (0000007)"] do
    let (declaration, compiled) ← accepted
      ("function literal() returns (Word) { return " ++ spelling ++ "; }")
      [] (.word (word 7)) .word 1
    completed declaration compiled [] (.word (word 7)) 1
  for (symbol, operator, operation) in strictOperations do
    let (declaration, compiled) ← accepted
      ("function strict(x: Word, y: Word) returns (Word) { return ((x)) " ++ symbol ++ " y; }")
      [.word, .word] (.binary operator (.var 1) (.var 0)) .word 5
    for left in [0, 1, 7, 2 ^ 256 - 1] do
      for right in [0, 1, 9] do
        completed declaration compiled [wordArg left, wordArg right]
          (.word (operation (word left) (word right))) 5
  let (mask, maskCompiled) ← accepted
    "function mask(x: Word) returns (Word) { return ~(x); }"
    [.word] (.unary .wordNot (.var 0)) .word 3
  for value in [0, 1, 170, 2 ^ 256 - 1] do
    completed mask maskCompiled [wordArg value] (.word (word value).bitNot) 3
  let (greater, greaterCompiled) ← accepted
    "function greater(x: Word, y: Word) returns (Bool) { return x > y; }"
    [.word, .word] (.binary .wordGt (.var 1) (.var 0)) .bool 5
  for left in [0, 1, 2 ^ 255, 2 ^ 256 - 1] do
    for right in [0, 1, 2 ^ 256 - 1] do
      completed greater greaterCompiled [wordArg left, wordArg right]
        (.bool (decide (word left > word right))) 5
  let literal := fun value => Core.Expr.word (word value)
  let (precedence, precedenceCompiled) ← accepted
    "function precedence() returns (Bool) { return 1 | 2 ^ 3 & 4 + 5 * 2 > 2; }"
    [] (.binary .wordGt (.binary .wordOr (literal 1)
      (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3)
        (.binary .wordAdd (literal 4) (.binary .wordMul (literal 5) (literal 2)))))) (literal 2))
    .bool 25
  completed precedence precedenceCompiled [] (.bool false) 25
  for (symbol, expectedCore) in [("&&", Core.Expr.ifE (.var 0)
      (.unary .boolNot (.var 0)) (.bool false)),
      ("||", Core.Expr.ifE (.var 0) (.bool true) (.unary .boolNot (.var 0)))] do
    let (declaration, compiled) ← accepted
      ("function short(c: Bool) returns (Bool) { return c " ++ symbol ++ " !c; }")
      [.bool] expectedCore .bool 6
    for choice in [false, true] do
      let isAnd := symbol == "&&"
      completed declaration compiled [boolArg choice] (.bool (!isAnd))
        (if choice == isAnd then 6 else 4)
  let (branch, branchCompiled) ← accepted
    "function branch(c: Bool, x: Word, y: Word) returns (Word) { return c ? x * y : x; }"
    [.bool, .word, .word] (.ifE (.var 2) (.binary .wordMul (.var 1) (.var 0)) (.var 1)) .word 8
  for choice in [false, true] do
    for left in [0, 7, 2 ^ 256 - 1] do
      completed branch branchCompiled [boolArg choice, wordArg left, wordArg 9]
        (.word (if choice then (word left).mul (word 9) else word left)) (if choice then 8 else 4)
  for arguments in [[], [boolArg false, wordArg 7], [wordArg 7, boolArg true, wordArg 9],
      [boolArg true, wordArg 7, boolArg false], [boolArg true, wordArg 7, wordArg 9, wordArg 1]] do
    rejectedArguments branch branchCompiled arguments
  let (arithmetic, arithmeticCompiled) ← accepted
    "function arithmetic(x: Word, y: Word) returns (Word) { return x * y > y ? x - y : x; }"
    [.word, .word] (.ifE (.binary .wordGt (.binary .wordMul (.var 1) (.var 0)) (.var 0))
      (.binary .wordSub (.var 1) (.var 0)) (.var 1)) .word 16
  for left in [0, 1, 7, 2 ^ 256 - 1] do
    for right in [0, 1, 9] do
      let selected := decide ((word left).mul (word right) > word right)
      completed arithmetic arithmeticCompiled [wordArg left, wordArg right]
        (.word (if selected then (word left).sub (word right) else word left)) (if selected then 16 else 12)
  let identity : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  for (name, argument) in [("Fn", identity), ("Cell", cell)] do
    let (declaration, compiled) ← accepted
      (s!"function identity(x: {name}) returns ({name})" ++ " { return x; }")
      [argument.type] (.var 0) argument.type 1
    completed declaration compiled [argument] argument.value 1
  let (nominal, nominalCompiled) ← accepted
    "function nominal(x: Opaque) returns (Opaque) { return x; }"
    [.namedData ⟨91⟩] (.var 0) (.namedData ⟨91⟩) 1
  for arguments in [[], [boolArg false], [wordArg 0], [cell], [identity]] do
    rejectedArguments nominal nominalCompiled arguments
  for (content, expectedBound) in [
      ("function empty() {}", 0), ("function multiple() { return; return; }", 0),
      ("function division(x: Word) returns (Word) { return x / x; }", 0),
      ("function missing() returns (Word) { return missing; }", 1),
      ("function string() returns (Word) { return \"7\"; }", 1),
      (s!"function overflow() returns (Word)" ++ " { return " ++ s!"{Core.wordModulus};" ++ " }", 1),
      ("function skipped(c: Bool) returns (Bool) { return c && missing; }", 4),
      ("function skipped(c: Bool, x: Word) returns (Bool) { return c || x / x; }", 4),
      ("function skipped(c: Bool, x: Word) returns (Word) { return c ? x : x / x; }", 4),
      ("function wrong(c: Bool, x: Word) returns (Word) { return c ? x : c; }", 4),
      ("function wrong(x: Word) returns (Word) { return x > 0; }", 5)] do
    let some declaration ← parsed? content | throw (IO.userError "whole-rejection fixture failed parsing")
    assertTrue (returnBodyFuelBound declaration.value.body == expectedBound)
      "rejected syntax lost its numerical bound or zero placeholder"
    assertTrue (compileRuntimeFunction? types owner declaration).isNone "numeric budget certified acceptance"
    for arguments in [[], [boolArg false], [boolArg true], [wordArg 7],
        [boolArg false, wordArg 7], [boolArg true, wordArg 7], [boolArg false, boolArg true]] do
      assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone
        "a numeric budget bypassed whole preparation"
      for initialStore in stores do
        for fuel in [0, expectedBound, expectedBound + 20] do
          assertTrue (runCase declaration arguments fuel initialStore).isNone
            "an ample budget bypassed whole declaration rejection"
  for content in ["", "function incomplete()", "function f() { return;",
      "function f() { return; } trailing", "function f() { return; } /*"] do
    assertTrue (← parsed? content).isNone "incomplete input entered source budget tests"

end Tests

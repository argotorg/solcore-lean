import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionExecutionFactorization

/-! Resume only genuine fuel-exhaustion states from fully parsed entries.
Every control, continuation, captured value, and store remains observable. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "resumption.sol"⟩, content }
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
  ⟨⟨.main, ⟨[⟨"ParsedResume", by decide⟩], by decide⟩⟩, 21⟩
private def types : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool)]
private def word (value : Nat) := Core.Word.ofNatModulo value
private def wordArg (value : Nat) : TypedRuntimeArgument := ⟨.word, .word (word value), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def stores : List Core.Store := [[], [.word (word 7), .bool false, .cellRef .word 40]]

private def accepted (content : String) (parameterTypes : List Core.Ty)
    (expectedCore : Core.Expr) (returnType : Core.Ty) :
    IO (Syntax.FunctionDecl × CompiledRuntimeFunction) := do
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

private def checkpoints (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) (value : Core.Value) (cost : Nat) : IO Unit := do
  assertTrue (cost > 0) "checkpoint fixture needs a positive known path cost"
  assertTrue (decide (arguments.map (·.type) = compiled.inputs.context.values.reverse))
    "checkpoint case did not pass the exact argument guard"
  for initialStore in stores do
    let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore
    assertTrue (decide (runCase declaration arguments cost initialStore =
      some (compiled.returnType, .done value initialStore))) "wrong original completion threshold"
    assertTrue (decide (Core.runStateful 0 (Core.State.final value initialStore) =
      .done value initialStore)) "final recognition charged a transition"
    for spent in List.range cost do
      let some (type, .outOfFuel checkpoint) := runCase declaration arguments spent initialStore
        | throw (IO.userError "source did not yield the expected genuine checkpoint")
      assertTrue (decide (type = compiled.returnType ∧ checkpoint.store = initialStore ∧
        Core.runStateful spent initial = .outOfFuel checkpoint))
        "checkpoint lost its actual compiled origin, type, or store"
      assertTrue (decide (Core.runStateful 0 checkpoint = .outOfFuel checkpoint))
        "a genuine pre-terminal checkpoint became done without another transition"
      if spent = 0 then
        assertTrue (decide (checkpoint = initial)) "zero-spent checkpoint changed actual argument values"
      let residual := cost - spent
      for additional in List.range (residual + 3) do
        let resumed := Core.runStateful additional checkpoint
        assertTrue (decide (runCase declaration arguments (spent + additional) initialStore =
          some (compiled.returnType, resumed))) "resumption changed the full same-total-fuel result"
        assertTrue (decide (resumed = Core.runStateful (spent + additional) initial))
          "resumption differed from the actual compiled machine"
        assertTrue (match resumed with
          | .done result finalStore => decide (residual ≤ additional ∧ result = value ∧ finalStore = initialStore)
          | .outOfFuel suspended => decide (additional < residual ∧ suspended.store = initialStore)
          | _ => false) "resumption lost the exact residual threshold, value, or own store"
      for middle in List.range residual do
        let .outOfFuel second := Core.runStateful middle checkpoint
          | throw (IO.userError "second genuine checkpoint unexpectedly terminated")
        assertTrue (decide (runCase declaration arguments (spent + middle) initialStore =
          some (compiled.returnType, .outOfFuel second))) "second checkpoint lost its source provenance"
        for last in List.range (residual - middle + 3) do
          let resumed := Core.runStateful last second
          assertTrue (decide (resumed = Core.runStateful (middle + last) checkpoint ∧
            runCase declaration arguments (spent + middle + last) initialStore =
              some (compiled.returnType, resumed))) "three-chunk execution changed the full result"

private def pendingSubtraction (declaration : Syntax.FunctionDecl)
    (left right : Nat) : IO Unit := do
  let arguments := [wordArg left, wordArg right]
  for initialStore in stores do
    let some (.word, .outOfFuel checkpoint) := runCase declaration arguments 4 initialStore
      | throw (IO.userError "subtraction did not yield its fuel-four checkpoint")
    let expected : Core.State :=
      ⟨.ret (.word (word right)), [.binaryApply .wordSub (.word (word left))], initialStore⟩
    assertTrue (decide (checkpoint = expected)) "noncommutative pending frame lost ordered argument values"
    assertTrue (decide (Core.runStateful 0 checkpoint = .outOfFuel expected ∧
      Core.runStateful 1 checkpoint = .done (.word ((word left).sub (word right))) initialStore))
      "pending binary application did not cost exactly one remaining transition"

private def rejectedArguments (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ compiled.inputs.context.values.reverse))
    "rejection case accidentally satisfied the exact argument guard"
  assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone
    "mismatched actual arguments prepared"
  for initialStore in stores do
    for fuel in List.range 20 do
      assertTrue (runCase declaration arguments fuel initialStore).isNone
        "an argument-guard failure exposed a resumable checkpoint"

def frontendParsedResumptionTests : IO Unit := do
  let (bare, bareCompiled) ← accepted "function bare() { return; }" [] .unit .unit
  checkpoints bare bareCompiled [] .unit 1
  rejectedArguments bare bareCompiled [boolArg false]
  let (subtraction, subtractionCompiled) ← accepted
    "function subtraction(x: Word, y: Word) returns (Word) { return ((x)) - y; }"
    [.word, .word] (.binary .wordSub (.var 1) (.var 0)) .word
  for (left, right) in [(7, 9), (9, 7), (0, 1), (1, 0), (2 ^ 256 - 1, 7)] do
    checkpoints subtraction subtractionCompiled [wordArg left, wordArg right]
      (.word ((word left).sub (word right))) 5
    pendingSubtraction subtraction left right
  for initialStore in stores do
    let some (_, .outOfFuel genuine) := runCase subtraction [wordArg 9, wordArg 7] 4 initialStore
      | throw (IO.userError "continuation counterexample has no genuine checkpoint")
    let dropped : Core.State := ⟨genuine.control, [], genuine.store⟩
    assertTrue (decide (Core.runStateful 0 genuine = .outOfFuel genuine ∧
      Core.runStateful 0 dropped = .done (.word (word 7)) initialStore ∧
      Core.runStateful 1 genuine = .done (.word (word 2)) initialStore ∧
      Core.runStateful 1 dropped ≠ Core.runStateful 1 genuine))
      "dropping the pending frame failed to change both cost and result"
  let (negation, negationCompiled) ← accepted
    "function negation(c: Bool) returns (Bool) { return !c; }"
    [.bool] (.unary .boolNot (.var 0)) .bool
  for choice in [false, true] do
    checkpoints negation negationCompiled [boolArg choice] (.bool (!choice)) 3
    for initialStore in stores do
      let pending : Core.State := ⟨.ret (.bool choice), [.unaryApply .boolNot], initialStore⟩
      assertTrue (decide (runCase negation [boolArg choice] 2 initialStore =
        some (.bool, .outOfFuel pending))) "pending unary frame or actual Bool changed"
  for (symbol, expectedCore) in [("&&", Core.Expr.ifE (.var 0)
      (.unary .boolNot (.var 0)) (.bool false)),
      ("||", Core.Expr.ifE (.var 0) (.bool true) (.unary .boolNot (.var 0)))] do
    let (declaration, compiled) ← accepted
      ("function short(c: Bool) returns (Bool) { return c " ++ symbol ++ " !c; }")
      [.bool] expectedCore .bool
    for choice in [false, true] do
      let isAnd := symbol == "&&"
      checkpoints declaration compiled [boolArg choice] (.bool (!isAnd))
        (if choice == isAnd then 6 else 4)
  let (branch, branchCompiled) ← accepted
    "function branch(c: Bool, x: Word, y: Word) returns (Word) { return c ? x * y : x; }"
    [.bool, .word, .word] (.ifE (.var 2) (.binary .wordMul (.var 1) (.var 0)) (.var 1)) .word
  for choice in [false, true] do
    checkpoints branch branchCompiled [boolArg choice, wordArg 7, wordArg 9]
      (.word (word (if choice then 63 else 7))) (if choice then 8 else 4)
  for arguments in [[], [boolArg false, wordArg 7], [wordArg 7, boolArg true, wordArg 9],
      [boolArg true, wordArg 7, boolArg false], [boolArg true, wordArg 7, wordArg 9, wordArg 1]] do
    rejectedArguments branch branchCompiled arguments
  let (arithmetic, arithmeticCompiled) ← accepted
    "function arithmetic(x: Word, y: Word) returns (Word) { return x * y > y ? x - y : x; }"
    [.word, .word] (.ifE (.binary .wordGt (.binary .wordMul (.var 1) (.var 0)) (.var 0))
      (.binary .wordSub (.var 1) (.var 0)) (.var 1)) .word
  for (left, right) in [(0, 9), (7, 9), (2 ^ 256 - 1, 1)] do
    let selected := decide ((word left).mul (word right) > word right)
    checkpoints arithmetic arithmeticCompiled [wordArg left, wordArg right]
      (.word (if selected then (word left).sub (word right) else word left)) (if selected then 16 else 12)
  let identity : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  for (name, argument) in [("Fn", identity), ("Cell", cell)] do
    let (declaration, compiled) ← accepted
      (s!"function identity(x: {name}) returns ({name})" ++ " { return x; }")
      [argument.type] (.var 0) argument.type
    checkpoints declaration compiled [argument] argument.value 1
  for content in ["function empty() {}", "function multiple() { return; return; }",
      "function missing() returns (Word) { return missing; }",
      "function skipped(c: Bool) returns (Bool) { return c && missing; }",
      "function skipped(c: Bool, x: Word) returns (Bool) { return c || x / x; }",
      "function skipped(c: Bool, x: Word) returns (Word) { return c ? x : x / x; }",
      "function wrong(c: Bool, x: Word) returns (Word) { return c ? x : c; }"] do
    let some declaration ← parsed? content | throw (IO.userError "whole-rejection fixture failed parsing")
    assertTrue (compileRuntimeFunction? types owner declaration).isNone "invalid whole declaration compiled"
    for arguments in [[], [boolArg false], [boolArg true], [wordArg 7],
        [boolArg false, wordArg 7], [boolArg true, wordArg 7], [boolArg false, boolArg true]] do
      assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone
        "an invalid whole declaration prepared"
      for initialStore in stores do
        for fuel in List.range 20 do
          assertTrue (runCase declaration arguments fuel initialStore).isNone
            "whole rejection exposed a resumable checkpoint"
  for content in ["", "function incomplete()", "function f() { return;",
      "function f() { return; } trailing", "function f() { return; } /*"] do
    assertTrue (← parsed? content).isNone "incomplete input entered source checkpoint tests"

end Tests

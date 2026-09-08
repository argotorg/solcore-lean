import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionObservationProperties

/-! Independently parsed declarations share observations through their actual
ordered type contexts and exact Core trees, not their names or eventual values.
Every expected execution uses the supplied values and an unchanged Core machine. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed? (path content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, path⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{path}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{path}: parser invariant {reprStr error}")

private def leftOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ObservationLeft", by decide⟩], by decide⟩⟩, 1⟩
private def rightOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ObservationRight", by decide⟩], by decide⟩⟩, 9⟩
private def leftTypes : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def rightTypes : TypeNameTable :=
  [(["Truth"], .bool), (["Number"], .word), (["Proc"], .function .bool .bool), (["Ref"], .cell .word)]
private def word (value : Nat) := Core.Word.ofNatModulo value
private def wordArg (value : Nat) : TypedRuntimeArgument := ⟨.word, .word (word value), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def cellArg (address : Nat) : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word address, .cellRef⟩
private def closureArg : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
private def store : Core.Store := [.word (word 91), .bool false]

private structure CompiledCase where
  types : TypeNameTable
  owner : Resolved.DeclarationId
  declaration : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction

private def compileCase (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (path content : String) : IO CompiledCase := do
  let some declaration ← parsed? path content | throw (IO.userError s!"{content}: incomplete declaration")
  let some compiled := compileRuntimeFunction? types owner declaration
    | throw (IO.userError s!"{content}: compilation failed")
  assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some compiled.returnType))
    s!"{content}: actual compiled Core failed typing"
  return ⟨types, owner, declaration, compiled⟩

private def runCase (entry : CompiledCase) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (initialStore : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) :=
  runRuntimeFunction? entry.types entry.owner entry.declaration arguments fuel initialStore

private def pair (leftSource rightSource : String) (parameterTypes : List Core.Ty)
    (expectedCore : Core.Expr) (expectedType : Core.Ty) : IO (CompiledCase × CompiledCase) := do
  let left ← compileCase leftTypes leftOwner "observations-left.sol" leftSource
  let right ← compileCase rightTypes rightOwner "observations-right.sol" ("\n/* renamed */\n" ++ rightSource)
  assertTrue (decide (left.compiled.inputs.context.values = right.compiled.inputs.context.values ∧
    left.compiled.core = right.compiled.core)) "independent compilations do not meet observation premises"
  assertTrue (decide (left.compiled.returnType = right.compiled.returnType))
    "independently inferred return types differ"
  assertTrue (decide (left.compiled.core = expectedCore ∧ left.compiled.returnType = expectedType ∧
    left.compiled.inputs.context.values = parameterTypes.reverse)) "wrong expected exact compiled output"
  assertTrue (decide (left.owner ≠ right.owner ∧ left.declaration.span ≠ right.declaration.span ∧
    left.declaration.value.signature.name.value ≠ right.declaration.value.signature.name.value))
    "renaming/range fixtures accidentally coincide"
  unless parameterTypes.isEmpty do
    assertTrue (decide (left.compiled.inputs.names ≠ right.compiled.inputs.names ∧
      left.compiled.inputs.context.ids ≠ right.compiled.inputs.context.ids))
      "identity-bearing tables should not be equal"
  return (left, right)

private def compareFuels (left right : CompiledCase) (arguments : List TypedRuntimeArgument)
    (limit : Nat) (initialStore : Core.Store) : IO Unit := do
  for fuel in List.range limit do
    let expected := if arguments.map (·.type) = left.compiled.inputs.context.values.reverse then
      some (left.compiled.returnType, Core.runStateful fuel
        (Core.State.initial left.compiled.core (arguments.reverse.map (·.value)) initialStore))
      else none
    assertTrue (decide (runCase left arguments fuel initialStore = expected ∧
      runCase right arguments fuel initialStore = expected))
      s!"same compiled observation changed at fuel {fuel}"

private def completedPair (left right : CompiledCase) (arguments : List TypedRuntimeArgument)
    (value : Core.Value) (cost : Nat) (initialStore : Core.Store := store) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) = left.compiled.inputs.context.values.reverse))
    "completion fixture failed the argument guard"
  compareFuels left right arguments (cost + 3) initialStore
  for entry in [left, right] do
    assertTrue (decide (runCase entry arguments 0 initialStore = some (entry.compiled.returnType,
      .outOfFuel (Core.State.initial entry.compiled.core (arguments.reverse.map (·.value)) initialStore))))
      "wrong exact initial state"
    assertTrue (match runCase entry arguments (cost - 1) initialStore with
      | some (_, .outOfFuel _) => true | _ => false) "completed below the expected cost"
    for fuel in [cost, cost + 2] do
      assertTrue (decide (runCase entry arguments fuel initialStore =
        some (entry.compiled.returnType, .done value initialStore))) "wrong result or completion boundary"

private def rejectedPair (left right : CompiledCase) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ left.compiled.inputs.context.values.reverse))
    "rejection fixture passed the argument guard"
  compareFuels left right arguments 20 store

/-- All 29 ordered pairs are compiled twice with different spellings and
owners; unequal source-position values expose subtraction/order mistakes. -/
private def compositePairs : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let leftParameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    let rightParameters := String.intercalate ", " (indices.map fun index => s!"q{index}: Number")
    for first in indices do
      for second in indices do
        let leftVar := Core.Expr.var (arity - 1 - first)
        let rightVar := Core.Expr.var (arity - 1 - second)
        let core := Core.Expr.ifE (.binary .wordGt (.binary .wordMul leftVar rightVar) rightVar)
          (.binary .wordSub leftVar rightVar) leftVar
        let (left, right) ← pair
          (s!"function original({leftParameters}) returns (Word)"
            ++ " { return " ++ s!"p{first} * p{second} > p{second} ? p{first} - p{second} : p{first};" ++ " }")
          (s!"function renamed({rightParameters}) returns (Number)"
            ++ " { return " ++ s!"(((q{first}) * (q{second})) > (q{second})) ? ((q{first}) - (q{second})) : ((q{first}));" ++ " }")
          (List.replicate arity .word) core .word
        for nonzero in [false, true] do
          let valueAt := fun index => if nonzero then 7 + 3 * index else 0
          let arguments := indices.map fun index => wordArg (valueAt index)
          let leftWord := word (valueAt first)
          let rightWord := word (valueAt second)
          let selected := decide (leftWord.mul rightWord > rightWord)
          completedPair left right arguments
            (.word (if selected then leftWord.sub rightWord else leftWord)) (if selected then 16 else 12)
        for arguments in [[], [boolArg false], indices.map (fun _ => boolArg true),
            (indices.map fun index => wordArg index) ++ [wordArg 0]] do
          rejectedPair left right arguments

private def necessaryPremises : IO Unit := do
  let left ← compileCase leftTypes leftOwner "unused-left.sol"
    "function unused(a: Word, b: Bool) { return; }"
  let right ← compileCase rightTypes rightOwner "unused-right.sol"
    "function reordered(u: Truth, v: Number) { return; }"
  let fewer ← compileCase rightTypes rightOwner "fewer.sol" "function fewer(u: Number) { return; }"
  assertTrue (decide (left.compiled.core = right.compiled.core ∧ left.compiled.core = fewer.compiled.core ∧
    left.compiled.returnType = right.compiled.returnType ∧ left.compiled.returnType = fewer.compiled.returnType ∧
    left.compiled.inputs.context.values ≠ right.compiled.inputs.context.values ∧
    left.compiled.inputs.context.values ≠ fewer.compiled.inputs.context.values)) "missing context counterexample"
  for fuel in List.range 10 do
    assertTrue (decide (runCase right [wordArg 7, boolArg false] fuel store = none ∧
      runCase fewer [wordArg 7, boolArg false] fuel store = none ∧
      runCase left [wordArg 7] fuel store = none)) "wrong type order or arity was accepted"
  assertTrue (decide (runCase left [wordArg 7, boolArg false] 1 store = some (.unit, .done .unit store) ∧
    runCase fewer [wordArg 7] 1 store = some (.unit, .done .unit store) ∧
    runCase right [boolArg false, wordArg 7] 1 store = some (.unit, .done .unit store)))
    "same Core did not retain its distinct argument guard"
  let direct ← compileCase leftTypes leftOwner "direct.sol"
    "function direct(a: Word) returns (Word) { return a; }"
  let added ← compileCase rightTypes rightOwner "added.sol"
    "function added(u: Number) returns (Number) { return u + 0; }"
  assertTrue (decide (direct.compiled.inputs.context.values = added.compiled.inputs.context.values ∧
    direct.compiled.returnType = added.compiled.returnType ∧ direct.compiled.core ≠ added.compiled.core))
    "algebraic equality was mistaken for exact Core equality"
  assertTrue (decide (runCase direct [wordArg 7] 5 store = some (.word, .done (.word (word 7)) store) ∧
    runCase added [wordArg 7] 5 store = some (.word, .done (.word (word 7)) store) ∧
    runCase direct [wordArg 7] 1 store = some (.word, .done (.word (word 7)) store) ∧
    runCase added [wordArg 7] 4 store = some (.word, .outOfFuel
      ⟨.ret (.word .zero), [.binaryApply .wordAdd (.word (word 7))], store⟩) ∧
    runCase direct [wordArg 7] 0 store ≠ runCase added [wordArg 7] 0 store))
    "equal eventual values erased the exact cost or suspended-state difference"
  assertTrue (decide (([wordArg 7].map (·.type)) = [wordArg 9].map (·.type) ∧
    runCase direct [wordArg 7] 0 store ≠ runCase direct [wordArg 9] 0 store ∧
    runCase direct [wordArg 7] 1 store ≠ runCase direct [wordArg 9] 1 store))
    "equal argument types erased actual values"

def frontendParsedCompiledObservationTests : IO Unit := do
  compositePairs
  for index in List.range 3 do
    let leftName := ["a", "b", "c"][index]!
    let rightName := ["x", "y", "z"][index]!
    let (left, right) ← pair
      ("function select(a: Bool, b: Bool, c: Bool) returns (Bool) { return " ++ leftName ++ "; }")
      ("function choose(x: Truth, y: Truth, z: Truth) returns (Truth) { return ((" ++ rightName ++ ")); }")
      [.bool, .bool, .bool] (.var (2 - index)) .bool
    for a in [false, true] do
      for b in [false, true] do
        for c in [false, true] do
          completedPair left right [boolArg a, boolArg b, boolArg c] (.bool ([a, b, c][index]!)) 1
    for arguments in [[], [boolArg false], [boolArg true, wordArg 7, boolArg false]] do
      rejectedPair left right arguments
  let (shortLeft, shortRight) ← pair
    "function short(c: Bool) returns (Bool) { return c && !c; }"
    "function renamedShort(flag: Truth) returns (Truth) { return (flag) && (!(flag)); }"
    [.bool] (.ifE (.var 0) (.unary .boolNot (.var 0)) (.bool false)) .bool
  for choice in [false, true] do
    completedPair shortLeft shortRight [boolArg choice] (.bool false) (if choice then 6 else 4)
  assertTrue (decide (runCase shortLeft [boolArg false] 5 store = some (.bool, .done (.bool false) store)))
    "short-circuit false path did not finish"
  assertTrue (match runCase shortRight [boolArg true] 5 store with
    | some (.bool, .outOfFuel _) => true | _ => false) "different actual values erased selected-path cost"
  for (leftType, rightType, type, arguments) in
      [("Cell", "Ref", Core.Ty.cell .word, [cellArg 40, cellArg 91]),
       ("Fn", "Proc", Core.Ty.function .bool .bool, [closureArg])] do
    let (left, right) ← pair
      (s!"function identity(a: {leftType}) returns ({leftType})" ++ " { return a; }")
      (s!"function renamedIdentity(value: {rightType}) returns ({rightType})" ++ " { return (((value))); }")
      [type] (.var 0) type
    for argument in arguments do
      completedPair left right [argument] argument.value 1 []
    for wrong in [[], [boolArg false], arguments ++ arguments] do
      rejectedPair left right wrong
  necessaryPremises
  for content in ["", "function incomplete()", "function f() { return;", "function f() { return; } trailing"] do
    assertTrue (← parsed? "incomplete-observation.sol" content).isNone "incomplete input entered observation tests"

end Tests

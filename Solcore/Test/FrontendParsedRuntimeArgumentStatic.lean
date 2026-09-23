import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunction

/-! Equal typed-argument type lists preserve static preparation, including
rejection. Actual runtime values, suspended states, and costs need not agree. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-argument-static.sol"⟩, content }
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

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Static", by decide⟩], by decide⟩⟩, 0⟩
private def types : TypeNameTable :=
  [(["Bool"], .bool), (["Word"], .word), (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def seven : Core.Word := ⟨7, by decide⟩
private def nine : Core.Word := ⟨9, by decide⟩
private def store : Core.Store := [.word nine, .bool true]
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def wordArg (value : Core.Word) : TypedRuntimeArgument := ⟨.word, .word value, .word⟩
private def cellArg (location : Core.Location) : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word location, .cellRef⟩
private def identityClosure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
private def constantClosure : TypedRuntimeArgument :=
  ⟨.function .bool .bool, .closure .bool .bool (.bool false) [], .closure .nil .bool⟩
private def sameStatic : Option PreparedRuntimeFunction → Option PreparedRuntimeFunction → Bool
  | none, none => true
  | some left, some right =>
      decide (left.inputs.ids = right.inputs.ids) && decide (left.inputs.names = right.inputs.names) &&
      decide (left.inputs.context = right.inputs.context) && decide (left.core = right.core) &&
      decide (left.returnType = right.returnType)
  | _, _ => false

private def checkRun (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (prepared : PreparedRuntimeFunction) (value : Core.Value) (cost : Nat) (initialStore : Core.Store) : IO Unit := do
  assertTrue (decide (prepared.inputs.environment.values = arguments.reverse.map (·.value)))
    "new typed argument values did not populate the actual runtime rows"
  assertTrue (decide (runRuntimeFunction? types owner source arguments 0 initialStore =
    some (prepared.returnType, .outOfFuel
      (Core.State.initial prepared.core prepared.inputs.environment.values initialStore))))
    "wrong actual zero-fuel environment"
  for fuel in [0, cost - 1] do
    match runRuntimeFunction? types owner source arguments fuel initialStore with
    | some (type, .outOfFuel _) =>
        assertTrue (decide (type = prepared.returnType)) "exhaustion changed the static return type"
    | _ => throw (IO.userError "execution did not exhaust below the expected cost")
  for fuel in [cost, cost + 5] do
    assertTrue (decide (runRuntimeFunction? types owner source arguments fuel initialStore =
      some (prepared.returnType, .done value initialStore))) "wrong new argument result, cost, or store"

private def checkAccepted (content : String) (left right : List TypedRuntimeArgument)
    (core : Core.Expr) (type : Core.Ty) (leftValue rightValue : Core.Value)
    (leftCost rightCost : Nat) (initialStore : Core.Store := store) : IO Unit := do
  let source ← parsed content
  assertTrue (decide (left.map (·.type) = right.map (·.type))) "fixture must preserve ordered argument types"
  let first := prepareRuntimeFunction? types owner source left
  let second := prepareRuntimeFunction? types owner source right
  assertTrue (sameStatic first second) s!"{content}: static preparation changed"
  let some first := first | throw (IO.userError s!"{content}: first valid entry rejected")
  let some second := second | throw (IO.userError s!"{content}: second valid entry rejected")
  assertTrue (decide (first.core = core ∧ first.returnType = type)) s!"{content}: unexpected checked Core/type"
  assertTrue (decide (first.inputs.environment.values ≠ second.inputs.environment.values))
    s!"{content}: counterexample must change actual runtime values"
  assertTrue (decide (runRuntimeFunction? types owner source left 0 initialStore ≠
    runRuntimeFunction? types owner source right 0 initialStore))
    s!"{content}: distinct initial environments must remain distinguishable"
  checkRun source left first leftValue leftCost initialStore
  checkRun source right second rightValue rightCost initialStore

def frontendParsedRuntimeArgumentStaticTests : IO Unit := do
  let left := [boolArg false, wordArg seven, wordArg nine]
  let right := [boolArg true, wordArg seven, wordArg nine]
  let header := "function selected(c: Bool, t: Word, f: Word)"
  checkAccepted (header ++ " returns (Word) { return c ? ~t : f; }") left right
    (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word (.word nine) (.word seven.bitNot) 4 6
  checkAccepted "function logical(c: Bool) returns (Bool) { return c && !c; }"
    [boolArg false] [boolArg true] (.ifE (.var 0) (.unary .boolNot (.var 0)) (.bool false))
    .bool (.bool false) (.bool false) 4 6
  checkAccepted "function first(x: Bool, y: Bool) returns (Bool) { return x; }"
    [boolArg false, boolArg true] [boolArg true, boolArg false] (.var 1) .bool (.bool false) (.bool true) 1 1
  checkAccepted "function cell(x: Cell) returns (Cell) { return x; }"
    [cellArg 40] [cellArg 41] (.var 0) (.cell .word) (.cellRef .word 40) (.cellRef .word 41) 1 1 []
  checkAccepted "function unused(x: Cell) { return; }"
    [cellArg 40] [cellArg 41] .unit .unit .unit .unit 1 1 []
  checkAccepted "function closure(x: Fn) returns (Fn) { return x; }"
    [identityClosure] [constantClosure] (.var 0) (.function .bool .bool)
    identityClosure.value constantClosure.value 1 1
  for content in [
      header ++ " returns (Word) { return c ? t : missing; }",
      header ++ " returns (Word) { return c ? t : c; }",
      header ++ " returns (Bool) { return t; }", header ++ " returns () { return; }",
      "function arity(c: Bool) returns (Bool) { return c; }",
      "function duplicate(c: Bool, t: Word, c: Word) returns (Word) { return t; }",
      "function annotation(c: Word, t: Word, f: Word) returns (Word) { return t; }"] do
    let source ← parsed content
    let first := prepareRuntimeFunction? types owner source left
    let second := prepareRuntimeFunction? types owner source right
    assertTrue (sameStatic first second) s!"{content}: rejection not preserved"
    assertTrue (first.isNone && second.isNone) s!"{content}: unsupported whole contract accepted"
    for fuel in [0, 4, 6, 20] do
      assertTrue ((runRuntimeFunction? types owner source left fuel store).isNone &&
        (runRuntimeFunction? types owner source right fuel store).isNone)
        s!"{content}: values bypassed whole preparation"

end Tests

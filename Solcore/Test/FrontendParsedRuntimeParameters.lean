import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.Parser.Term
import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.LocalFunctionApplication

/-! Completely parsed parameter lists feed the actual input builder, and the
returned tables feed existing expression checking and execution. This does not
execute a function declaration or give meaning to its remaining signature. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-runtime-parameters.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Parameters", by decide⟩], by decide⟩⟩, 0⟩
private def types : TypeNameTable :=
  [(["Bool"], .bool), (["Boolean"], .bool), (["Word"], .word), (["Pkg", "Flag"], .bool)]
private def boolArgument (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def seven : Core.Word := ⟨7, by decide⟩
private def nine : Core.Word := ⟨9, by decide⟩
private def wordArgument (value : Core.Word) : TypedRuntimeArgument := ⟨.word, .word value, .word⟩
private def store : Core.Store := [.word nine, .bool false]

private def checkOrder (parameters : List Syntax.FunctionParameter)
    (arguments : List TypedRuntimeArgument) (inputs : LocalInputs) : IO Unit := do
  let names : List String ← parameters.mapM fun parameter => do
    let .typed none name _ := parameter.value
      | throw (IO.userError "accepted a non-runtime parameter")
    pure name.value
  assertTrue (decide (names.length = arguments.length)) "accepted mismatched arity"
  let expected : List (String × Resolved.LocalId × Core.Ty × Core.Value) :=
    (names.zip arguments).zipIdx.map fun (entry, index) =>
    (entry.1, (⟨owner, index⟩ : Resolved.LocalId), entry.2.type, entry.2.value)
  let actual : List (String × Resolved.LocalId × Core.Ty × Core.Value) := inputs.bindings.map fun binding =>
    (binding.name, binding.id, binding.type, binding.value)
  assertTrue (decide (actual = expected.reverse))
    "parameter/argument pairing, generated identity, or reverse storage order changed"

private def prepare (content : String) (arguments : List TypedRuntimeArgument) : IO LocalInputs := do
  let some parameters ← parsed? Syntax.Parser.functionParameters content
    | throw (IO.userError s!"{content}: expected a complete parameter list")
  let some inputs := bindRuntimeParameters? types owner parameters.elements arguments
    | throw (IO.userError s!"{content}: valid runtime arguments did not bind")
  checkOrder parameters.elements arguments inputs
  return inputs

private def checkRun (inputs : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let some source ← parsed? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete local expression")
  let checked := inputs.check? source
  assertTrue (decide (checked = some (expectedCore, type)))
    s!"{content}: wrong checked type or parameter position"
  let some (actualCore, _) := checked
    | throw (IO.userError s!"{content}: checking unexpectedly failed")
  assertTrue (decide (inputs.run? 0 source store =
    some (type, .outOfFuel (Core.State.initial actualCore inputs.environment.values store))))
    s!"{content}: wrong actual initial environment or zero-fuel result"
  for fuel in [0, cost - 1] do
    match inputs.run? fuel source store with
    | some (actualType, .outOfFuel _) =>
        assertTrue (decide (actualType = type)) s!"{content}: exhaustion changed the type"
    | _ => throw (IO.userError s!"{content}: execution did not exhaust below its exact cost")
  for fuel in [cost, cost + 5] do
    assertTrue (decide (inputs.run? fuel source store = some (type, .done value store)))
      s!"{content}: wrong supplied argument, completion boundary, or final store"

def frontendParsedRuntimeParameterTests : IO Unit := do
  let empty ← prepare "()" []
  assertTrue empty.bindings.isEmpty "empty parameters introduced a binding"
  for left in [false, true] do
    for right in [false, true] do
      let inputs ← prepare "(left: Bool, right: Boolean,)" [boolArgument left, boolArgument right]
      checkRun inputs "left" (.var 1) .bool (.bool left) 1
      checkRun inputs "right" (.var 0) .bool (.bool right) 1
      checkRun inputs "left && right" (.ifE (.var 1) (.var 0) (.bool false))
        .bool (.bool (left && right)) 4
      checkRun inputs "left || right" (.ifE (.var 1) (.bool true) (.var 0))
        .bool (.bool (left || right)) 4
  for choice in [false, true] do
    let arguments := [boolArgument choice, wordArgument seven, wordArgument nine]
    let inputs ← prepare "(c: Pkg /* qualified */ . Flag, t: Word, f: Word)" arguments
    checkRun inputs "c ? t : f" (.ifE (.var 2) (.var 1) (.var 0))
      .word (.word (if choice then seven else nine)) 4
    checkRun inputs "t ^ f" (.binary .wordXor (.var 1) (.var 0))
      .word (.word (seven.bitXor nine)) 5
    let some missing ← parsed? Syntax.Parser.expression "c ? t : missing"
      | throw (IO.userError "missing branch expression did not parse")
    for fuel in [0, 4, 20] do
      assertTrue (inputs.run? fuel missing store).isNone
        "parameter input preparation bypassed whole-expression checking"
  let some signature ← parsed? (Syntax.Parser.functionSignature .module)
      "function choose(c: Bool, t: Word, f: Word) returns (Word)"
    | throw (IO.userError "complete signature parsing failed")
  let arguments := [boolArgument true, wordArgument seven, wordArgument nine]
  let some signatureInputs := bindRuntimeParameters? types owner signature.parameters.elements arguments
    | throw (IO.userError "actual signature parameters failed to bind")
  checkOrder signature.parameters.elements arguments signatureInputs
  checkRun signatureInputs "c ? t : f" (.ifE (.var 2) (.var 1) (.var 0)) .word (.word seven) 4
  for (content, arguments) in [
      ("(x: Bool)", []), ("()", [boolArgument false]),
      ("(x: Bool)", [boolArgument false, boolArgument true]),
      ("(x: Bool, y: Bool)", [boolArgument false]),
      ("(x: Bool, x: Bool)", [boolArgument false, boolArgument true]),
      ("(x: Bool, y: Bool, x: Bool)", [boolArgument false, boolArgument true, boolArgument false]),
      ("(x: Word)", [boolArgument true]), ("(x: Bool)", [wordArgument seven]),
      ("(x: Unknown)", [boolArgument true]), ("(x: Bool<Word>)", [boolArgument true]),
      ("(x: @Bool)", [boolArgument true]), ("(comptime x: Bool)", [boolArgument true])] do
    let some parameters ← parsed? Syntax.Parser.functionParameters content
      | throw (IO.userError s!"{content}: adapter rejection case should parse")
    assertTrue (bindRuntimeParameters? types owner parameters.elements arguments).isNone
      s!"{content}: unsupported or mismatched arguments were accepted"
  for content in ["", "(x)", "(x:)", "(x: Bool", "(x: Bool) trailing", "(x: comptime<Bool>)"] do
    assertTrue (← parsed? Syntax.Parser.functionParameters content).isNone
      s!"{content}: accepted malformed, diagnosed, or only partially consumed parameters"

end Tests

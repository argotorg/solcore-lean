import Solcore.Syntax.Parser.Function
import Solcore.Frontend.ReturnBody
import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.LocalInputsExecution

/-! Actual singleton return bodies retain the checked expression's Core and
fuel behavior. Parsed declarations supply parameters and body separately; this
test does not interpret a signature contract or invoke a source function. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-return-body.sol"⟩, content }
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

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ReturnBody", by decide⟩], by decide⟩⟩, 0⟩
private def seven : Core.Word := ⟨7, by decide⟩
private def nine : Core.Word := ⟨9, by decide⟩
private def store : Core.Store := [.word nine, .bool true]
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def arguments (choice : Bool) : List TypedRuntimeArgument :=
  [⟨.bool, .bool choice, .bool⟩, ⟨.word, .word seven, .word⟩, ⟨.word, .word nine, .word⟩]

private def checkBody (inputs : LocalInputs) (body : Syntax.Block) (label : String)
    (expectedCore : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let checked := inputs.checkReturnBody? body
  assertTrue (decide (checked = some (expectedCore, type))) s!"{label}: wrong body Core or type"
  let some (actualCore, _) := checked
    | throw (IO.userError s!"{label}: body checking failed")
  assertTrue (decide (inputs.runReturnBody? 0 body store =
    some (type, .outOfFuel (Core.State.initial actualCore inputs.environment.values store))))
    s!"{label}: wrong zero-fuel initial state"
  for fuel in [0, cost - 1] do
    match inputs.runReturnBody? fuel body store with
    | some (actualType, .outOfFuel _) =>
        assertTrue (decide (actualType = type)) s!"{label}: exhaustion changed the type"
    | _ => throw (IO.userError s!"{label}: body did not exhaust below its cost")
  for fuel in [cost, cost + 5] do
    assertTrue (decide (inputs.runReturnBody? fuel body store = some (type, .done value store)))
      s!"{label}: wrong returned value, preserved store, or completion threshold"
  match body.value with
  | [⟨_, .returnStmt (some expression)⟩] =>
      assertTrue (decide (checked = inputs.check? expression))
        s!"{label}: return changed the exact expression Core"
      for fuel in [0, 1, 3, 4, 5, 6, 8, cost, cost + 5] do
        assertTrue (decide (inputs.runReturnBody? fuel body store = inputs.run? fuel expression store))
          s!"{label}: return introduced execution overhead or altered a suspended state"
  | [⟨_, .returnStmt none⟩] => pure ()
  | _ => throw (IO.userError s!"{label}: accepted a non-singleton return body")
  let invalidSpan : Syntax.SourceSpan := ⟨⟨.main, "unrelated.sol"⟩, 900, 2⟩
  let moved : Syntax.Block := ⟨invalidSpan, body.value.map fun statement =>
    { statement with span := invalidSpan }⟩
  assertTrue (decide (inputs.checkReturnBody? moved = checked))
    s!"{label}: block or statement range changed body checking"

private def checkText (inputs : LocalInputs) (content : String) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let some body ← parsed? (Syntax.Parser.block .allow) content
    | throw (IO.userError s!"{content}: expected a complete body")
  checkBody inputs body content core type value cost

def frontendParsedReturnBodyTests : IO Unit := do
  checkText LocalInputs.empty "{ return; }" .unit .unit .unit 1
  checkText LocalInputs.empty " /* lead */ { /* inside */ return /* unit */ ; } " .unit .unit .unit 1
  checkText LocalInputs.empty "{ return ((0007)); }" (.word seven) .word (.word seven) 1
  checkText LocalInputs.empty "{ return ~7; }" (.unary .wordNot (.word seven)) .word (.word seven.bitNot) 3
  let some mismatched ← parsed? (Syntax.Parser.functionDecl .module)
      "function mismatch() returns (Bool) { return 7; }"
    | throw (IO.userError "signature mismatch example should parse")
  let some returns := mismatched.value.signature.returnsClause
    | throw (IO.userError "explicit return annotation disappeared")
  let [annotation] := returns.types.elements
    | throw (IO.userError "expected one declared return type")
  assertTrue (decide (interpretTypeName? types annotation = some .bool))
    "mismatch example must declare Bool independently of its Word body"
  checkBody LocalInputs.empty mismatched.value.body "body type is not signature checking"
    (.word seven) .word (.word seven) 1
  for choice in [false, true] do
    let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
        "function choose(c: Bool, t: Word, f: Word) returns (Word) { return c ? t : f; }"
      | throw (IO.userError "complete declaration parsing failed")
    let some inputs := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements (arguments choice)
      | throw (IO.userError "actual declaration parameters failed to bind")
    checkBody inputs declaration.value.body "actual declaration body"
      (.ifE (.var 2) (.var 1) (.var 0)) .word (.word (if choice then seven else nine)) 4
    checkText inputs "{ return; }" .unit .unit .unit 1
    checkText inputs "{ return c ? ~t : f; }"
      (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word
      (.word (if choice then seven.bitNot else nine)) (if choice then 6 else 4)
    checkText inputs "{ return c && !c; }"
      (.ifE (.var 2) (.unary .boolNot (.var 2)) (.bool false)) .bool (.bool false)
      (if choice then 6 else 4)
    checkText inputs "{ return t ^ f; }" (.binary .wordXor (.var 1) (.var 0)) .word (.word (seven.bitXor nine)) 5
    checkText inputs "{ return t + f; }" (.binary .wordAdd (.var 1) (.var 0)) .word (.word (seven.add nine)) 5
    checkText inputs "{ return t - f; }" (.binary .wordSub (.var 1) (.var 0)) .word (.word (seven.sub nine)) 5
    checkText inputs "{ return t * f; }" (.binary .wordMul (.var 1) (.var 0)) .word (.word (seven.mul nine)) 5
    for content in ["{}", "{ t; }", "{ t }", "{ { return t; } }", "{ return t; return f; }",
        "{ t; return f; }", "{ return t; missing; }", "{ let x = t; return x; }",
        "{ return c ? t : missing; }", "{ return c ? t : c; }", "{ return t(c); }",
        "{ return \"7\"; }"] do
      let some body ← parsed? (Syntax.Parser.block .allow) content
        | throw (IO.userError s!"{content}: unsupported body should still parse")
      assertTrue (inputs.checkReturnBody? body).isNone s!"{content}: unsupported body or expression checked"
      for fuel in [0, 4, 20] do
        assertTrue (inputs.runReturnBody? fuel body store).isNone
          s!"{content}: dropped written syntax or bypassed body checking"
  for content in ["", "return;", "{ return;", "{ return 7 }", "{ return; } trailing"] do
    assertTrue (← parsed? (Syntax.Parser.block .allow) content).isNone
      s!"{content}: accepted malformed, diagnosed, or incompletely consumed body text"

end Tests

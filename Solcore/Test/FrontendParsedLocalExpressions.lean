import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalInputsExecution
import Solcore.Resolved.Eval
import Solcore.Core.Machine

/-! Executable source-text regressions through the existing canonical lexer,
expression parser, explicit-table frontend checker, and Core machine. This is
test wiring, not a new public source parser or an Oracle endpoint. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def localId (index : Nat) : Resolved.LocalId :=
  ⟨⟨⟨.main, ⟨[⟨"Parsed", by decide⟩], by decide⟩⟩, 0⟩, index⟩
private def names : LocalNameTable :=
  [("c", localId 0), ("t", localId 1), ("e", localId 2), ("d", localId 3),
    ("n", localId 4), ("true", localId 5), ("false", localId 6)]
private def context : Resolved.Context :=
  [(localId 99, .unit), (localId 0, .bool), (localId 1, .word), (localId 2, .word),
    (localId 3, .bool), (localId 4, .word), (localId 5, .bool), (localId 6, .bool)]
private def word (value : Nat) : Core.Value := .word (Core.Word.ofNatModulo value)
private def environment (condition nestedCondition : Bool) : Resolved.Environment :=
  [(localId 99, .unit), (localId 0, .bool condition), (localId 1, word 11), (localId 2, word 22),
    (localId 3, .bool nestedCondition), (localId 4, word 0),
    (localId 5, .bool false), (localId 6, .bool true)]
private def store : Core.Store := [word 91, .bool false]

private def parsedExpression (content : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-local.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  assertTrue lexed.diagnostics.isEmpty s!"{content}: unexpected lexical diagnostic"
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      assertTrue next.atEnd s!"{content}: unconsumed source tokens"
      assertTrue next.diagnostics.isEmpty s!"{content}: unexpected parse diagnostic"
      pure source
  | .reject failure _ => throw (IO.userError s!"{content}: rejected expression {reprStr failure}")
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def checkRun (content : String) (expectedCore : Core.Expr)
    (condition nestedCondition : Bool) (expectedValue : Core.Value) (required : Nat) : IO Unit := do
  let source ← parsedExpression content
  let checked := elaborateLocalExpression? names context source
  assertTrue (decide (checked = some (expectedCore, .word))) s!"{content}: wrong checked Core expression"
  let some (actualCore, _) := checked
    | throw (IO.userError s!"{content}: no checked expression")
  let initial := Core.State.initial actualCore
    (Resolved.LocalScope.values (environment condition nestedCondition)) store
  assertTrue (decide (Core.runStateful required initial = .done expectedValue store))
    s!"{content}: wrong value or store at sufficient fuel"
  assertTrue (decide (Core.runStateful (required + 5) initial = .done expectedValue store))
    s!"{content}: larger fuel changed result"
  assertTrue (match Core.runStateful (required - 1) initial with
    | .outOfFuel _ => true
    | _ => false) s!"{content}: expected exhaustion just below exact transition count"

private def checkUnsupported (content : String) : IO Unit := do
  let source ← parsedExpression content
  assertTrue (decide (resolveLocalExpression? names source = none))
    s!"{content}: unsupported or unmapped source unexpectedly resolved"
  assertTrue (decide (elaborateLocalExpression? names context source = none))
    s!"{content}: unsupported or unmapped source unexpectedly checked"

private def checkIllTyped (content : String) : IO Unit := do
  let source ← parsedExpression content
  assertTrue (resolveLocalExpression? names source).isSome s!"{content}: expected name resolution"
  assertTrue (decide (elaborateLocalExpression? names context source = none))
    s!"{content}: ill-typed conditional unexpectedly checked"

private def bundledInputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh (localId 0).owner "e" .word (word 22) .word).bindFresh
    (localId 0).owner "t" .word (word 11) .word).bindFresh
      (localId 0).owner "c" .bool (.bool choice) .bool

private def checkBundledRun : IO Unit := do
  let source ← parsedExpression "c ? t : e"
  let unsupported ← parsedExpression "c ? t : missing"
  for choice in [false, true] do
    let inputs := bundledInputs choice
    let expectedCore : Core.Expr := .ifE (.var 0) (.var 1) (.var 2)
    let expectedValue := if choice then word 11 else word 22
    assertTrue (decide (inputs.check? source = some (expectedCore, .word)))
      "bundled source check returned the wrong Core or type"
    assertTrue (decide (inputs.run? 4 source store = some (.word, .done expectedValue store)))
      "bundled source execution changed the checked type, selected value, or store"
    assertTrue (decide (inputs.run? 0 source store = some (.word,
      .outOfFuel (Core.State.initial expectedCore
        (Resolved.LocalScope.values inputs.environment) store))))
      "bundled source fuel exhaustion was lost or confused with failed checking"
    assertTrue (decide (inputs.run? 4 unsupported store = none))
      "bundled source execution skipped whole-expression checking"

def frontendParsedLocalExpressionTests : IO Unit := do
  let simple : Core.Expr := .ifE (.var 1) (.var 2) (.var 3)
  checkRun "c ? t : e" simple true false (word 11) 4
  checkRun "c ? t : e" simple false true (word 22) 4
  checkRun "(c) ? ((t)) : e" simple true false (word 11) 4
  checkRun " /* before */ c ? /* branch */ t : e " simple false false (word 22) 4
  let rightNested : Core.Expr := .ifE (.var 1) (.var 2) (.ifE (.var 4) (.var 3) (.var 5))
  checkRun "c ? t : d ? e : n" rightNested true false (word 11) 4
  checkRun "c ? t : d ? e : n" rightNested false true (word 22) 7
  checkRun "c ? t : d ? e : n" rightNested false false (word 0) 7
  checkRun "c ? d ? t : e : n"
    (.ifE (.var 1) (.ifE (.var 4) (.var 2) (.var 3)) (.var 5)) true false (word 22) 7
  checkRun "(c ? d : false) ? t : e"
    (.ifE (.ifE (.var 1) (.var 4) (.var 7)) (.var 2) (.var 3)) false false (word 11) 7
  checkRun "true ? t : e" (.ifE (.var 6) (.var 2) (.var 3)) true true (word 22) 4
  checkRun "false ? t : e" (.ifE (.var 7) (.var 2) (.var 3)) false false (word 11) 4
  checkUnsupported "c ? t : missing"
  checkUnsupported "c ? t : 7"
  checkUnsupported "t + e"
  checkIllTyped "n ? t : e"
  checkIllTyped "c ? t : d"
  checkIllTyped "c ? t : (d ? e : c)"
  let rejectsTrailingTokens ← try
    let _ ← parsedExpression "t e"
    pure false
  catch error => pure (error.toString == "t e: unconsumed source tokens")
  assertTrue rejectsTrailingTokens "source-text test helper accepted an incomplete expression parse"
  checkBundledRun

end Tests

import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalInputsExecution
import Solcore.Frontend.LocalInputsRenaming

/-! Actual parsed-source execution for strict binary Word operators. Full AST
checking is mandatory, and expected Core shapes retain precedence and order. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedBitwise", by decide⟩], by decide⟩⟩, 0⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literalCore (value : Nat) : Core.Expr := .word (word value)
private def store : Core.Store := [.word (word 91), .bool true]
private def inputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "a" .word (.word (word 170)) .word).bindFresh
    owner "b" .word (.word (word 204)) .word).bindFresh owner "c" .bool (.bool choice) .bool

private def relabel (id : Resolved.LocalId) : Resolved.LocalId :=
  { id with binderIndex := id.binderIndex + 23 }
private theorem relabel_injective : Function.Injective relabel := by
  intro left right same
  cases left with
  | mk leftOwner leftIndex =>
      cases right with
      | mk rightOwner rightIndex =>
          have owners := congrArg Resolved.LocalId.owner same
          have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
          cases owners; cases indices; rfl

private def parsedExpression (content : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-bitwise.sol"⟩, content }
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

private def checkRun (supplied : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (expected : Core.Word) (required : Nat) : IO Unit := do
  let source ← parsedExpression content
  let checked := supplied.check? source
  assertTrue (decide (checked = some (expectedCore, .word))) s!"{content}: wrong checked Core or type"
  let some (actualCore, _) := checked
    | throw (IO.userError s!"{content}: expression did not check")
  let initial := Core.State.initial actualCore (Resolved.LocalScope.values supplied.environment) store
  for fuel in [required, required + 6] do
    assertTrue (decide (Core.runStateful fuel initial = .done (.word expected) store))
      s!"{content}: wrong checked value or final store"
  assertTrue (match Core.runStateful (required - 1) initial with
    | .outOfFuel _ => true | _ => false) s!"{content}: wrong exact fuel boundary"
  assertTrue (decide (supplied.run? required source store = some (.word, .done (.word expected) store)))
    s!"{content}: bundled execution diverged from checked Core"

private def checkRejected (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← parsedExpression content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves)
    s!"{content}: wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: expression unexpectedly checked"
  for fuel in [0, 30] do
    assertTrue (supplied.run? fuel source store).isNone s!"{content}: failed checking reached execution"

private def operations : List (String × Core.BinaryOp × (Core.Word → Core.Word → Core.Word) × Nat) :=
  [("&", .wordAnd, Core.Word.bitAnd, 136), ("|", .wordOr, Core.Word.bitOr, 238),
    ("^", .wordXor, Core.Word.bitXor, 102)]

/-- Input insertion preserves completed observations and exhaustion presence,
not the suspended states themselves. All other result fields remain exact. -/
private def sameObservation (left right : Option (Core.Ty × Core.StatefulRunResult)) : Bool :=
  match left, right with
  | some (leftType, .outOfFuel _), some (rightType, .outOfFuel _) => decide (leftType = rightType)
  | _, _ => decide (left = right)

private def checkInputInvariance : IO Unit := do
  for choice in [false, true] do
    let supplied := inputs choice
    let extended := supplied.bindFresh owner "extra" .unit .unit .unit
    let renamed := extended.mapIds relabel relabel_injective
    for content in ["7", "a & b", "a | b", "a ^ b", "~a & (b | 0x0F)",
        "c ? a & b : a ^ b", "c && !c", "c || !c", "c ? 7 : missing",
        "0 & missing", "c | b", "0 ^ \"7\""] do
      let source ← parsedExpression content
      assertTrue (decide (extended.check? source =
        (supplied.check? source).map (fun result => (result.1.weakenAt 0, result.2))))
        s!"{content}: unused input changed Core beyond positional weakening"
      assertTrue (decide (extended.run? 30 source store = supplied.run? 30 source store))
        s!"{content}: unused input changed a completed result or failed checking"
      assertTrue (decide (renamed.check? source = extended.check? source))
        s!"{content}: ID relabeling changed checked Core or type"
      for fuel in [0, 1, 3, 4, 5, 6, 7, 8, 13] do
        assertTrue (sameObservation (extended.run? fuel source store) (supplied.run? fuel source store))
          s!"{content}: unused input changed a same-fuel completion or exhaustion observation"
        assertTrue (decide (renamed.run? fuel source store = extended.run? fuel source store))
          s!"{content}: ID relabeling changed the result or exact suspended state"
    let constant ← parsedExpression "7"
    assertTrue (decide (extended.run? 0 constant store ≠ supplied.run? 0 constant store))
      "input insertion should retain distinct initial environments when exhausted"
    assertTrue (sameObservation (extended.run? 0 constant store) (supplied.run? 0 constant store))
      "distinct suspended states must still have equal exhaustion observations"

def frontendParsedWordBitwiseTests : IO Unit := do
  let supplied := inputs true
  for (symbol, operator, operation, maskResult) in operations do
    checkRun supplied s!"0xAA {symbol} 0xCC"
      (.binary operator (literalCore 170) (literalCore 204)) (word maskResult) 5
    checkRun supplied s!"a {symbol} b" (.binary operator (.var 2) (.var 1)) (word maskResult) 5
    checkRun supplied s!"a {symbol} 0" (.binary operator (.var 2) (literalCore 0))
      (operation (word 170) Core.Word.zero) 5
    checkRun supplied s!"a {symbol} a" (.binary operator (.var 2) (.var 2))
      (operation (word 170) (word 170)) 5
    checkRun supplied s!"1 {symbol} 2 {symbol} 4"
      (.binary operator (.binary operator (literalCore 1) (literalCore 2)) (literalCore 4))
      (operation (operation (word 1) (word 2)) (word 4)) 9
    checkRejected supplied s!"c {symbol} a" true
    checkRejected supplied s!"a {symbol} c" true
    checkRejected supplied s!"0 {symbol} missing" false
    checkRejected supplied s!"0 {symbol} \"7\"" false
    checkRejected supplied s!"0 {symbol} {Core.wordModulus}" false
    checkRejected supplied s!"(c && a) {symbol} b" true
  checkRun supplied "1 | 2 ^ 3 & 4"
    (.binary .wordOr (literalCore 1)
      (.binary .wordXor (literalCore 2) (.binary .wordAnd (literalCore 3) (literalCore 4)))) (word 3) 13
  checkRun supplied "1 | 2 & 4"
    (.binary .wordOr (literalCore 1) (.binary .wordAnd (literalCore 2) (literalCore 4))) (word 1) 9
  checkRun supplied "(1 | 2) & 4"
    (.binary .wordAnd (.binary .wordOr (literalCore 1) (literalCore 2)) (literalCore 4)) (word 0) 9
  checkRun supplied " /* mask */ ~0xAA & /* right */ 0xCC"
    (.binary .wordAnd (.unary .wordNot (literalCore 170)) (literalCore 204)) (word 68) 7
  checkRun supplied "~(0xAA & 0xCC)"
    (.unary .wordNot (.binary .wordAnd (literalCore 170) (literalCore 204))) (word 136).bitNot 7
  for choice in [false, true] do
    checkRun (inputs choice) "c ? 0xAA & 0xCC : 0xAA | 0xCC"
      (.ifE (.var 0) (.binary .wordAnd (literalCore 170) (literalCore 204))
        (.binary .wordOr (literalCore 170) (literalCore 204))) (word (if choice then 136 else 238)) 8
  checkRejected supplied "(a & b) ? 1 : 0" true
  checkRejected supplied "c && (a & b)" true
  checkRejected supplied "a + b" false
  let rejectsTrailing ← try
    let _ ← parsedExpression "a & b 7"
    pure false
  catch error => pure (error.toString == "a & b 7: unconsumed source tokens")
  assertTrue rejectsTrailing "bitwise source helper accepted only a valid prefix"
  checkInputInvariance

end Tests

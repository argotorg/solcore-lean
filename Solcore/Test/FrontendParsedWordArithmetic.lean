import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionPreparationFactorization
import Solcore.Frontend.LocalInputsExecution

/-! Fully parsed subtraction and multiplication retain ordered syntax/Core,
modular results, strict checking, and exact pending-frame fuel boundaries. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedArithmetic", by decide⟩], by decide⟩⟩, 5⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)
private def store : Core.Store := [.word (word 91), .bool false]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def inputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "l" .word (.word (word 7)) .word).bindFresh
    owner "r" .word (.word (word 9)) .word).bindFresh owner "c" .bool (.bool choice) .bool

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) :
    IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-arithmetic.sol"⟩, content }
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

private def expression (content : String) : IO Syntax.Expr := do
  let some source ← parsed? Syntax.Parser.expression content
    | throw (IO.userError s!"{content}: expected a complete diagnostic-free expression")
  return source

private def checkRun (supplied : LocalInputs) (content : String) (expectedCore : Core.Expr)
    (expected : Core.Word) (cost : Nat) : IO Unit := do
  let source ← expression content
  let checked := supplied.check? source
  assertTrue (decide (checked = some (expectedCore, .word))) s!"{content}: wrong exact Core/type"
  let some (actualCore, _) := checked | throw (IO.userError "missing checked Core")
  let initial := Core.State.initial actualCore supplied.environment.values store
  for fuel in [0, cost - 1, cost, cost + 5] do
    assertTrue (decide (supplied.run? fuel source store =
      some (.word, Core.runStateful fuel initial))) s!"{content}: bundled machine mismatch"
  assertTrue (match Core.runStateful (cost - 1) initial with
    | .outOfFuel _ => true | _ => false) s!"{content}: completed below exact cost"
  for fuel in [cost, cost + 5] do
    assertTrue (decide (Core.runStateful fuel initial = .done (.word expected) store))
      s!"{content}: wrong value, store, or completion threshold"

private def checkRejected (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves)
    s!"{content}: wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid expression checked"
  for fuel in [0, 4, 30] do
    assertTrue (supplied.run? fuel source store).isNone s!"{content}: checking was bypassed"
  let declarationText := "function rejected(l: Word, r: Word, c: Bool) returns (Word) { return "
    ++ content ++ "; }"
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module) declarationText
    | throw (IO.userError s!"{content}: wrapped declaration did not parse")
  assertTrue (compileRuntimeFunction? types owner declaration).isNone
    s!"{content}: invalid whole body compiled"

private def checkShapes : IO Unit := do
  let leftAssociated ← expression "8 - 3 - 2"
  assertTrue (match leftAssociated.value with
    | .binary ⟨_, .binary _ ⟨_, .subtract⟩ _⟩ ⟨_, .subtract⟩ _ => true
    | _ => false) "subtraction parser changed left associativity"
  let rightGrouped ← expression "8 - (3 - 2)"
  assertTrue (match rightGrouped.value with
    | .binary _ ⟨_, .subtract⟩ ⟨_, .group ⟨_, .binary _ ⟨_, .subtract⟩ _⟩⟩ => true
    | _ => false) "subtraction parser lost right grouping"
  let multiplyAssociated ← expression "2 * 3 * 4"
  assertTrue (match multiplyAssociated.value with
    | .binary ⟨_, .binary _ ⟨_, .multiply⟩ _⟩ ⟨_, .multiply⟩ _ => true
    | _ => false) "multiplication parser changed left associativity"
  let mixed ← expression "8 - 2 * 3 | 1"
  assertTrue (match mixed.value with
    | .binary ⟨_, .binary _ ⟨_, .subtract⟩ ⟨_, .binary _ ⟨_, .multiply⟩ _⟩⟩ ⟨_, .bitOr⟩ _ => true
    | _ => false) "arithmetic/bitwise parser precedence changed"

/-- Check each tested source pair, not just endpoint parameters. The pending
frame distinguishes left and right even when multiplication results commute. -/
private def checkParameterPositions (symbol : String) (sourceOperator : Syntax.BinaryOp)
    (operator : Core.BinaryOp) (operation : Core.Word → Core.Word → Core.Word) : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function arithmetic_{arity}_{left}_{right}({parameters}) returns (Word)"
          ++ " { return " ++ s!"p{left} {symbol} p{right};" ++ " }"
        let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
          | throw (IO.userError s!"{content}: expected complete declaration")
        assertTrue (match declaration.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨_, op⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              op == sourceOperator && l.value == s!"p{left}" && r.value == s!"p{right}"
          | _ => false) s!"{content}: source operator or parameter references changed"
        let some compiled := compileRuntimeFunction? types owner declaration
          | throw (IO.userError s!"{content}: value-free compilation failed")
        let expectedCore := Core.Expr.binary operator (.var (arity - 1 - left)) (.var (arity - 1 - right))
        assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = .word))
          s!"{content}: compilation changed exact open Core/type"
        assertTrue (decide (compiled.inputs.context.values = List.replicate arity Core.Ty.word))
          s!"{content}: wrong static context"
        assertTrue (decide (compiled.inputs.names = (indices.map fun index =>
          (s!"p{index}", (⟨owner, index⟩ : Resolved.LocalId))).reverse)) s!"{content}: wrong source IDs/names"
        assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some .word))
          s!"{content}: open Core failed typing in its parameter context"
        let arguments : List TypedRuntimeArgument := indices.map fun index =>
          ⟨.word, .word (word (10 * index + 1)), .word⟩
        let some prepared := prepareRuntimeFunction? types owner declaration arguments
          | throw (IO.userError s!"{content}: matching arguments failed preparation")
        assertTrue (decide (prepared.core = compiled.core ∧ prepared.returnType = compiled.returnType ∧
          prepared.inputs.names = compiled.inputs.names ∧ prepared.inputs.context = compiled.inputs.context))
          s!"{content}: runtime preparation changed its compiled projection"
        let values := arguments.reverse.map (·.value)
        assertTrue (decide (prepared.inputs.environment.values = values)) s!"{content}: argument values were reordered"
        let initial := Core.State.initial compiled.core values store
        for fuel in List.range 8 do
          assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel store =
            some (.word, Core.runStateful fuel initial))) s!"{content}: same-fuel full result differs"
          assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel store =
            prepared.inputs.runReturnBody? fuel declaration.value.body store))
            s!"{content}: entry changed actual body execution"
        assertTrue (decide (runRuntimeFunction? types owner declaration arguments 0 store =
          some (.word, .outOfFuel initial))) s!"{content}: wrong exact zero-fuel state"
        let leftValue := word (10 * left + 1)
        let rightValue := word (10 * right + 1)
        let pending : Core.State := ⟨.ret (.word rightValue), [.binaryApply operator (.word leftValue)], store⟩
        assertTrue (decide (runRuntimeFunction? types owner declaration arguments 4 store =
          some (.word, .outOfFuel pending))) s!"{content}: wrong left/right values or fuel-four state"
        assertTrue (decide (runRuntimeFunction? types owner declaration arguments 5 store =
          some (.word, .done (.word (operation leftValue rightValue)) store))) s!"{content}: wrong exact five-fuel result"

private def operations : List (String × Syntax.BinaryOp × Core.BinaryOp × (Core.Word → Core.Word → Core.Word)) :=
  [("-", .subtract, .wordSub, Core.Word.sub), ("*", .multiply, .wordMul, Core.Word.mul)]

def frontendParsedWordArithmeticTests : IO Unit := do
  let supplied := inputs true
  checkRun supplied "0 - 1" (.binary .wordSub (literal 0) (literal 1)) Core.Word.maximum 5
  checkRun supplied s!"{Core.Word.maximum.val} * 2"
    (.binary .wordMul (.word Core.Word.maximum) (literal 2)) (word (Core.wordModulus - 2)) 5
  checkRun supplied "l - r" (.binary .wordSub (.var 2) (.var 1)) (word (Core.wordModulus - 2)) 5
  checkRun supplied "r - l" (.binary .wordSub (.var 1) (.var 2)) (word 2) 5
  checkRun supplied "/* left */ 0x09 - /* right */ 0007" (.binary .wordSub (literal 9) (literal 7)) (word 2) 5
  checkRun supplied "8 - 3 - 2" (.binary .wordSub (.binary .wordSub (literal 8) (literal 3)) (literal 2)) (word 3) 9
  checkRun supplied "8 - (3 - 2)" (.binary .wordSub (literal 8) (.binary .wordSub (literal 3) (literal 2))) (word 7) 9
  checkRun supplied "2 * 3 * 4" (.binary .wordMul (.binary .wordMul (literal 2) (literal 3)) (literal 4)) (word 24) 9
  checkRun supplied "1 + 2 * 3" (.binary .wordAdd (literal 1) (.binary .wordMul (literal 2) (literal 3))) (word 7) 9
  checkRun supplied "8 - 3 * 2" (.binary .wordSub (literal 8) (.binary .wordMul (literal 3) (literal 2))) (word 2) 9
  checkRun supplied "(8 - 3) * 2" (.binary .wordMul (.binary .wordSub (literal 8) (literal 3)) (literal 2)) (word 10) 9
  checkRun supplied "8 - 2 * 3 | 1" (.binary .wordOr
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3))) (literal 1)) (word 3) 13
  checkRun supplied "1 ^ 8 - 2 * 3" (.binary .wordXor (literal 1)
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3)))) (word 3) 13
  for (symbol, sourceOperator, operator, operation) in operations do
    checkRun supplied s!"l {symbol} r" (.binary operator (.var 2) (.var 1)) (operation (word 7) (word 9)) 5
    for identity in [0, 1] do
      checkRun supplied s!"{identity} {symbol} l" (.binary operator (literal identity) (.var 2))
        (operation (word identity) (word 7)) 5
      checkRun supplied s!"l {symbol} {identity}" (.binary operator (.var 2) (literal identity))
        (operation (word 7) (word identity)) 5
    for choice in [false, true] do
      let selected := inputs choice
      checkRun selected s!"c ? l {symbol} r : 0"
        (.ifE (.var 0) (.binary operator (.var 2) (.var 1)) (literal 0))
        (if choice then operation (word 7) (word 9) else Core.Word.zero) (if choice then 8 else 4)
      checkRun selected s!"c ? 0 : l {symbol} r"
        (.ifE (.var 0) (literal 0) (.binary operator (.var 2) (.var 1)))
        (if choice then Core.Word.zero else operation (word 7) (word 9)) (if choice then 4 else 8)
      for content in [s!"c {symbol} l", s!"l {symbol} c", s!"c ? l : 0 {symbol} c", s!"c ? c {symbol} 0 : r"] do
        checkRejected selected content true
      for content in [s!"0 {symbol} missing", s!"missing {symbol} 0", s!"1 {symbol} missing", s!"missing {symbol} 1",
          s!"0 {symbol} {Core.wordModulus}", s!"{Core.wordModulus} {symbol} 0",
          s!"0 {symbol} \"1\"", s!"\"1\" {symbol} 0",
          s!"c ? l : 0 {symbol} missing", s!"c ? missing {symbol} 0 : r",
          s!"c ? l : 0 {symbol} {Core.wordModulus}", s!"c ? {Core.wordModulus} {symbol} 0 : r"] do
        checkRejected selected content false
    checkParameterPositions symbol sourceOperator operator operation
  let equality ← expression "l == r"
  let equalityCore := Core.Expr.binary .wordEq (.var 2) (.var 1)
  assertTrue (decide (supplied.check? equality = some (equalityCore, .bool)))
    "Word equality must check as the actual Bool-valued Core primitive"
  let equalityInitial := Core.State.initial equalityCore supplied.environment.values store
  for fuel in [0, 4, 5, 10] do
    assertTrue (decide (supplied.run? fuel equality store =
      some (.bool, Core.runStateful fuel equalityInitial))) "equality changed the checked Core execution"
  assertTrue (match Core.runStateful 4 equalityInitial with | .outOfFuel _ => true | _ => false)
    "equality completed below its five-transition cost"
  assertTrue (decide (supplied.run? 5 equality store = some (.bool, .done (.bool false) store)))
    "equality lost its Bool result or exact five-transition cost"
  for content in ["l / r", "l % r"] do
    checkRejected supplied content false
  checkShapes
  for content in ["-1", "+1", "8 -", "2 *", "8 - 3 2", "2 * 3 trailing", "l -= r", "l *= r"] do
    assertTrue (← parsed? Syntax.Parser.expression content).isNone
      s!"{content}: malformed, unsupported prefix, or unconsumed source accepted"
  assertTrue (← parsed? (Syntax.Parser.functionDecl .module)
    "function trailing() returns (Word) { return 8 - 3 * 2; } trailing").isNone
    "function parser helper accepted only a valid prefix"

end Tests

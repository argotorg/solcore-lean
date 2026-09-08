import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionPreparationFactorization
import Solcore.Frontend.LocalInputsExecution

/-! Complete source parsing connects unsigned Word comparison to exact Bool
typing, ordered parameter positions, and checked machine states and costs. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedGreater", by decide⟩], by decide⟩⟩, 6⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)
private def store : Core.Store := [.word (word 91), .bool false]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def inputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "l" .word (.word (word 7)) .word).bindFresh
    owner "r" .word (.word (word 9)) .word).bindFresh owner "c" .bool (.bool choice) .bool

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) :
    IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-greater.sol"⟩, content }
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
    (expectedType : Core.Ty) (expected : Core.Value) (cost : Nat) : IO Unit := do
  let source ← expression content
  let checked := supplied.check? source
  assertTrue (decide (checked = some (expectedCore, expectedType))) s!"{content}: wrong exact Core/type"
  let some (actualCore, _) := checked | throw (IO.userError "missing checked Core")
  let initial := Core.State.initial actualCore supplied.environment.values store
  for fuel in [0, cost - 1, cost, cost + 5] do
    assertTrue (decide (supplied.run? fuel source store =
      some (expectedType, Core.runStateful fuel initial))) s!"{content}: bundled machine mismatch"
  assertTrue (match Core.runStateful (cost - 1) initial with
    | .outOfFuel _ => true | _ => false) s!"{content}: completed below exact cost"
  for fuel in [cost, cost + 5] do
    assertTrue (decide (Core.runStateful fuel initial = .done expected store))
      s!"{content}: wrong value, store, or completion threshold"

private def checkLeaf (content : String) (left right : Core.Expr)
    (leftWord rightWord : Core.Word) (expected : Bool) : IO Unit := do
  let supplied := inputs true
  checkRun supplied content (.binary .wordGt left right) .bool (.bool expected) 5
  let source ← expression content
  assertTrue (decide (supplied.run? 4 source store = some (.bool, .outOfFuel
    ⟨.ret (.word rightWord), [.binaryApply .wordGt (.word leftWord)], store⟩)))
    s!"{content}: wrong ordered Word values in fuel-four frame"

private def checkRejected (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves)
    s!"{content}: wrong resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid expression checked"
  for fuel in [0, 4, 30] do
    assertTrue (supplied.run? fuel source store).isNone s!"{content}: checking was bypassed"
  let text := "function rejected(l: Word, r: Word, c: Bool) returns (Bool) { return " ++ content ++ "; }"
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module) text
    | throw (IO.userError s!"{content}: wrapped declaration did not parse")
  assertTrue (compileRuntimeFunction? types owner declaration).isNone
    s!"{content}: invalid whole body compiled"

/-- All 4 + 9 + 16 ordered source pairs retain exact identity, index, value,
and the pending left-valued frame, including repeated and distant references. -/
private def checkParameterPositions : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let content := s!"function greater_{arity}_{left}_{right}({parameters}) returns (Bool)"
          ++ " { return " ++ s!"p{left} > p{right};" ++ " }"
        let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
          | throw (IO.userError s!"{content}: expected complete declaration")
        assertTrue (match declaration.value.body.value with
          | [⟨_, .returnStmt (some ⟨_, .binary ⟨_, .identifier l⟩ ⟨_, .greater⟩ ⟨_, .identifier r⟩⟩)⟩] =>
              l.value == s!"p{left}" && r.value == s!"p{right}"
          | _ => false) s!"{content}: source operator or parameter references changed"
        let some compiled := compileRuntimeFunction? types owner declaration
          | throw (IO.userError s!"{content}: value-free compilation failed")
        let expectedCore := Core.Expr.binary .wordGt (.var (arity - 1 - left)) (.var (arity - 1 - right))
        assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = .bool))
          s!"{content}: compilation changed exact open Core/type"
        assertTrue (decide (compiled.inputs.context.values = List.replicate arity Core.Ty.word))
          s!"{content}: wrong static context"
        assertTrue (decide (compiled.inputs.names = (indices.map fun index =>
          (s!"p{index}", (⟨owner, index⟩ : Resolved.LocalId))).reverse)) s!"{content}: wrong source IDs/names"
        assertTrue (decide (compiled.inputs.context.ids =
          (indices.map fun index => (⟨owner, index⟩ : Resolved.LocalId)).reverse))
          s!"{content}: wrong context identity order"
        assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some .bool))
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
            some (.bool, Core.runStateful fuel initial))) s!"{content}: same-fuel full result differs"
          assertTrue (decide (runRuntimeFunction? types owner declaration arguments fuel store =
            prepared.inputs.runReturnBody? fuel declaration.value.body store))
            s!"{content}: entry changed actual body execution"
        assertTrue (decide (runRuntimeFunction? types owner declaration arguments 0 store =
          some (.bool, .outOfFuel initial))) s!"{content}: wrong exact zero-fuel state"
        let leftValue := word (10 * left + 1)
        let rightValue := word (10 * right + 1)
        let pending : Core.State := ⟨.ret (.word rightValue), [.binaryApply .wordGt (.word leftValue)], store⟩
        assertTrue (decide (runRuntimeFunction? types owner declaration arguments 4 store =
          some (.bool, .outOfFuel pending))) s!"{content}: wrong left/right values or fuel-four state"
        assertTrue (decide (runRuntimeFunction? types owner declaration arguments 5 store =
          some (.bool, .done (.bool (decide (left > right))) store))) s!"{content}: wrong exact five-fuel result"

private def checkReturnContract : IO Unit := do
  let content := "function wrong(l: Word, r: Word) returns (Word) { return r > l; }"
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
    | throw (IO.userError "wrong return contract did not parse")
  let arguments : List TypedRuntimeArgument := [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
  let some bound := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
    | throw (IO.userError "wrong return contract parameters did not bind")
  assertTrue (decide (bound.checkReturnBody? declaration.value.body =
    some (.binary .wordGt (.var 0) (.var 1), .bool))) "body-only checker lost Bool comparison"
  assertTrue (compileRuntimeFunction? types owner declaration).isNone "comparison compiled with declared Word result"
  assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone "comparison prepared with Word return"
  for fuel in [0, 5, 30] do
    assertTrue (runRuntimeFunction? types owner declaration arguments fuel store).isNone "return contract bypassed"

def frontendParsedWordGreaterTests : IO Unit := do
  let supplied := inputs true
  checkLeaf "l > r" (.var 2) (.var 1) (word 7) (word 9) false
  checkLeaf "r > l" (.var 1) (.var 2) (word 9) (word 7) true
  checkLeaf "l > l" (.var 2) (.var 2) (word 7) (word 7) false
  checkLeaf s!"{2 ^ 255} > 0" (literal (2 ^ 255)) (literal 0) (word (2 ^ 255)) .zero true
  checkLeaf s!"{Core.Word.maximum.val} > 0" (.word .maximum) (literal 0) .maximum .zero true
  checkLeaf s!"0 > {Core.Word.maximum.val}" (literal 0) (.word .maximum) .zero .maximum false
  checkLeaf s!"{Core.Word.maximum.val} > {Core.Word.maximum.val}" (.word .maximum) (.word .maximum) .maximum .maximum false
  checkLeaf "/* left */ 0x09 > /* right */ 0007" (literal 9) (literal 7) (word 9) (word 7) true
  checkRun supplied "((r)) > (l)" (.binary .wordGt (.var 1) (.var 2)) .bool (.bool true) 5
  checkRun supplied "8 - 2 * 3 | 1 > 2" (.binary .wordGt (.binary .wordOr
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3))) (literal 1)) (literal 2))
    .bool (.bool true) 17
  checkRun supplied "1 | 2 ^ 3 & 4 + 5 * 2 > 2" (.binary .wordGt (.binary .wordOr (literal 1)
    (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3)
      (.binary .wordAdd (literal 4) (.binary .wordMul (literal 5) (literal 2)))))) (literal 2))
    .bool (.bool false) 25
  checkRun supplied "r - l > 0 ? l * r : 1" (.ifE
    (.binary .wordGt (.binary .wordSub (.var 1) (.var 2)) (literal 0))
    (.binary .wordMul (.var 2) (.var 1)) (literal 1)) .word (.word (word 63)) 16
  checkRun supplied "r - l > 2 ? l * r : 1" (.ifE
    (.binary .wordGt (.binary .wordSub (.var 1) (.var 2)) (literal 2))
    (.binary .wordMul (.var 2) (.var 1)) (literal 1)) .word (.word (word 1)) 12
  let forward := Core.Expr.binary .wordGt (.var 2) (.var 1)
  let reversed := Core.Expr.binary .wordGt (.var 1) (.var 2)
  checkRun supplied "l > r && r > l" (.ifE forward reversed (.bool false)) .bool (.bool false) 8
  checkRun supplied "r > l && l > r" (.ifE reversed forward (.bool false)) .bool (.bool false) 12
  checkRun supplied "r > l || l > r" (.ifE reversed (.bool true) forward) .bool (.bool true) 8
  checkRun supplied "l > r || r > l" (.ifE forward (.bool true) reversed) .bool (.bool true) 12
  for choice in [false, true] do
    let selected := inputs choice
    checkRun selected "l > r || r > l && c" (.ifE forward (.bool true) (.ifE reversed (.var 0) (.bool false)))
      .bool (.bool choice) 15
    checkRun selected "c ? l > r : r > l" (.ifE (.var 0) forward reversed) .bool (.bool (!choice)) 8
    for content in ["c > l", "l > c", "(l > r) > l", "l > (r > l)",
        "c ? r > l : c > l", "c ? l > c : r > l", "l > r && c > l", "r > l || l > c"] do
      checkRejected selected content true
    for content in ["missing > 0", "0 > missing", s!"{Core.wordModulus} > 0", s!"0 > {Core.wordModulus}",
        "l > r && missing > 0", "r > l || 0 > missing", s!"r > l || 0 > {Core.wordModulus}",
        "c ? r > l : missing > 0", s!"c ? {Core.wordModulus} > 0 : r > l"] do
      checkRejected selected content false
  checkRun supplied "l == r" (.binary .wordEq (.var 2) (.var 1)) .bool (.bool false) 5
  checkRun supplied "l != r" (.unary .boolNot (.binary .wordEq (.var 2) (.var 1))) .bool (.bool true) 7
  checkRun supplied "l <= r" (.unary .boolNot (.binary .wordGt (.var 2) (.var 1))) .bool (.bool true) 7
  for content in ["l >= r", "l / r", "l % r"] do
    checkRejected supplied content false
  checkParameterPositions
  checkReturnContract
  for content in ["l > r > l", "-1 > 0", "+1 > 0", "l >", "l > r trailing", "l > r 0"] do
    assertTrue (← parsed? Syntax.Parser.expression content).isNone
      s!"{content}: non-associative, prefix, incomplete, or unconsumed source accepted"
  assertTrue (← parsed? (Syntax.Parser.functionDecl .module)
    "function trailing(l: Word) returns (Bool) { return l > 0; } trailing").isNone
    "function parser helper accepted only a valid prefix"

end Tests

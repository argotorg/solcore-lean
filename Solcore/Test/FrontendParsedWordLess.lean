import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionExecutionFactorization
import Solcore.Frontend.ReturnBodyFuelBoundProperties

/-! Fully parsed unsigned less-than retains both original operands in two Core
lets. Actual checkpoints, their environments, and their pending frames survive
resumption unchanged; type-only compilation carries its own provenance. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ParsedLess", by decide⟩], by decide⟩⟩, 25⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)
private def lt (left right : Core.Expr) : Core.Expr :=
  .letE left (.letE (right.weakenAt 0) (.binary .wordGt (.var 0) (.var 1)))
private def store : Core.Store := [.word (word 91), .bool false]
private def types : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def inputs (choice : Bool) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "l" .word (.word (word 7)) .word).bindFresh
    owner "r" .word (.word (word 9)) .word).bindFresh owner "c" .bool (.bool choice) .bool

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-less.sol"⟩, content }
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
    | throw (IO.userError s!"{content}: expected complete diagnostic-free expression")
  return source
private def compile (declaration : Syntax.FunctionDecl) :
    IO { compiled // RuntimeFunctionCompiles types owner declaration compiled } :=
  match accepted : compileRuntimeFunction? types owner declaration with
  | some compiled => pure ⟨compiled, compileRuntimeFunction?_sound accepted⟩
  | none => throw (IO.userError "parsed declaration did not compile")

private def checkMachine (run : Nat → Option (Core.Ty × Core.StatefulRunResult))
    (initial : Core.State) (type : Core.Ty) (expected : Core.Value) (cost : Nat) : IO Unit := do
  for fuel in List.range (cost + 3) do
    let observed := run fuel
    assertTrue (decide (observed = some (type, Core.runStateful fuel initial))) "full actual Core result changed"
    assertTrue (match observed with
      | some (actualType, .done value finalStore) =>
          decide (cost ≤ fuel ∧ actualType = type ∧ value = expected ∧ finalStore = store)
      | some (actualType, .outOfFuel suspended) =>
          decide (fuel < cost ∧ actualType = type ∧ suspended.store = store)
      | _ => false) "wrong exact cost, value, type, or store"
  for spent in List.range cost do
    let some (_, .outOfFuel checkpoint) := run spent | throw (IO.userError "genuine checkpoint missing")
    for remaining in List.range (cost - spent + 3) do
      assertTrue (decide (run (spent + remaining) = some (type, Core.runStateful remaining checkpoint)))
        "resumption changed full result or discarded a pending frame"

private def checkPending (run : Nat → Option (Core.Ty × Core.StatefulRunResult))
    (right : Core.Expr) (environment : Core.Environment) (leftWord rightWord : Core.Word) : IO Unit := do
  let body := Core.Expr.binary .wordGt (.var 0) (.var 1)
  let two : Core.State := ⟨.ret (.word leftWord), [.letBody (.letE (right.weakenAt 0) body) environment], store⟩
  let five : Core.State := ⟨.ret (.word rightWord), [.letBody body (.word leftWord :: environment)], store⟩
  let ten : Core.State := ⟨.ret (.word leftWord), [.binaryApply .wordGt (.word rightWord)], store⟩
  let some (.bool, .outOfFuel actualTwo) := run 2 | throw (IO.userError "first let checkpoint missing")
  let some (.bool, .outOfFuel actualFive) := run 5 | throw (IO.userError "second let checkpoint missing")
  let some (.bool, .outOfFuel actualTen) := run 10 | throw (IO.userError "ordered comparison frame missing")
  assertTrue (decide (actualTwo = two ∧ actualFive = five ∧ actualTen = ten)) "two-let order/environments changed"
  assertTrue (decide (Core.runStateful 3 actualTwo = .outOfFuel actualFive ∧
    Core.runStateful 5 actualFive = .outOfFuel actualTen ∧
    Core.runStateful 1 actualTen = .done (.bool (decide (leftWord < rightWord))) store ∧
    Core.runStateful 0 actualTen = .outOfFuel actualTen ∧
    Core.runStateful 0 { actualTen with continuation := [] } = .done (.word leftWord) store))
    "genuine multichunk resumption or dropped-frame counterexample changed"

private def checkRun (supplied : LocalInputs) (content : String) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let source ← expression content
  assertTrue (decide (supplied.check? source = some (core, type))) s!"{content}: wrong exact Core/type"
  assertTrue (decide (cost ≤ localExpressionFuelBound source)) "source-only bound insufficient"
  for fuel in [localExpressionFuelBound source, localExpressionFuelBound source + 2] do
    assertTrue (decide (supplied.run? fuel source store = some (type, .done value store))) "conservative bound did not finish"
  checkMachine (fun fuel => supplied.run? fuel source store)
    (Core.State.initial core supplied.environment.values store) type value cost
private def checkLeaf (content : String) (left right : Core.Expr) (l r : Core.Word) : IO Unit := do
  let supplied := inputs true
  checkRun supplied content (lt left right) .bool (.bool (decide (l < r))) 11
  let source ← expression content
  assertTrue (localExpressionFuelBound source == 11) "two leaves no longer have source bound eleven"
  checkPending (fun fuel => supplied.run? fuel source store) right supplied.environment.values l r

private def checkRejected (supplied : LocalInputs) (content : String) (resolves : Bool) : IO Unit := do
  let source ← expression content
  assertTrue ((resolveLocalExpression? supplied.names source).isSome == resolves) s!"{content}: resolution boundary"
  assertTrue (supplied.check? source).isNone s!"{content}: invalid less-than checked"
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
    ("function rejected(l: Word, r: Word, c: Bool) returns (Bool) { return " ++ content ++ "; }")
    | throw (IO.userError "wrapped rejection declaration did not parse")
  assertTrue (compileRuntimeFunction? types owner declaration).isNone "invalid whole body compiled"
  for choice in [false, true] do
    let arguments : List TypedRuntimeArgument :=
      [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩, ⟨.bool, .bool choice, .bool⟩]
    assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone "invalid body prepared"
    for fuel in [0, 2, 5, 10, 11, 50] do
      assertTrue ((supplied.run? fuel source store).isNone &&
        (runRuntimeFunction? types owner declaration arguments fuel store).isNone) "whole rejection bypassed"

private def checkParameterPositions : IO Unit := do
  for arity in [2, 3, 4] do
    let indices := List.range arity
    let parameters := String.intercalate ", " (indices.map fun index => s!"p{index}: Word")
    for left in indices do
      for right in indices do
        let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
          (s!"function less_{arity}_{left}_{right}({parameters}) returns (Bool)" ++
            " { return " ++ s!"p{left} < p{right};" ++ " }")
          | throw (IO.userError "ordered parameter declaration did not parse")
        let ⟨compiled, provenance⟩ ← compile declaration
        let core := lt (.var (arity - 1 - left)) (.var (arity - 1 - right))
        assertTrue (decide (compiled.core = core ∧ compiled.returnType = .bool ∧
          compiled.inputs.context.values = List.replicate arity Core.Ty.word ∧
          compiled.inputs.names = (indices.map fun index => (s!"p{index}", (⟨owner, index⟩ : Resolved.LocalId))).reverse))
          "open compilation changed original positions or allocated hidden source identities"
        assertTrue (returnBodyFuelBound declaration.value.body == 11) "entry source bound changed"
        match declaration.value.body.value with
        | [⟨_, .returnStmt (some source)⟩] =>
            assertTrue (match source.value with
              | .binary ⟨_, .identifier l⟩ ⟨_, .less⟩ ⟨_, .identifier r⟩ => l.value == s!"p{left}" && r.value == s!"p{right}"
              | _ => false) "canonical operator or ordered source references changed"
            assertTrue (decide (resolveLocalExpression? compiled.inputs.names source =
              some (.wordLt (.var ⟨owner, left⟩) (.var ⟨owner, right⟩)))) "identity-free resolved shape changed"
        | _ => throw (IO.userError "own compiled body not a single return")
        let boundaries := [0, 1, 2 ^ 255, Core.Word.maximum.val]
        let vectors := if arity == 2 && left == 0 && right == 1 then
          boundaries.flatMap (fun l => boundaries.map (fun r => [l, r])) else [indices.map (fun i => 10 * i + 1)]
        for vector in vectors do
          let arguments : List TypedRuntimeArgument := vector.map (fun value => ⟨.word, .word (word value), .word⟩)
          let some prepared := prepareRuntimeFunction? types owner declaration arguments
            | throw (IO.userError "actual matching arguments did not prepare")
          let values := arguments.reverse.map (·.value)
          assertTrue (decide (prepared.inputs.environment.values = values ∧ prepared.core = compiled.core ∧
            prepared.inputs.context = compiled.inputs.context ∧ prepared.returnType = compiled.returnType))
            "actual runtime values or compiled projection changed"
          if matching : arguments.map (·.type) = compiled.inputs.context.values.reverse then
            have _ := provenance.run_eq arguments matching 11 store
            let run := fun fuel => runRuntimeFunction? types owner declaration arguments fuel store
            let l := word (vector[left]!)
            let r := word (vector[right]!)
            checkMachine run (Core.State.initial compiled.core values store) .bool (.bool (decide (l < r))) 11
            checkPending run (.var (arity - 1 - right)) values l r
          else throw (IO.userError "actual argument guard disagreed with own compilation")

private def checkArithmeticEntry : IO Unit := do
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
    "function guard(l: Word, r: Word) returns (Word) { return l * r < r ? l - r : l; }"
    | throw (IO.userError "arithmetic entry did not parse")
  let ⟨compiled, _⟩ ← compile declaration
  assertTrue (decide (compiled.core = .ifE (lt (.binary .wordMul (.var 1) (.var 0)) (.var 0))
    (.binary .wordSub (.var 1) (.var 0)) (.var 1) ∧ compiled.returnType = .word)) "arithmetic compiled shape changed"
  assertTrue (returnBodyFuelBound declaration.value.body == 22) "arithmetic source bound changed"
  for left in [0, 1, 7, Core.Word.maximum.val] do
    for right in [0, 1, 9] do
      let arguments : List TypedRuntimeArgument := [⟨.word, .word (word left), .word⟩, ⟨.word, .word (word right), .word⟩]
      let selected := decide ((word left).mul (word right) < word right)
      let expected := Core.Value.word (if selected then (word left).sub (word right) else word left)
      checkMachine (fun fuel => runRuntimeFunction? types owner declaration arguments fuel store)
        (Core.State.initial compiled.core (arguments.reverse.map (·.value)) store) .word expected (if selected then 22 else 18)

private def checkReturnContract : IO Unit := do
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
    "function wrong(l: Word, r: Word) returns (Word) { return l < r; }"
    | throw (IO.userError "wrong return declaration did not parse")
  let arguments : List TypedRuntimeArgument := [⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
  let some bound := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
    | throw (IO.userError "actual parameters did not bind")
  assertTrue (decide (bound.checkReturnBody? declaration.value.body = some (lt (.var 1) (.var 0), .bool))) "body lost Bool type"
  assertTrue ((compileRuntimeFunction? types owner declaration).isNone &&
    (prepareRuntimeFunction? types owner declaration arguments).isNone) "Bool body accepted under Word return contract"
  for fuel in [0, 11, 50] do
    assertTrue (runRuntimeFunction? types owner declaration arguments fuel store).isNone "return contract bypassed"

def frontendParsedWordLessTests : IO Unit := do
  let supplied := inputs true
  checkLeaf "l < r" (.var 2) (.var 1) (word 7) (word 9)
  checkLeaf "r < l" (.var 1) (.var 2) (word 9) (word 7)
  checkLeaf "l < l" (.var 2) (.var 2) (word 7) (word 7)
  for left in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
    for right in [0, 1, 2 ^ 255, Core.Word.maximum.val] do
      checkLeaf s!"{left} < {right}" (literal left) (literal right) (word left) (word right)
  checkLeaf "/* left */ 0x09 < /* right */ 0009" (literal 9) (literal 9) (word 9) (word 9)
  checkLeaf "((r)) < (l)" (.var 1) (.var 2) (word 9) (word 7)
  checkRun supplied "~0 < 1" (lt (.unary .wordNot (literal 0)) (literal 1)) .bool (.bool false) 13
  let precedence ← expression "l < r == c"
  assertTrue (match precedence.value with
    | .binary ⟨_, .binary _ ⟨_, .less⟩ _⟩ ⟨_, .equal⟩ _ => true | _ => false) "relational/equality precedence changed"
  let reversePrecedence ← expression "c != l < r"
  assertTrue (match reversePrecedence.value with
    | .binary _ ⟨_, .notEqual⟩ ⟨_, .binary _ ⟨_, .less⟩ _⟩ => true | _ => false) "right relational precedence changed"
  checkRun supplied "8 - 2 * 3 | 1 < 3" (lt (.binary .wordOr
    (.binary .wordSub (literal 8) (.binary .wordMul (literal 2) (literal 3))) (literal 1)) (literal 3)) .bool (.bool false) 23
  checkRun supplied "1 | 2 ^ 3 & 4 + 5 * 2 < 3" (lt (.binary .wordOr (literal 1)
    (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3)
      (.binary .wordAdd (literal 4) (.binary .wordMul (literal 5) (literal 2)))))) (literal 3)) .bool (.bool true) 31
  let forward := lt (.var 2) (.var 1)
  let reversed := lt (.var 1) (.var 2)
  checkRun supplied "!(l < r)" (.unary .boolNot forward) .bool (.bool false) 13
  checkRun supplied "r < l && l < r" (.ifE reversed forward (.bool false)) .bool (.bool false) 14
  checkRun supplied "l < r && r < l" (.ifE forward reversed (.bool false)) .bool (.bool false) 24
  checkRun supplied "l < r || r < l" (.ifE forward (.bool true) reversed) .bool (.bool true) 14
  checkRun supplied "r < l || l < r" (.ifE reversed (.bool true) forward) .bool (.bool true) 24
  for choice in [false, true] do
    let selected := inputs choice
    checkRun selected "r < l || l < r && c" (.ifE reversed (.bool true)
      (.ifE forward (.var 0) (.bool false))) .bool (.bool choice) 27
    checkRun selected "c ? l < r : r < l" (.ifE (.var 0) forward reversed) .bool (.bool choice) 14
    checkRun selected "(c ? l : r) < (c ? r : l)" (lt (.ifE (.var 0) (.var 2) (.var 1))
      (.ifE (.var 0) (.var 1) (.var 2))) .bool (.bool choice) 17
    for content in ["c < l", "l < c", "c < c", "(l < r) < l", "l < (r < l)", "l < r == c", "c != l < r",
        "c ? l < r : c < c", "l < r || c < c", "r < l && c < c"] do
      checkRejected selected content true
    for content in ["missing < 0", "0 < missing", s!"{Core.wordModulus} < 0", s!"0 < {Core.wordModulus}",
        "l < r || missing < 0", "r < l && 0 < missing", s!"l < r || 0 < {Core.wordModulus}", "c ? l < r : missing < 0"] do
      checkRejected selected content false
  for name in ["Bool", "Unit", "Cell", "Fn", "Opaque"] do
    let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
      (s!"function same(x: {name}, y: {name}) returns (Bool)" ++ " { return x < y; }")
      | throw (IO.userError "non-Word declaration did not parse")
    assertTrue (compileRuntimeFunction? types owner declaration).isNone "matching non-Word operands enabled less-than"
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let closure : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  for (name, argument) in [("Unit", unit), ("Cell", cell), ("Fn", closure)] do
    for returned in ["x < y", "y < x"] do
      let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
        (s!"function wrong(x: {name}, y: Word) returns (Bool)" ++ " { return " ++ returned ++ "; }")
        | throw (IO.userError "actual mixed operand declaration did not parse")
      let arguments := [argument, (⟨.word, .word (word 7), .word⟩ : TypedRuntimeArgument)]
      assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone "actual non-Word operand prepared"
      for fuel in [0, 11, 50] do
        assertTrue (runRuntimeFunction? types owner declaration arguments fuel store).isNone "actual non-Word operand ran"
  for content in ["l(c)", "r(c)"] do checkRejected supplied content false
  checkParameterPositions
  checkReturnContract
  checkArithmeticEntry
  for content in ["l < r < l", "l < r > l", "l <= r < l", "l < r <= l", "l <", "-1 < 0", "+1 < 0",
      "l < r trailing", "l < r 0"] do
    assertTrue (← parsed? Syntax.Parser.expression content).isNone "non-associative or incomplete source accepted"
  assertTrue (← parsed? (Syntax.Parser.functionDecl .module)
    "function trailing(l: Word) returns (Bool) { return l < 0; } trailing").isNone "only a function prefix was accepted"

end Tests

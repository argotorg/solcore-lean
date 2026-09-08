import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TypedLetReturnTreeFuelBoundProperties
import Solcore.Frontend.TypedLetReturnTreeResumptionProperties
import Solcore.Frontend.TypedLetReturnTreeRunnerEmbeddingProperties
import Solcore.Frontend.TypedLetReturnBodyFuelBoundProperties
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties
import Solcore.Frontend.RuntimeFunctionCompilation

/-! Actual parsed parameters and independent source scripts meet the new body
runner. All checkpoints come from real execution; expectations are not inferred
from runner output. Old entry/body policies and old bounds remain unchanged. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetTreeRunner", by decide⟩], by decide⟩⟩, 17⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def stores : List Core.Store := [[.word (word 101), .cellRef .word 31],
  [.closure .bool .bool (.var 0) [], .bool false, .word Core.Word.maximum]]
private def actual (content : String) (arguments : List TypedRuntimeArgument) : IO (Syntax.FunctionDecl × LocalInputs) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-let-tree-runner.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"function did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "diagnosed or incomplete source"
  match bound : bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "actual typed arguments did not bind")
  | some inputs =>
      have _ := (bindRuntimeParameters?_sound bound).erase_values.complete
      let names := source.value.signature.parameters.elements.filterMap fun parameter => match parameter.value with
        | .typed none name _ => some name.value | _ => none
      assertTrue (decide (inputs.environment.values = arguments.reverse.map (·.value) ∧
        inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
        (declareRuntimeParameters? types owner source.value.signature.parameters.elements).map (fun i => (i.names, i.context.values)) =
          some (inputs.names, inputs.context.values))) "original names, IDs, actual values or static factorization changed"
      return (source, inputs)
private structure Expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table environment store source value store cost
private def reference (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "script expected an existing name")
      | some id =>
          match found : environment.lookup? id with
          | none => throw (IO.userError "script expected an actual value")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "script expected a reference")
private def expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ => reference table environment store source
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← reference table environment store operand
      match valueAt : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (valueAt ▸ child.costed)⟩
      | _ => throw (IO.userError "word-not expected Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table environment store left
      let second ← reference table environment store right
      match leftAt : first.value, rightAt : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]; exact .subtract (leftAt ▸ first.costed) (rightAt ▸ second.costed)⟩
      | _, _ => throw (IO.userError "ordered subtraction expected Words")
  | _ => throw (IO.userError "expression outside fixture script")
private structure Certificate (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table environment store source value store cost
private def certify (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) (choices : List Bool) : IO (Certificate table environment store source) := do
  match sourceAt : source with
  | ⟨blockSpan, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let child ← expression table environment store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, child.value) :: environment) store ⟨blockSpan, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by rw [sourceAt]; exact .binding child.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "missing selected-branch script")
      let guard ← reference table environment store condition
      if agrees : guard.value = .bool choice then
        match choiceAt : choice with
        | true =>
            let child ← certify table environment store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]; exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
        | false =>
            let child ← certify table environment store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]; exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
      else throw (IO.userError "script disagrees with actual guard")
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ =>
      assertTrue choices.isEmpty "script continued after bare return"
      return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      assertTrue choices.isEmpty "script continued after return"
      let child ← expression table environment store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | _ => throw (IO.userError "script cannot describe original source")
termination_by sizeOf source
private def oldShapes (inputs : LocalInputs) (body : Syntax.Block) (fuel : Nat) (store : Core.Store) : IO Unit := do
  let run := inputs.runTypedLetReturnTree? types owner fuel body store
  match body.value with
  | [⟨returnSpan, .returnStmt returned⟩] =>
      have _ := inputs.runTypedLetReturnTree?_single types owner fuel returned body.span returnSpan store
      assertTrue (decide (run = inputs.runReturnBody? fuel body store)) "singleton full Option result changed"
  | _ => pure ()
  match accepted : inputs.runTerminalReturnTree? fuel body store with
  | none => pure ()
  | some result =>
      have _ := LocalInputs.runTypedLetReturnTree?_some_of_terminalReturnTree types owner accepted
      assertTrue (decide (run = some result)) "old terminal-tree success changed complete same-fuel result"
  match accepted : inputs.runTypedLetReturnBody? types owner fuel body store with
  | none => pure ()
  | some result =>
      have _ := LocalInputs.runTypedLetReturnTree?_some_of_typedLetReturnBody accepted
      assertTrue (decide (run = some result)) "old prefix success changed complete same-fuel result"
private def checked (source : Syntax.FunctionDecl) (inputs : LocalInputs) (choices : List Bool)
    (core : Core.Expr) (expected : TypedRuntimeArgument) (cost bound : Nat) (branchBindings : Bool := true) : IO Unit := do
  have aligned : inputs.environment.ids = inputs.toTypeInputs.context.ids := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
  have typed : Core.EnvironmentHasTypes inputs.environment.values inputs.toTypeInputs.context.values := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.environmentTyped
  for store in stores do
    let certificate ← certify inputs.toTypeInputs.names inputs.environment store source.value.body choices
    assertTrue (decide (certificate.value = expected.value ∧ certificate.cost = cost ∧ typedLetReturnTreeFuelBound source.value.body = bound))
      "independent source value/cost or maximum bound changed"
    match accepted : inputs.checkTypedLetReturnTree? types owner source.value.body with
    | none => throw (IO.userError "whole tree rejected")
    | some (actualCore, type) =>
        assertTrue (decide (actualCore = core ∧ type = expected.type ∧ Core.infer? inputs.context.values core = some type ∧
          interpretRuntimeFunctionHeader? types source.value.signature = some type)) "actual source Core/type/header changed"
        if branchBindings then assertTrue (compileRuntimeFunction? types owner source).isNone "body runner expanded existing entry"
        let typing := elaborateTypedLetReturnTree?_sound accepted
        have _ := certificate.costed.cost_le_fuelBound
        have _ := certificate.costed.checked_runStateful_done_iff (fuel := cost) accepted aligned
        have _ := certificate.costed.checked_runStateful_outOfFuel_iff (fuel := 0) accepted aligned
        have _ := elaborateTypedLetReturnTree?_run_done_iff_cost (initialStore := store) (finalStore := store)
          (value := expected.value) (fuel := cost) accepted aligned
        have _ := LocalInputs.typedLetReturnTree_typed_cost_execution (inputs := inputs) typing store
        have _ := elaborateTypedLetReturnTree?_run_done_of_fuelBound accepted aligned typed store
          (typedLetReturnTreeFuelBound source.value.body) (Nat.le_refl _)
        have _ := LocalInputs.runTypedLetReturnTree?_done_of_fuelBound (inputs := inputs) typing store
          (typedLetReturnTreeFuelBound source.value.body) (Nat.le_refl _)
        let initial := Core.State.initial core inputs.environment.values store
        let run := fun fuel => inputs.runTypedLetReturnTree? types owner fuel source.value.body store
        for fuel in List.range (bound + 3) do
          oldShapes inputs source.value.body fuel store
          have _ := LocalInputs.runTypedLetReturnTree?_never_faults inputs types owner source.value.body fuel store type
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel initial))) "runner changed Core, original values or complete machine state"
          match outcome : run fuel with
          | some (actualType, .done value finalStore) =>
              have _ := LocalInputs.runTypedLetReturnTree?_done_iff_typed_cost.mp outcome
              assertTrue (decide (cost ≤ fuel ∧ actualType = type ∧ value = expected.value ∧ finalStore = store)) "completion threshold or own value/store changed"
          | some (actualType, .outOfFuel state) =>
              have _ := LocalInputs.runTypedLetReturnTree?_outOfFuel_iff_typed_cost.mp ⟨state, outcome⟩
              assertTrue (decide (fuel < cost ∧ actualType = type ∧ state.store = store)) "exhaustion threshold or own store changed"
          | _ => throw (IO.userError "whole typed runner faulted or disappeared")
        for spent in List.range cost do
          match exhausted : run spent with
          | some (type, .outOfFuel checkpoint) =>
              have _ : spent < certificate.cost ∧ Core.Steps (certificate.cost - spent) checkpoint (.final certificate.value store) := by
                obtain ⟨_, checkedAt, pathAt⟩ := LocalInputs.runTypedLetReturnTree?_eq_some_iff.mp exhausted
                exact certificate.costed.checked_residual_of_outOfFuel checkedAt aligned pathAt
              assertTrue (decide (Core.runStateful 0 checkpoint = .outOfFuel checkpoint)) "zero fuel changed a genuine checkpoint"
              for remaining in List.range (cost - spent + 3) do
                have _ := LocalInputs.runTypedLetReturnTree?_resume exhausted remaining
                let resumed := Core.runStateful remaining checkpoint
                assertTrue (decide (run (spent + remaining) = some (type, resumed))) "full genuine resumption changed"
                assertTrue (match resumed with
                  | .done value finalStore => decide (cost - spent ≤ remaining ∧ value = expected.value ∧ finalStore = store)
                  | .outOfFuel state => decide (remaining < cost - spent ∧ state.store = store)
                  | _ => false) "residual threshold or original store changed"
              for middle in [0, (cost - spent) / 2, cost - spent - 1] do
                let .outOfFuel second := Core.runStateful middle checkpoint | throw (IO.userError "second genuine checkpoint disappeared")
                for last in [0, cost - spent - middle - 1, cost - spent - middle, cost - spent - middle + 2] do
                  assertTrue (decide (run (spent + middle + last) = some (type, Core.runStateful last second))) "three genuine chunks changed their complete result"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done expected.value store))) "restart was mistaken for checkpoint resumption"
          | _ => throw (IO.userError "expected actual exhaustion below independent cost")
private def alternating (remaining level : Nat) : String × Core.Expr :=
  match remaining with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 1 else 0))
  | count + 1 =>
      let (tail, core) := alternating count (level + 1)
      let recText := s!"let z{level}: Word=" ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail
      let leafText := s!"let z{level}: Word=y;return z{level};"
      let recCore := Core.Expr.letE (.var (if level = 0 then 1 else 0)) core
      let leafCore := Core.Expr.letE (.var level) (.var 0)
      if level % 2 = 0 then ("if(c){" ++ recText ++ "}else{" ++ leafText ++ "}", .ifE (.var (level + 3)) recCore leafCore)
      else ("if(d){" ++ leafText ++ "}else{" ++ recText ++ "}", .ifE (.var (level + 2)) leafCore recCore)

def frontendParsedTypedLetReturnTreeRunnerTests : IO Unit := do
  for depth in [0, 1, 2, 5] do
    let (body, core) := alternating depth 0
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs) ← actual ("function alternating(c: Bool,d: Bool,x: Word,y: Word) returns (Word){" ++ body ++ "}")
          [boolArg c, boolArg d, wordArg 9, wordArg 2]
        let choices := if depth = 0 then [] else if !c then [false] else if depth = 1 then [true]
          else if d then [true, true] else (List.range depth).map fun level => level % 2 == 0
        checked source inputs choices core (if depth == 0 || (c && (depth == 1 || !d)) then wordArg 9 else wordArg 2)
          (if depth = 0 then 1 else if !c || depth == 1 then 7 else if d then 13 else 6 * depth + 1) (6 * depth + 1) (depth != 0)
  for (x, y) in [(9, 2), (2, 9), (0, Core.Word.maximum.val), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs) ← actual "function asymmetric(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x - y;if(d){let w: Word=z;return ~w;}else{let w: Word=y - z;return w;}}else{let z: Word=y - x;return y;}}"
          [boolArg c, boolArg d, wordArg x, wordArg y]
        checked source inputs (if c then [true, d] else [false]) (.ifE (.var 3)
          (.letE (.binary .wordSub (.var 1) (.var 0)) (.ifE (.var 3) (.letE (.var 0) (.unary .wordNot (.var 0)))
            (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 1)))
          ⟨.word, .word (if c then if d then ((word x).sub (word y)).bitNot else (word y).sub ((word x).sub (word y)) else word y), .word⟩
          (if c then if d then 19 else 21 else 11) 21
  let left : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let right : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, x, y) in [("Fn", left, right), ("Cell", ⟨.cell .word, .cellRef .word 17, .cellRef⟩, ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
      ("Unit", ⟨.unit, .unit, .unit⟩, ⟨.unit, .unit, .unit⟩)] do
    for c in [false, true] do
      let (source, inputs) ← actual (s!"function opaque(c: Bool,x: {name},y: {name}) returns ({name})" ++ "{if(c){let z: " ++ name ++
        "=x;if(c){let w: " ++ name ++ "=y;return z;}else{return z;}}else{let z: " ++ name ++ "=y;return z;}}") [boolArg c, x, y]
      checked source inputs (if c then [true, true] else [false]) (.ifE (.var 2)
        (.letE (.var 1) (.ifE (.var 3) (.letE (.var 1) (.var 1)) (.var 0))) (.letE (.var 0) (.var 0))) (if c then x else y) (if c then 13 else 7) 13
  for c in [false, true] do
    let (source, inputs) ← actual "function simple(c: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x;return z;}else{return y;}}" [boolArg c, wordArg 9, wordArg 2]
    let selected := Core.Expr.letE (.var 1) (.var 0)
    checked source inputs [c] (.ifE (.var 2) selected (.var 0)) (if c then wordArg 9 else wordArg 2) (if c then 7 else 4) 7
    assertTrue (decide (terminalReturnTreeFuelBound source.value.body = 4 ∧ typedLetReturnBodyFuelBound source.value.body = 4)) "old source-only bounds changed"
    for store in stores do
      assertTrue ((inputs.runTerminalReturnTree? 7 source.value.body store).isNone && (inputs.runTypedLetReturnBody? types owner 7 source.value.body store).isNone)
        "old rejected branch-local profile was expanded"
      if c then
        let environment := inputs.environment.values
        let run := fun fuel => inputs.runTypedLetReturnTree? types owner fuel source.value.body store
        let frame := Core.Frame.letBody (.var 0) environment
        for (spent, state) in [(1, (⟨.eval (.var 2) environment, [.ifBranches selected (.var 0) environment], store⟩ : Core.State)),
            (3, ⟨.eval selected environment, [], store⟩), (4, ⟨.eval (.var 1) environment, [frame], store⟩),
            (5, ⟨.ret (.word (word 9)), [frame], store⟩), (6, ⟨.eval (.var 0) (.word (word 9) :: environment), [], store⟩)] do
          assertTrue (decide (run spent = some (.word, .outOfFuel state))) "actual if/initializer/obtained-value/tail checkpoint changed"
        let some (_, .outOfFuel checkpoint) := run 5 | throw (IO.userError "genuine retained initializer value disappeared")
        assertTrue (decide (Core.runStateful 0 { checkpoint with continuation := [] } = .done (.word (word 9)) store ∧
          Core.runStateful 0 checkpoint = .outOfFuel checkpoint ∧ Core.runStateful 2 checkpoint = .done (.word (word 9)) store ∧
          run 2 ≠ some (.word, .done (.word (word 9)) store))) "dropping pending frames or restarting became resumption"
  for (body, choices, core, value, cost) in [("{return x;}", [], Core.Expr.var 1, wordArg 9, 1),
      ("{return;}", [], .unit, (⟨.unit, .unit, .unit⟩ : TypedRuntimeArgument), 1),
      ("{if(c){if(c){return x;}else{return y;}}else{return y;}}", [true, true], .ifE (.var 2) (.ifE (.var 2) (.var 1) (.var 0)) (.var 0), wordArg 9, 7),
      ("{let z: Word=x;let w: Word=z - y;return w;}", [], .letE (.var 1) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0)), wordArg 7, 11)] do
    let (source, inputs) ← actual ("function old(c: Bool,x: Word,y: Word)" ++ (if value.type = .unit then "" else " returns (Word)") ++ body)
      [boolArg true, wordArg 9, wordArg 2]
    checked source inputs choices core value cost cost false
  for (body, bound, script) in [("{if(c){let z: Unknown=x;return z;}else{return y;}}", 7, some [true]),
      ("{if(c){let x: Word=x;return x;}else{return y;}}", 7, some [true]),
      ("{if(c){let z: Word=x;return z;}else{if(c){return y;}else{return missing;}}}", 7, some [true]),
      ("{if(c){let z: Word=missing;return x;}else{return y;}}", 7, none), ("{if(c){return x;}else{return c;}}", 4, none),
      ("{let z=x;return z;}", 0, none), ("{let z: Word;return x;}", 0, none), ("{}", 0, none), ("{return x;return y;}", 0, none), ("{return missing;}", 1, none)] do
    let (source, inputs) ← actual ("function rejected(c: Bool,x: Word,y: Word) returns (Word)" ++ body) [boolArg true, wordArg 9, wordArg 2]
    assertTrue (decide (typedLetReturnTreeFuelBound source.value.body = bound) && (inputs.checkTypedLetReturnTree? types owner source.value.body).isNone)
      "numerical bound licensed whole rejected syntax"
    for store in stores do
      if let some choices := script then
        let certificate ← certify inputs.names inputs.environment store source.value.body choices
        have _ := certificate.costed.cost_le_fuelBound
        assertTrue (decide (certificate.cost = 7 ∧ certificate.value = .word (word 9))) "raw upper bound required whole acceptance"
      for fuel in [0, 1, bound, bound + 2, 50] do
        have _ := LocalInputs.runTypedLetReturnTree?_eq_none_iff (inputs := inputs) (types := types) (owner := owner)
          (body := source.value.body) (fuel := fuel) (store := store)
        oldShapes inputs source.value.body fuel store
        assertTrue (inputs.runTypedLetReturnTree? types owner fuel source.value.body store).isNone "fuel repaired whole rejection"

end Tests

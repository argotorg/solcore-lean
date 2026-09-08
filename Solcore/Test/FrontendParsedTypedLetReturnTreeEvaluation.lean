import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TypedLetReturnTreeExecutionProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluationProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluationEmbeddingProperties
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties
import Solcore.Frontend.LocalInputsProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties

/-! Actual source-path scripts certify strict old-scope initializers and selected
recursive arms. Independent expected Core, values and costs are not runner output.
The existing runtime entry remains unchanged; no new runner or bound is defined. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetTreeEvaluation", by decide⟩], by decide⟩⟩, 9⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def stores : List Core.Store := [[.word (word 101), .cellRef .word 31],
  [.closure .bool .bool (.var 0) [], .bool false, .word Core.Word.maximum]]
private def actual (content : String) (arguments : List TypedRuntimeArgument) : IO (Syntax.FunctionDecl × LocalInputs) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-let-tree-evaluation.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"function did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "function was diagnosed or incompletely consumed"
  match bound : bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "actual typed arguments did not bind")
  | some inputs =>
      have declared := (bindRuntimeParameters?_sound bound).erase_values
      have _ := declared.complete
      let names := source.value.signature.parameters.elements.filterMap fun parameter => match parameter.value with
        | .typed none name _ => some name.value | _ => none
      assertTrue (decide (inputs.environment.values = arguments.reverse.map (·.value) ∧
        inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
        (declareRuntimeParameters? types owner source.value.signature.parameters.elements).map (fun i => (i.names, i.context.values)) =
          some (inputs.names, inputs.context.values))) "actual source positions, original IDs, values or static factorization changed"
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
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (by simpa only [valueAt] using child.costed)⟩
      | _ => throw (IO.userError "word-not script received a non-Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table environment store left
      let second ← reference table environment store right
      match leftAt : first.value, rightAt : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]
          exact .subtract (by simpa only [leftAt] using first.costed) (by simpa only [rightAt] using second.costed)⟩
      | _, _ => throw (IO.userError "subtraction script received a non-Word")
  | _ => throw (IO.userError "expression is outside the fixture script")
private structure Certificate (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  raw : TypedLetReturnTreeEvaluates owner table environment store source value store
  costed : TypedLetReturnTreeEvaluatesWithCost owner table environment store source value store cost
private structure Leaf (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : ReturnBodyEvaluatesWithCost table environment store source value store cost
private def certify (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) (choices : List Bool) : IO (Certificate table environment store source) := do
  match sourceAt : source with
  | ⟨blockSpan, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let child ← expression table environment store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, child.value) :: environment) store ⟨blockSpan, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by rw [sourceAt]; exact .binding child.costed.erase tail.raw,
        by rw [sourceAt]; exact .binding child.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "missing selected-branch script")
      let guard ← reference table environment store condition
      if agrees : guard.value = .bool choice then
        match choiceAt : choice with
        | true =>
            let child ← certify table environment store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]
              exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed.erase) child.raw,
              by rw [sourceAt]; exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
        | false =>
            let child ← certify table environment store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]
              exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed.erase) child.raw,
              by rw [sourceAt]; exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
      else throw (IO.userError "script disagrees with actual guard")
  | ⟨_, [⟨_, .returnStmt returned⟩]⟩ =>
      assertTrue choices.isEmpty "script continued after return"
      let leaf : Leaf table environment store source ←
        match returnedAt : returned with
        | none => pure ⟨.unit, 1, by rw [sourceAt, returnedAt]; exact .bare⟩
        | some operand => do
            let child ← expression table environment store operand
            pure ⟨child.value, child.cost, by rw [sourceAt, returnedAt]; exact .expression child.costed⟩
      let oldTree := TerminalReturnTreeEvaluatesWithCost.single leaf.costed
      let oldPrefix := TypedLetReturnBodyEvaluatesWithCost.terminal (owner := owner) oldTree
      let oldRaw := TerminalReturnTreeEvaluates.single leaf.costed.erase
      have _ := oldRaw.typedLetReturnTree owner
      have _ := oldTree.typedLetReturnTree owner
      have _ := (TypedLetReturnBodyEvaluates.terminal (owner := owner) oldRaw).returnTree
      have _ := oldPrefix.returnTree
      return ⟨leaf.value, leaf.cost, .single leaf.costed.erase, .single leaf.costed⟩
  | _ => throw (IO.userError "script cannot describe this original body")
termination_by sizeOf source
private theorem arbitraryContinuation {inputs : LocalTypeInputs} {environment : Resolved.Environment}
    {store : Core.Store} {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (certificate : Certificate inputs.names environment store source)
    (accepted : elaborateTypedLetReturnTree? types owner inputs source = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) (continuation : List Core.Frame) :
    Core.Steps certificate.cost ⟨.eval core environment.values, continuation, store⟩ ⟨.ret certificate.value, continuation, store⟩ :=
  certificate.costed.checked_toStepsWithContinuation accepted sameIds continuation
private def checked (source : Syntax.FunctionDecl) (inputs : LocalInputs) (choices : List Bool)
    (expectedCore : Core.Expr) (expected : TypedRuntimeArgument) (cost : Nat) (branchBindings : Bool := true) : IO Unit := do
  have aligned : inputs.environment.ids = inputs.toTypeInputs.context.ids := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
  have environmentTyped : Core.EnvironmentHasTypes inputs.environment.values inputs.toTypeInputs.context.values := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.environmentTyped
  for store in stores do
    let certificate ← certify inputs.toTypeInputs.names inputs.environment store source.value.body choices
    assertTrue (decide (certificate.value = expected.value ∧ certificate.cost = cost)) "independent selected source value/cost changed"
    match accepted : elaborateTypedLetReturnTree? types owner inputs.toTypeInputs source.value.body with
    | none => throw (IO.userError "whole tree rejected")
    | some (core, type) =>
        let typing := elaborateTypedLetReturnTree?_sound accepted
        have _ := typing.evaluates aligned environmentTyped store
        have _ := certificate.raw.preserves_type typing aligned environmentTyped
        have _ := certificate.raw.store_eq
        have _ := certificate.raw.exists_cost
        have _ := typedLetReturnTreeEvaluates_iff_exists_cost.mp certificate.raw
        have _ := certificate.raw.deterministic certificate.costed.erase
        have _ := certificate.costed.store_eq
        have _ := certificate.costed.cost_pos
        have _ := certificate.costed.deterministic certificate.costed
        let bridge := elaborateTypedLetReturnTree?_evaluates_iff accepted aligned
        have _ := bridge.mpr (bridge.mp certificate.raw)
        have _ := certificate.costed.checked_toSteps accepted aligned
        have _ := arbitraryContinuation certificate accepted aligned
        assertTrue (decide (core = expectedCore ∧ type = expected.type ∧ Core.infer? inputs.context.values core = some type ∧
          interpretRuntimeFunctionHeader? types source.value.signature = some type)) "actual accepted Core/type/header changed"
        if branchBindings then assertTrue (compileRuntimeFunction? types owner source).isNone "dynamic theorem expanded the existing entry"
        for fuel in List.range (cost + 3) do
          assertTrue (match Core.runStateful fuel (.initial core inputs.environment.values store) with
            | .done value finalStore => decide (cost ≤ fuel ∧ value = expected.value ∧ finalStore = store)
            | .outOfFuel checkpoint => decide (fuel < cost ∧ checkpoint.store = store)
            | .fault _ _ => false) "exact independent cost threshold, value or own store changed"
        let safe : List Core.Frame := [.letBody (.var 0) [.word (word 17)], .unaryApply .wordNot]
        have _ := arbitraryContinuation certificate accepted aligned safe
        assertTrue (decide (Core.runStateful cost ⟨.eval core inputs.environment.values, safe, store⟩ =
          .outOfFuel ⟨.ret expected.value, safe, store⟩)) "pending continuation was executed or discarded"
        if (Core.UnaryOp.wordNot.apply expected.value).isNone then
          let bad : List Core.Frame := [.unaryApply .wordNot]
          have _ := arbitraryContinuation certificate accepted aligned bad
          assertTrue (decide (Core.runStateful cost ⟨.eval core inputs.environment.values, bad, store⟩ =
            .fault (.invalidUnaryOperand .wordNot expected.value) ⟨.ret expected.value, bad, store⟩)) "zero remaining fuel concealed the incompatible frame"
private def alternating (remaining level : Nat) : String × Core.Expr :=
  match remaining with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 1 else 0))
  | count + 1 =>
      let (tail, core) := alternating count (level + 1)
      let recursiveText := s!"let z{level}: Word=" ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail
      let leafText := s!"let z{level}: Word=y;return z{level};"
      let recCore := Core.Expr.letE (.var (if level = 0 then 1 else 0)) core
      let leafCore := Core.Expr.letE (.var level) (.var 0)
      if level % 2 = 0 then ("if(c){" ++ recursiveText ++ "}else{" ++ leafText ++ "}", .ifE (.var (level + 3)) recCore leafCore)
      else ("if(d){" ++ leafText ++ "}else{" ++ recursiveText ++ "}", .ifE (.var (level + 2)) leafCore recCore)
private theorem initializerRequired {table : LocalNameTable} {environment : Resolved.Environment} {store : Core.Store}
    {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier} {annotation : Syntax.TypeExpr}
    {initializer : Syntax.Expr} {rest : List Syntax.Statement}
    (absent : ¬ ∃ value finalStore, LocalExpressionEvaluates table environment store initializer value finalStore) :
    ¬ ∃ value finalStore, TypedLetReturnTreeEvaluates owner table environment store
      ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore := by
  rintro ⟨value, finalStore, evaluation⟩
  cases evaluation with
  | single child => cases child
  | binding child _ => exact absent ⟨_, _, child⟩
private def boundaries : IO Unit := do
  let (source, inputs) ← actual "function alignment(x: Word,y: Word) returns (Word){let z: Word=x;return y;}" [wordArg 9, wordArg 2]
  let untyped : Resolved.Environment := inputs.environment.map fun row => (row.1, Core.Value.bool true)
  have aligned : untyped.ids = inputs.toTypeInputs.context.ids := by
    simpa only [untyped, Resolved.LocalScope.ids, List.map_map, Function.comp_def, LocalInputs.toTypeInputs_context] using inputs.sameIds
  for store in stores do
    let certificate ← certify inputs.toTypeInputs.names untyped store source.value.body []
    match accepted : elaborateTypedLetReturnTree? types owner inputs.toTypeInputs source.value.body with
    | none => throw (IO.userError "alignment contrast lost static acceptance")
    | some (core, type) =>
        let bridge := elaborateTypedLetReturnTree?_evaluates_iff accepted aligned
        have _ := bridge.mpr (bridge.mp certificate.raw)
        have _ := certificate.costed.checked_toSteps accepted aligned
        assertTrue (decide (core = .letE (.var 1) (.var 1) ∧ type = .word ∧ certificate.value = .bool true ∧ certificate.cost = 4 ∧
          Core.runStateful 4 (.initial core untyped.values store) = .done (.bool true) store)) "aligned raw correspondence demanded runtime typing"
        let reordered : Resolved.Environment := inputs.environment.reverse
        let raw ← certify inputs.names reordered store source.value.body []
        assertTrue (decide (reordered.ids ≠ inputs.context.ids ∧ raw.value = .word (word 2) ∧ raw.cost = 4 ∧
          Core.runStateful 4 (.initial core reordered.values store) = .done (.word (word 9)) store)) "misaligned name lookup became positional lookup"
    match source.value.body with
    | ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some ⟨span, .identifier referenceName⟩)⟩ :: rest⟩ =>
        match named : inputs.names.lookup? referenceName.value with
        | none => throw (IO.userError "strict initializer name disappeared")
        | some id =>
            let missing : Resolved.Environment := inputs.environment.filter (fun row => row.1 != id)
            if absent : missing.lookup? id = none then
              have impossible : ¬ ∃ value finalStore, LocalExpressionEvaluates inputs.names missing store ⟨span, .identifier referenceName⟩ value finalStore := by
                rintro ⟨value, finalStore, evaluated⟩
                cases evaluated with
                | identifier other found =>
                    cases (LocalNameTable.lookup?_iff.mp named).id_unique other
                    have present := Resolved.LocalScope.lookup?_iff.mpr found
                    rw [absent] at present
                    cases present
              have _ := initializerRequired (blockSpan := blockSpan) (letSpan := letSpan) (name := name) (annotation := annotation) (rest := rest) impossible
              let tail ← certify inputs.names missing store ⟨blockSpan, rest⟩ []
              assertTrue (decide (tail.value = .word (word 2) ∧ tail.cost = 1)) "unused initializer strictness contrast lost its successful tail"
            else throw (IO.userError "removed runtime value was still available")
    | _ => throw (IO.userError "strictness contrast lost original initializer syntax")

def frontendParsedTypedLetReturnTreeEvaluationTests : IO Unit := do
  boundaries
  for depth in [0, 1, 2, 5, 12] do
    let (body, core) := alternating depth 0
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs) ← actual ("function alternating(c: Bool,d: Bool,x: Word,y: Word) returns (Word){" ++ body ++ "}")
          [boolArg c, boolArg d, wordArg 9, wordArg 2]
        let choices := if depth = 0 then [] else if !c then [false] else if depth = 1 then [true]
          else if d then [true, true] else (List.range depth).map fun level => level % 2 == 0
        checked source inputs choices core (if depth == 0 || (c && (depth == 1 || !d)) then wordArg 9 else wordArg 2)
          (if depth = 0 then 1 else if !c || depth == 1 then 7 else if d then 13 else 6 * depth + 1) (depth != 0)
  for (x, y) in [(9, 2), (2, 9), (0, Core.Word.maximum.val), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs) ← actual "function asymmetric(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x - y;if(d){let w: Word=z;return ~w;}else{let w: Word=y - z;return w;}}else{let z: Word=y - x;return y;}}"
          [boolArg c, boolArg d, wordArg x, wordArg y]
        checked source inputs (if c then [true, d] else [false]) (.ifE (.var 3)
          (.letE (.binary .wordSub (.var 1) (.var 0)) (.ifE (.var 3) (.letE (.var 0) (.unary .wordNot (.var 0)))
            (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 1)))
          ⟨.word, .word (if c then if d then ((word x).sub (word y)).bitNot else (word y).sub ((word x).sub (word y)) else word y), .word⟩
          (if c then if d then 19 else 21 else 11)
  let left : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let right : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, x, y) in [("Fn", left, right), ("Cell", ⟨.cell .word, .cellRef .word 17, .cellRef⟩, ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
      ("Unit", ⟨.unit, .unit, .unit⟩, ⟨.unit, .unit, .unit⟩)] do
    for c in [false, true] do
      let (source, inputs) ← actual (s!"function opaque(c: Bool,x: {name},y: {name}) returns ({name})" ++ "{if(c){let z: " ++ name ++
        "=x;if(c){let w: " ++ name ++ "=y;return z;}else{return z;}}else{let z: " ++ name ++ "=y;return z;}}") [boolArg c, x, y]
      checked source inputs (if c then [true, true] else [false]) (.ifE (.var 2)
        (.letE (.var 1) (.ifE (.var 3) (.letE (.var 1) (.var 1)) (.var 0))) (.letE (.var 0) (.var 0))) (if c then x else y) (if c then 13 else 7)
  let (bare, bareInputs) ← actual "function bare(c: Bool,x: Word){if(c){let z: Word=x;return;}else{return;}}" [boolArg true, wordArg 9]
  checked bare bareInputs [true] (.ifE (.var 1) (.letE (.var 0) .unit) .unit) ⟨.unit, .unit, .unit⟩ 7
  for (body, expected) in [("{if(c){let z: Unknown=x;return z;}else{return y;}}", 9), ("{if(c){let z: Bool=x;return z;}else{return y;}}", 9),
      ("{if(c){let x: Word=y;return x;}else{return y;}}", 2), ("{if(c){let z: Word=x;return z;}else{let z: Word=missing;return y;}}", 9),
      ("{if(c){let z: Word=x;return z;}else{return c;}}", 9), ("{if(c){let z: Word=x;return z;}else{if(c){return y;}else{return missing;}}}", 9)] do
    let (source, inputs) ← actual ("function raw(c: Bool,x: Word,y: Word) returns (Word)" ++ body) [boolArg true, wordArg 9, wordArg 2]
    for store in stores do
      let certificate ← certify inputs.names inputs.environment store source.value.body [true]
      assertTrue (decide (certificate.cost = 7 ∧ certificate.value = .word (word expected)) &&
        (elaborateTypedLetReturnTree? types owner inputs.toTypeInputs source.value.body).isNone) "raw selected success was mistaken for whole acceptance"

end Tests

import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TypedLetReturnBodyExecutionProperties
import Solcore.Frontend.TypedLetReturnBodyEvaluationProperties
import Solcore.Frontend.TypedLetReturnBodyEvaluationEmbeddingProperties
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties
import Solcore.Frontend.LocalInputsProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties

/-! Actual parsed initializers certify their old-scope values before adding
bindings. Fixture scripts construct source paths, never derive expectations
from Core execution, and distinguish raw success from whole acceptance. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"PrefixEvaluation", by decide⟩], by decide⟩⟩, 9⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def stores : List Core.Store := [[.word (word 101), .cellRef .word 31],
  [.closure .bool .bool (.var 0) [], .bool false, .word Core.Word.maximum]]
private def actual (content : String) (arguments : List TypedRuntimeArgument) : IO (Syntax.FunctionDecl × LocalInputs) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-prefix-evaluation.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "function did not completely parse")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "function was diagnosed or incompletely consumed"
  match bound : bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "actual typed arguments did not bind")
  | some inputs =>
      have declared := (bindRuntimeParameters?_sound bound).erase_values
      have _ := declared.complete
      assertTrue (decide (inputs.environment.values = (arguments.map (·.value)).reverse ∧
        (declareRuntimeParameters? types owner source.value.signature.parameters.elements).map (fun i => (i.names, i.context)) =
          some (inputs.names, inputs.context))) "actual values were reordered or static factorization changed"
      return (source, inputs)

private structure ExprCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table environment store source value store cost
private def reference (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (ExprCertificate table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "script expected an existing source name")
      | some id =>
          match found : environment.lookup? id with
          | none => throw (IO.userError "script expected an existing actual value")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "script expected an actual reference")
private def expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (ExprCertificate table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ => reference table environment store source
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← reference table environment store operand
      match valueAt : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (by simpa only [valueAt] using child.costed)⟩
      | _ => throw (IO.userError "bit-not script expected Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table environment store left
      let second ← reference table environment store right
      match leftAt : first.value, rightAt : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]
          exact .subtract (by simpa only [leftAt] using first.costed) (by simpa only [rightAt] using second.costed)⟩
      | _, _ => throw (IO.userError "ordered subtraction script expected Words")
  | ⟨_, .conditional condition _ left _ _⟩ =>
      let guard ← reference table environment store condition
      let selected ← reference table environment store left
      if agrees : guard.value = .bool true then
        return ⟨selected.value, guard.cost + selected.cost + 2, by rw [sourceAt]; exact .ifTrue (agrees ▸ guard.costed) selected.costed⟩
      else throw (IO.userError "initializer script requires the supplied true branch")
  | _ => throw (IO.userError "initializer is outside the fixture script")

private structure TreeCertificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TerminalReturnTreeEvaluatesWithCost table environment store source value store cost
private def tree (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) (choices : List Bool) : IO (TreeCertificate table environment store source) := do
  match choices, sourceAt : source with
  | [], ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | [], ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table environment store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | choice :: rest, ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let guard ← reference table environment store condition
      if agrees : guard.value = .bool choice then
        match choiceAt : choice with
        | true =>
            let child ← tree table environment store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]
              exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
        | false =>
            let child ← tree table environment store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]
              exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
      else throw (IO.userError "branch script disagrees with the actual guard")
  | _, _ => throw (IO.userError "branch script does not describe the original terminal tree")
termination_by choices.length

private structure Certificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  raw : TypedLetReturnBodyEvaluates owner table environment store source value store
  costed : TypedLetReturnBodyEvaluatesWithCost owner table environment store source value store cost
private def certify (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) (choices : List Bool) : IO (Certificate table environment store source) := do
  match sourceAt : source with
  | ⟨blockSpan, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let child ← expression table environment store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, child.value) :: environment) store ⟨blockSpan, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by rw [sourceAt]; exact .binding child.costed.erase tail.raw,
        by rw [sourceAt]; exact .binding child.costed tail.costed⟩
  | _ =>
      let child ← tree table environment store source choices
      have _ := child.costed.erase.typedLetReturnBody owner
      have _ := child.costed.typedLetReturnBody owner
      return ⟨child.value, child.cost, .terminal child.costed.erase, .terminal child.costed⟩
termination_by source.value.length

private theorem arbitraryContinuation {inputs : LocalTypeInputs} {environment : Resolved.Environment}
    {store : Core.Store} {source : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (certificate : Certificate inputs.names environment store source)
    (accepted : elaborateTypedLetReturnBody? types owner inputs source = some (core, type))
    (sameIds : environment.ids = inputs.context.ids) (continuation : List Core.Frame) :
    Core.Steps certificate.cost ⟨.eval core environment.values, continuation, store⟩
      ⟨.ret certificate.value, continuation, store⟩ :=
  certificate.costed.checked_toStepsWithContinuation accepted sameIds continuation

private def checked (source : Syntax.FunctionDecl) (inputs : LocalInputs) (choices : List Bool)
    (expected : Core.Expr) (value : Core.Value) (cost : Nat) : IO Unit := do
  have sameIds : inputs.environment.ids = inputs.toTypeInputs.context.ids := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
  have typedEnvironment : Core.EnvironmentHasTypes inputs.environment.values inputs.toTypeInputs.context.values := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.environmentTyped
  have _ := inputs.toTypeInputs.names_ids
  for store in stores do
    let certificate ← certify inputs.toTypeInputs.names inputs.environment store source.value.body choices
    assertTrue (decide (certificate.value = value ∧ certificate.cost = cost)) "independent source value or cost changed"
    match accepted : elaborateTypedLetReturnBody? types owner inputs.toTypeInputs source.value.body with
    | none => throw (IO.userError "whole prefix checking failed")
    | some (core, type) =>
        let typing := elaborateTypedLetReturnBody?_sound accepted
        assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some type)) "old entry rejection was caused by a different header contract"
        have _ := typing.evaluates sameIds typedEnvironment store
        have _ := certificate.raw.preserves_type typing sameIds typedEnvironment
        have _ := certificate.raw.store_eq
        have _ := certificate.raw.exists_cost
        have _ := typedLetReturnBodyEvaluates_iff_exists_cost.mp certificate.raw
        have _ := certificate.raw.deterministic certificate.costed.erase
        have _ := certificate.costed.store_eq
        have _ := certificate.costed.cost_pos
        have _ := certificate.costed.deterministic certificate.costed
        let bridge := elaborateTypedLetReturnBody?_evaluates_iff accepted sameIds
        have _ := bridge.mpr (bridge.mp certificate.raw)
        have _ := certificate.costed.checked_toSteps accepted sameIds
        have _ := arbitraryContinuation certificate accepted sameIds
        assertTrue (decide (core = expected ∧ Core.infer? inputs.context.values core = some type ∧
          Core.runStateful cost (.initial core inputs.environment.values store) = .done value store)) "actual accepted Core lost the certified endpoint"
        let safe : List Core.Frame := [.letBody (.var 0) [.word (word 17)], .unaryApply .wordNot]
        have _ := arbitraryContinuation certificate accepted sameIds safe
        assertTrue (decide (Core.runStateful cost ⟨.eval core inputs.environment.values, safe, store⟩ =
          .outOfFuel ⟨.ret value, safe, store⟩)) "retained continuation was changed or executed"
        if (Core.UnaryOp.wordNot.apply value).isNone then
          let bad : List Core.Frame := [.unaryApply .wordNot]
          have _ := arbitraryContinuation certificate accepted sameIds bad
          assertTrue (decide (Core.runStateful cost ⟨.eval core inputs.environment.values, bad, store⟩ =
            .fault (.invalidUnaryOperand .wordNot value) ⟨.ret value, bad, store⟩)) "zero remaining fuel concealed an incompatible continuation"
    assertTrue (compileRuntimeFunction? types owner source).isNone "body correspondence expanded the old runtime entry"

private theorem initializerRequired {table : LocalNameTable} {environment : Resolved.Environment}
    {store : Core.Store} {blockSpan letSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
    {annotation : Syntax.TypeExpr} {initializer : Syntax.Expr} {rest : List Syntax.Statement}
    (absent : ¬ ∃ value finalStore, LocalExpressionEvaluates table environment store initializer value finalStore) :
    ¬ ∃ value finalStore, TypedLetReturnBodyEvaluates owner table environment store
      ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some initializer)⟩ :: rest⟩ value finalStore := by
  rintro ⟨value, finalStore, evaluation⟩
  cases evaluation with
  | terminal child => cases child with | single returned => cases returned
  | binding child _ => exact absent ⟨_, _, child⟩

private def boundaries : IO Unit := do
  let args : List TypedRuntimeArgument := [⟨.word, .word (word 9), .word⟩, ⟨.word, .word (word 2), .word⟩]
  let (missing, initial) ← actual "function missing(x: Word,r: Word) returns (Word){let z: Word=missing;return x;}" args
  for store in stores do
    match missing.value.body with
    | ⟨blockSpan, ⟨letSpan, .letDecl name (some annotation) (some ⟨span, .identifier referenceName⟩)⟩ :: rest⟩ =>
        if absent : initial.names.lookup? referenceName.value = none then
          have impossible : ¬ ∃ value finalStore, LocalExpressionEvaluates initial.names initial.environment store
              ⟨span, .identifier referenceName⟩ value finalStore := by
            rintro ⟨value, finalStore, evaluated⟩
            cases evaluated with
            | identifier named _ =>
                have found := LocalNameTable.lookup?_iff.mpr named
                rw [absent] at found
                cases found
          have _ := initializerRequired (blockSpan := blockSpan) (letSpan := letSpan)
            (name := name) (annotation := annotation) (rest := rest) impossible
          assertTrue (elaborateTypedLetReturnBody? types owner initial.toTypeInputs missing.value.body).isNone
            "unused missing initializer bypassed whole checking"
        else throw (IO.userError "missing initializer name was unexpectedly bound")
    | _ => throw (IO.userError "strictness fixture lost its actual let/reference syntax")
  let (source, inputs) ← actual "function alignment(x: Word,r: Word) returns (Word){let z: Word=x;return z;}" args
  let untyped : Resolved.Environment := inputs.environment.map fun entry => (entry.1, Core.Value.bool true)
  have aligned : untyped.ids = inputs.toTypeInputs.context.ids := by
    simpa only [untyped, Resolved.LocalScope.ids, List.map_map, Function.comp_def, LocalInputs.toTypeInputs_context] using inputs.sameIds
  for store in stores do
    let certificate ← certify inputs.toTypeInputs.names untyped store source.value.body []
    match accepted : elaborateTypedLetReturnBody? types owner inputs.toTypeInputs source.value.body with
    | none => throw (IO.userError "aligned untyped contrast lost static acceptance")
    | some (core, type) =>
        let bridge := elaborateTypedLetReturnBody?_evaluates_iff accepted aligned
        have _ := bridge.mpr (bridge.mp certificate.raw)
        have _ := certificate.costed.checked_toSteps accepted aligned
        have _ := arbitraryContinuation certificate accepted aligned
        assertTrue (decide (core = .letE (.var 1) (.var 0) ∧ type = .word ∧ certificate.value = .bool true ∧ certificate.cost = 4 ∧
          Core.runStateful 4 (.initial core untyped.values store) = .done (.bool true) store)) "aligned raw bridge inferred runtime typing"
        let reordered : Resolved.Environment := inputs.environment.reverse
        let raw ← certify inputs.names reordered store source.value.body []
        assertTrue (decide (reordered.ids ≠ inputs.context.ids ∧ raw.value = .word (word 9) ∧ raw.cost = 4 ∧
          Core.runStateful 4 (.initial core reordered.values store) = .done (.word (word 2)) store)) "misaligned identities preserved positional meaning"

def frontendParsedTypedLetReturnBodyEvaluationTests : IO Unit := do
  boundaries
  for count in [1, 2, 5, 12] do
    let indices := List.range count
    let declarations := String.join (indices.map fun index => "let z" ++ toString index ++ ": Word=" ++
      (if index = 0 then "x" else s!"z{index - 1}") ++ ";")
    let (source, inputs) ← actual ("function chain(x: Word) returns (Word){" ++ declarations ++ s!"return z{count - 1};" ++ "}")
      [⟨.word, .word (word 9), .word⟩]
    checked source inputs [] (indices.foldr (fun _ tail => Core.Expr.letE (.var 0) tail) (.var 0)) (.word (word 9)) (3 * count + 1)
  for (x, r) in [(word 9, word 2), (Core.Word.zero, Core.Word.maximum), (word (2 ^ 255), word 7)] do
    let args : List TypedRuntimeArgument := [⟨.word, .word x, .word⟩, ⟨.word, .word r, .word⟩]
    for (text, core, value, cost) in [
        ("{let y: Word=x;let z: Word=y - x;return z;}", Core.Expr.letE (.var 1)
          (.letE (.binary .wordSub (.var 0) (.var 2)) (.var 0)), Core.Value.word Core.Word.zero, 11),
        ("{let y: Word=x;let z: Word=y - r;return z;}", .letE (.var 1)
          (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0)), .word (x.sub r), 11),
        ("{let z: Word=x - r;return x;}", .letE (.binary .wordSub (.var 1) (.var 0)) (.var 2), .word x, 8)] do
      let (source, inputs) ← actual ("function ordered(x: Word,r: Word) returns (Word)" ++ text) args
      checked source inputs [] core value cost
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs) ← actual "function asymmetric(c: Bool,d: Bool,x: Word,r: Word) returns (Word){let y: Word=x;if(c){if(d){return ~y;}else{return y - r;}}else{return r;}}"
          ([⟨.bool, .bool c, .bool⟩, ⟨.bool, .bool d, .bool⟩] ++ args)
        checked source inputs (if c then [true, d] else [false]) (.letE (.var 1)
          (.ifE (.var 4) (.ifE (.var 3) (.unary .wordNot (.var 0)) (.binary .wordSub (.var 0) (.var 1))) (.var 1)))
          (.word (if c then if d then x.bitNot else x.sub r else r)) (if c then if d then 12 else 14 else 7)
  let pool : List (String × TypedRuntimeArgument) := [("Cell", ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
    ("Fn", ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩),
    ("Unit", ⟨.unit, .unit, .unit⟩)]
  for (name, argument) in pool do
    let (source, inputs) ← actual (s!"function opaque(x: {name}) returns ({name})" ++ "{let z: " ++ name ++ "=x;return z;}") [argument]
    checked source inputs [] (.letE (.var 0) (.var 0)) argument.value 4
    let (bare, bareInputs) ← actual (s!"function bare(x: {name})" ++ "{let z: " ++ name ++ "=x;return;}") [argument]
    checked bare bareInputs [] (.letE (.var 0) .unit) .unit 4
  let args : List TypedRuntimeArgument := [⟨.word, .word (word 9), .word⟩, ⟨.word, .word (word 2), .word⟩, ⟨.bool, .bool true, .bool⟩]
  for (bodyText, choices, value, cost) in [
      ("{let z: Word=c ? x : missing;return x;}", [], Core.Value.word (word 9), 7),
      ("{let z: Unknown=x;return z;}", [], .word (word 9), 4),
      ("{let z: Bool=x;return z;}", [], .word (word 9), 4),
      ("{let x: Word=r;return x;}", [], .word (word 2), 4),
      ("{let z: Word=x;if(c){if(c){return z;}else{return missing;}}else{return r;}}", [true, true], .word (word 9), 10),
      ("{let z: Word=x;if(c){return z;}else{return c;}}", [true], .word (word 9), 7)] do
    let (source, inputs) ← actual ("function raw(x: Word,r: Word,c: Bool) returns (Word)" ++ bodyText) args
    for store in stores do
      let certificate ← certify inputs.names inputs.environment store source.value.body choices
      have _ := certificate.raw.store_eq
      have _ := certificate.raw.exists_cost
      have _ := certificate.costed.cost_pos
      assertTrue (decide (certificate.value = value ∧ certificate.cost = cost) &&
        (elaborateTypedLetReturnBody? types owner inputs.toTypeInputs source.value.body).isNone) "raw selected path was mistaken for whole acceptance"

end Tests

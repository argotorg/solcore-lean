import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TypedLetReturnBodyFuelBoundProperties
import Solcore.Frontend.TypedLetReturnBodyResumptionProperties
import Solcore.Frontend.TypedLetReturnBodyRunnerEmbeddingProperties
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties
import Solcore.Frontend.RuntimeFunctionCompilation

/-! Independent parsed source certificates meet the actual checked runner.
Every checkpoint is obtained by running its predecessor; no state, actual
argument, binder frame or expected source cost is reconstructed from a result. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"PrefixRunner", by decide⟩], by decide⟩⟩, 17⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def stores : List Core.Store := [[.word (word 101), .cellRef .word 31],
  [.closure .bool .bool (.var 0) [], .bool false, .word Core.Word.maximum]]
private def actual (content : String) (arguments : List TypedRuntimeArgument) : IO (Syntax.FunctionDecl × LocalInputs) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-prefix-runner.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"function did not completely parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "diagnosed or incomplete source"
  match bound : bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "actual typed arguments did not bind")
  | some inputs =>
      have _ := (bindRuntimeParameters?_sound bound).erase_values.complete
      assertTrue (decide (inputs.environment.values = (arguments.map (·.value)).reverse ∧
        (declareRuntimeParameters? types owner source.value.signature.parameters.elements).map (fun i => (i.names, i.context)) =
          some (inputs.names, inputs.context))) "original actual argument order or static factorization changed"
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
      | none => throw (IO.userError "script referenced an unknown name")
      | some id =>
          match found : environment.lookup? id with
          | none => throw (IO.userError "script referenced a missing actual value")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "script expected a source reference")
private def expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (ExprCertificate table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ => reference table environment store source
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← reference table environment store operand
      match atValue : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (atValue ▸ child.costed)⟩
      | _ => throw (IO.userError "bit-not script expected Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table environment store left
      let second ← reference table environment store right
      match leftAt : first.value, rightAt : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]
          exact .subtract (leftAt ▸ first.costed) (rightAt ▸ second.costed)⟩
      | _, _ => throw (IO.userError "ordered subtraction script expected Words")
  | _ => throw (IO.userError "expression outside the bounded certificate vocabulary")

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
              rw [sourceAt]; exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
        | false =>
            let child ← tree table environment store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]; exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
      else throw (IO.userError "choice script disagreed with its actual guard")
  | _, _ => throw (IO.userError "choice script did not end at the actual terminal shape")
termination_by choices.length
private structure Certificate (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnBodyEvaluatesWithCost owner table environment store source value store cost
private def certify (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) (choices : List Bool) : IO (Certificate table environment store source) := do
  match sourceAt : source with
  | ⟨blockSpan, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let child ← expression table environment store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, child.value) :: environment) store ⟨blockSpan, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by rw [sourceAt]; exact .binding child.costed tail.costed⟩
  | _ =>
      let child ← tree table environment store source choices
      return ⟨child.value, child.cost, .terminal child.costed⟩
termination_by source.value.length

private def oldShapes (inputs : LocalInputs) (source : Syntax.Block) (fuel : Nat) (store : Core.Store) : IO Unit := do
  let run := inputs.runTypedLetReturnBody? types owner fuel source store
  match source.value with
  | [⟨returnSpan, .returnStmt returned⟩] =>
      have _ := inputs.runTypedLetReturnBody?_single types owner fuel returned source.span returnSpan store
      assertTrue (decide (run = inputs.runReturnBody? fuel source store)) "old singleton full Option result changed"
  | [⟨ifSpan, .ifThen condition left (some right)⟩] =>
      have _ := inputs.runTypedLetReturnBody?_conditional types owner fuel condition left right source.span ifSpan store
      assertTrue (decide (run = inputs.runTerminalReturnTree? fuel source store)) "old recursive tree full Option result changed"
      match left.value, right.value with
      | [⟨leftReturn, .returnStmt l⟩], [⟨rightReturn, .returnStmt r⟩] =>
          have _ := inputs.runTypedLetReturnBody?_conditional_singletons types owner fuel condition l r
            source.span ifSpan left.span leftReturn right.span rightReturn store
          assertTrue (decide (run = inputs.runConditionalReturnBody? fuel source store)) "old shallow conditional full Option result changed"
      | _, _ => pure ()
  | _ => pure ()

private def checked (inputs : LocalInputs) (source : Syntax.FunctionDecl) (choices : List Bool)
    (expected : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  have aligned : inputs.environment.ids = inputs.toTypeInputs.context.ids := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
  have typed : Core.EnvironmentHasTypes inputs.environment.values inputs.toTypeInputs.context.values := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.environmentTyped
  for store in stores do
    let certificate ← certify inputs.toTypeInputs.names inputs.environment store source.value.body choices
    assertTrue (decide (certificate.value = value ∧ certificate.cost = cost ∧ typedLetReturnBodyFuelBound source.value.body = bound))
      "independent source value, cost or source-only bound changed"
    match accepted : inputs.checkTypedLetReturnBody? types owner source.value.body with
    | none => throw (IO.userError "whole typed-prefix check failed")
    | some (core, actualType) =>
        assertTrue (decide (core = expected ∧ actualType = type ∧ interpretRuntimeFunctionHeader? types source.value.signature = some type))
          "actual checked Core, type or original header changed"
        have _ := certificate.costed.cost_le_fuelBound
        let typing := elaborateTypedLetReturnBody?_sound accepted
        have _ := certificate.costed.checked_runStateful_done_iff (fuel := cost) accepted aligned
        have _ := certificate.costed.checked_runStateful_outOfFuel_iff (fuel := 0) accepted aligned
        have _ := elaborateTypedLetReturnBody?_run_done_iff_cost (initialStore := store) (finalStore := store)
          (value := value) (fuel := cost) accepted aligned
        have _ := LocalInputs.typedLetReturnBody_typed_cost_execution (inputs := inputs) typing store
        have _ := elaborateTypedLetReturnBody?_run_done_of_fuelBound accepted aligned typed store
          (typedLetReturnBodyFuelBound source.value.body) (Nat.le_refl _)
        have _ := LocalInputs.runTypedLetReturnBody?_done_of_fuelBound (inputs := inputs) typing store
          (typedLetReturnBodyFuelBound source.value.body) (Nat.le_refl _)
        let initial := Core.State.initial core inputs.environment.values store
        let run := fun fuel => inputs.runTypedLetReturnBody? types owner fuel source.value.body store
        for fuel in List.range (bound + 3) do
          oldShapes inputs source.value.body fuel store
          have _ := LocalInputs.runTypedLetReturnBody?_never_faults inputs types owner source.value.body fuel store type
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel initial))) "runner replaced Core or reordered actual values"
          match outcome : run fuel with
          | some (resultType, .done result finalStore) =>
              have _ := LocalInputs.runTypedLetReturnBody?_done_iff_typed_cost.mp outcome
              assertTrue (decide (cost ≤ fuel ∧ resultType = type ∧ result = value ∧ finalStore = store)) "completion boundary, value or store changed"
          | some (resultType, .outOfFuel state) =>
              have _ := LocalInputs.runTypedLetReturnBody?_outOfFuel_iff_typed_cost.mp ⟨state, outcome⟩
              assertTrue (decide (fuel < cost ∧ resultType = type ∧ state.store = store)) "exhaustion boundary or store changed"
          | _ => throw (IO.userError "whole typed runner faulted or disappeared")
        for spent in List.range cost do
          match exhausted : run spent with
          | some (checkpointType, .outOfFuel checkpoint) =>
              have _ : spent < certificate.cost ∧ Core.Steps (certificate.cost - spent) checkpoint (.final certificate.value store) := by
                obtain ⟨_, checkedAt, pathAt⟩ := LocalInputs.runTypedLetReturnBody?_eq_some_iff.mp exhausted
                exact certificate.costed.checked_residual_of_outOfFuel checkedAt aligned pathAt
              assertTrue (decide (Core.runStateful 0 checkpoint = .outOfFuel checkpoint)) "actual checkpoint did not retain its complete state"
              for remaining in List.range (cost - spent + 3) do
                have _ := LocalInputs.runTypedLetReturnBody?_resume exhausted remaining
                let resumed := Core.runStateful remaining checkpoint
                assertTrue (decide (run (spent + remaining) = some (checkpointType, resumed))) "full resumption result changed"
                assertTrue (match resumed with
                  | .done result finalStore => decide (cost - spent ≤ remaining ∧ result = value ∧ finalStore = store)
                  | .outOfFuel state => decide (remaining < cost - spent ∧ state.store = store)
                  | _ => false) "residual threshold or retained store changed"
              for middle in List.range (cost - spent) do
                let .outOfFuel second := Core.runStateful middle checkpoint | throw (IO.userError "second genuine checkpoint disappeared")
                for last in List.range (cost - spent - middle + 3) do
                  assertTrue (decide (run (spent + middle + last) = some (type, Core.runStateful last second))) "three genuine chunks changed the full result"
          | _ => throw (IO.userError "expected a genuine checkpoint below the independent cost")
        match core, source.value.body.value with
        | .letE initializerCore tailCore, ⟨_, .letDecl _ (some _) (some initializer)⟩ :: _ =>
            let child ← expression inputs.names inputs.environment store initializer
            let environment := inputs.environment.values
            let pending : Core.State := ⟨.eval initializerCore environment, [.letBody tailCore environment], store⟩
            let retained : Core.State := ⟨.ret child.value, [.letBody tailCore environment], store⟩
            assertTrue (decide (run 1 = some (type, .outOfFuel pending) ∧ run (child.cost + 1) = some (type, .outOfFuel retained) ∧
              run (child.cost + 2) = some (type, .outOfFuel ⟨.eval tailCore (child.value :: environment), [], store⟩))) "initializer once, captured environment or actual bound value changed"
            let some (_, .outOfFuel checkpoint) := run (child.cost + 1) | throw (IO.userError "actual initializer checkpoint disappeared")
            assertTrue (decide (Core.runStateful 0 { checkpoint with continuation := [] } = .done child.value store ∧
              Core.runStateful 0 checkpoint = .outOfFuel checkpoint ∧
              run (cost - (child.cost + 1)) ≠ some (type, Core.runStateful (cost - (child.cost + 1)) checkpoint))) "dropping frames or restarting was mistaken for resumption"
            assertTrue ((inputs.runTerminalReturnTree? bound source.value.body store).isNone &&
              (compileRuntimeFunction? types owner source).isNone) "separate body runner extended old tree or entry policy"
        | _, _ => pure ()

def frontendParsedTypedLetReturnBodyRunnerTests : IO Unit := do
  for count in [1, 2, 5, 12] do
    let indices := List.range count
    let declarations := String.join (indices.map fun index => s!"let z{index}: Word=" ++ (if index = 0 then "x" else s!"z{index - 1}") ++ ";")
    let (source, inputs) ← actual ("function chain(x: Word) returns (Word){" ++ declarations ++ s!"return z{count - 1};" ++ "}") [⟨.word, .word (word 9), .word⟩]
    checked inputs source [] (indices.foldr (fun _ tail => Core.Expr.letE (.var 0) tail) (.var 0)) .word (.word (word 9)) (3 * count + 1) (3 * count + 1)
  for (x, r) in [(word 9, word 2), (Core.Word.zero, Core.Word.maximum), (word (2 ^ 255), word 7)] do
    let args : List TypedRuntimeArgument := [⟨.word, .word x, .word⟩, ⟨.word, .word r, .word⟩]
    for (body, core, value, cost) in [
        ("{let y: Word=x;let z: Word=y - r;return z;}", Core.Expr.letE (.var 1) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0)), Core.Value.word (x.sub r), 11),
        ("{let z: Word=x - r;return x;}", .letE (.binary .wordSub (.var 1) (.var 0)) (.var 2), .word x, 8)] do
      let (source, inputs) ← actual ("function ordered(x: Word,r: Word) returns (Word)" ++ body) args
      checked inputs source [] core .word value cost cost
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs) ← actual "function asymmetric(c: Bool,d: Bool,x: Word,r: Word) returns (Word){let y: Word=x;if(c){if(d){return ~y;}else{return y - r;}}else{return r;}}"
          ([⟨.bool, .bool c, .bool⟩, ⟨.bool, .bool d, .bool⟩] ++ args)
        checked inputs source (if c then [true, d] else [false]) (.letE (.var 1)
          (.ifE (.var 4) (.ifE (.var 3) (.unary .wordNot (.var 0)) (.binary .wordSub (.var 0) (.var 1))) (.var 1))) .word
          (.word (if c then if d then x.bitNot else x.sub r else r)) (if c then if d then 12 else 14 else 7) 14
  for (name, argument) in [("Cell", (⟨.cell .word, .cellRef .word 29, .cellRef⟩ : TypedRuntimeArgument)),
      ("Fn", ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩),
      ("Unit", ⟨.unit, .unit, .unit⟩), ("Bool", ⟨.bool, .bool false, .bool⟩)] do
    let (source, inputs) ← actual (s!"function opaque(x: {name}) returns ({name})" ++ "{let z: " ++ name ++ "=x;return z;}") [argument]
    checked inputs source [] (.letE (.var 0) (.var 0)) argument.type argument.value 4 4
  let args : List TypedRuntimeArgument := [⟨.word, .word (word 9), .word⟩, ⟨.bool, .bool true, .bool⟩]
  for (body, choices, core, type, value, cost) in [
      ("{return x;}", [], Core.Expr.var 1, Core.Ty.word, Core.Value.word (word 9), 1),
      ("{return;}", [], .unit, .unit, .unit, 1),
      ("{if(c){return x;}else{return x;}}", [true], .ifE (.var 0) (.var 1) (.var 1), .word, .word (word 9), 4),
      ("{if(c){if(c){return x;}else{return x;}}else{return x;}}", [true, true], .ifE (.var 0) (.ifE (.var 0) (.var 1) (.var 1)) (.var 1), .word, .word (word 9), 7)] do
    let header := if type = .unit then "" else " returns (Word)"
    let (source, inputs) ← actual ("function old(x: Word,c: Bool)" ++ header ++ body) args
    checked inputs source choices core type value cost cost
  for (body, bound, script) in [("{let z: Unknown=x;return z;}", 4, some []), ("{let z: Bool=x;return z;}", 4, some []),
      ("{let x: Word=x;return x;}", 4, some []), ("{let z: Word=x;if(c){return z;}else{return missing;}}", 7, some [true]),
      ("{let z: Word=missing;return x;}", 4, none), ("{let z=x;return z;}", 0, none), ("{let z: Word;return x;}", 0, none),
      ("{}", 0, none), ("{return x;return x;}", 0, none), ("{return missing;}", 1, none), ("{if(c){return x;}else{return c;}}", 4, none)] do
    let (source, inputs) ← actual ("function rejected(x: Word,c: Bool) returns (Word)" ++ body) args
    assertTrue (typedLetReturnBodyFuelBound source.value.body == bound && (inputs.checkTypedLetReturnBody? types owner source.value.body).isNone)
      "zero or positive numerical bounds licensed a rejected body"
    for store in stores do
      if let some choices := script then
        let raw ← certify inputs.names inputs.environment store source.value.body choices
        have _ := raw.costed.cost_le_fuelBound
        assertTrue (decide (raw.cost = bound ∧ raw.value = .word (word 9))) "raw source-bound law incorrectly needed whole acceptance"
      for fuel in [0, 1, bound, bound + 2, 50] do
        have _ := LocalInputs.runTypedLetReturnBody?_eq_none_iff (inputs := inputs) (types := types) (owner := owner)
          (body := source.value.body) (fuel := fuel) (store := store)
        oldShapes inputs source.value.body fuel store
        assertTrue (inputs.runTypedLetReturnBody? types owner fuel source.value.body store).isNone "generous fuel bypassed whole checking"

end Tests

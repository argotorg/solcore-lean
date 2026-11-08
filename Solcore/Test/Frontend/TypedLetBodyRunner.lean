import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions

/-!
# Typed let body runner tests

The runner on typed let return bodies.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetReturnBodyRunner
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
  let arguments := inputs.bindings.reverse.map (fun row => (⟨row.type, row.value, row.valueTyped⟩ : TypedRuntimeArgument))
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
        assertTrue (decide ((compileRuntimeFunction? types owner source).map (fun compiled =>
          (compiled.core, compiled.returnType, compiled.inputs.names, compiled.inputs.context.values)) =
            some (expected, type, inputs.names, inputs.context.values))) "entry changed exact Core or original parameter-only rows"
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
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel initial) ∧
            runRuntimeFunction? types owner source arguments fuel store = run fuel)) "body or entry replaced Core, reordered actual values or added steps"
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
            assertTrue ((inputs.runTerminalReturnTree? bound source.value.body store).isNone) "entry integration expanded the old tree adapter"
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
end

section
-- leanmerge: from Solcore.Test.FrontendTypedLetReturnBodyRunnerProperties
/-! Independent let chains distinguish actual typed inputs, numerical bounds,
whole acceptance and genuine suspended frames. No runtime value is fabricated. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetReturnBodyRunner

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetRunner", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-runner.sol"⟩, 151, 7⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def binding (name previous : String) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some (ref previous))⟩
private def returned (name : String) : Syntax.Statement := ⟨span, .returnStmt (some (ref name))⟩
private def statements : List String → String → List Syntax.Statement
  | [], previous => [returned previous]
  | name :: rest, previous => binding name previous :: statements rest name
private def chain (names : List String) (previous : String) : Syntax.Block := ⟨span, statements names previous⟩
private def body (twice : Bool) := chain (if twice then ["x", "y"] else ["x"]) "seed"
private def oneCore : Core.Expr := .letE (.var 0) (.var 0)
private def core (twice : Bool) : Core.Expr := if twice then .letE (.var 0) oneCore else oneCore
private def required (twice : Bool) : Nat := if twice then 7 else 4
private def staticInputs (type : Core.Ty) := LocalTypeInputs.empty.bindFresh owner "seed" type
private def table : LocalNameTable := [("seed", id 0)]
private def environment (value : Core.Value) : Resolved.Environment := [(id 0, value)]
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def inputs {type : Core.Ty} (actual : Actual type) :=
  LocalInputs.empty.bindFresh owner "seed" type actual.val actual.property
private theorem elaborated (twice : Bool) (type : Core.Ty) :
    TypedLetReturnBodyElaborates (types type) owner (staticInputs type) (body twice) (core twice) type := by
  cases twice
  · exact .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head))))
  · exact .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.binding (.named .head) (by change "y" ∉ ["x", "seed"]; decide) (.identifier .head) (.var .head) (.var .head)
        (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head)))))
private theorem chainCost (names : List String) (previous : String) (namesTable : LocalNameTable)
    (values : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost namesTable values store (ref previous) value store 1) :
    TypedLetReturnBodyEvaluatesWithCost owner namesTable values store (chain names previous) value store (3 * names.length + 1) := by
  induction names generalizing previous namesTable values with
  | nil => exact .terminal (.single (.expression head))
  | cons name rest ih =>
      have arithmetic : 1 + (3 * rest.length + 1) + 2 = 3 * (name :: rest).length + 1 := by simp; omega
      simpa only [arithmetic, chain, statements, binding] using
        TypedLetReturnBodyEvaluatesWithCost.binding (name := ⟨span, name⟩) (annotation := annotation)
          head (ih name _ _ (.identifier .head .head))
private theorem costed (twice : Bool) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store (body twice) value store (required twice) := by
  cases twice
  · exact chainCost ["x"] "seed" table (environment value) value store (.identifier .head .head)
  · exact chainCost ["x", "y"] "seed" table (environment value) value store (.identifier .head .head)
private theorem chainBound (names : List String) (previous : String) :
    typedLetReturnBodyFuelBound (chain names previous) = 3 * names.length + 1 := by
  induction names generalizing previous with
  | nil => simp [chain, statements, returned, ref, typedLetReturnBodyFuelBound, terminalReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  | cons name rest ih =>
      simp only [chain, statements, binding, typedLetReturnBodyFuelBound, ref, localExpressionFuelBound, List.length_cons]
      have tail := ih name
      simp only [chain] at tail
      rw [tail]; omega
private theorem bounded (twice : Bool) : typedLetReturnBodyFuelBound (body twice) = required twice := by
  cases twice <;> exact chainBound _ _
private theorem runExact {type : Core.Ty} (twice : Bool) (actual : Actual type) (store : Core.Store)
    (fuel : Nat) (result : Core.StatefulRunResult) :
    (inputs actual).runTypedLetReturnBody? (types type) owner fuel (body twice) store = some (type, result) ↔
      Core.runStateful fuel (Core.State.initial (core twice) [actual.val] store) = result := by
  constructor
  · intro observed
    obtain ⟨candidate, checked, ran⟩ := LocalInputs.runTypedLetReturnBody?_eq_some_iff.mp observed
    change elaborateTypedLetReturnBody? (types type) owner (staticInputs type) (body twice) = _ at checked
    rw [(elaborated twice type).complete] at checked
    cases checked
    exact ran
  · intro ran
    exact LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨core twice, (elaborated twice type).complete, ran⟩

theorem arbitrary_raw_lists_have_exact_bounds_without_requiring_fresh_names_or_typed_values
    (names : List String) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store (chain names "seed") value store (3 * names.length + 1) ∧
    typedLetReturnBodyFuelBound (chain names "seed") = 3 * names.length + 1 :=
  ⟨chainCost names "seed" table (environment value) value store (.identifier .head .head), chainBound names "seed"⟩

theorem static_provenance_needs_no_runtime_inhabitant_and_the_old_bound_misses_let_work
    (type : Core.Ty) (twice : Bool) :
    TypedLetReturnBodyElaborates (types type) owner (staticInputs type) (body twice) (core twice) type ∧
    typedLetReturnBodyFuelBound (body twice) = required twice ∧ terminalReturnTreeFuelBound (body twice) = 0 := by
  refine ⟨elaborated twice type, bounded twice, ?_⟩
  cases twice <;> simp [body, chain, statements, binding, terminalReturnTreeFuelBound]

theorem arbitrary_length_accepted_prefixes_use_the_independent_exact_count_at_every_fuel
    {type : Core.Ty} (names : List String) (actual : Actual type) (store : Core.Store) (fuel : Nat)
    (candidate : Core.Expr)
    (accepted : elaborateTypedLetReturnBody? (types type) owner (staticInputs type) (chain names "seed") = some (candidate, type)) :
    ((inputs actual).runTypedLetReturnBody? (types type) owner fuel (chain names "seed") store =
      some (type, .done actual.val store) ↔ 3 * names.length + 1 ≤ fuel) ∧
    ((∃ checkpoint, (inputs actual).runTypedLetReturnBody? (types type) owner fuel (chain names "seed") store =
      some (type, .outOfFuel checkpoint)) ↔ fuel < 3 * names.length + 1) := by
  have count := chainCost names "seed" table (environment actual.val) actual.val store (.identifier .head .head)
  have checked : (inputs actual).checkTypedLetReturnBody? (types type) owner (chain names "seed") = some (candidate, type) := accepted
  have boundaries := And.intro (count.checked_runStateful_done_iff (fuel := fuel) accepted rfl)
    (count.checked_runStateful_outOfFuel_iff (fuel := fuel) accepted rfl)
  simp only [LocalInputs.runTypedLetReturnBody?, checked, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq, true_and]
  exact boundaries

theorem actual_typed_values_determine_all_fuel_thresholds_and_independent_cost_witnesses
    {type : Core.Ty} (twice : Bool) (actual : Actual type) (store : Core.Store) (fuel : Nat) :
    ((inputs actual).runTypedLetReturnBody? (types type) owner fuel (body twice) store = some (type, .done actual.val store) ↔ required twice ≤ fuel) ∧
    ((∃ checkpoint, (inputs actual).runTypedLetReturnBody? (types type) owner fuel (body twice) store =
      some (type, .outOfFuel checkpoint)) ↔ fuel < required twice) ∧
    (Core.runStateful fuel (Core.State.initial (core twice) [actual.val] store) = .done actual.val store ↔
      ∃ cost, TypedLetReturnBodyEvaluatesWithCost owner table (environment actual.val) store (body twice) actual.val store cost ∧ cost ≤ fuel) := by
  have accepted := (elaborated twice type).complete
  refine ⟨(runExact twice actual store fuel _).trans ((costed twice actual.val store).checked_runStateful_done_iff accepted rfl), ?_,
    elaborateTypedLetReturnBody?_run_done_iff_cost (environment := environment actual.val) accepted rfl⟩
  simp only [runExact]
  exact (costed twice actual.val store).checked_runStateful_outOfFuel_iff (fuel := fuel) accepted rfl

theorem both_typed_cost_characterizations_include_whole_typing_and_cannot_report_faults
    {type : Core.Ty} (twice : Bool) (actual : Actual type) (store finalStore : Core.Store)
    (value : Core.Value) (fuel : Nat) (error : Core.MachineFault) (state : Core.State) :
    ((inputs actual).runTypedLetReturnBody? (types type) owner fuel (body twice) store = some (type, .done value finalStore) ↔
      TypedLetReturnBodyHasType (types type) owner (inputs actual).toTypeInputs (body twice) type ∧
      ∃ cost, TypedLetReturnBodyEvaluatesWithCost owner table (environment actual.val) store (body twice) value finalStore cost ∧ cost ≤ fuel) ∧
    ((∃ checkpoint, (inputs actual).runTypedLetReturnBody? (types type) owner fuel (body twice) store = some (type, .outOfFuel checkpoint)) ↔
      TypedLetReturnBodyHasType (types type) owner (inputs actual).toTypeInputs (body twice) type ∧
      ∃ value cost, TypedLetReturnBodyEvaluatesWithCost owner table (environment actual.val) store (body twice) value store cost ∧ fuel < cost) ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner fuel (body twice) store ≠ some (type, .fault error state) :=
  ⟨LocalInputs.runTypedLetReturnBody?_done_iff_typed_cost, LocalInputs.runTypedLetReturnBody?_outOfFuel_iff_typed_cost,
    (inputs actual).runTypedLetReturnBody?_never_faults (types type) owner (body twice) fuel store type error state⟩

theorem actual_typed_existence_and_both_bound_interfaces_keep_the_original_value_and_store
    {type : Core.Ty} (twice : Bool) (actual : Actual type) (store : Core.Store) :
    required twice ≤ typedLetReturnBodyFuelBound (body twice) ∧ Core.ValueHasType actual.val type ∧
    Core.runStateful (required twice) (Core.State.initial (core twice) [actual.val] store) = .done actual.val store ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner (required twice) (body twice) store = some (type, .done actual.val store) := by
  have typing : TypedLetReturnBodyHasType (types type) owner (inputs actual).toTypeInputs (body twice) type := (elaborated twice type).hasType
  obtain ⟨value, cost, evaluation, valueTyped, _⟩ := LocalInputs.typedLetReturnBody_typed_cost_execution typing store
  have same := evaluation.deterministic (costed twice actual.val store)
  obtain ⟨generic, _, genericRun⟩ := elaborateTypedLetReturnBody?_run_done_of_fuelBound (environment := environment actual.val)
    (elaborated twice type).complete rfl (Core.EnvironmentHasTypes.cons actual.property .nil) store (required twice) (by simp only [bounded, Nat.le_refl])
  obtain ⟨wrapped, _, wrappedRun⟩ := LocalInputs.runTypedLetReturnBody?_done_of_fuelBound typing store (required twice) (by simp only [bounded, Nat.le_refl])
  have completed := (actual_typed_values_determine_all_fuel_thresholds_and_independent_cost_witnesses twice actual store _).1.mpr (Nat.le_refl _)
  have machine := (runExact twice actual store _ _).mp completed
  change Core.runStateful (required twice) (Core.State.initial (core twice) [actual.val] store) = _ at genericRun
  rw [machine] at genericRun
  rw [completed] at wrappedRun
  cases genericRun
  cases wrappedRun
  exact ⟨(costed twice actual.val store).cost_le_fuelBound, same.1 ▸ valueTyped, machine, completed⟩

private def firstCheckpoint (twice : Bool) (value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody (if twice then oneCore else .var 0) [value]], store⟩
private def secondCheckpoint (value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody (.var 0) [value, value]], store⟩
theorem genuine_initializer_and_bound_checkpoints_keep_the_captured_and_extended_environments
    {type : Core.Ty} (twice : Bool) (actual : Actual type) (store : Core.Store) :
    (inputs actual).runTypedLetReturnBody? (types type) owner 1 (body twice) store =
      some (type, .outOfFuel ⟨.eval (.var 0) [actual.val], (firstCheckpoint twice actual.val store).continuation, store⟩) ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner 2 (body twice) store = some (type, .outOfFuel (firstCheckpoint twice actual.val store)) ∧
    Core.Steps (required twice - 2) (firstCheckpoint twice actual.val store) (Core.State.final actual.val store) ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner 3 (body twice) store =
      some (type, .outOfFuel ⟨.eval (if twice then oneCore else .var 0) [actual.val, actual.val], [], store⟩) ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner 5 (body true) store = some (type, .outOfFuel (secondCheckpoint actual.val store)) ∧
    Core.Steps 2 (secondCheckpoint actual.val store) (Core.State.final actual.val store) := by
  have first : Core.runStateful 2 (Core.State.initial (core twice) [actual.val] store) = .outOfFuel (firstCheckpoint twice actual.val store) := by cases twice <;> rfl
  have second : Core.runStateful 5 (Core.State.initial (core true) [actual.val] store) = .outOfFuel (secondCheckpoint actual.val store) := rfl
  refine ⟨(runExact twice actual store 1 _).mpr (by cases twice <;> rfl), (runExact twice actual store 2 _).mpr first,
    ((costed twice actual.val store).checked_residual_of_outOfFuel (elaborated twice type).complete rfl first).2,
    (runExact twice actual store 3 _).mpr (by cases twice <;> rfl), (runExact true actual store 5 _).mpr second,
    ((costed true actual.val store).checked_residual_of_outOfFuel (elaborated true type).complete rfl second).2⟩

theorem two_and_three_chunks_resume_real_frames_while_dropping_them_or_restarting_changes_the_result
    {type : Core.Ty} (actual : Actual type) (store : Core.Store) (additional : Nat) :
    Core.runStateful 1 (firstCheckpoint true actual.val store) = .outOfFuel ⟨.eval oneCore [actual.val, actual.val], [], store⟩ ∧
    Core.runStateful 2 ⟨.eval oneCore [actual.val, actual.val], [], store⟩ = .outOfFuel (secondCheckpoint actual.val store) ∧
    Core.runStateful 3 (firstCheckpoint true actual.val store) = .outOfFuel (secondCheckpoint actual.val store) ∧
    Core.runStateful 2 (secondCheckpoint actual.val store) = .done actual.val store ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner (2 + additional) (body true) store =
      some (type, Core.runStateful additional (firstCheckpoint true actual.val store)) ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner (5 + additional) (body true) store =
      some (type, Core.runStateful additional (secondCheckpoint actual.val store)) ∧
    Core.runStateful 0 ⟨.ret actual.val, [], store⟩ = .done actual.val store ∧
    Core.runStateful 0 (secondCheckpoint actual.val store) = .outOfFuel (secondCheckpoint actual.val store) ∧
    Core.runStateful 2 (Core.State.initial (core true) [actual.val] store) ≠ .done actual.val store := by
  have checkpoints := genuine_initializer_and_bound_checkpoints_keep_the_captured_and_extended_environments true actual store
  exact ⟨rfl, rfl, rfl, rfl, LocalInputs.runTypedLetReturnBody?_resume checkpoints.2.1 additional,
    LocalInputs.runTypedLetReturnBody?_resume checkpoints.2.2.2.2.1 additional, rfl, rfl, by intro impossible; cases impossible⟩

theorem existing_cells_and_captured_closures_are_returned_without_store_access_or_invocation
    (location : Core.Location) (word : Core.Word) (store : Core.Store) :
    (inputs (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word))).runTypedLetReturnBody? (types (.cell .word)) owner 7 (body true) store =
      some (.cell .word, .done (.cellRef .word location) store) ∧
    (inputs (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word))).runTypedLetReturnBody?
      (types (.function .bool .word)) owner 7 (body true) store = some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨(runExact true _ store 7 _).mpr rfl, (runExact true _ store 7 _).mpr rfl⟩

theorem unknown_annotations_and_zero_bounds_do_not_turn_raw_paths_into_accepted_safe_runs
    {type : Core.Ty} (actual : Actual type) (store : Core.Store) (fuel : Nat) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment actual.val) store (body false) actual.val store 4 ∧
    typedLetReturnBodyFuelBound (body false) = 4 ∧
    (inputs actual).runTypedLetReturnBody? [] owner fuel (body false) store = none ∧
    typedLetReturnBodyFuelBound ⟨span, []⟩ = 0 ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner fuel ⟨span, []⟩ store = none := by
  refine ⟨costed false actual.val store, bounded false, LocalInputs.runTypedLetReturnBody?_eq_none_iff.mpr ?_, ?_,
    LocalInputs.runTypedLetReturnBody?_eq_none_iff.mpr ?_⟩
  · simp [LocalInputs.checkTypedLetReturnBody?, body, chain, statements, binding, elaborateTypedLetReturnBody?, interpretTypeName?, annotation,
      TypeNameTable.lookup?]
  · simp [typedLetReturnBodyFuelBound, terminalReturnTreeFuelBound]
  · simp [LocalInputs.checkTypedLetReturnBody?, elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?]

private def guarded : Syntax.Block := ⟨span, [binding "x" "seed",
  ⟨span, .ifThen (ref "x") ⟨span, [returned "x"]⟩ (some ⟨span, [returned "x"]⟩)⟩]⟩
private def guardedCore : Core.Expr := .letE (.var 0) (.ifE (.var 0) (.var 0) (.var 0))
private theorem guardedElab : TypedLetReturnBodyElaborates (types .bool) owner (staticInputs .bool) guarded guardedCore .bool :=
  .binding (.named .head) (by decide) (.identifier .head) (.var .head) (.var .head)
    (.terminal (.conditional (.identifier .head) (.var .head) (.var .head)
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))))
theorem accepted_aligned_but_untyped_environments_can_fault_even_at_the_full_bound (word : Core.Word) (store : Core.Store) :
    elaborateTypedLetReturnBody? (types .bool) owner (staticInputs .bool) guarded = some (guardedCore, .bool) ∧
    (environment (.word word)).ids = (staticInputs .bool).context.ids ∧ typedLetReturnBodyFuelBound guarded = 7 ∧
    Core.runStateful 5 (Core.State.initial guardedCore [.word word] store) =
      .fault (.expectedBool (.word word)) ⟨.ret (.word word), [.ifBranches (.var 0) (.var 0) [.word word, .word word]], store⟩ ∧
    Core.runStateful 7 (Core.State.initial guardedCore [.word word] store) =
      .fault (.expectedBool (.word word)) ⟨.ret (.word word), [.ifBranches (.var 0) (.var 0) [.word word, .word word]], store⟩ := by
  refine ⟨guardedElab.complete, rfl, ?_, rfl, rfl⟩
  simp [guarded, binding, returned, ref, typedLetReturnBodyFuelBound, terminalReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]

theorem old_shapes_preserve_the_entire_optional_result_including_failures_and_checkpoints
    (actual : LocalInputs) (typeNames : TypeNameTable) (fuel : Nat) (store : Core.Store)
    (condition : Syntax.Expr) (yes no : Syntax.Block) (yesValue noValue : Option Syntax.Expr) :
    actual.runTypedLetReturnBody? typeNames owner fuel ⟨span, [⟨span, .returnStmt yesValue⟩]⟩ store =
      actual.runReturnBody? fuel ⟨span, [⟨span, .returnStmt yesValue⟩]⟩ store ∧
    actual.runTypedLetReturnBody? typeNames owner fuel ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩ store =
      actual.runTerminalReturnTree? fuel ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩ store ∧
    actual.runTypedLetReturnBody? typeNames owner fuel
        ⟨span, [⟨span, .ifThen condition ⟨span, [⟨span, .returnStmt yesValue⟩]⟩ (some ⟨span, [⟨span, .returnStmt noValue⟩]⟩)⟩]⟩ store =
      actual.runConditionalReturnBody? fuel
        ⟨span, [⟨span, .ifThen condition ⟨span, [⟨span, .returnStmt yesValue⟩]⟩ (some ⟨span, [⟨span, .returnStmt noValue⟩]⟩)⟩]⟩ store :=
  ⟨actual.runTypedLetReturnBody?_single typeNames owner fuel yesValue span span store,
    actual.runTypedLetReturnBody?_conditional typeNames owner fuel condition yes no span span store,
    actual.runTypedLetReturnBody?_conditional_singletons typeNames owner fuel condition yesValue noValue span span span span span span store⟩

end Tests.FrontendTypedLetReturnBodyRunner
end

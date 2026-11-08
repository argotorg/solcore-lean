import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions

/-!
# Typed let body store tests

Stores of typed let return bodies.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetReturnBodyStore
/-! Actual parsed prefixes replay at distinct stores without replacing their
values, identities or source paths. Same control and frames do not identify
complete checkpoints, and each continuation resumes with its own store. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"PrefixStores", by decide⟩], by decide⟩⟩, 17⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def leftStore : Core.Store := [.word (word 101), .cellRef .word 31]
private def rightStore : Core.Store := [.closure .bool .bool (.var 0) [], .bool false, .word Core.Word.maximum]
private def actual (content : String) (arguments : List TypedRuntimeArgument) : IO (Syntax.FunctionDecl × LocalInputs) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-prefix-stores.sol"⟩, content }
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
          some (inputs.names, inputs.context))) "original values, source order or static factorization changed"
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
          rw [sourceAt]; exact .subtract (leftAt ▸ first.costed) (rightAt ▸ second.costed)⟩
      | _, _ => throw (IO.userError "ordered subtraction script expected Words")
  | _ => throw (IO.userError "expression outside the fixture certificate vocabulary")
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
  | _, _ => throw (IO.userError "choice script disagreed with the original terminal shape")
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

private def replay (table : LocalNameTable) (environment : Resolved.Environment) (source : Syntax.Block)
    (choices : List Bool) (value : Core.Value) (cost : Nat) : IO (Certificate table environment leftStore source) := do
  let left ← certify table environment leftStore source choices
  let right ← certify table environment rightStore source choices
  assertTrue (decide (left.value = value ∧ right.value = value ∧ left.cost = cost ∧ right.cost = cost)) "independent source value or cost depended on the store"
  have rawForward := left.costed.erase.change_store rightStore
  have rawBackward := right.costed.erase.change_store leftStore
  have _ := rawForward.deterministic right.costed.erase
  have _ := rawBackward.deterministic left.costed.erase
  have _ := (left.costed.change_store rightStore).deterministic right.costed
  have _ := (right.costed.change_store leftStore).deterministic left.costed
  have _ := (typedLetReturnBodyEvaluates_store_iff (replacement := rightStore)).mpr
    ((typedLetReturnBodyEvaluates_store_iff (replacement := rightStore)).mp left.costed.erase)
  have _ := (typedLetReturnBodyEvaluates_store_iff (replacement := leftStore)).mpr
    ((typedLetReturnBodyEvaluates_store_iff (replacement := leftStore)).mp right.costed.erase)
  have _ := (typedLetReturnBodyEvaluatesWithCost_store_iff (replacement := rightStore)).mpr
    ((typedLetReturnBodyEvaluatesWithCost_store_iff (replacement := rightStore)).mp left.costed)
  have _ := (typedLetReturnBodyEvaluatesWithCost_store_iff (replacement := leftStore)).mpr
    ((typedLetReturnBodyEvaluatesWithCost_store_iff (replacement := leftStore)).mp right.costed)
  have distinct : leftStore ≠ rightStore := by
    intro same
    have lengths := congrArg List.length same
    simp [leftStore, rightStore] at lengths
  have _ : ¬ TypedLetReturnBodyEvaluates owner table environment leftStore source value rightStore := by
    intro wrong
    exact distinct ((typedLetReturnBodyEvaluates_store_iff (replacement := leftStore)).mp wrong).1.symm
  have _ : ¬ TypedLetReturnBodyEvaluatesWithCost owner table environment leftStore source value rightStore cost := by
    intro wrong
    exact distinct ((typedLetReturnBodyEvaluatesWithCost_store_iff (replacement := leftStore)).mp wrong).1.symm
  return left

private def checked (inputs : LocalInputs) (source : Syntax.FunctionDecl) (choices : List Bool)
    (expected : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let arguments := inputs.bindings.reverse.map (fun row => (⟨row.type, row.value, row.valueTyped⟩ : TypedRuntimeArgument))
  let certificate ← replay inputs.toTypeInputs.names inputs.environment source.value.body choices value cost
  match accepted : inputs.checkTypedLetReturnBody? types owner source.value.body with
  | none => throw (IO.userError "whole prefix failed to check")
  | some (core, actualType) =>
      have _ := certificate.costed.cost_le_fuelBound
      assertTrue (decide (core = expected ∧ actualType = type ∧ typedLetReturnBodyFuelBound source.value.body = bound ∧
        interpretRuntimeFunctionHeader? types source.value.signature = some type)) "actual Core, type, bound or header changed"
      let run := fun store fuel => inputs.runTypedLetReturnBody? types owner fuel source.value.body store
      for fuel in List.range (bound + 3) do
        let doneLaw := inputs.runTypedLetReturnBody?_done_store_iff types owner fuel source.value.body leftStore rightStore type value
        let outLaw := inputs.runTypedLetReturnBody?_outOfFuel_store_iff types owner fuel source.value.body leftStore rightStore type
        assertTrue (decide (run leftStore fuel = some (type, Core.runStateful fuel (.initial core inputs.environment.values leftStore)) ∧
          run rightStore fuel = some (type, Core.runStateful fuel (.initial core inputs.environment.values rightStore)) ∧
          runRuntimeFunction? types owner source arguments fuel leftStore = run leftStore fuel ∧
          runRuntimeFunction? types owner source arguments fuel rightStore = run rightStore fuel ∧
          run leftStore fuel ≠ run rightStore fuel)) "store replacement changed execution or erased the result's own store"
        if doneLeft : run leftStore fuel = some (type, .done value leftStore) then
          have rightDone := doneLaw.mp doneLeft
          have _ := doneLaw.mpr rightDone
          assertTrue (decide (cost ≤ fuel ∧ run rightStore fuel = some (type, .done value rightStore))) "completed observations did not retain their own stores"
        else
          match leftAt : run leftStore fuel, rightAt : run rightStore fuel with
          | some (leftType, .outOfFuel left), some (rightType, .outOfFuel right) =>
              if sameType : leftType = type then
                have leftOut : run leftStore fuel = some (type, .outOfFuel left) := by simpa only [sameType] using leftAt
                have rightExists := outLaw.mp ⟨left, leftOut⟩
                have _ := outLaw.mpr rightExists
                assertTrue (decide (fuel < cost ∧ rightType = type ∧ left.control = right.control ∧ left.continuation = right.continuation ∧
                  left.store = leftStore ∧ right.store = rightStore ∧ left ≠ right)) "full checkpoints were equated or their controls, frames or own stores changed"
                for remaining in [0, cost - fuel, cost - fuel + 2] do
                  have _ := LocalInputs.runTypedLetReturnBody?_resume leftOut remaining
                  have _ := LocalInputs.runTypedLetReturnBody?_resume rightAt remaining
                  assertTrue (decide (run leftStore (fuel + remaining) = some (type, Core.runStateful remaining left) ∧
                    run rightStore (fuel + remaining) = some (type, Core.runStateful remaining right))) "a genuine checkpoint resumed with the other store"
                if fuel + 1 < cost then
                  let .outOfFuel nextLeft := Core.runStateful 1 left | throw (IO.userError "left second checkpoint disappeared")
                  let .outOfFuel nextRight := Core.runStateful 1 right | throw (IO.userError "right second checkpoint disappeared")
                  assertTrue (decide (nextLeft.control = nextRight.control ∧ nextLeft.continuation = nextRight.continuation ∧ nextLeft ≠ nextRight ∧
                    Core.runStateful (cost - fuel - 1) nextLeft = .done value leftStore ∧
                    Core.runStateful (cost - fuel - 1) nextRight = .done value rightStore)) "three genuine chunks lost their own store or value"
              else throw (IO.userError "exhaustion changed the checked type")
          | _, _ => throw (IO.userError "store change altered completion, exhaustion or whole acceptance")
      match core, source.value.body.value with
      | .letE initializerCore tailCore, ⟨_, .letDecl _ (some _) (some initializer)⟩ :: _ =>
          for store in [leftStore, rightStore] do
            let child ← expression inputs.names inputs.environment store initializer
            let environment := inputs.environment.values
            assertTrue (decide (run store 1 = some (type, .outOfFuel ⟨.eval initializerCore environment, [.letBody tailCore environment], store⟩) ∧
              run store (child.cost + 1) = some (type, .outOfFuel ⟨.ret child.value, [.letBody tailCore environment], store⟩) ∧
              run store (child.cost + 2) = some (type, .outOfFuel ⟨.eval tailCore (child.value :: environment), [], store⟩))) "initializer or post-binding checkpoint lost original arguments or its own store"
          assertTrue (decide ((compileRuntimeFunction? types owner source).map (fun compiled =>
            (compiled.core, compiled.returnType, compiled.inputs.names, compiled.inputs.context.values)) =
              some (expected, type, inputs.names, inputs.context.values))) "entry changed original parameter rows or independently checked Core"
      | _, _ =>
          for store in [leftStore, rightStore] do
            for fuel in List.range (bound + 3) do
              assertTrue (decide (run store fuel = inputs.runTerminalReturnTree? fuel source.value.body store)) "old tree full Option behavior changed"

def frontendParsedTypedLetReturnBodyStoreTests : IO Unit := do
  assertTrue (decide (leftStore ≠ rightStore ∧ leftStore ≠ [] ∧ rightStore ≠ [])) "store contrast was not distinct and nonempty"
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
      ("{return;}", [], Core.Expr.unit, Core.Ty.unit, Core.Value.unit, 1),
      ("{return x;}", [], .var 1, .word, .word (word 9), 1),
      ("{if(c){if(c){return x;}else{return x;}}else{return x;}}", [true, true], .ifE (.var 0) (.ifE (.var 0) (.var 1) (.var 1)) (.var 1), .word, .word (word 9), 7)] do
    let header := if type = .unit then "" else " returns (Word)"
    let (source, inputs) ← actual ("function old(x: Word,c: Bool)" ++ header ++ body) args
    checked inputs source choices core type value cost cost
  for (body, choices, cost) in [("{let z: Unknown=x;return z;}", [], 4), ("{let z: Bool=x;return z;}", [], 4),
      ("{let x: Word=x;return x;}", [], 4),
      ("{let z: Word=x;if(c){if(c){return z;}else{return missing;}}else{return x;}}", [true, true], 10),
      ("{let z: Word=x;if(c){return z;}else{return c;}}", [true], 7)] do
    let (source, inputs) ← actual ("function rejected(x: Word,c: Bool) returns (Word)" ++ body) args
    let _ ← replay inputs.names inputs.environment source.value.body choices (.word (word 9)) cost
    assertTrue (inputs.checkTypedLetReturnBody? types owner source.value.body).isNone "raw replay licensed whole acceptance"
    for fuel in List.range (typedLetReturnBodyFuelBound source.value.body + 3) do
      have _ := inputs.runTypedLetReturnBody?_done_store_iff types owner fuel source.value.body leftStore rightStore .word (.word (word 9))
      have _ := inputs.runTypedLetReturnBody?_outOfFuel_store_iff types owner fuel source.value.body leftStore rightStore .word
      assertTrue ((inputs.runTypedLetReturnBody? types owner fuel source.value.body leftStore).isNone &&
        (inputs.runTypedLetReturnBody? types owner fuel source.value.body rightStore).isNone) "changing store or fuel repaired rejected source"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendTypedLetReturnBodyStoreProperties
/-! Exact source replay does not identify stores or erase pending work.
Core loads demonstrate why preservation alone cannot establish independence. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetReturnBodyStore

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetStore", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-store.sol"⟩, 163, 9⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def binding (name : String) (value : Syntax.Expr) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some value)⟩
private def returned (value : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some value)⟩]⟩
private def statements : List String → String → List Syntax.Statement
  | [], previous => (returned (ref previous)).value
  | name :: rest, previous => binding name (ref previous) :: statements rest name
private def chain (names : List String) (previous : String) : Syntax.Block := ⟨span, statements names previous⟩
private def seedTable : LocalNameTable := [("seed", id 0)]
private def seedEnv (value : Core.Value) : Resolved.Environment := [(id 0, value)]
private theorem chainCost (names : List String) (previous : String) (table : LocalNameTable)
    (environment : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost table environment store (ref previous) value store 1) :
    TypedLetReturnBodyEvaluatesWithCost owner table environment store (chain names previous) value store (3 * names.length + 1) := by
  induction names generalizing previous table environment with
  | nil => exact .terminal (.single (.expression head))
  | cons name rest ih =>
      have arithmetic : 1 + (3 * rest.length + 1) + 2 = 3 * (name :: rest).length + 1 := by simp; omega
      simpa only [arithmetic, chain, statements, binding] using
        TypedLetReturnBodyEvaluatesWithCost.binding (name := ⟨span, name⟩) (annotation := annotation)
          head (ih name _ _ (.identifier .head .head))

theorem arbitrary_length_raw_paths_replay_actual_values_without_typing_or_name_freshness
    (names : List String) (value : Core.Value) (first replacement : Core.Store) :
    TypedLetReturnBodyEvaluates owner seedTable (seedEnv value) first (chain names "seed") value first ∧
    TypedLetReturnBodyEvaluates owner seedTable (seedEnv value) replacement (chain names "seed") value replacement ∧
    TypedLetReturnBodyEvaluatesWithCost owner seedTable (seedEnv value) replacement (chain names "seed") value replacement (3 * names.length + 1) := by
  have original := chainCost names "seed" seedTable (seedEnv value) value first (.identifier .head .head)
  exact ⟨original.erase, original.erase.change_store replacement, original.change_store replacement⟩

theorem bidirectional_replay_requires_the_claimed_final_store_to_equal_its_own_initial_store
    (names : List String) (actual value : Core.Value) (first finalStore replacement : Core.Store) (cost : Nat) :
    (TypedLetReturnBodyEvaluates owner seedTable (seedEnv actual) first (chain names "seed") value finalStore ↔
      finalStore = first ∧ TypedLetReturnBodyEvaluates owner seedTable (seedEnv actual) replacement (chain names "seed") value replacement) ∧
    (TypedLetReturnBodyEvaluatesWithCost owner seedTable (seedEnv actual) first (chain names "seed") value finalStore cost ↔
      finalStore = first ∧ TypedLetReturnBodyEvaluatesWithCost owner seedTable (seedEnv actual) replacement (chain names "seed") value replacement cost) :=
  ⟨typedLetReturnBodyEvaluates_store_iff, typedLetReturnBodyEvaluatesWithCost_store_iff⟩

theorem replacement_success_cannot_justify_an_incorrect_original_final_store
    (names : List String) (value : Core.Value) (first replacement : Core.Store) (different : replacement ≠ first) :
    TypedLetReturnBodyEvaluates owner seedTable (seedEnv value) replacement (chain names "seed") value replacement ∧
    ¬ TypedLetReturnBodyEvaluates owner seedTable (seedEnv value) first (chain names "seed") value replacement := by
  refine ⟨(chainCost names "seed" seedTable (seedEnv value) value replacement (.identifier .head .head)).erase, ?_⟩
  intro wrong
  exact different ((typedLetReturnBodyEvaluates_store_iff (replacement := replacement)).mp wrong).1

private def subtract (left right : String) : Syntax.Expr := ⟨span, .binary (ref left) ⟨span, .subtract⟩ (ref right)⟩
private def table : LocalNameTable := [("right", id 2), ("left", id 1), ("c", id 0)]
private def staticInputs : LocalTypeInputs :=
  ⟨[⟨"right", id 2, .word⟩, ⟨"left", id 1, .word⟩, ⟨"c", id 0, .bool⟩], by decide⟩
private def environment (choice : Bool) (left right : Core.Word) : Resolved.Environment :=
  [(id 2, .word right), (id 1, .word left), (id 0, .bool choice)]
private def inputs (choice : Bool) (left right : Core.Word) : LocalInputs :=
  ⟨[⟨"right", id 2, .word, .word right, .word⟩, ⟨"left", id 1, .word, .word left, .word⟩,
    ⟨"c", id 0, .bool, .bool choice, .bool⟩], by change [id 2, id 1, id 0].Nodup; decide⟩
private def tailBody : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") (returned (ref "left")) (some (returned (subtract "right" "left")))⟩]⟩
private def body : Syntax.Block := ⟨span, binding "unused" (subtract "left" "right") :: tailBody.value⟩
private def tailCore : Core.Expr := .ifE (.var 3) (.var 2) (.binary .wordSub (.var 1) (.var 2))
private def core : Core.Expr := .letE (.binary .wordSub (.var 1) (.var 0)) tailCore
private def result (choice : Bool) (left right : Core.Word) : Core.Value := .word (if choice then left else right.sub left)
private def required (choice : Bool) : Nat := if choice then 11 else 15
private theorem elaborated : TypedLetReturnBodyElaborates (types .word) owner staticInputs body core .word :=
  .binding (.named .head) (by decide)
    (.subtract (.identifier (.tail (by decide) .head)) (.identifier .head))
    (.binary (.var (.tail (by decide) .head)) (.var .head)) (.binary (.var (.tail (by decide) .head)) (.var .head))
    (.terminal (.conditional (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.single (.expression (.identifier (.tail (by decide) (.tail (by decide) .head)))
        (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) (.tail (by decide) .head)))))
      (.single (.expression (.subtract (.identifier (.tail (by decide) .head)) (.identifier (.tail (by decide) (.tail (by decide) .head))))
        (.binary (.var (.tail (by decide) .head)) (.var (.tail (by decide) (.tail (by decide) .head))))
        (.binary (.var (.tail (by decide) .head)) (.var (.tail (by decide) (.tail (by decide) .head))))))))
private theorem costed (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment choice left right) store body (result choice left right) store (required choice) := by
  have leftC : LocalExpressionEvaluatesWithCost table (environment choice left right) store (ref "left") (.word left) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have rightC : LocalExpressionEvaluatesWithCost table (environment choice left right) store (ref "right") (.word right) store 1 := .identifier .head .head
  have initial : LocalExpressionEvaluatesWithCost table (environment choice left right) store (subtract "left" "right") (.word (left.sub right)) store 5 :=
    .subtract leftC rightC
  have c : LocalExpressionEvaluatesWithCost (("unused", id 3) :: table) ((id 3, .word (left.sub right)) :: environment choice left right)
      store (ref "c") (.bool choice) store 1 :=
    .identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
  have l : LocalExpressionEvaluatesWithCost (("unused", id 3) :: table) ((id 3, .word (left.sub right)) :: environment choice left right)
      store (ref "left") (.word left) store 1 := .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
  have r : LocalExpressionEvaluatesWithCost (("unused", id 3) :: table) ((id 3, .word (left.sub right)) :: environment choice left right)
      store (ref "right") (.word right) store 1 := .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  cases choice
  · exact TypedLetReturnBodyEvaluatesWithCost.binding (owner := owner) (name := ⟨span, "unused"⟩)
      (annotation := annotation) (tailCost := 8) initial (.terminal (.ifFalse c (.single (.expression (.subtract r l)))))
  · exact TypedLetReturnBodyEvaluatesWithCost.binding (owner := owner) (name := ⟨span, "unused"⟩)
      (annotation := annotation) (tailCost := 4) initial (.terminal (.ifTrue c (.single (.expression l))))
private theorem runExact (choice : Bool) (left right : Core.Word) (store : Core.Store) (fuel : Nat) (observed : Core.StatefulRunResult)
    (ran : Core.runStateful fuel (Core.State.initial core [.word right, .word left, .bool choice] store) = observed) :
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body store = some (.word, observed) :=
  LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨core, elaborated.complete, ran⟩

theorem unused_noncommutative_initializers_and_asymmetric_arms_retain_their_own_exact_costs
    (choice : Bool) (left right : Core.Word) (first replacement : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment choice left right) first body (result choice left right) first (required choice) ∧
    TypedLetReturnBodyEvaluatesWithCost owner table (environment choice left right) replacement body (result choice left right) replacement (required choice) ∧
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner (required choice) body replacement = some (.word, .done (result choice left right) replacement) :=
  ⟨costed choice left right first, (costed choice left right first).change_store replacement,
    runExact choice left right replacement _ _
      ((((costed choice left right first).change_store replacement).checked_runStateful_done_iff elaborated.complete rfl).mpr (Nat.le_refl _))⟩

theorem actual_typed_same_fuel_observations_replay_values_and_exhaustion_not_complete_states
    (choice : Bool) (left right : Core.Word) (value : Core.Value) (fuel : Nat) (first replacement : Core.Store) :
    ((inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body first = some (.word, .done value first) ↔
      (inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body replacement = some (.word, .done value replacement)) ∧
    ((∃ checkpoint, (inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body first = some (.word, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, (inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body replacement = some (.word, .outOfFuel checkpoint)) :=
  ⟨(inputs choice left right).runTypedLetReturnBody?_done_store_iff (types .word) owner fuel body first replacement .word value,
    (inputs choice left right).runTypedLetReturnBody?_outOfFuel_store_iff (types .word) owner fuel body first replacement .word⟩

theorem independent_eleven_or_fifteen_step_thresholds_hold_at_every_fuel_in_each_store
    (choice : Bool) (left right : Core.Word) (fuel : Nat) (first replacement : Core.Store) :
    ((inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body first =
      some (.word, .done (result choice left right) first) ↔ required choice ≤ fuel) ∧
    ((∃ checkpoint, (inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body replacement =
      some (.word, .outOfFuel checkpoint)) ↔ fuel < required choice) := by
  have checked : (inputs choice left right).checkTypedLetReturnBody? (types .word) owner body = some (core, .word) := elaborated.complete
  simp only [LocalInputs.runTypedLetReturnBody?, checked, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq, true_and]
  exact ⟨(costed choice left right first).checked_runStateful_done_iff elaborated.complete rfl,
    ((costed choice left right first).change_store replacement).checked_runStateful_outOfFuel_iff elaborated.complete rfl⟩

private def initializerCheckpoint (choice : Bool) (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.binaryRight .wordSub (.var 0) [.word right, .word left, .bool choice],
    .letBody tailCore [.word right, .word left, .bool choice]], store⟩
private def tailCheckpoint (choice : Bool) (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (.var 2) (.binary .wordSub (.var 1) (.var 2))
    [.word (left.sub right), .word right, .word left, .bool choice]], store⟩
private theorem initialExhausted (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner 3 body store = some (.word, .outOfFuel (initializerCheckpoint choice left right store)) :=
  runExact choice left right store 3 _ rfl
private theorem tailExhausted (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner 9 body store = some (.word, .outOfFuel (tailCheckpoint choice left right store)) := by
  apply runExact choice left right store 9 _
  cases choice <;> rfl
theorem distinct_nonempty_stores_remain_distinct_in_initializer_and_tail_checkpoints
    (choice : Bool) (left right : Core.Word) (tail : Core.Store) :
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner 3 body (.unit :: tail) =
      some (.word, .outOfFuel (initializerCheckpoint choice left right (.unit :: tail))) ∧
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner 3 body (.bool true :: tail) =
      some (.word, .outOfFuel (initializerCheckpoint choice left right (.bool true :: tail))) ∧
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner 9 body (.unit :: tail) =
      some (.word, .outOfFuel (tailCheckpoint choice left right (.unit :: tail))) ∧
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner 9 body (.bool true :: tail) =
      some (.word, .outOfFuel (tailCheckpoint choice left right (.bool true :: tail))) ∧
    initializerCheckpoint choice left right (.unit :: tail) ≠ initializerCheckpoint choice left right (.bool true :: tail) ∧
    tailCheckpoint choice left right (.unit :: tail) ≠ tailCheckpoint choice left right (.bool true :: tail) := by
  refine ⟨initialExhausted choice left right _, initialExhausted choice left right _,
    tailExhausted choice left right _, tailExhausted choice left right _, ?_, ?_⟩ <;>
    intro same <;> have stored := congrArg Core.State.store same <;> cases stored

theorem each_genuine_checkpoint_resumes_its_own_store_through_the_unused_initializer
    (choice : Bool) (left right : Core.Word) (first replacement : Core.Store) (additional : Nat) :
    Core.runStateful 6 (initializerCheckpoint choice left right first) = .outOfFuel (tailCheckpoint choice left right first) ∧
    Core.runStateful (required choice - 9) (tailCheckpoint choice left right replacement) = .done (result choice left right) replacement ∧
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner (3 + additional) body first =
      some (.word, Core.runStateful additional (initializerCheckpoint choice left right first)) ∧
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner (9 + additional) body replacement =
      some (.word, Core.runStateful additional (tailCheckpoint choice left right replacement)) :=
  ⟨by cases choice <;> rfl, by cases choice <;> rfl,
    LocalInputs.runTypedLetReturnBody?_resume (initialExhausted choice left right first) additional,
    LocalInputs.runTypedLetReturnBody?_resume (tailExhausted choice left right replacement) additional⟩

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def seedInputs {type : Core.Ty} (actual : Actual type) := LocalInputs.empty.bindFresh owner "seed" type actual.val actual.property
private theorem oneElaborated (type : Core.Ty) : TypedLetReturnBodyElaborates (types type) owner
    (LocalTypeInputs.empty.bindFresh owner "seed" type) (chain ["x"] "seed") (.letE (.var 0) (.var 0)) type :=
  .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
    (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head))))
private theorem oneCompleted {type : Core.Ty} (actual : Actual type) (store : Core.Store) :
    (seedInputs actual).runTypedLetReturnBody? (types type) owner 4 (chain ["x"] "seed") store = some (type, .done actual.val store) :=
  LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨_, (oneElaborated type).complete, rfl⟩
theorem actual_cells_and_captured_closures_replay_without_allocation_or_invocation
    (location : Core.Location) (word : Core.Word) (first replacement : Core.Store) :
    (seedInputs (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word))).runTypedLetReturnBody? (types (.cell .word)) owner 4 (chain ["x"] "seed") replacement =
      some (.cell .word, .done (.cellRef .word location) replacement) ∧
    (seedInputs (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word))).runTypedLetReturnBody?
      (types (.function .bool .word)) owner 4 (chain ["x"] "seed") replacement = some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) replacement) :=
  ⟨(LocalInputs.runTypedLetReturnBody?_done_store_iff _ _ owner _ _ first replacement _ _).mp (oneCompleted _ first),
    (LocalInputs.runTypedLetReturnBody?_done_store_iff _ _ owner _ _ first replacement _ _).mp (oneCompleted _ first)⟩

theorem unknown_annotations_replay_raw_but_fail_whole_checking_in_every_store
    {type : Core.Ty} (actual : Actual type) (first replacement : Core.Store) (fuel : Nat) :
    TypedLetReturnBodyEvaluatesWithCost owner seedTable (seedEnv actual.val) replacement (chain ["x"] "seed") actual.val replacement 4 ∧
    (seedInputs actual).runTypedLetReturnBody? [] owner fuel (chain ["x"] "seed") first = none ∧
    (seedInputs actual).runTypedLetReturnBody? [] owner fuel (chain ["x"] "seed") replacement = none := by
  have rejected : (seedInputs actual).checkTypedLetReturnBody? [] owner (chain ["x"] "seed") = none := by
    simp [LocalInputs.checkTypedLetReturnBody?, chain, statements, binding, elaborateTypedLetReturnBody?, interpretTypeName?, annotation, TypeNameTable.lookup?]
  exact ⟨(chainCost ["x"] "seed" seedTable (seedEnv actual.val) actual.val first (.identifier .head .head)).change_store replacement,
    LocalInputs.runTypedLetReturnBody?_eq_none_iff.mpr rejected, LocalInputs.runTypedLetReturnBody?_eq_none_iff.mpr rejected⟩

theorem old_tree_shapes_keep_the_same_store_observation_contract
    (actual : LocalInputs) (typeNames : TypeNameTable) (fuel : Nat) (condition : Syntax.Expr) (yes no : Syntax.Block)
    (first replacement : Core.Store) (type : Core.Ty) (value : Core.Value) :
    (actual.runTypedLetReturnBody? typeNames owner fuel ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩ first = some (type, .done value first) ↔
      actual.runTerminalReturnTree? fuel ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩ replacement = some (type, .done value replacement)) := by
  rw [actual.runTypedLetReturnBody?_conditional]
  exact actual.runTerminalReturnTree?_done_store_iff fuel _ first replacement type value

theorem a_core_load_preserves_each_store_but_cannot_replay_its_original_value_at_another_store
    (left right : Core.Word) (different : left ≠ right) :
    (∀ (before after : Core.Store) (value : Core.Value),
      Core.Evaluates [.cellRef .word 0] before (.loadCell (.var 0)) value after → after = before) ∧
    Core.Evaluates [.cellRef .word 0] [.word left] (.loadCell (.var 0)) (.word left) [.word left] ∧
    Core.Evaluates [.cellRef .word 0] [.word right] (.loadCell (.var 0)) (.word right) [.word right] ∧
    ¬ Core.Evaluates [.cellRef .word 0] [.word right] (.loadCell (.var 0)) (.word left) [.word right] := by
  refine ⟨?_, .loadCell (.var rfl) rfl, .loadCell (.var rfl) rfl, ?_⟩
  · intro before after value evaluation
    cases evaluation with
    | loadCell reference _ => cases reference; rfl
  · intro replay
    have same := (Core.evaluation_deterministic replay (Core.Evaluates.loadCell (.var rfl) rfl)).1
    exact different (Core.Value.word.inj same)

theorem pending_core_loads_can_fault_or_exhaust_at_zero_fuel_depending_on_the_store (word : Core.Word) :
    Core.runStateful 0 ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ ∧
    Core.runStateful 0 ⟨.ret (.cellRef .word 0), [.loadCellApply], [.word word]⟩ =
      .outOfFuel ⟨.ret (.cellRef .word 0), [.loadCellApply], [.word word]⟩ ∧
    Core.runStateful 1 ⟨.ret (.cellRef .word 0), [.loadCellApply], [.word word]⟩ = .done (.word word) [.word word] ∧
    Core.runStateful 4 ⟨.eval (.letE (.var 0) (.var 0)) [.cellRef .word 0], [.loadCellApply], []⟩ =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ := ⟨rfl, rfl, rfl, rfl⟩

end Tests.FrontendTypedLetReturnBodyStore
end

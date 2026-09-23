import Solcore.Syntax.Parser.Function
import Solcore.Frontend.TypedLetReturnBody
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.RuntimeFunction

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

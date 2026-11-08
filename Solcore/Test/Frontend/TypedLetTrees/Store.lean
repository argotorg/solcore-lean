import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Frontend.Fragments.Internal.RuntimeFunctions

/-!
# Typed let tree store tests

Stores of typed let return trees.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetReturnTreeStore
/-! Store replay on actual parsed recursive bodies keeps inputs and source paths
fixed. Independent source certificates precede execution; full checkpoints are
different and resume separately. Pending Core loads lie outside this contract. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetTreeStores", by decide⟩], by decide⟩⟩, 17⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def leftStore : Core.Store := [.word (word 101), .cellRef .word 31]
private def rightStore : Core.Store := [.word (word 202), .bool false, .closure .bool .bool (.var 0) []]
private def actual (content : String) (arguments : List TypedRuntimeArgument) : IO (Syntax.FunctionDecl × LocalInputs × List TypedRuntimeArgument) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-let-tree-stores.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"function did not completely parse: {content}")
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
          some (inputs.names, inputs.context.values))) "original names, IDs, ordered values or static factorization changed"
      return (source, inputs, arguments)
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
private def replay (table : LocalNameTable) (environment : Resolved.Environment) (source : Syntax.Block)
    (choices : List Bool) (value : Core.Value) (cost : Nat) : IO Unit := do
  let left ← certify table environment leftStore source choices
  let right ← certify table environment rightStore source choices
  assertTrue (decide (left.value = value ∧ right.value = value ∧ left.cost = cost ∧ right.cost = cost)) "independent source value or cost depended on store"
  have _ := (left.costed.erase.change_store rightStore).deterministic right.costed.erase
  have _ := (right.costed.erase.change_store leftStore).deterministic left.costed.erase
  have _ := (left.costed.change_store rightStore).deterministic right.costed
  have _ := (right.costed.change_store leftStore).deterministic left.costed
  have _ := (typedLetReturnTreeEvaluates_store_iff (replacement := rightStore)).mpr
    ((typedLetReturnTreeEvaluates_store_iff (replacement := rightStore)).mp left.costed.erase)
  have _ := (typedLetReturnTreeEvaluates_store_iff (replacement := leftStore)).mpr
    ((typedLetReturnTreeEvaluates_store_iff (replacement := leftStore)).mp right.costed.erase)
  have _ := (typedLetReturnTreeEvaluatesWithCost_store_iff (replacement := rightStore)).mpr
    ((typedLetReturnTreeEvaluatesWithCost_store_iff (replacement := rightStore)).mp left.costed)
  have _ := (typedLetReturnTreeEvaluatesWithCost_store_iff (replacement := leftStore)).mpr
    ((typedLetReturnTreeEvaluatesWithCost_store_iff (replacement := leftStore)).mp right.costed)
  have distinct : leftStore ≠ rightStore := by
    intro same
    have lengths := congrArg List.length same
    simp [leftStore, rightStore] at lengths
  have _ : ¬ TypedLetReturnTreeEvaluates owner table environment leftStore source value rightStore := by
    intro wrong
    exact distinct ((typedLetReturnTreeEvaluates_store_iff (replacement := leftStore)).mp wrong).1.symm
  have _ : ¬ TypedLetReturnTreeEvaluatesWithCost owner table environment leftStore source value rightStore cost := by
    intro wrong
    exact distinct ((typedLetReturnTreeEvaluatesWithCost_store_iff (replacement := leftStore)).mp wrong).1.symm
private def checked (source : Syntax.FunctionDecl) (inputs : LocalInputs) (arguments : List TypedRuntimeArgument) (choices : List Bool)
    (core : Core.Expr) (expected : TypedRuntimeArgument) (cost bound : Nat) : IO Unit := do
  replay inputs.names inputs.environment source.value.body choices expected.value cost
  assertTrue (decide (inputs.checkTypedLetReturnTree? types owner source.value.body = some (core, expected.type) ∧
    Core.infer? inputs.context.values core = some expected.type ∧ typedLetReturnTreeFuelBound source.value.body = bound ∧
    interpretRuntimeFunctionHeader? types source.value.signature = some expected.type)) "actual ordered Core, type or maximum bound changed"
  assertTrue (decide ((compileRuntimeFunction? types owner source).map (fun c => (c.core, c.returnType, c.inputs.names, c.inputs.context.values)) =
    some (core, expected.type, inputs.names, inputs.context.values)) && (prepareRuntimeFunction? types owner source arguments).any (fun p =>
      decide (p.core = core ∧ p.returnType = expected.type ∧ p.inputs.names = inputs.names ∧ p.inputs.context.values = inputs.context.values ∧
        p.inputs.environment.values = arguments.reverse.map (·.value)))) "entry changed Core or original actual parameter rows"
  let run := fun store fuel => inputs.runTypedLetReturnTree? types owner fuel source.value.body store
  for fuel in List.range (bound + 3) do
    let doneLaw := inputs.runTypedLetReturnTree?_done_store_iff types owner fuel source.value.body leftStore rightStore expected.type expected.value
    let outLaw := inputs.runTypedLetReturnTree?_outOfFuel_store_iff types owner fuel source.value.body leftStore rightStore expected.type
    assertTrue (decide (run leftStore fuel = some (expected.type, Core.runStateful fuel (.initial core inputs.environment.values leftStore)) ∧
      run rightStore fuel = some (expected.type, Core.runStateful fuel (.initial core inputs.environment.values rightStore)) ∧
      run leftStore fuel ≠ run rightStore fuel ∧
      runRuntimeFunction? types owner source arguments fuel leftStore = run leftStore fuel ∧
      runRuntimeFunction? types owner source arguments fuel rightStore = run rightStore fuel)) "entry/body results erased their own store or differed from actual checked Core"
    if doneLeft : run leftStore fuel = some (expected.type, .done expected.value leftStore) then
      have rightDone := doneLaw.mp doneLeft
      have _ := doneLaw.mpr rightDone
      assertTrue (decide (cost ≤ fuel ∧ run rightStore fuel = some (expected.type, .done expected.value rightStore))) "completion threshold, value or own store changed"
    else
      match leftAt : run leftStore fuel, rightAt : run rightStore fuel with
      | some (leftType, .outOfFuel left), some (rightType, .outOfFuel right) =>
          if sameType : leftType = expected.type then
            have leftOut : run leftStore fuel = some (expected.type, .outOfFuel left) := by simpa only [sameType] using leftAt
            have rightExists := outLaw.mp ⟨left, leftOut⟩
            have _ := outLaw.mpr rightExists
            assertTrue (decide (fuel < cost ∧ rightType = expected.type ∧ left.control = right.control ∧ left.continuation = right.continuation ∧
              left.store = leftStore ∧ right.store = rightStore ∧ left ≠ right)) "full checkpoints were equated or changed control, frames or own store"
            for remaining in List.range (cost - fuel + 3) do
              have _ := LocalInputs.runTypedLetReturnTree?_resume leftOut remaining
              have _ := LocalInputs.runTypedLetReturnTree?_resume rightAt remaining
              assertTrue (decide (run leftStore (fuel + remaining) = some (expected.type, Core.runStateful remaining left) ∧
                run rightStore (fuel + remaining) = some (expected.type, Core.runStateful remaining right))) "own checkpoint replay changed full summed-fuel result"
              if cost - fuel ≤ remaining then
                assertTrue (decide (Core.runStateful remaining left = .done expected.value leftStore ∧
                  Core.runStateful remaining right = .done expected.value rightStore)) "resumed completion forgot independent value or own store"
              else
                match Core.runStateful remaining left, Core.runStateful remaining right with
                | .outOfFuel nextLeft, .outOfFuel nextRight =>
                    assertTrue (decide (nextLeft.store = leftStore ∧ nextRight.store = rightStore ∧ nextLeft ≠ nextRight))
                      "insufficient residual fuel changed exhaustion or its own store"
                | _, _ => throw (IO.userError "residual replay completed before independent cost")
            if fuel + 1 < cost then
              let .outOfFuel secondLeft := Core.runStateful 1 left | throw (IO.userError "left second checkpoint disappeared")
              let .outOfFuel secondRight := Core.runStateful 1 right | throw (IO.userError "right second checkpoint disappeared")
              assertTrue (decide (secondLeft ≠ secondRight ∧ secondLeft.store = leftStore ∧ secondRight.store = rightStore ∧
                Core.runStateful (cost - fuel - 1) secondLeft = .done expected.value leftStore ∧
                Core.runStateful (cost - fuel - 1) secondRight = .done expected.value rightStore)) "extra genuine chunk lost its own store"
          else throw (IO.userError "exhaustion changed checked type")
      | _, _ => throw (IO.userError "store change altered completion, exhaustion or whole acceptance")
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

def frontendParsedTypedLetReturnTreeStoreTests : IO Unit := do
  assertTrue (decide (leftStore ≠ rightStore ∧ leftStore ≠ [] ∧ rightStore ≠ [])) "store contrast was not distinct and nonempty"
  for depth in [1, 2, 5] do
    let (body, core) := alternating depth 0
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs, arguments) ← actual ("function alternating(c: Bool,d: Bool,x: Word,y: Word) returns (Word){" ++ body ++ "}")
          [boolArg c, boolArg d, wordArg 9, wordArg 2]
        let choices := if !c then [false] else if depth = 1 then [true] else if d then [true, true]
          else (List.range depth).map fun level => level % 2 == 0
        checked source inputs arguments choices core (if c && (depth == 1 || !d) then wordArg 9 else wordArg 2)
          (if !c || depth == 1 then 7 else if d then 13 else 6 * depth + 1) (6 * depth + 1)
  for (x, y) in [(9, 2), (2, 9), (0, Core.Word.maximum.val), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs, arguments) ← actual "function asymmetric(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x - y;if(d){let w: Word=z;return ~w;}else{let w: Word=y - z;return w;}}else{let z: Word=y - x;return y;}}"
          [boolArg c, boolArg d, wordArg x, wordArg y]
        checked source inputs arguments (if c then [true, d] else [false]) (.ifE (.var 3)
          (.letE (.binary .wordSub (.var 1) (.var 0)) (.ifE (.var 3) (.letE (.var 0) (.unary .wordNot (.var 0)))
            (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 1)))
          ⟨.word, .word (if c then if d then ((word x).sub (word y)).bitNot else (word y).sub ((word x).sub (word y)) else word y), .word⟩
          (if c then if d then 19 else 21 else 11) 21
  let left : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let right : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, x, y) in [("Fn", left, right), ("Cell", ⟨.cell .word, .cellRef .word 0, .cellRef⟩, ⟨.cell .word, .cellRef .word 9, .cellRef⟩),
      ("Unit", ⟨.unit, .unit, .unit⟩, ⟨.unit, .unit, .unit⟩)] do
    for c in [false, true] do
      let (source, inputs, arguments) ← actual (s!"function opaque(c: Bool,x: {name},y: {name}) returns ({name})" ++ "{if(c){let z: " ++ name ++
        "=x;if(c){let w: " ++ name ++ "=y;return z;}else{return z;}}else{let z: " ++ name ++ "=y;return z;}}") [boolArg c, x, y]
      checked source inputs arguments (if c then [true, true] else [false]) (.ifE (.var 2)
        (.letE (.var 1) (.ifE (.var 3) (.letE (.var 1) (.var 1)) (.var 0))) (.letE (.var 0) (.var 0))) (if c then x else y) (if c then 13 else 7) 13
  for c in [false, true] do
    let (source, inputs, arguments) ← actual "function simple(c: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x;return z;}else{return y;}}" [boolArg c, wordArg 9, wordArg 2]
    let selected := Core.Expr.letE (.var 1) (.var 0)
    checked source inputs arguments [c] (.ifE (.var 2) selected (.var 0)) (if c then wordArg 9 else wordArg 2) (if c then 7 else 4) 7
    if c then
      for store in [leftStore, rightStore] do
        let environment := inputs.environment.values
        let frame := Core.Frame.letBody (.var 0) environment
        for (spent, state) in [(2, (⟨.ret (.bool true), [.ifBranches selected (.var 0) environment], store⟩ : Core.State)),
            (4, ⟨.eval (.var 1) environment, [frame], store⟩), (5, ⟨.ret (.word (word 9)), [frame], store⟩),
            (6, ⟨.eval (.var 0) (.word (word 9) :: environment), [], store⟩)] do
          assertTrue (decide (inputs.runTypedLetReturnTree? types owner spent source.value.body store = some (.word, .outOfFuel state)))
            "actual conditional, initializer or bound-tail checkpoint lost original values or own store"
  for (body, expected) in [("{if(c){let z: Unknown=x;return z;}else{return y;}}", 9), ("{if(c){let z: Bool=x;return z;}else{return y;}}", 9),
      ("{if(c){let x: Word=y;return x;}else{return y;}}", 2), ("{if(c){let z: Word=x;return z;}else{let z: Word=missing;return y;}}", 9),
      ("{if(c){let z: Word=x;return z;}else{return c;}}", 9), ("{if(c){let z: Word=x;return z;}else{if(c){return y;}else{return missing;}}}", 9)] do
    let (source, inputs, _) ← actual ("function rejected(c: Bool,x: Word,y: Word) returns (Word)" ++ body) [boolArg true, wordArg 9, wordArg 2]
    replay inputs.names inputs.environment source.value.body [true] (.word (word expected)) 7
    assertTrue (decide (typedLetReturnTreeFuelBound source.value.body = 7) && (inputs.checkTypedLetReturnTree? types owner source.value.body).isNone)
      "raw replay or positive bound licensed whole acceptance"
    for fuel in List.range 10 do
      have _ := inputs.runTypedLetReturnTree?_done_store_iff types owner fuel source.value.body leftStore rightStore .word (.word (word expected))
      have _ := inputs.runTypedLetReturnTree?_outOfFuel_store_iff types owner fuel source.value.body leftStore rightStore .word
      assertTrue ((inputs.runTypedLetReturnTree? types owner fuel source.value.body leftStore).isNone &&
        (inputs.runTypedLetReturnTree? types owner fuel source.value.body rightStore).isNone) "store replacement repaired rejected source"
  let (source, inputs, _) ← actual "function misaligned(x: Word,y: Word) returns (Word){let z: Word=x;return y;}" [wordArg 9, wordArg 2]
  let reordered : Resolved.Environment := inputs.environment.reverse
  replay inputs.names reordered source.value.body [] (.word (word 2)) 4
  assertTrue (decide (reordered.ids ≠ inputs.context.ids ∧ inputs.checkTypedLetReturnTree? types owner source.value.body =
    some (.letE (.var 1) (.var 1), .word))) "raw replay acquired an alignment premise or changed whole checking"
  for store in [leftStore, rightStore] do
    assertTrue (decide (Core.runStateful 4 (.initial (.letE (.var 1) (.var 1)) reordered.values store) = .done (.word (word 9)) store))
      "misaligned Core accidentally matched source lookup replay"
  let pending := fun store => (⟨.ret (.cellRef .word 0), [.loadCellApply], store⟩ : Core.State)
  assertTrue (decide (Core.runStateful 1 (pending leftStore) = .done (.word (word 101)) leftStore ∧
    Core.runStateful 1 (pending rightStore) = .done (.word (word 202)) rightStore ∧
    Core.runStateful 0 (pending leftStore) = .outOfFuel (pending leftStore) ∧
    Core.runStateful 0 (pending []) = .fault (.invalidCellLocation 0) (pending []))) "pending Core load was mistaken for body store replay"
  let (source, inputs, _) ← actual "function pending(c: Bool,x: Cell) returns (Cell){if(c){let z: Cell=x;return z;}else{return x;}}"
    [boolArg true, ⟨.cell .word, .cellRef .word 0, .cellRef⟩]
  let core := Core.Expr.ifE (.var 1) (.letE (.var 0) (.var 0)) (.var 0)
  if accepted : inputs.checkTypedLetReturnTree? types owner source.value.body = some (core, .cell .word) then
    have aligned : inputs.environment.ids = inputs.toTypeInputs.context.ids := by
      simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
    for store in [leftStore, rightStore, []] do
      let certificate ← certify inputs.toTypeInputs.names inputs.environment store source.value.body [true]
      have _ := certificate.costed.checked_toStepsWithContinuation accepted aligned [.loadCellApply]
      assertTrue (decide (certificate.cost = 7 ∧ certificate.value = .cellRef .word 0 ∧
        inputs.runTypedLetReturnTree? types owner 7 source.value.body store = some (.cell .word, .done (.cellRef .word 0) store)))
        "opaque body started reading its referenced cell"
      let retained : Core.State := ⟨.eval core inputs.environment.values, [.loadCellApply], store⟩
      assertTrue (decide (Core.runStateful 7 retained = Core.runStateful 0 (pending store) ∧
        Core.runStateful 8 retained = Core.runStateful 1 (pending store))) "checked continuation endpoint was mistaken for runner replay"
  else throw (IO.userError "pending-load contrast lost actual checked Core")

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendTypedLetReturnTreeStoreProperties
/-! Replay retains values and costs but not the store fields of full results.
Pending loads delimit the claim; they are not part of the source body. -/
set_option autoImplicit false
namespace Tests.FrontendTypedLetReturnTreeStore
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetTreeStore", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-tree-store.sol"⟩, 37, 8⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def binding (name previous : String) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some (ref previous))⟩ :: tail.value⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def zero : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span, .binary zero ⟨span, .equal⟩ zero⟩
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => binding name previous (branch guard (tree rest name) (returned name))
private def seedTable : LocalNameTable := [("seed", id 0)]
private def unaligned (value decoy : Core.Value) : Resolved.Environment := [(id 9, decoy), (id 0, value)]
private theorem treeCost (names : List String) (previous : String) (table : LocalNameTable)
    (environment : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost table environment store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment store (tree names previous) value store (10 * names.length + 1) := by
  induction names generalizing previous table environment with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
    have arithmetic : 1 + (5 + (10 * rest.length + 1) + 2) + 2 = 10 * (name :: rest).length + 1 := by simp; omega
    simpa only [arithmetic, tree, binding, branch, guard, zero] using TypedLetReturnTreeEvaluatesWithCost.binding
      (name := ⟨span, name⟩) (annotation := annotation) head
      (.ifTrue (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)) (ih name _ _ (.identifier .head .head)))
private theorem independent (names : List String) (value decoy : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner seedTable (unaligned value decoy) store (tree names "seed") value store (10 * names.length + 1) :=
  treeCost names "seed" seedTable _ value store (.identifier .head (.tail (by decide) .head))

theorem arbitrary_raw_lists_and_unaligned_values_replay_without_name_or_type_assumptions
    (names : List String) (value decoy : Core.Value) (first replacement : Core.Store) :
    (unaligned value decoy).ids ≠ seedTable.map Prod.snd ∧
    TypedLetReturnTreeEvaluates owner seedTable (unaligned value decoy) first (tree names "seed") value first ∧
    TypedLetReturnTreeEvaluates owner seedTable (unaligned value decoy) replacement (tree names "seed") value replacement ∧
    TypedLetReturnTreeEvaluatesWithCost owner seedTable (unaligned value decoy) replacement (tree names "seed") value replacement (10 * names.length + 1) := by
  have original := independent names value decoy first
  exact ⟨(by intro same; cases same), original.erase, original.erase.change_store replacement, original.change_store replacement⟩

theorem both_replay_equivalences_retain_the_original_final_store_equality
    (names : List String) (actual decoy value : Core.Value) (first finalStore replacement : Core.Store) (cost : Nat) :
    (TypedLetReturnTreeEvaluates owner seedTable (unaligned actual decoy) first (tree names "seed") value finalStore ↔
      finalStore = first ∧ TypedLetReturnTreeEvaluates owner seedTable (unaligned actual decoy) replacement (tree names "seed") value replacement) ∧
    (TypedLetReturnTreeEvaluatesWithCost owner seedTable (unaligned actual decoy) first (tree names "seed") value finalStore cost ↔
      finalStore = first ∧ TypedLetReturnTreeEvaluatesWithCost owner seedTable (unaligned actual decoy) replacement (tree names "seed") value replacement cost) :=
  ⟨typedLetReturnTreeEvaluates_store_iff, typedLetReturnTreeEvaluatesWithCost_store_iff⟩

theorem a_replacement_path_cannot_validate_an_arbitrary_original_final_store
    (names : List String) (value decoy : Core.Value) (first replacement : Core.Store) (different : replacement ≠ first) :
    TypedLetReturnTreeEvaluates owner seedTable (unaligned value decoy) replacement (tree names "seed") value replacement ∧
    ¬ TypedLetReturnTreeEvaluates owner seedTable (unaligned value decoy) first (tree names "seed") value replacement ∧
    ¬ TypedLetReturnTreeEvaluatesWithCost owner seedTable (unaligned value decoy) first (tree names "seed") value replacement (10 * names.length + 1) := by
  refine ⟨(independent names value decoy replacement).erase, ?_, ?_⟩
  · intro wrong
    exact different ((typedLetReturnTreeEvaluates_store_iff (replacement := replacement)).mp wrong).1
  · intro wrong
    exact different ((typedLetReturnTreeEvaluatesWithCost_store_iff (replacement := replacement)).mp wrong).1

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def staticInputs (type : Core.Ty) : LocalTypeInputs := ⟨[⟨"seed", id 1, type⟩, ⟨"c", id 0, .bool⟩], by change [id 1, id 0].Nodup; decide⟩
private def inputs {type : Core.Ty} (choice : Bool) (actual : Actual type) : LocalInputs :=
  ⟨[⟨"seed", id 1, type, actual.val, actual.property⟩, ⟨"c", id 0, .bool, .bool choice, .bool⟩], by change [id 1, id 0].Nodup; decide⟩
private def environment (choice : Bool) (value : Core.Value) : Resolved.Environment := [(id 1, value), (id 0, .bool choice)]
private def thenBody := binding "unused" "seed" (returned "seed")
private def body := branch (ref "c") thenBody (returned "seed")
private def core : Core.Expr := .ifE (.var 1) (.letE (.var 0) (.var 1)) (.var 0)
private def required (choice : Bool) : Nat := if choice then 7 else 4
private theorem elaborated (type : Core.Ty) : TypedLetReturnTreeElaborates (types type) owner (staticInputs type) body core type :=
  .conditional (.identifier (.tail (by change "seed" ≠ "c"; decide) .head))
    (.var (.tail (by change id 1 ≠ id 0; decide) .head)) (.var (.tail (by change id 1 ≠ id 0; decide) .head))
    (.binding (.named .head) (by change "unused" ∉ ["seed", "c"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.single (.expression (.identifier (.tail (by change "unused" ≠ "seed"; decide) .head))
        (.var (.tail (by change id 2 ≠ id 1; decide) .head)) (.var (.tail (by change id 2 ≠ id 1; decide) .head)))))
    (.single (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem costed (choice : Bool) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (staticInputs .unit).names (environment choice value) store body value store (required choice) := by
  have c : LocalExpressionEvaluatesWithCost (staticInputs .unit).names (environment choice value) store (ref "c") (.bool choice) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have seed : LocalExpressionEvaluatesWithCost (staticInputs .unit).names (environment choice value) store (ref "seed") value store 1 := .identifier .head .head
  cases choice
  · exact .ifFalse c (.single (.expression seed))
  · have tailSeed : LocalExpressionEvaluatesWithCost (("unused", id 2) :: (staticInputs .unit).names)
        ((id 2, value) :: environment true value) store (ref "seed") value store 1 :=
      .identifier (.tail (by decide) .head) (.tail (by decide) .head)
    exact .ifTrue c (.binding (owner := owner) (name := ⟨span, "unused"⟩) (annotation := annotation) seed (.single (.expression tailSeed)))
private theorem runExact {type : Core.Ty} (choice : Bool) (actual : Actual type) (store : Core.Store) (fuel : Nat)
    (result : Core.StatefulRunResult) (ran : Core.runStateful fuel (Core.State.initial core [actual.val, .bool choice] store) = result) :
    (inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body store = some (type, result) :=
  LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, (elaborated type).complete, ran⟩
private theorem completed {type : Core.Ty} (choice : Bool) (actual : Actual type) (store : Core.Store) :
    (inputs choice actual).runTypedLetReturnTree? (types type) owner (required choice) body store = some (type, .done actual.val store) :=
  runExact choice actual store _ _ (by cases choice <;> rfl)

theorem unused_work_and_asymmetric_selected_costs_replay_at_their_own_stores {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (first replacement : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (staticInputs type).names (environment choice actual.val) first body actual.val first (required choice) ∧
    TypedLetReturnTreeEvaluatesWithCost owner (staticInputs type).names (environment choice actual.val) replacement body actual.val replacement (required choice) ∧
    (inputs choice actual).runTypedLetReturnTree? (types type) owner (required choice) body replacement = some (type, .done actual.val replacement) :=
  ⟨costed choice actual.val first, (costed choice actual.val first).change_store replacement,
    ((inputs choice actual).runTypedLetReturnTree?_done_store_iff (types type) owner _ body first replacement type actual.val).mp (completed choice actual first)⟩

theorem every_fuel_preserves_own_store_observations_and_the_independent_threshold {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (value : Core.Value) (fuel : Nat) (first replacement : Core.Store) :
    ((inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body first = some (type, .done value first) ↔
      (inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body replacement = some (type, .done value replacement)) ∧
    ((∃ checkpoint, (inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body first = some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, (inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body replacement = some (type, .outOfFuel checkpoint)) ∧
    ((inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body first = some (type, .done actual.val first) ↔ required choice ≤ fuel) ∧
    ((∃ checkpoint, (inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body replacement =
      some (type, .outOfFuel checkpoint)) ↔ fuel < required choice) := by
  refine ⟨(inputs choice actual).runTypedLetReturnTree?_done_store_iff (types type) owner fuel body first replacement type value,
    (inputs choice actual).runTypedLetReturnTree?_outOfFuel_store_iff (types type) owner fuel body first replacement type, ?_⟩
  have checked : (inputs choice actual).checkTypedLetReturnTree? (types type) owner body = some (core, type) := (elaborated type).complete
  simp only [LocalInputs.runTypedLetReturnTree?, checked, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq, true_and]
  exact ⟨(costed choice actual.val first).checked_runStateful_done_iff (inputs := staticInputs type) (elaborated type).complete rfl,
    ((costed choice actual.val first).change_store replacement).checked_runStateful_outOfFuel_iff (inputs := staticInputs type) (elaborated type).complete rfl⟩

theorem equal_completed_values_do_not_make_full_results_equal {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (first replacement : Core.Store) (different : first ≠ replacement) :
    (inputs choice actual).runTypedLetReturnTree? (types type) owner (required choice) body first = some (type, .done actual.val first) ∧
    (inputs choice actual).runTypedLetReturnTree? (types type) owner (required choice) body replacement = some (type, .done actual.val replacement) ∧
    (inputs choice actual).runTypedLetReturnTree? (types type) owner (required choice) body first ≠
      (inputs choice actual).runTypedLetReturnTree? (types type) owner (required choice) body replacement := by
  refine ⟨completed choice actual first, completed choice actual replacement, ?_⟩
  rw [completed, completed]
  intro same
  cases same
  exact different rfl

private def ifCheckpoint (value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool true), [.ifBranches (.letE (.var 0) (.var 1)) (.var 0) [value, .bool true]], store⟩
private def initCheckpoint (value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody (.var 1) [value, .bool true]], store⟩
private def tailCheckpoint (value : Core.Value) (store : Core.Store) : Core.State := ⟨.eval (.var 1) [value, value, .bool true], [], store⟩
private theorem ifExhausted {type : Core.Ty} (actual : Actual type) (store : Core.Store) :
    (inputs true actual).runTypedLetReturnTree? (types type) owner 2 body store = some (type, .outOfFuel (ifCheckpoint actual.val store)) := runExact true actual store _ _ rfl
private theorem initExhausted {type : Core.Ty} (actual : Actual type) (store : Core.Store) :
    (inputs true actual).runTypedLetReturnTree? (types type) owner 5 body store = some (type, .outOfFuel (initCheckpoint actual.val store)) := runExact true actual store _ _ rfl

theorem distinct_stores_are_retained_in_conditional_initializer_and_tail_states {type : Core.Ty}
    (actual : Actual type) (first replacement : Core.Store) (different : first ≠ replacement) :
    (inputs true actual).runTypedLetReturnTree? (types type) owner 2 body first = some (type, .outOfFuel (ifCheckpoint actual.val first)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner 2 body replacement = some (type, .outOfFuel (ifCheckpoint actual.val replacement)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner 5 body first = some (type, .outOfFuel (initCheckpoint actual.val first)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner 5 body replacement = some (type, .outOfFuel (initCheckpoint actual.val replacement)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner 6 body first = some (type, .outOfFuel (tailCheckpoint actual.val first)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner 6 body replacement = some (type, .outOfFuel (tailCheckpoint actual.val replacement)) ∧
    ifCheckpoint actual.val first ≠ ifCheckpoint actual.val replacement ∧ initCheckpoint actual.val first ≠ initCheckpoint actual.val replacement ∧
    tailCheckpoint actual.val first ≠ tailCheckpoint actual.val replacement := by
  refine ⟨ifExhausted actual first, ifExhausted actual replacement, initExhausted actual first, initExhausted actual replacement,
    runExact true actual first _ _ rfl, runExact true actual replacement _ _ rfl, ?_, ?_, ?_⟩ <;>
    intro same <;> exact different (congrArg Core.State.store same)

theorem each_genuine_checkpoint_resumes_its_own_store_for_all_additional_fuel {type : Core.Ty}
    (actual : Actual type) (first replacement : Core.Store) (additional : Nat) :
    Core.runStateful 3 (ifCheckpoint actual.val first) = .outOfFuel (initCheckpoint actual.val first) ∧
    Core.runStateful 1 (initCheckpoint actual.val replacement) = .outOfFuel (tailCheckpoint actual.val replacement) ∧
    Core.runStateful 2 (initCheckpoint actual.val replacement) = .done actual.val replacement ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner (2 + additional) body first = some (type, Core.runStateful additional (ifCheckpoint actual.val first)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner (2 + additional) body replacement = some (type, Core.runStateful additional (ifCheckpoint actual.val replacement)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner (5 + additional) body first = some (type, Core.runStateful additional (initCheckpoint actual.val first)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner (5 + additional) body replacement = some (type, Core.runStateful additional (initCheckpoint actual.val replacement)) :=
  ⟨rfl, rfl, rfl, LocalInputs.runTypedLetReturnTree?_resume (ifExhausted actual first) additional,
    LocalInputs.runTypedLetReturnTree?_resume (ifExhausted actual replacement) additional,
    LocalInputs.runTypedLetReturnTree?_resume (initExhausted actual first) additional,
    LocalInputs.runTypedLetReturnTree?_resume (initExhausted actual replacement) additional⟩

theorem opaque_cell_references_and_closures_replay_without_accessing_either_store
    (location : Core.Location) (word : Core.Word) (first replacement : Core.Store) :
    (inputs true (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word))).runTypedLetReturnTree? (types (.cell .word)) owner 7 body replacement =
      some (.cell .word, .done (.cellRef .word location) replacement) ∧
    (inputs true (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word))).runTypedLetReturnTree?
      (types (.function .bool .word)) owner 7 body replacement = some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) replacement) :=
  ⟨(LocalInputs.runTypedLetReturnTree?_done_store_iff _ _ owner _ _ first replacement _ _).mp (completed true _ first),
    (LocalInputs.runTypedLetReturnTree?_done_store_iff _ _ owner _ _ first replacement _ _).mp (completed true _ first)⟩

theorem unknown_annotations_replay_selected_paths_but_fail_whole_checking_in_both_stores {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (first replacement : Core.Store) (fuel : Nat) :
    TypedLetReturnTreeEvaluatesWithCost owner (staticInputs type).names (environment choice actual.val) replacement body actual.val replacement (required choice) ∧
    (inputs choice actual).runTypedLetReturnTree? [] owner fuel body first = none ∧
    (inputs choice actual).runTypedLetReturnTree? [] owner fuel body replacement = none := by
  have rejected : (inputs choice actual).checkTypedLetReturnTree? [] owner body = none := by
    apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
    rintro ⟨_, typing⟩
    cases typing with
    | single child => cases child
    | conditional _ yes _ =>
      cases yes with
      | single child => cases child
      | binding meaning _ _ _ => cases meaning with | named found => cases found
  exact ⟨(costed choice actual.val first).change_store replacement,
    LocalInputs.runTypedLetReturnTree?_eq_none_iff.mpr rejected, LocalInputs.runTypedLetReturnTree?_eq_none_iff.mpr rejected⟩

theorem pending_loads_after_the_same_source_body_can_observe_different_stored_values
    (left right : Core.Word) (different : left ≠ right) (store : Core.Store) :
    (∀ (before after : Core.Store) (value : Core.Value), Core.Evaluates [.cellRef .word 0] before (.loadCell (.var 0)) value after → after = before) ∧
    Core.Steps 7 ⟨.eval core [.cellRef .word 0, .bool true], [.loadCellApply], store⟩ ⟨.ret (.cellRef .word 0), [.loadCellApply], store⟩ ∧
    Core.runStateful 8 ⟨.eval core [.cellRef .word 0, .bool true], [.loadCellApply], [.word left]⟩ = .done (.word left) [.word left] ∧
    Core.runStateful 8 ⟨.eval core [.cellRef .word 0, .bool true], [.loadCellApply], [.word right]⟩ = .done (.word right) [.word right] ∧
    Core.runStateful 8 ⟨.eval core [.cellRef .word 0, .bool true], [.loadCellApply], [.word right]⟩ ≠ .done (.word left) [.word right] := by
  refine ⟨?_, (costed true (.cellRef .word 0) store).checked_toStepsWithContinuation (inputs := staticInputs (.cell .word))
    (elaborated (.cell .word)).complete rfl _, rfl, rfl, ?_⟩
  · intro before after value evaluation
    cases evaluation with
    | loadCell reference _ => cases reference; rfl
  · intro same
    exact different (Core.Value.word.inj (Core.StatefulRunResult.done.inj same).1).symm

theorem zero_fuel_load_faults_and_exhaustion_are_store_dependent_even_after_the_exact_body_path (word : Core.Word) :
    Core.runStateful 0 ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ ∧
    Core.runStateful 0 ⟨.ret (.cellRef .word 0), [.loadCellApply], [.word word]⟩ =
      .outOfFuel ⟨.ret (.cellRef .word 0), [.loadCellApply], [.word word]⟩ ∧
    Core.runStateful 7 ⟨.eval core [.cellRef .word 0, .bool true], [.loadCellApply], []⟩ =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ ∧
    Core.runStateful 7 ⟨.eval core [.cellRef .word 0, .bool true], [.loadCellApply], [.word word]⟩ =
      .outOfFuel ⟨.ret (.cellRef .word 0), [.loadCellApply], [.word word]⟩ := ⟨rfl, rfl, rfl, rfl⟩

end Tests.FrontendTypedLetReturnTreeStore
end

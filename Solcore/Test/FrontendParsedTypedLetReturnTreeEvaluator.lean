import Solcore.Syntax.Parser.Term
import Solcore.Frontend.TypedLetReturnTreeEvaluatorExecutionProperties
import Solcore.Frontend.TypedLetReturnTreeFuelBoundProperties
import Solcore.Frontend.TypedLetReturnTreeResumptionProperties

/-! Completely parsed original blocks, independent raw certificates and separate
Core/value/cost expectations. Direct evaluation neither checks nor changes entry policy. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"DirectTree", by decide⟩], by decide⟩⟩, 17⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .word .word)]
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def inputs (l r : Nat) (c d : Bool) : LocalInputs := ⟨[
  ⟨"c", ⟨owner, 2⟩, .bool, .bool c, .bool⟩, ⟨"d", ⟨other, 999⟩, .bool, .bool d, .bool⟩,
  ⟨"r", ⟨owner, 5⟩, .word, w r, .word⟩, ⟨"l", ⟨owner, 7⟩, .word, w l, .word⟩], by
    change ([⟨owner, 2⟩, ⟨other, 999⟩, ⟨owner, 5⟩, ⟨owner, 7⟩] : List Resolved.LocalId).Nodup
    decide⟩
private def parsed? (content : String) : IO (Option Syntax.Block) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "direct-tree.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed) with
  | .ok body next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      assertTrue (decide (body.span.source = file.id ∧ body.span.startByte = 0 ∧ body.span.endByte = content.utf8ByteSize))
        "original block range changed"
      return some body
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"parser invariant: {reprStr error}")
private def parsed (content : String) : IO Syntax.Block := do
  let some body ← parsed? content | throw (IO.userError s!"incomplete block: {content}")
  return body
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def reference (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "certificate name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "certificate actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "certificate expected original reference")
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ => reference table env store source
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← reference table env store operand
      match atValue : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (atValue ▸ child.costed)⟩
      | _ => throw (IO.userError "certificate expected Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table env store left
      let second ← reference table env store right
      match atLeft : first.value, atRight : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]; exact .subtract (atLeft ▸ first.costed) (atRight ▸ second.costed)⟩
      | _, _ => throw (IO.userError "certificate subtraction expected Words")
  | _ => throw (IO.userError "expression outside independent certificate script")
private structure Certificate (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store body value store cost
private def certify (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (body : Syntax.Block) (choices : List Bool) : IO (Certificate table env store body) := do
  match atBody : body with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let child ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, child.value) :: env) store ⟨span, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by rw [atBody]; exact .binding child.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "independent branch script missing")
      let guard ← reference table env store condition
      if agrees : guard.value = .bool choice then
        match atChoice : choice with
        | true =>
            let child ← certify table env store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifTrue (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
        | false =>
            let child ← certify table env store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifFalse (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
      else throw (IO.userError "independent branch script disagrees with actual guard")
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ =>
      assertTrue choices.isEmpty "script continued past bare return"
      return ⟨.unit, 1, by rw [atBody]; exact .single .bare⟩
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      assertTrue choices.isEmpty "script continued past return"
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [atBody]; exact .single (.expression child.costed)⟩
  | _ => throw (IO.userError "body outside independent certificate script")
termination_by sizeOf body
private def raw (table : LocalNameTable) (env : Resolved.Environment) (body : Syntax.Block)
    (expected : Option (Core.Value × Nat)) (choices : List Bool := []) : IO Unit := do
  assertTrue (decide (evaluateTypedLetReturnTreeWithCost? owner table env body = expected)) "independent raw value/cost disagreed"
  for store in stores do
    match evaluated : evaluateTypedLetReturnTreeWithCost? owner table env body with
    | none => have _ := (evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mp evaluated; pure ()
    | some (_, cost) =>
        let certificate ← certify table env store body choices
        assertTrue (decide (some (certificate.value, certificate.cost) = expected)) "independent original-source certificate disagreed"
        have _ := evaluateTypedLetReturnTreeWithCost?_sound evaluated store
        have _ := evaluateTypedLetReturnTreeWithCost?_complete certificate.costed
        have _ := (evaluateTypedLetReturnTreeWithCost?_iff store).mpr certificate.costed
        have _ := typedLetReturnTreeEvaluatesWithCost_iff_evaluate.mp certificate.costed
        have _ := (evaluateTypedLetReturnTreeWithCost?_exists_cost_iff store).mp ⟨cost, evaluated⟩
        have _ := (evaluateTypedLetReturnTreeWithCost?_value_iff store).mpr certificate.costed.erase
        pure ()
private def checked (content : String) (actual : LocalInputs) (choices : List Bool)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let body ← parsed content
  raw actual.names actual.environment body (some (value, cost)) choices
  assertTrue (decide (actual.checkTypedLetReturnTree? types owner body = some (core, type) ∧
    Core.infer? actual.context.values core = some type)) "independent checked Core/type changed"
  have aligned : actual.environment.ids = actual.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using actual.sameIds
  have envTyped : Core.EnvironmentHasTypes actual.environment.values actual.toTypeInputs.context.values := by
    simpa only [LocalInputs.toTypeInputs_context] using actual.environmentTyped
  match accepted : actual.checkTypedLetReturnTree? types owner body,
      evaluated : evaluateTypedLetReturnTreeWithCost? owner actual.toTypeInputs.names actual.environment body with
  | some (_, actualType), some (found, _) =>
      let typing := elaborateTypedLetReturnTree?_sound accepted
      have _ := elaborateTypedLetReturnTree?_typed_evaluator_exists accepted aligned envTyped
      for store in stores do
        let costed := evaluateTypedLetReturnTreeWithCost?_sound evaluated store
        have _ := costed.cost_le_fuelBound
        have _ := LocalInputs.typedLetReturnTree_evaluator_execution (inputs := actual) typing store
        for continuation in [[], [.letBody (.var 0) [w 17]], [.unaryApply .wordNot]] do
          have _ := evaluateTypedLetReturnTreeWithCost?_checked_toStepsWithContinuation (store := store) evaluated accepted aligned continuation
          pure () -- Retained endpoints do not guarantee that the pending frames succeed.
        let run := fun fuel => actual.runTypedLetReturnTree? types owner fuel body store
        for fuel in List.range (typedLetReturnTreeFuelBound body + 3) do
          have _ := evaluateTypedLetReturnTreeWithCost?_checked_runStateful_done_iff (fuel := fuel) (store := store) evaluated accepted aligned
          have _ := evaluateTypedLetReturnTreeWithCost?_checked_runStateful_outOfFuel_iff (fuel := fuel) (store := store) evaluated accepted aligned
          have _ := elaborateTypedLetReturnTree?_run_done_iff_evaluator (value := found) (fuel := fuel)
            (initialStore := store) (finalStore := store) accepted aligned
          have _ := LocalInputs.runTypedLetReturnTree?_done_iff_evaluator (inputs := actual) (types := types) (owner := owner)
            (body := body) (type := actualType) (value := found) (fuel := fuel) (initialStore := store) (finalStore := store)
          have _ := LocalInputs.runTypedLetReturnTree?_outOfFuel_iff_evaluator (inputs := actual) (types := types) (owner := owner)
            (body := body) (type := actualType) (fuel := fuel) (store := store)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel (.initial core actual.environment.values store)))) "full actual Core result changed"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel state) => decide (fuel < cost ∧ t = type ∧ state.store = store)
            | _ => false) "exact threshold/value/own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              have _ : spent < _ ∧ Core.Steps (_ - spent) checkpoint (.final found store) := by
                obtain ⟨_, checkedAt, pathAt⟩ := LocalInputs.runTypedLetReturnTree?_eq_some_iff.mp exhausted
                exact costed.checked_residual_of_outOfFuel checkedAt aligned pathAt
              for remaining in List.range (cost - spent + 3) do
                have _ := LocalInputs.runTypedLetReturnTree?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "genuine resumption changed full result"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "independent residual cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart impersonated actual checkpoint"
          | _ => throw (IO.userError "genuine checkpoint missing")
  | _, _ => throw (IO.userError "positive whole/raw evidence disappeared")
private def contrast (content : String) (actual : LocalInputs) (expected : Option (Core.Value × Nat))
    (choices : List Bool := []) : IO Unit := do
  let body ← parsed content
  raw actual.names actual.environment body expected choices
  assertTrue (actual.checkTypedLetReturnTree? types owner body).isNone "raw success bypassed whole checking"
  for store in stores do
    for fuel in [0, 30] do assertTrue (actual.runTypedLetReturnTree? types owner fuel body store).isNone "whole rejection exposed a result"
private def spine (remaining level : Nat) : String × Core.Expr :=
  match remaining with
  | 0 => ("return " ++ (if level = 0 then "l" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 3 else 0))
  | count + 1 =>
      let (tail, core) := spine count (level + 1)
      ("if(c){" ++ s!"let z{level}: Word=" ++ (if level = 0 then "l" else s!"z{level - 1}") ++ ";" ++ tail ++
        "}else{" ++ s!"let z{level}: Word=r;return z{level};" ++ "}",
        .ifE (.var level) (.letE (.var (if level = 0 then 3 else 0)) core) (.letE (.var (level + 2)) (.var 0)))
private def checkOpaque (annotation : String) (type : Core.Ty) (x y : Core.Value)
    (typedX : Core.ValueHasType x type) (typedY : Core.ValueHasType y type) : IO Unit := do
  for c in [false, true] do
    let supplied := ((LocalInputs.empty.bindFresh owner "y" type y typedY).bindFresh owner "x" type x typedX).bindFresh other "c" .bool (.bool c) .bool
    let core : Core.Expr := .ifE (.var 0) (.letE (.var 1) (.letE (.var 3) (.var 1))) (.letE (.var 2) (.var 0))
    let value := if c then x else y
    let cost := if c then 10 else 7
    checked ("{if(c){let z: " ++ annotation ++ "=x;let q: " ++ annotation ++ "=y;return z;}else{let z: " ++ annotation ++ "=y;return z;}}")
      supplied [c] core type value cost
    for store in stores do
      let continuation : List Core.Frame := [.unaryApply .wordNot]
      assertTrue (decide (Core.runStateful cost ⟨.eval core supplied.environment.values, continuation, store⟩ =
        .fault (.invalidUnaryOperand .wordNot value) ⟨.ret value, continuation, store⟩))
        "retained endpoint promised success or exhaustion after incompatible pending frames"

def frontendParsedTypedLetReturnTreeEvaluatorTests : IO Unit := do
  for depth in [0, 1, 2, 5, 12] do
    let (content, core) := spine depth 0
    for c in [false, true] do
      checked ("{" ++ content ++ "}") (inputs 9 2 c false) (if depth = 0 then [] else if c then List.replicate depth true else [false])
        core .word (w (if depth = 0 || c then 9 else 2)) (if depth = 0 then 1 else if c then 6 * depth + 1 else 7)
  for (l, r) in [(9, 2), (2, 9), (0, Core.wordModulus - 1), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        checked "{if(c){let z: Word=l - r;if(d){let q: Word=z;return ~q;}else{let q: Word=r - z;return q;}}else{let z: Word=r - l;return r;}}"
          (inputs l r c d) (if c then [true, d] else [false]) (.ifE (.var 0)
            (.letE (.binary .wordSub (.var 3) (.var 2)) (.ifE (.var 2) (.letE (.var 0) (.unary .wordNot (.var 0)))
              (.letE (.binary .wordSub (.var 3) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 2) (.var 3)) (.var 3)))
          .word (if c then if d then w (Core.wordModulus - 1 - (l + Core.wordModulus - r) % Core.wordModulus)
            else w (r + Core.wordModulus - (l + Core.wordModulus - r) % Core.wordModulus) else w r) (if c then if d then 19 else 21 else 11)
  let actual := inputs 9 2 true false
  checked "{return;}" actual [] .unit .unit .unit 1
  checked "{let z: Word=l;return;}" actual [] (.letE (.var 3) .unit) .unit .unit 4
  checked "{let unused: Word=l - r;return r;}" actual [] (.letE (.binary .wordSub (.var 3) (.var 2)) (.var 3)) .word (w 2) 8
  checkOpaque "Cell" (.cell .word) (.cellRef .word 999) (.cellRef .word 40) .cellRef .cellRef
  checkOpaque "Fn" (.function .word .word) (.closure .word .word (.var 0) []) (.closure .word .word (.var 1) [w 7])
    (.closure .nil (.var rfl)) (.closure (.cons .word .nil) (.var rfl))
  checkOpaque "Unit" .unit .unit .unit .unit .unit
  for (content, value, cost, choices) in [("{let z: Unknown=l;return z;}", w 9, 4, []),
      ("{let z: Bool=l;return z;}", w 9, 4, []), ("{let l: Word=r;return l;}", w 2, 4, []),
      ("{let l: Word=l - r;return l;}", w 7, 8, []),
      ("{if(c){let z: Word=l;return z;}else{let z: Unknown=missing;return z;}}", w 9, 7, [true]),
      ("{if(c){return l;}else{return c;}}", w 9, 4, [true])] do contrast content actual (some (value, cost)) choices
  for content in ["{}", "{let z=l;return z;}", "{let z: Word;return l;}", "{let z: Word=l;}",
      "{return l;return r;}", "{if(c){return l;}}", "{if(c){return l;}else{return r;}return l;}",
      "{let z: Word=missing;return r;}", "{let z: Word=z;return l;}", "{let z: Word=f(l);return r;}",
      "{if(l){return l;}else{return r;}}", "{if(c && l){return l;}else{return r;}}"] do contrast content actual none
  let id : Resolved.LocalId := ⟨other, 999⟩
  let fresh : Resolved.LocalId := ⟨owner, 8⟩
  let body ← parsed "{let z: Word=l;return z;}"
  let collision : Resolved.Environment := (fresh, w 99) :: actual.environment
  assertTrue (decide (Resolved.freshLocalId owner (actual.names.map Prod.snd) = fresh ∧
    Resolved.freshLocalId owner collision.ids = ⟨owner, 9⟩ ∧
    Resolved.LocalScope.lookup? ((fresh, w 9) :: collision) fresh = some (w 9))) "allocator used the wrong table or lost its new head"
  raw actual.names collision body (some (w 9, 4))
  assertTrue (decide (collision.ids ≠ actual.context.ids ∧ Core.runStateful 4
    (.initial (.letE (.var 3) (.var 0)) collision.values []) = .done (w 2) [])) "unaligned raw lookup became positional execution"
  raw (("l", id) :: actual.names) ((id, w 4) :: (id, w 9) :: actual.environment) body (some (w 4, 4))
  raw actual.names [] body none
  for store in stores do
    let run := fun fuel => actual.runTypedLetReturnTree? types owner fuel body store
    assertTrue (decide (run 2 = some (.word, .outOfFuel
      ⟨.ret (w 9), [.letBody (.var 0) actual.environment.values], store⟩) ∧
      run 3 = some (.word, .outOfFuel ⟨.eval (.var 0) (w 9 :: actual.environment.values), [], store⟩)))
      "old-scope initializer checkpoint or actual extended tail environment changed"
  let untyped : Resolved.Environment := actual.environment.map fun row => (row.1, Core.Value.bool true)
  have aligned : untyped.ids = actual.toTypeInputs.context.ids := by
    simpa only [untyped, Resolved.LocalScope.ids, List.map_map, Function.comp_def, LocalInputs.toTypeInputs_context] using actual.sameIds
  raw actual.names untyped body (some (.bool true, 4))
  match accepted : actual.checkTypedLetReturnTree? types owner body,
      evaluated : evaluateTypedLetReturnTreeWithCost? owner actual.toTypeInputs.names untyped body with
  | some (core, type), some (_, _) =>
      have _ := evaluateTypedLetReturnTreeWithCost?_checked_runStateful_done_iff (fuel := 4) (store := []) evaluated accepted aligned
      assertTrue (decide (core = .letE (.var 3) (.var 0) ∧ type = .word ∧
        Core.runStateful 4 (.initial core untyped.values []) = .done (.bool true) [])) "aligned raw bridge acquired a runtime typing premise"
  | _, _ => throw (IO.userError "aligned untyped contrast lost whole or raw acceptance")
  let missing ← parsed "{let z: Word=missing;return r;}"
  match missing with
  | ⟨span, _ :: rest⟩ => raw actual.names actual.environment ⟨span, rest⟩ (some (w 2, 1))
  | _ => throw (IO.userError "strict unused initializer contrast lost its successful tail")
  for content in ["{", "{return l;", "{let z: Word=;return z;}", "{if(c){return l;}else", "{return;} trailing"] do
    assertTrue (← parsed? content).isNone "incomplete source acquired raw tree meaning"

end Tests

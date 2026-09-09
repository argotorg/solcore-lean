import Solcore.Syntax.Parser.Term
import Solcore.Frontend.TypedLetReturnTreeRawOwnerProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluatorExecutionProperties
import Solcore.Frontend.TypedLetReturnTreeRunnerOwnerProperties

/-! Original complete blocks and independent raw certificates on arbitrary caller
rows. Owner collapse changes lookup; allocator noncommutation alone says less. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RawTreeOwners", by decide⟩], by decide⟩⟩, 17⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def shift (id : Resolved.DeclarationId) : Resolved.DeclarationId := { id with declarationIndex := id.declarationIndex + 11 }
private theorem shiftInjective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := Nat.add_right_cancel (congrArg Resolved.DeclarationId.declarationIndex same)
  cases left; cases right; cases modules; cases indices; rfl
private theorem shiftNotSurjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨original, same⟩ := onto { owner with declarationIndex := 0 }
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  change original.declarationIndex + 11 = 0 at indices
  omega
private def mapping := ownerLocalIdMap shift
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def inputs (l r : Nat) (c d : Bool) : LocalInputs := ⟨[
  ⟨"c", ⟨owner, 2⟩, .bool, .bool c, .bool⟩, ⟨"d", ⟨other, 999⟩, .bool, .bool d, .bool⟩,
  ⟨"r", ⟨owner, 5⟩, .word, w r, .word⟩, ⟨"l", ⟨owner, 7⟩, .word, w l, .word⟩], by
    change ([⟨owner, 2⟩, ⟨other, 999⟩, ⟨owner, 5⟩, ⟨owner, 7⟩] : List Resolved.LocalId).Nodup
    decide⟩
private def parsed (content : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := { id := ⟨.main, "raw-tree-owners.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok body next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"block did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "incomplete original block"
  assertTrue (decide (body.span.source = file.id ∧ body.span.startByte = 0 ∧ body.span.endByte = content.utf8ByteSize))
    "original block span changed"
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
private structure Certificate (currentOwner : Resolved.DeclarationId) (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost currentOwner table env store body value store cost
private def certify (currentOwner : Resolved.DeclarationId) (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (body : Syntax.Block) (choices : List Bool) : IO (Certificate currentOwner table env store body) := do
  match atBody : body with
  | ⟨span, ⟨_, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      let child ← expression table env store initializer
      let id := Resolved.freshLocalId currentOwner (table.map Prod.snd)
      let tail ← certify currentOwner ((name.value, id) :: table) ((id, child.value) :: env) store ⟨span, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by
        rw [atBody]
        cases annotation with
        | none => exact .inferred child.costed tail.costed
        | some _ => exact .binding child.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "independent branch script missing")
      let guard ← reference table env store condition
      if agrees : guard.value = .bool choice then
        match atChoice : choice with
        | true =>
            let child ← certify currentOwner table env store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifTrue (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
        | false =>
            let child ← certify currentOwner table env store right rest
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
  let mappedTable := LocalNameTable.mapIds mapping table
  let mappedEnv := Resolved.LocalScope.mapIds mapping env
  have same := evaluateTypedLetReturnTreeWithCost?_mapOwner shift shiftInjective owner table env body
  have _ := same.symm
  assertTrue (decide (evaluateTypedLetReturnTreeWithCost? owner table env body = expected ∧
    evaluateTypedLetReturnTreeWithCost? (shift owner) mappedTable mappedEnv body = expected ∧
    mappedEnv.values = env.values ∧ mappedTable.map Prod.fst = table.map Prod.fst))
    "independent raw value/cost or unchanged rows disagreed"
  for store in stores do
    match expected with
    | none =>
        match original : evaluateTypedLetReturnTreeWithCost? owner table env body,
            mapped : evaluateTypedLetReturnTreeWithCost? (shift owner) mappedTable mappedEnv body with
        | none, none =>
            have _ := (evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mp original
            have _ := (evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mp mapped
            pure ()
        | _, _ => throw (IO.userError "raw absence changed under owner relabeling")
    | some (value, cost) =>
        let original ← certify owner table env store body choices
        let mapped ← certify (shift owner) mappedTable mappedEnv store body choices
        assertTrue (decide (original.value = value ∧ mapped.value = value ∧ original.cost = cost ∧ mapped.cost = cost))
          "independent original-AST certificates disagreed"
        have mappedForward := (typedLetReturnTreeEvaluatesWithCost_mapOwner_iff shift shiftInjective).mpr original.costed
        have _ := (typedLetReturnTreeEvaluatesWithCost_mapOwner_iff shift shiftInjective
          (owner := owner) (table := table) (environment := env)).mp mapped.costed
        have _ := (typedLetReturnTreeEvaluates_mapOwner_iff shift shiftInjective).mpr original.costed.erase
        have _ := (typedLetReturnTreeEvaluates_mapOwner_iff shift shiftInjective
          (owner := owner) (table := table) (environment := env)).mp mapped.costed.erase
        have _ := mappedForward.store_eq
        have _ : ¬ TypedLetReturnTreeEvaluatesWithCost (shift owner) mappedTable mappedEnv
            store body value (.unit :: store) cost := by
          intro impossible
          have lengths := congrArg List.length impossible.store_eq
          simp only [List.length_cons] at lengths
          omega
        pure ()
private def spine (remaining level : Nat) : String :=
  match remaining with
  | 0 => "return " ++ (if level = 0 then "l" else s!"z{level - 1}") ++ ";"
  | count + 1 => "if(c){" ++ s!"let z{level}: Word=" ++
      (if level = 0 then "l" else s!"z{level - 1}") ++ ";" ++ spine count (level + 1) ++
      "}else{" ++ s!"let z{level}: Word=r;return z{level};" ++ "}"
private def checked (actual : LocalInputs) (body : Syntax.Block) : IO Unit := do
  let renamed := actual.mapIds mapping (ownerLocalIdMap_injective shift shiftInjective)
  let core : Core.Expr := .letE (.var 3) (.var 0)
  assertTrue (decide (actual.checkTypedLetReturnTree? types owner body = some (core, .word) ∧
    renamed.checkTypedLetReturnTree? types (shift owner) body = some (core, .word)))
    "separate whole acceptance changed exact Core"
  match accepted : actual.checkTypedLetReturnTree? types owner body,
      evaluated : evaluateTypedLetReturnTreeWithCost? owner actual.toTypeInputs.names actual.environment body with
  | some _, some _ =>
      have aligned : actual.environment.ids = actual.toTypeInputs.context.ids := by
        simpa only [LocalInputs.toTypeInputs_context] using actual.sameIds
      for store in stores do
        have _ := evaluateTypedLetReturnTreeWithCost?_checked_toStepsWithContinuation
          (store := store) evaluated accepted aligned [.letBody (.var 0) [w 99]]
        for fuel in List.range 7 do
          have _ := actual.runTypedLetReturnTree?_mapOwner shift shiftInjective types owner fuel body store
          assertTrue (decide (actual.runTypedLetReturnTree? types owner fuel body store =
            some (.word, Core.runStateful fuel (.initial core actual.environment.values store)) ∧
            renamed.runTypedLetReturnTree? types (shift owner) fuel body store =
              actual.runTypedLetReturnTree? types owner fuel body store)) "fixed-store full checkpoint changed"
        assertTrue (decide (actual.runTypedLetReturnTree? types owner 2 body store =
          some (.word, .outOfFuel ⟨.ret (w 9), [.letBody (.var 0) actual.environment.values], store⟩)))
          "old-scope initializer checkpoint changed"
  | _, _ => throw (IO.userError "separate checked premises missing")

def frontendParsedTypedLetReturnTreeRawOwnerTests : IO Unit := do
  have _ := shiftNotSurjective
  for depth in [0, 1, 2, 5, 12] do
    let body ← parsed ("{" ++ spine depth 0 ++ "}")
    for c in [false, true] do
      let actual := inputs 9 2 c false
      raw actual.names actual.environment body
        (some (w (if depth = 0 || c then 9 else 2), if depth = 0 then 1 else if c then 6 * depth + 1 else 7))
        (if depth = 0 then [] else if c then List.replicate depth true else [false])
  let asymmetric ← parsed "{if(c){let z: Word=l - r;if(d){let q: Word=z;return ~q;}else{let q: Word=r - z;return q;}}else{let z: Word=r - l;return r;}}"
  for (l, r) in [(9, 2), (2, 9), (0, Core.wordModulus - 1), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        let actual := inputs l r c d
        raw actual.names actual.environment asymmetric
          (some (if c then if d then w (Core.wordModulus - 1 - (l + Core.wordModulus - r) % Core.wordModulus)
            else w (r + Core.wordModulus - (l + Core.wordModulus - r) % Core.wordModulus) else w r,
            if c then if d then 19 else 21 else 11)) (if c then [true, d] else [false])
  let actual := inputs 9 2 true false
  let inferred ← parsed "{let z=l;return z;}"
  raw actual.names actual.environment inferred (some (w 9, 4))
  checked actual inferred
  for (content, value, cost, choices) in [("{return;}", Core.Value.unit, 1, []),
      ("{let unused: Word=l - r;return r;}", w 2, 8, []),
      ("{let z: Unknown=l;return z;}", w 9, 4, []), ("{let z: Bool=l;return z;}", w 9, 4, []),
      ("{let l: Word=l - r;return l;}", w 7, 8, []),
      ("{if(c){let z: Word=l;return z;}else{let z: Unknown=missing;return z;}}", w 9, 7, [true]),
      ("{if(c){return l;}else{return c;}}", w 9, 4, [true])] do
    let body ← parsed content
    raw actual.names actual.environment body (some (value, cost)) choices
    if content != "{return;}" && content != "{let unused: Word=l - r;return r;}" then
      assertTrue ((actual.checkTypedLetReturnTree? types owner body).isNone) "raw success became whole acceptance"
  for content in ["{}", "{let z: Word;return l;}", "{let z: Word=l;}",
      "{return l;return r;}", "{if(c){return l;}}", "{if(c){return l;}else{return r;}return l;}",
      "{let unused: Word=missing;return r;}", "{let unused: Word=~c;return r;}", "{let z: Word=z;return l;}", "{return f(l);}",
      "{if(l){return l;}else{return r;}}"] do raw actual.names actual.environment (← parsed content) none
  let body ← parsed "{let z: Word=l;return z;}"
  checked actual body
  let fresh : Resolved.LocalId := ⟨owner, 8⟩
  let collision : Resolved.Environment := (fresh, w 99) :: actual.environment
  assertTrue (decide (Resolved.freshLocalId owner (actual.names.map Prod.snd) = fresh ∧
    Resolved.freshLocalId owner collision.ids = ⟨owner, 9⟩ ∧ collision.ids ≠ actual.context.ids ∧
    Core.runStateful 4 (.initial (.letE (.var 3) (.var 0)) collision.values []) = .done (w 2) []))
    "name-table allocation and unaligned positional Core execution were conflated"
  raw actual.names collision body (some (w 9, 4))
  let id : Resolved.LocalId := ⟨other, 999⟩
  raw (("l", id) :: actual.names) ((id, w 4) :: (id, w 9) :: collision) body (some (w 4, 4))
  raw actual.names [] body none
  for value in [Core.Value.unit, .cellRef .word 999, .closure .word .word (.var 1) [w 7],
      .closure .word .word (.var 80) [], .bool false, .constructed ⟨⟨91⟩, 4⟩ (.pair .unit (w 7))] do
    raw actual.names (actual.environment.map fun row => (row.1, value)) body (some (value, 4))
  let returned ← parsed "{return x;}"
  let a : Resolved.LocalId := ⟨owner, 0⟩
  let b : Resolved.LocalId := ⟨other, 0⟩
  let table : LocalNameTable := [("x", b)]
  let environment : Resolved.Environment := [(a, w 2), (b, w 9)]
  let collapse := ownerLocalIdMap (fun _ => owner)
  assertTrue (decide (a ≠ b ∧ collapse a = collapse b ∧
    evaluateTypedLetReturnTreeWithCost? owner table environment returned = some (w 9, 1) ∧
    evaluateTypedLetReturnTreeWithCost? owner (LocalNameTable.mapIds collapse table)
      (Resolved.LocalScope.mapIds collapse environment) returned = some (w 2, 1))) "owner collapse failed to expose changed first-match value"
  let indexShift := fun id : Resolved.LocalId => { id with binderIndex := id.binderIndex + 1 }
  let source ← parsed "{let z: Unknown=x;return z;}"
  let env : Resolved.Environment := [(b, w 9)]
  assertTrue (decide (Resolved.freshLocalId owner ((LocalNameTable.mapIds indexShift table).map Prod.snd) ≠
    indexShift (Resolved.freshLocalId owner (table.map Prod.snd)) ∧
    evaluateTypedLetReturnTreeWithCost? owner table env source = some (w 9, 4) ∧
    evaluateTypedLetReturnTreeWithCost? owner (LocalNameTable.mapIds indexShift table)
      (Resolved.LocalScope.mapIds indexShift env) source = some (w 9, 4)))
    "allocator noncommutation was wrongly presented as raw result inequality"

end Tests

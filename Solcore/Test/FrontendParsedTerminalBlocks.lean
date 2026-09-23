import Solcore.Syntax.Parser.Term
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.TypedLetReturnBody
import Solcore.Core.LocalFragment

/-! Original terminal block spans and independent source/Core paths. Wrappers
add no transitions, names or positional shifts, even around mixed prefixes. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace TerminalBlocks
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TerminalBlock", by decide⟩], by decide⟩⟩, 17⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def inputs (type : Core.Ty) : LocalTypeInputs := ⟨[
  ⟨"c", ⟨other, 999⟩, .bool⟩, ⟨"r", id 2, .word⟩, ⟨"x", id 7, type⟩, ⟨"x", id 3, .bool⟩], by
    change ([⟨other, 999⟩, id 2, id 7, id 3] : List Resolved.LocalId).Nodup; decide⟩
private def env (value : Core.Value) (choice : Bool) : Resolved.Environment :=
  [(⟨other, 999⟩, .bool choice), (id 2, w 2), (id 7, value), (id 3, .bool false)]
private def stores : List Core.Store := [[.unit, w 40], [w 91, .cellRef .word 40, .bool false]]
private def parsed (content : String) (clean : Bool := true) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main, "terminal-block.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok body next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"complete block rejected: {content}")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty == clean && next.atEnd &&
    decide (body.span = ⟨file.id, 0, content.utf8ByteSize⟩)) s!"{content}: original block/range changed"
  return body
private structure Expression (s : LocalTypeInputs) (e : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.ids resolved core
  typing : Resolved.HasType s.context resolved type
  raw : LocalExpressionEvaluatesWithCost s.names e store source value store cost
  paths : ∀ k, Core.Steps cost ⟨.eval core e.values, k, store⟩ ⟨.ret value, k, store⟩
private def expression (s : LocalTypeInputs) (e : Resolved.Environment) (aligned : e.ids = s.ids)
    (store : Core.Store) (source : Syntax.Expr) : IO (Expression s e store source) := do
  match atSource : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | none => throw (IO.userError "independent name absent")
      | some binder =>
          match typed : s.context.lookup? binder, found : e.lookup? binder, indexed : Resolved.LocalScope.index? s.ids binder with
          | some type, some value, some index =>
              let position := Resolved.LocalScope.index?_iff.mp indexed
              return ⟨.var binder, .var index, type, value, 1,
                by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named), .var position,
                .var (Resolved.LocalScope.lookup?_iff.mp typed),
                by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found),
                fun _ => .cons (.var ((Resolved.LocalScope.lookup_iff_getElem? (aligned.symm ▸ position)).mp
                  (Resolved.LocalScope.lookup?_iff.mp found))) .refl⟩
          | _, _, _ => throw (IO.userError "independent row absent")
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, .unit, .unit, .unit, 1,
      by rw [atSource]; exact .unit, .unit, .unit, by rw [atSource]; exact .unit, fun _ => .cons .unit .refl⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← expression s e aligned store left; let b ← expression s e aligned store right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type, .pair a.value b.value, a.cost + b.cost + 3,
        by rw [atSource]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing,
        by rw [atSource]; exact .pair a.raw b.raw, fun k => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core e.values :: k)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← expression s e aligned store left; let b ← expression s e aligned store right
      match av : a.value, bv : b.value with
      | .word x, .word y =>
          if leftType : a.type = .word then
            if rightType : b.type = .word then
            return ⟨.binary .wordSub a.resolved b.resolved, .binary .wordSub a.core b.core, .word, .word (x.sub y), a.cost + b.cost + 3,
              by rw [atSource]; exact .subtract a.resolution b.resolution, .binary a.lowered b.lowered,
              .binary (show Resolved.HasType s.context a.resolved .word from leftType ▸ a.typing)
                (show Resolved.HasType s.context b.resolved .word from rightType ▸ b.typing),
              by rw [atSource]; exact .subtract (av ▸ a.raw) (bv ▸ b.raw), fun k => by
                have path := Core.Steps.cons .enterBinary ((av ▸ a.paths (.binaryRight .wordSub b.core e.values :: k)).trans
                  (.cons .enterBinaryRight ((bv ▸ b.paths _).trans (.cons (.applyBinary rfl) .refl))))
                simpa only [Nat.add_assoc] using path⟩
            else throw (IO.userError "right is not Word")
          else throw (IO.userError "left is not Word")
      | _, _ => throw (IO.userError "actual operand not Word")
  | _ => throw (IO.userError "outside independent expression script")
termination_by sizeOf source
private structure Certificate (s : LocalTypeInputs) (e : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  elaboration : TypedLetReturnTreeElaborates types owner s body core type
  raw : TypedLetReturnTreeEvaluatesWithCost owner s.names e store body value store cost
  paths : ∀ k, Core.Steps cost ⟨.eval core e.values, k, store⟩ ⟨.ret value, k, store⟩
private def certify (s : LocalTypeInputs) (e : Resolved.Environment) (aligned : e.ids = s.ids)
    (store : Core.Store) (body : Syntax.Block) : IO (Certificate s e store body) := do
  match atBody : body with
  | ⟨outer, [⟨inner, .block statements⟩]⟩ =>
      check (outer.contains inner && decide (outer.startByte < inner.startByte ∧ inner.endByte < outer.endByte) &&
        statements.all (fun statement => inner.contains statement.span)) "original inner span or child order changed"
      let child ← certify s e aligned store ⟨inner, statements⟩
      return ⟨child.core, child.type, child.value, child.cost,
        by rw [atBody]; exact .block child.elaboration, by rw [atBody]; exact .block child.raw, child.paths⟩
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ =>
      return ⟨.unit, .unit, .unit, 1, by rw [atBody]; exact .single .bare,
        by rw [atBody]; exact .single .bare, fun _ => .cons .unit .refl⟩
  | ⟨_, [⟨_, .returnStmt (some source)⟩]⟩ =>
      let a ← expression s e aligned store source
      return ⟨a.core, a.type, a.value, a.cost,
        by rw [atBody]; exact .single (.expression a.resolution (by simpa only [LocalTypeInputs.context_ids] using a.lowered) a.typing),
        by rw [atBody]; exact .single (.expression a.raw), a.paths⟩
  | ⟨span, ⟨_, .expression source true⟩ :: rest⟩ =>
      let a ← expression s e aligned store source
      let b ← certify s e aligned store ⟨span, rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0), b.type, b.value, a.cost + b.cost + 2,
        by rw [atBody]; exact .discard a.resolution a.lowered a.typing b.elaboration,
        by rw [atBody]; exact .discard a.raw b.raw, fun k => by
          have shifted := (b.paths []).weakenAt_zero_localFragment b.elaboration.localFragment a.value k
          have path := Core.Steps.cons .enterLet
            ((a.paths (.letBody (b.core.weakenAt 0) e.values :: k)).trans (.cons .bindLet shifted))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨span, ⟨_, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      if unused : name.value ∉ s.names.map Prod.fst then
        let a ← expression s e aligned store initializer
        let next := s.bindFresh owner name.value a.type
        let b ← certify next ((Resolved.freshLocalId owner s.ids, a.value) :: e)
          (by simpa only [next, LocalTypeInputs.bindFresh_ids, Resolved.LocalScope.ids, List.map_cons]
            using congrArg (List.cons _) aligned) store ⟨span, rest⟩
        let rawTail := by simpa only [next, LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using b.raw
        let common := fun elaboration raw => (⟨.letE a.core b.core, b.type, b.value, a.cost + b.cost + 2, elaboration, raw, fun k => by
          have path := Core.Steps.cons .enterLet ((a.paths (.letBody b.core e.values :: k)).trans (.cons .bindLet (b.paths k)))
          simpa only [Resolved.LocalScope.values, List.map_cons, Nat.add_assoc] using path⟩ : Certificate s e store body)
        match atAnnotation : annotation with
        | none => return (common (by rw [atBody, atAnnotation]; exact .inferred unused a.resolution a.lowered a.typing b.elaboration)
            (by rw [atBody, atAnnotation]; exact .inferred a.raw (by simpa only [LocalTypeInputs.names_ids] using rawTail)))
        | some written =>
            match atWritten : written with
            | ⟨_, .named name none⟩ =>
                if meaning : types.lookup? (qualifiedTypeNameKey name) = some a.type then
                  return (common (by rw [atBody, atAnnotation, atWritten]; exact .binding (.named (TypeNameTable.lookup?_iff.mp meaning)) unused a.resolution a.lowered a.typing b.elaboration)
                    (by rw [atBody, atAnnotation]; exact .binding a.raw (by simpa only [LocalTypeInputs.names_ids] using rawTail)))
                else throw (IO.userError "written annotation disagrees")
            | _ => throw (IO.userError "outside independent annotation script")
      else throw (IO.userError "written name is already used")
  | ⟨_, [⟨_, .ifThen guard yes (some no)⟩]⟩ =>
      let c ← expression s e aligned store guard
      let a ← certify s e aligned store yes; let b ← certify s e aligned store no
      if ct : c.type = .bool then
        if bt : b.type = a.type then
        have elaboration : TypedLetReturnTreeElaborates types owner s body (.ifE c.core a.core b.core) a.type := by
          rw [atBody]; exact .conditional c.resolution c.lowered (ct ▸ c.typing) a.elaboration (bt ▸ b.elaboration)
        match cv : c.value with
        | .bool true => return ⟨.ifE c.core a.core b.core, a.type, a.value, c.cost + a.cost + 2, elaboration,
            by rw [atBody]; exact .ifTrue (cv ▸ c.raw) a.raw, fun k => by
              have path := Core.Steps.cons .enterIf ((cv ▸ c.paths (.ifBranches a.core b.core e.values :: k)).trans (.cons .chooseTrue (a.paths k)))
              simpa only [Nat.add_assoc] using path⟩
        | .bool false => return ⟨.ifE c.core a.core b.core, a.type, b.value, c.cost + b.cost + 2, elaboration,
            by rw [atBody]; exact .ifFalse (cv ▸ c.raw) b.raw, fun k => by
              have path := Core.Steps.cons .enterIf ((cv ▸ c.paths (.ifBranches a.core b.core e.values :: k)).trans (.cons .chooseFalse (b.paths k)))
              simpa only [Nat.add_assoc] using path⟩
        | _ => throw (IO.userError "actual guard not Bool")
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "guard type not Bool")
  | _ => throw (IO.userError "outside independent body script")
termination_by sizeOf body
private structure Actual where
  type : Core.Ty
  value : Core.Value
  typed : Core.ValueHasType value type
private def supplied (a : Actual) (choice : Bool) : LocalInputs := ⟨[
  ⟨"c", ⟨other, 999⟩, .bool, .bool choice, .bool⟩, ⟨"r", id 2, .word, w 2, .word⟩,
  ⟨"x", id 7, a.type, a.value, a.typed⟩, ⟨"x", id 3, .bool, .bool false, .bool⟩], by
    change ([⟨other, 999⟩, id 2, id 7, id 3] : List Resolved.LocalId).Nodup; decide⟩
private def unwrap (body : Syntax.Block) : Syntax.Block :=
  match body with
  | ⟨_, [⟨inner, .block statements⟩]⟩ => unwrap ⟨inner, statements⟩
  | _ => body
termination_by sizeOf body
private def checked (content : String) (a : Actual) (choice : Bool) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let body ← parsed content; let actual := supplied a choice
  let s := actual.toTypeInputs; let e := actual.environment
  have _ : s = inputs a.type := rfl
  check (decide (e = env a.value choice ∧ actual.bindings.length = 4)) "original supplied rows changed"
  for store in stores do
    let cert ← certify s e rfl store body
    check (decide (cert.core = core ∧ cert.type = type ∧ cert.value = value ∧ cert.cost = cost)) "independent expectations changed"
    match body with
    | ⟨outer, [⟨inner, .block statements⟩]⟩ =>
        have _ := elaborateTypedLetReturnTree?_block types owner s outer inner statements
        pure ()
    | _ => pure ()
    check (decide (actual.checkTypedLetReturnTree? types owner body = some (core, type) ∧
      evaluateTypedLetReturnTreeWithCost? owner s.names e body = some (value, cost) ∧
      Core.infer? s.context.values core = some type ∧ typedLetReturnTreeFuelBound body = bound ∧ cost ≤ bound ∧
      typedLetReturnTreeFuelBound (unwrap body) = bound)) "wrapper changed exact Core/type/value/cost/bound"
    check ((elaborateTypedLetReturnBody? types owner s body).isNone) "old prefix adapter widened"
    let start := Core.State.initial core e.values store
    let run := fun fuel => actual.runTypedLetReturnTree? types owner fuel body store
    have _ := cert.paths [.letBody (.var 0) [w 17]]
    have _ := cert.raw.checked_toStepsWithContinuation cert.elaboration.complete rfl [.unaryApply .wordNot]
    for fuel in List.range (bound + 3) do
      check (decide (run fuel = some (type, Core.runStateful fuel start) ∧
        run fuel = actual.runTypedLetReturnTree? types owner fuel (unwrap body) store)) "wrapper altered the full same-fuel result"
      check (match run fuel with
        | some (_, .done v st) => decide (cost ≤ fuel ∧ v = value ∧ st = store)
        | some (_, .outOfFuel cp) => decide (fuel < cost ∧ cp.store = store)
        | _ => false) "exact threshold or own store changed"
    for spent in List.range cost do
      match exhausted : run spent with
      | some (_, .outOfFuel cp) =>
          have _ := actual.runTypedLetReturnTree?_resume exhausted (cost - spent)
          for remaining in [0, 1, cost - spent, cost - spent + 2] do
            check (decide (run (spent + remaining) = some (type, Core.runStateful remaining cp))) "genuine checkpoint replay changed"
          check (decide (Core.runStateful (cost - spent) cp = .done value store)) "exact residual cost changed"
          if cost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 cp | throw (IO.userError "second chunk missing")
            check (decide (Core.runStateful (cost - spent - 1) next = .done value store)) "third chunk lost its continuation"
          if spent > 0 then check (Core.runStateful (cost - spent) start != .done value store) "restart impersonated resume"
      | _ => throw (IO.userError "checkpoint missing")
private def nominal (type : Core.Ty) (body : Syntax.Block) :
    IO (PLift (TypedLetReturnTreeElaborates types owner (inputs type) body (.var 2) type)) := do
  match atBody : body with
  | ⟨_, [⟨inner, .block statements⟩]⟩ =>
      let child ← nominal type ⟨inner, statements⟩
      return ⟨by rw [atBody]; exact .block child.down⟩
  | ⟨_, [⟨_, .returnStmt (some ⟨_, .identifier name⟩)⟩]⟩ =>
      if same : name.value = "x" then
        have named : LocalNameTable.Lookup (inputs type).names "x" (id 7) := .tail (by decide) (.tail (by decide) .head)
        return ⟨by rw [atBody]; exact .single (.expression (.identifier (same ▸ named))
          (.var (.tail (by change (⟨other, 999⟩ : Resolved.LocalId) ≠ id 7; decide) (.tail (by change id 2 ≠ id 7; decide) .head)))
          (.var (.tail (by change (⟨other, 999⟩ : Resolved.LocalId) ≠ id 7; decide) (.tail (by change id 2 ≠ id 7; decide) .head))))⟩
      else throw (IO.userError "nominal source spelling changed")
  | _ => throw (IO.userError "nominal original block shape changed")
termination_by sizeOf body
private def wrap : Nat → String → String
  | 0, content => content
  | n + 1, content => "{" ++ wrap n content ++ "}"
end TerminalBlocks
open TerminalBlocks
def frontendParsedTerminalBlockTests : IO Unit := do
  let a : Actual := ⟨.word, w 9, .word⟩
  for depth in [1, 2, 5, 16, 40] do
    checked (wrap depth "{return x;}") a true (.var 2) .word (w 9) 1 1
    checked (wrap depth "{let z=x;return z;}") a false (.letE (.var 2) (.var 0)) .word (w 9) 4 4
    checked (wrap depth "{x - r;return r;}") a true (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 2)) .word (w 2) 8 8
  checked "{{{return;}}}" a false .unit .unit .unit 1 1
  checked "{let z=x;{{return;}}}" a true (.letE (.var 2) .unit) .unit .unit 4 4
  checked "{let z: Word=x;{z;let q=z - r;{{return q;}}}}" a true
    (.letE (.var 2) (.letE (.var 0) (.letE (.binary .wordSub (.var 1) (.var 3)) (.var 0)))) .word (w 7) 14 14
  checked "{{(x,r);{let z=x;{return z;}}}}" a true (.letE (.pair (.var 2) (.var 1)) (.letE (.var 3) (.var 0))) .word (w 9) 11 11
  for choice in [false, true] do
    checked "{if(c){{x - r;{return x;}}}else{{return r;}}}" a choice
      (.ifE (.var 0) (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 3)) (.var 1))
      .word (if choice then w 9 else w 2) (if choice then 11 else 4) 11
  for value in [⟨.cell .word, .cellRef .word 999, .cellRef⟩,
      ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩,
      ⟨.unit, .unit, .unit⟩, ⟨.product .unit (.cell .word), .pair .unit (.cellRef .word 19), .pair .unit .cellRef⟩] do
    checked "{{let z=x;{{return z;}}}}" value true (.letE (.var 2) (.var 0)) value.type value.value 4 4
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨99⟩) (.cell (.namedData ⟨13⟩)), .function .word (.namedData ⟨99⟩)] do
    let body ← parsed (wrap 12 "{return x;}"); let evidence := (← nominal type body).down
    have _ (definitions : Core.DataEnvironment) : Core.HasType (inputs type).context.values (.var 2) type definitions := .var rfl
    have _ : ¬ TypedLetReturnTreeElaborates types owner (inputs type) body (.letE .unit (.var 3)) type := by
      intro wrong; have impossible := evidence.result_unique wrong; cases impossible.1
    check (decide (elaborateTypedLetReturnTree? types owner (inputs type) body = some (.var 2, type) ∧
      Core.infer? (inputs type).context.values (.letE .unit (.var 3)) = some type)) "nominal or same-typed wrong-Core boundary changed"
  for store in stores do
    let actual := supplied a true; let e := actual.environment.values
    let body ← parsed "{{x - r;{return r;}}}"
    let cp : Core.State := ⟨.ret (w 7), [.letBody (.var 2) e], store⟩
    check (decide (actual.runTypedLetReturnTree? types owner 6 body store = some (.word, .outOfFuel cp) ∧
      Core.runStateful 2 cp = .done (w 2) store ∧ Core.runStateful 0 {cp with continuation := []} = .done (w 7) store))
      "wrappers changed the actual initializer checkpoint or lost the saved tail"
  for content in ["{{}}", "{{x;}}", "{{return x;}return x;}", "{{let z=x;return z;}return z;}",
      "{let z=x;{{let z=r;return z;}}}", "{{let x=r;return x;}}", "{{let z=missing;return x;}}",
      "{if(c){{let z=x;return z;}}else{{return z;}}}", "{{return x;return r;}}", "{{f(x);return x;}}"] do
    let body ← parsed content
    check ((elaborateTypedLetReturnTree? types owner (inputs .word) body).isNone) "invalid lexical boundary accepted"
    check (decide (elaborateTypedLetReturnTree? types owner (inputs .word) body =
      elaborateTypedLetReturnTree? types owner (inputs .word) (unwrap body))) "wrapper full Option equality lost rejection"
  let unterminated ← parsed "{{x}}" false
  check (match unterminated.value with | [⟨_, .block [⟨_, .expression _ false⟩]⟩] => true | _ => false)
    "diagnosed inner expression lost its original absent semicolon"
  check ((elaborateTypedLetReturnTree? types owner (inputs .word) unterminated).isNone) "diagnosed unterminated inner block accepted"
  let skipped ← parsed "{if(c){{return x;}}else{{missing;return x;}}}"
  check (decide (evaluateTypedLetReturnTreeWithCost? owner (inputs .word).names (env (w 9) true) skipped = some (w 9, 4) ∧
    elaborateTypedLetReturnTree? types owner (inputs .word) skipped = none)) "raw selection bypassed whole block checking"
end Tests

import Solcore.Syntax.Parser.Term
import Solcore.Frontend.TypedLetReturnTreeEvaluatorExecutionProperties
import Solcore.Frontend.TypedLetReturnTreeFuelBoundProperties
import Solcore.Frontend.TypedLetReturnTreeResumptionProperties
import Solcore.Frontend.LocalFragmentProperties
import Solcore.Core.LocalFragmentExactInsertionProperties
import Solcore.Core.LocalFragmentInferenceInsertionProperties

/-! Exact parsed provenance supplies fragment membership, then existing insertion
laws transport independently hand-composed paths. Suspensions are not equated. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace LocalFragments
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Inferred", by decide⟩], by decide⟩⟩, 17⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def inputs (type : Core.Ty) : LocalTypeInputs := ⟨[
  ⟨"c", ⟨other, 999⟩, .bool⟩, ⟨"r", id 2, .word⟩, ⟨"x", id 7, type⟩, ⟨"x", id 3, .bool⟩], by
    change ([⟨other, 999⟩, id 2, id 7, id 3] : List Resolved.LocalId).Nodup; decide⟩
private def env (value : Core.Value) (choice : Bool) : Resolved.Environment :=
  [(⟨other, 999⟩, .bool choice), (id 2, w 2), (id 7, value), (id 3, .bool false)]
private def stores : List Core.Store := [[], [w 91, .cellRef .word 40, .bool false]]
private def parsed (content : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main, "inferred.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok body next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"complete block rejected: {content}")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (body.span = ⟨file.id, 0, content.utf8ByteSize⟩)) "original block/range changed"
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
  | ⟨_, [⟨_, .returnStmt (some source)⟩]⟩ =>
      let a ← expression s e aligned store source
      return ⟨a.core, a.type, a.value, a.cost,
        by rw [atBody]; exact .single (.expression a.resolution (by simpa only [LocalTypeInputs.context_ids] using a.lowered) a.typing),
        by rw [atBody]; exact .single (.expression a.raw), a.paths⟩
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
private def checked (content : String) (inputType : Core.Ty) (actual : Core.Value) (choice : Bool)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let body ← parsed content; let s := inputs inputType; let e := env actual choice
  for store in stores do
    let cert ← certify s e rfl store body
    check (decide (cert.core = core ∧ cert.type = type ∧ cert.value = value ∧ cert.cost = cost))
      "independent original-source certificate disagreed"
    let fragment := cert.elaboration.localFragment
    check (decide (elaborateTypedLetReturnTree? types owner s body = some (core, type) ∧
      evaluateTypedLetReturnTreeWithCost? owner s.names e body = some (value, cost)))
      "original exact acceptance or raw result changed"
    for cutoff in List.range (e.values.length + 1) do
      let leading := e.values.take cutoff; let suffix := e.values.drop cutoff
      have original : Core.Steps cert.cost
          (Core.State.initial cert.core (leading ++ suffix) store) (Core.State.final cert.value store) := by
        simpa only [leading, suffix, List.take_append_drop, Core.State.initial, Core.State.final] using cert.paths []
      for inserted in [Core.Value.unit, w 81, .cellRef .word 999,
          .closure .word .word (.var 1) [w 23]] do
        let shifted := cert.core.weakenAt leading.length
        let expanded := leading ++ inserted :: suffix
        let start := Core.State.initial shifted expanded store
        let path := fragment.steps_insert leading suffix inserted original []
        have _ := fragment.steps_reflect_insert leading suffix inserted path []
        have _ := (fragment.evaluates_insert_iff leading suffix inserted).mpr
          (Core.steps_from_initial_sound original)
        for k in [[], [.letBody (.var 0) [w 17]], [.unaryApply .wordNot]] do
          have _ := fragment.steps_insert leading suffix inserted original k
          have _ := fragment.steps_reflect_insert leading suffix inserted path k
          pure ()
        for fuel in List.range (cost + 3) do
          check (match Core.runStateful fuel start with
            | .done v st => decide (cost ≤ fuel ∧ v = value ∧ st = store)
            | .outOfFuel cp => decide (fuel < cost ∧ cp.store = store)
            | _ => false) "inserted exact cost/value/store changed"
        for spent in List.range cost do
          match exhausted : Core.runStateful spent start,
              unshifted : Core.runStateful spent (.initial cert.core e.values store) with
          | .outOfFuel cp, .outOfFuel originalCp =>
              have _ := path.residual_of_outOfFuel exhausted
              have _ := (cert.paths []).residual_of_outOfFuel unshifted
              for remaining in [0, 1, cost - spent, cost - spent + 2] do
                have _ := Core.runStateful_resume exhausted remaining
                check (decide (Core.runStateful remaining cp = Core.runStateful (spent + remaining) start))
                  "inserted checkpoint was restarted"
              check (decide (Core.runStateful (cost - spent) cp = .done value store ∧
                Core.runStateful (cost - spent) originalCp = .done value store))
                "separate original/inserted residuals changed"
              if cost - spent > 1 then
                let .outOfFuel next := Core.runStateful 1 cp | throw (IO.userError "second chunk absent")
                check (decide (Core.runStateful (cost - spent - 1) next = .done value store))
                  "third inserted chunk lost its environment"
          | _, _ => throw (IO.userError "genuine original or inserted checkpoint absent")
      for insertedType in [Core.Ty.word, .namedData ⟨99⟩, .function (.namedData ⟨13⟩) (.namedData ⟨99⟩)] do
        have _ := fragment.infer_insert (s.context.values.take cutoff) (s.context.values.drop cutoff) insertedType
        check (decide (Core.infer? (s.context.values.take cutoff ++ insertedType :: s.context.values.drop cutoff)
          (cert.core.weakenAt cutoff) = some type)) "value-free type insertion changed"
private def spine (n level : Nat) : String × Core.Expr :=
  match n with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 2 else 0))
  | n + 1 =>
      let (tail, core) := spine n (level + 1)
      (s!"let z{level}" ++ (if level % 2 = 0 then "" else ": Word") ++ "=" ++
        (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail, .letE (.var (if level = 0 then 2 else 0)) core)
end LocalFragments
open LocalFragments

def frontendParsedLocalFragmentTests : IO Unit := do
  checked "{return x;}" .word (w 9) true (.var 2) .word (w 9) 1
  checked "{return (x,r);}" .word (w 9) true (.pair (.var 2) (.var 1))
    (.product .word .word) (.pair (w 9) (w 2)) 5
  checked "{let z=x - r;return r;}" .word (w 9) true
    (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 2)) .word (w 2) 8
  for depth in [1, 3, 9, 20] do
    let (source, core) := spine depth 0
    checked ("{" ++ source ++ "}") .word (w 9) true core .word (w 9) (3 * depth + 1)
  for c in [false, true] do
    checked "{if(c){let z=x;return z;}else{return r;}}" .word (w 9) c
      (.ifE (.var 0) (.letE (.var 2) (.var 0)) (.var 1))
      .word (if c then w 9 else w 2) (if c then 7 else 4)
  checked "{let z=();return z;}" .word (w 9) false (.letE .unit (.var 0)) .unit .unit 4
  checked "{let z=x;return z;}" (.cell .word) (.cellRef .word 999) true
    (.letE (.var 2) (.var 0)) (.cell .word) (.cellRef .word 999) 4
  checked "{let z=x;return z;}" (.function .word .word) (.closure .word .word (.var 1) [w 7]) true
    (.letE (.var 2) (.var 0)) (.function .word .word) (.closure .word .word (.var 1) [w 7]) 4
  let body ← parsed "{let z=x;return z;}"
  match body.value with
  | [⟨span, .letDecl name none (some initializer)⟩, _] =>
      check (decide (span.startByte = 1 ∧ span.endByte = 9 ∧ name.value = "z" ∧
        initializer.span.startByte = 7 ∧ initializer.span.endByte = 8)) "original optional annotation/ranges changed"
  | _ => throw (IO.userError "original inferred-let shape changed")
  for store in stores do
    let values := (env (w 9) true).values
    let original := Core.State.initial (.letE (.var 2) (.var 0)) values store
    let shifted := Core.State.initial ((Core.Expr.letE (.var 2) (.var 0)).weakenAt 0) (.unit :: values) store
    check (decide (Core.runStateful 2 original = .outOfFuel ⟨.ret (w 9), [.letBody (.var 0) values], store⟩ ∧
      Core.runStateful 2 shifted = .outOfFuel ⟨.ret (w 9), [.letBody (.var 0) (.unit :: values)], store⟩ ∧
      Core.runStateful 2 original ≠ Core.runStateful 2 shifted)) "different captured environments were identified"
  for source in ["{x;return x;}", "{let z;return x;}", "{let z=z;return x;}",
      "{let x=r;return x;}", "{return f(x);}", "{if(c){return x;}else{return missing;}}"] do
    check ((elaborateTypedLetReturnTree? types owner (inputs .word) (← parsed source)).isNone)
      "structural bridge changed a source rejection"
  let skipped ← parsed "{if(c){return x;}else{return missing;}}"
  check (decide (evaluateTypedLetReturnTreeWithCost? owner (inputs .word).names (env (w 9) true) skipped = some (w 9, 4)))
    "raw selected execution was confused with whole provenance"

end Tests

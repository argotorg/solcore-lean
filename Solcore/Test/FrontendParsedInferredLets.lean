import Solcore.Syntax.Parser.Term
import Solcore.Frontend.TypedLetReturnTreeEvaluatorExecutionProperties
import Solcore.Frontend.TypedLetReturnTreeFuelBoundProperties
import Solcore.Frontend.TypedLetReturnTreeResumptionProperties
import Solcore.Frontend.TypedLetReturnBody

/-! Original optional annotations, independent source evidence and hand-composed
Core paths. Static input types are independent of the actual values returned. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace InferredLets
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
    check (decide (cert.core = core ∧ cert.type = type ∧ cert.value = value ∧ cert.cost = cost)) "independent certificate disagreed"
    let accepted := cert.elaboration.complete
    have _ := cert.elaboration.hasType
    match atShape : body with
    | ⟨_, ⟨_, .letDecl _ none (some _)⟩ :: _⟩ =>
        have _ := elaborateTypedLetReturnTree?_inferred_children (by rw [← atShape]; exact accepted)
        pure ()
    | _ => pure ()
    check (decide (elaborateTypedLetReturnTree? types owner s body = some (core, type) ∧
      evaluateTypedLetReturnTreeWithCost? owner s.names e body = some (value, cost) ∧
      Core.infer? s.context.values core = some type ∧ cost ≤ typedLetReturnTreeFuelBound body)) "fixed static/raw expectations changed"
    let start := Core.State.initial cert.core e.values store
    for k in [[], [.letBody (.var 0) [w 17]], [.unaryApply .wordNot]] do
      have _ := cert.paths k
      have _ := cert.raw.checked_toStepsWithContinuation accepted rfl k
      pure ()
    for fuel in List.range (typedLetReturnTreeFuelBound body + 3) do
      check (match Core.runStateful fuel start with
        | .done v st => decide (cost ≤ fuel ∧ v = value ∧ st = store)
        | .outOfFuel cp => decide (fuel < cost ∧ cp.store = store)
        | _ => false) "exact fuel/store boundary changed"
    for spent in List.range cost do
      match exhausted : Core.runStateful spent start with
      | .outOfFuel cp =>
          have _ := (cert.paths []).residual_of_outOfFuel exhausted
          have _ := cert.raw.checked_residual_of_outOfFuel accepted rfl exhausted
          for remaining in [0, 1, cost - spent, cost - spent + 2] do
            have _ := Core.runStateful_resume exhausted remaining
            check (decide (Core.runStateful remaining cp = Core.runStateful (spent + remaining) start)) "genuine checkpoint replay changed"
          check (decide (Core.runStateful (cost - spent) cp = .done value store)) "independent residual budget changed"
          if cost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 cp | throw (IO.userError "second chunk missing")
            check (decide (Core.runStateful (cost - spent - 1) next = .done value store)) "third chunk lost the captured continuation"
          if spent > 0 then check (Core.runStateful (cost - spent) start != .done value store) "restart impersonated resume"
      | _ => throw (IO.userError "checkpoint missing")
private def spine (n level : Nat) : String × Core.Expr :=
  match n with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 2 else 0))
  | n + 1 =>
      let (tail, core) := spine n (level + 1)
      (s!"let z{level}" ++ (if level % 2 = 0 then "" else ": Word") ++ "=" ++
        (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail, .letE (.var (if level = 0 then 2 else 0)) core)
private def originalOne (bs ls ns is rs us : Syntax.SourceSpan) : Syntax.Block :=
  ⟨bs, [⟨ls, .letDecl ⟨ns, "z"⟩ none (some ⟨is, .identifier ⟨is, "x"⟩⟩)⟩,
    ⟨rs, .returnStmt (some ⟨us, .identifier ⟨us, "z"⟩⟩)⟩]⟩
private theorem oneElaboration (type : Core.Ty) (bs ls ns is rs us : Syntax.SourceSpan) :
    TypedLetReturnTreeElaborates types owner (inputs type) (originalOne bs ls ns is rs us)
      (.letE (.var 2) (.var 0)) type := by
  apply TypedLetReturnTreeElaborates.inferred (inferredType := type) (initializerResolved := .var (id 7))
  · change "z" ∉ (["c", "r", "x", "x"] : List String); decide
  · exact .identifier (.tail (by change "c" ≠ "x"; decide) (.tail (by change "r" ≠ "x"; decide) .head))
  · exact .var (.tail (by decide) (.tail (by decide) .head))
  · exact .var (.tail (by decide) (.tail (by decide) .head))
  · exact .single (.expression (.identifier .head) (.var .head) (.var .head))
private theorem oneCoreType (type : Core.Ty) (definitions : Core.DataEnvironment) :
    Core.HasType (inputs type).context.values (.letE (.var 2) (.var 0)) type definitions :=
  .letE (.var rfl) (.var rfl)
private def checkedOpaque (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : IO Unit := do
  have _ : Core.EnvironmentHasTypes (env value true).values (inputs type).context.values :=
    .cons .bool (.cons .word (.cons typed (.cons .bool .nil)))
  checked "{let z=x;let q=z;return q;}" type value true (.letE (.var 2) (.letE (.var 0) (.var 0))) type value 7
end InferredLets
open InferredLets

def frontendParsedInferredLetTests : IO Unit := do
  for depth in [3, 4, 9, 20, 40] do
    let (content, core) := spine depth 0
    checked ("{" ++ content ++ "}") .word (w 9) true core .word (w 9) (3 * depth + 1)
  checked "{let z=x - r;return r;}" .word (w 9) true (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 2)) .word (w 2) 8
  checked "{let z=x - r;return z;}" .word (w 9) true (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 0)) .word (w 7) 8
  checked "{let z=(x,r);return z;}" .word (w 9) true (.letE (.pair (.var 2) (.var 1)) (.var 0)) (.product .word .word) (.pair (w 9) (w 2)) 8
  checked "{let z=();return z;}" .word (w 9) true (.letE .unit (.var 0)) .unit .unit 4
  checked "{let z=c;return z;}" .word (w 9) false (.letE (.var 0) (.var 0)) .bool (.bool false) 4
  checkedOpaque (.cell .word) (.cellRef .word 999) .cellRef
  checkedOpaque (.function .word .word) (.closure .word .word (.var 1) [w 7]) (.closure (.cons .word .nil) (.var rfl))
  checkedOpaque (.product .unit (.cell .word)) (.pair .unit (.cellRef .word 19)) (.pair .unit .cellRef)
  checkedOpaque .unit .unit .unit
  for c in [false, true] do
    checked "{if(c){let z=x;return z;}else{return r;}}" .word (w 9) c
      (.ifE (.var 0) (.letE (.var 2) (.var 0)) (.var 1)) .word (if c then w 9 else w 2) (if c then 7 else 4)
  let body ← parsed "{let z=x;return z;}"
  match body.value with
  | [⟨span, .letDecl name none (some initializer)⟩, ⟨returnSpan, .returnStmt (some result)⟩] =>
      check (decide (span.startByte = 1 ∧ span.endByte = 9 ∧ name.value = "z" ∧
        initializer.span.startByte = 7 ∧ initializer.span.endByte = 8)) "original none annotation or byte ranges changed"
      let source := originalOne body.span span name.span initializer.span returnSpan result.span
      check (body == source) "independent original source reconstruction disagreed"
      for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨99⟩) (.cell (.namedData ⟨13⟩)),
          .function (.namedData ⟨99⟩) (.namedData ⟨13⟩)] do
        let evidence := oneElaboration type body.span span name.span initializer.span returnSpan result.span
        have _ : ∀ definitions, Core.HasType (inputs type).context.values (.letE (.var 2) (.var 0)) type definitions := oneCoreType type
        have _ : ¬ TypedLetReturnTreeElaborates types owner (inputs type) source (.var 2) type := by
          intro wrong
          have impossible := evidence.result_unique wrong
          cases impossible.1
        check (decide (elaborateTypedLetReturnTree? types owner (inputs type) body = some (.letE (.var 2) (.var 0), type) ∧
          elaborateTypedLetReturnTree? [] owner (inputs type) body = some (.letE (.var 2) (.var 0), type) ∧
          Core.infer? (inputs type).context.values (.var 2) = some type)) "value-free nominal or same-typed wrong-Core boundary changed"
  | _ => throw (IO.userError "inferred original syntax was rewritten")
  check (decide (Resolved.freshLocalId owner (inputs .word).ids = InferredLets.id 8 ∧
    ((inputs .word).bindFresh owner "z" .word).context = (InferredLets.id 8, .word) :: (inputs .word).context)) "sparse owner-relative scope changed"
  check ((elaborateTypedLetReturnBody? types owner (inputs .word) body).isNone) "old annotated-only prefix unexpectedly widened"
  for store in stores do
    let e := env (w 9) true
    check (decide (Core.runStateful 2 (.initial (.letE (.var 2) (.var 0)) e.values store) =
      .outOfFuel ⟨.ret (w 9), [.letBody (.var 0) e.values], store⟩)) "old-scope initializer frame changed"
  for content in ["{let z;return x;}", "{let z: Word;return x;}", "{let z=missing;return x;}",
      "{let z=z;return x;}", "{let z=q;let q=x;return z;}", "{let z=~c;return x;}", "{let z=f(x);return x;}"] do
    check ((evaluateTypedLetReturnTreeWithCost? owner (inputs .word).names (env (w 9) true) (← parsed content)).isNone)
      "invalid or missing initializer acquired raw evaluation"
  for content in ["{let z;return x;}", "{let z: Word;return x;}", "{let z=missing;return x;}", "{let z=z;return x;}",
      "{let z=q;let q=x;return z;}", "{let x=r;return x;}", "{let z=x;let z=r;return z;}",
      "{if(c){let z=x;return z;}else{return z;}}", "{let z=~c;return x;}", "{let z=f(x);return x;}"] do
    check ((elaborateTypedLetReturnTree? types owner (inputs .word) (← parsed content)).isNone) "invalid scope/strict initializer accepted"
  let skipped ← parsed "{if(c){let z=x;return z;}else{let q=missing;return q;}}"
  check (decide (evaluateTypedLetReturnTreeWithCost? owner (inputs .word).names (env (w 9) true) skipped = some (w 9, 7) ∧
    elaborateTypedLetReturnTree? types owner (inputs .word) skipped = none)) "raw selection bypassed whole arm checking"

end Tests

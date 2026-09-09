import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalExpressionEvaluatorExecutionProperties
import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Frontend.LocalExpressionFuelBound
import Solcore.Frontend.TypeName

/-! Original parsed many-element tuples with independently constructed source evidence
and Core transition paths. Static types never manufacture or constrain raw values. -/
set_option autoImplicit false
namespace Tests
namespace ManyExpressions
open Solcore Solcore.Frontend
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"BinaryTuple", by decide⟩], by decide⟩⟩, 17⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def table : LocalNameTable := [("l", id 7), ("l", id 501), ("r", id 2), ("c", id 99)]
private def context (a b : Core.Ty) : Resolved.Context := [(id 7, a), (id 2, b), (id 99, .bool)]
private def env (a b : Core.Value) (c : Bool) : Resolved.Environment := [(id 7, a), (id 2, b), (id 99, .bool c)]
private def stores : List Core.Store := [[], [w 40, .cellRef .word 999, .bool false]]
private def file (content : String) : Syntax.SourceFile := ⟨⟨.main, "many-expressions.sol"⟩, content⟩
private def parsed (content : String) : IO Syntax.Expr := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "lexer diagnostics"
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial (file content) lexed)
    | throw (IO.userError "complete expression did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide
    (source.span = ⟨(file content).id, 0, content.utf8ByteSize⟩)) s!"original complete byte range changed: {content}"
  return source
private structure Certificate (ctx : Resolved.Context) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  resolution : ResolvesLocalExpression table source resolved
  lowered : Resolved.Lowers ctx.ids resolved core
  typing : LocalExpressionHasType table ctx source type
  raw : LocalExpressionEvaluatesWithCost table environment store source value store cost
  paths : ∀ continuation, Core.Steps cost ⟨.eval core environment.values, continuation, store⟩
    ⟨.ret value, continuation, store⟩
private def certify (ctx : Resolved.Context) (environment : Resolved.Environment)
    (aligned : environment.ids = ctx.ids) (store : Core.Store) (source : Syntax.Expr) :
    IO (Certificate ctx environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      let some identity := table.lookup? name.value | throw (IO.userError "certificate spelling missing")
      match named : table.lookup? name.value, typed : ctx.lookup? identity,
          found : environment.lookup? identity, indexed : Resolved.LocalScope.index? ctx.ids identity with
      | some actualId, some type, some value, some index =>
          if same : actualId = identity then
            let namedProof := LocalNameTable.lookup?_iff.mp (same ▸ named)
            let indexProof := Resolved.LocalScope.index?_iff.mp indexed
            return ⟨.var identity, .var index, type, value, 1,
              by rw [sourceAt]; exact .identifier namedProof, .var indexProof,
              by rw [sourceAt]; exact .identifier namedProof (Resolved.LocalScope.lookup?_iff.mp typed),
              by rw [sourceAt]; exact .identifier namedProof (Resolved.LocalScope.lookup?_iff.mp found),
              fun _ => .cons (.var ((Resolved.LocalScope.lookup_iff_getElem?
                (aligned.symm ▸ indexProof)).mp (Resolved.LocalScope.lookup?_iff.mp found))) .refl⟩
          else throw (IO.userError "certificate name changed")
      | _, _, _, _ => throw (IO.userError "certificate row missing")
  | ⟨_, .group inner⟩ =>
      let child ← certify ctx environment aligned store inner
      return { child with resolution := by rw [sourceAt]; exact .group child.resolution
                          typing := by rw [sourceAt]; exact .group child.typing
                          raw := by rw [sourceAt]; exact .group child.raw }
  | ⟨_, .tuple ⟨_, []⟩⟩ =>
      return ⟨.unit, .unit, .unit, .unit, 1,
        by rw [sourceAt]; exact .unit, .unit,
        by rw [sourceAt]; exact .unit, by rw [sourceAt]; exact .unit,
        fun _ => .cons .unit .refl⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← certify ctx environment aligned store left; let b ← certify ctx environment aligned store right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        .pair a.value b.value, a.cost + b.cost + 3,
        by rw [sourceAt]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered,
        by rw [sourceAt]; exact .pair a.typing b.typing,
        by rw [sourceAt]; exact .pair a.raw b.raw, fun continuation => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core environment.values :: continuation)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨span, .tuple ⟨tupleSpan, first :: second :: third :: rest⟩⟩ =>
      let a ← certify ctx environment aligned store first
      let b ← certify ctx environment aligned store ⟨span,.tuple ⟨tupleSpan,second :: third :: rest⟩⟩
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type, .pair a.value b.value, a.cost + b.cost + 3,
        by rw [sourceAt]; exact .many a.resolution b.resolution, .pair a.lowered b.lowered,
        by rw [sourceAt]; exact .many a.typing b.typing, by rw [sourceAt]; exact .many a.raw b.raw, fun k => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core environment.values :: k)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← certify ctx environment aligned store left; let b ← certify ctx environment aligned store right
      if aType : a.type = .word then
        if bt : b.type = .word then
          match av : a.value, bv : b.value with
          | .word x, .word y => return ⟨.binary .wordSub a.resolved b.resolved, .binary .wordSub a.core b.core, .word,
              .word (x.sub y), a.cost + b.cost + 3, by rw [sourceAt]; exact .subtract a.resolution b.resolution,
              .binary a.lowered b.lowered, by rw [sourceAt]; exact .subtract (aType ▸ a.typing) (bt ▸ b.typing),
              by rw [sourceAt]; exact .subtract (av ▸ a.raw) (bv ▸ b.raw), fun k => by
                have path := Core.Steps.cons .enterBinary
                  ((av ▸ a.paths (.binaryRight .wordSub b.core environment.values :: k)).trans
                    (.cons .enterBinaryRight ((bv ▸ b.paths _).trans (.cons (.applyBinary rfl) .refl))))
                simpa only [Nat.add_assoc] using path⟩
          | _,_ => throw (IO.userError "actual subtraction operands are not Words")
        else throw (IO.userError "right subtraction type is not Word")
      else throw (IO.userError "left subtraction type is not Word")
  | ⟨_, .conditional guard _ left _ right⟩ =>
      let c ← certify ctx environment aligned store guard
      let a ← certify ctx environment aligned store left; let b ← certify ctx environment aligned store right
      if guardType : c.type = .bool then
        if armType : b.type = a.type then
          let common := fun value cost raw paths =>
            (⟨.ifE c.resolved a.resolved b.resolved, .ifE c.core a.core b.core, a.type, value, cost,
              by rw [sourceAt]; exact .conditional c.resolution a.resolution b.resolution,
              .ifE c.lowered a.lowered b.lowered,
              by rw [sourceAt]; exact .conditional (guardType ▸ c.typing) a.typing (armType ▸ b.typing),
              raw, paths⟩ : Certificate ctx environment store source)
          match guardValue : c.value with
          | .bool true => return (common a.value (c.cost + a.cost + 2)
              (by rw [sourceAt]; exact .ifTrue (guardValue ▸ c.raw) a.raw) (fun continuation => by
                have path := Core.Steps.cons .enterIf ((guardValue ▸ c.paths
                  (.ifBranches a.core b.core environment.values :: continuation)).trans (.cons .chooseTrue (a.paths _)))
                simpa only [Nat.add_assoc] using path))
          | .bool false => return (common b.value (c.cost + b.cost + 2)
              (by rw [sourceAt]; exact .ifFalse (guardValue ▸ c.raw) b.raw) (fun continuation => by
                have path := Core.Steps.cons .enterIf ((guardValue ▸ c.paths
                  (.ifBranches a.core b.core environment.values :: continuation)).trans (.cons .chooseFalse (b.paths _)))
                simpa only [Nat.add_assoc] using path))
          | _ => throw (IO.userError "certificate actual guard not Bool")
        else throw (IO.userError "certificate arm types differ")
      else throw (IO.userError "certificate guard type not Bool")
  | _ => throw (IO.userError "outside independent certificate grammar")
termination_by sizeOf source
private def checked (text : String) (left right : Core.Value) (choice : Bool)
    (core : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let source ← parsed text
  for store in stores do
    let proof ← certify (context .word .word) (env left right choice) rfl store source
    assertTrue (decide (proof.core = core ∧ proof.type = type ∧ proof.value = value ∧ proof.cost = cost))
      "original source certificate differs from the external fixture"
    have accepted := elaborateLocalExpression?_complete proof.resolution proof.lowered (proof.resolution.preserves_type proof.typing)
    have evaluated := evaluateLocalExpressionWithCost?_complete proof.raw
    assertTrue (decide (resolveLocalExpression? table source = some proof.resolved ∧
      elaborateLocalExpression? table (context .word .word) source = some (core,type) ∧
      evaluateLocalExpressionWithCost? table (env left right choice) source = some (value,cost) ∧
      Core.infer? [.word,.word,.bool] core = some type ∧ cost ≤ localExpressionFuelBound source))
      "exact lowering, static type, raw value or cost changed"
    for k in [[],[.letBody (.var 0) []],[.unaryApply .wordNot]] do
      have _ := proof.paths k
      have _ := proof.raw.toStepsWithContinuation proof.resolution proof.lowered k
      have _ := evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation (store := store) evaluated accepted rfl k
      pure ()
    let start := Core.State.initial proof.core (env left right choice).values store
    for fuel in List.range (cost + 3) do
      have _ := (proof.paths []).runStateful_done_iff (fuel := fuel)
      assertTrue (match Core.runStateful fuel start with
        | .done result final => decide (cost ≤ fuel ∧ result = value ∧ final = store)
        | .outOfFuel saved => decide (fuel < cost ∧ saved.store = store)
        | _ => false) "whole exact fuel or own-store observation changed"
    for spent in List.range cost do
      match exhausted : Core.runStateful spent start with
      | .outOfFuel saved =>
          have _ := (proof.paths []).residual_of_outOfFuel exhausted
          have _ := proof.raw.checked_residual_of_outOfFuel accepted rfl exhausted
          for additional in List.range (cost - spent + 3) do
            have _ := Core.runStateful_resume exhausted additional
            assertTrue (decide (Core.runStateful additional saved = Core.runStateful (spent + additional) start))
              "actual checkpoint replay changed the full result"
            assertTrue (match Core.runStateful additional saved with
              | .done result final => decide (cost - spent ≤ additional ∧ result = value ∧ final = store)
              | .outOfFuel next => decide (additional < cost - spent ∧ next.store = store)
              | _ => false) "independent remaining-cost threshold changed"
          if spent > 0 then assertTrue (Core.runStateful (cost - spent) start != .done value store) "restart discarded consumed work"
          if cost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 saved | throw (IO.userError "second chunk absent")
            assertTrue (decide (Core.runStateful (cost - spent - 1) next = .done value store)) "third chunk failed"
      | _ => throw (IO.userError "genuine partial execution absent")
    assertTrue (match Core.runStateful cost ⟨.eval core (env left right choice).values,[.unaryApply .wordNot],store⟩ with
      | .fault _ endpoint => decide (endpoint = ⟨.ret value,[.unaryApply .wordNot],store⟩)
      | _ => false) "arbitrary continuation endpoint implied unconditional exhaustion"
private def skipped (source : Syntax.Expr) (store : Core.Store) : IO Unit := do
  match original : source with
  | ⟨span,.tuple ⟨tupleSpan,[head,⟨cs,.conditional guard question yes colon no⟩,⟨us,.tuple ⟨uts,[]⟩⟩]⟩⟩ =>
      let a ← certify (context .word .word) (env (w 9) (w 2) true) rfl store head
      let c ← certify (context .word .word) (env (w 9) (w 2) true) rfl store guard
      let b ← certify (context .word .word) (env (w 9) (w 2) true) rfl store yes
      if selected : c.value = .bool true then
        have costed : LocalExpressionEvaluatesWithCost table (env (w 9) (w 2) true) store source
            (.pair a.value (.pair b.value .unit)) store (a.cost + (c.cost + b.cost + 2 + 1 + 3) + 3) := by
          rw [original]
          exact .many (headCost := a.cost) (tailCost := c.cost + b.cost + 2 + 1 + 3) a.raw
            (.pair (leftCost := c.cost + b.cost + 2) (rightCost := 1)
              (.ifTrue (conditionCost := c.cost) (branchCost := b.cost) (selected ▸ c.raw) b.raw) .unit)
        have _ := evaluateLocalExpressionWithCost?_complete costed
        assertTrue (decide (a.value = w 9 ∧ b.value = w 2 ∧ a.cost = 1 ∧ b.cost = 1 ∧ c.cost = 1))
          "selected-only independent component certificate changed"
      else throw (IO.userError "raw chosen condition changed")
  | _ => throw (IO.userError "original flat tuple/conditional shape changed")
end ManyExpressions
open ManyExpressions Solcore Solcore.Frontend
def frontendParsedManyExpressionTests : IO Unit := do
  let triple : Core.Expr := .pair (.var 0) (.pair (.var 1) (.var 2))
  let tripleType : Core.Ty := .product .word (.product .word .bool)
  for (left,right) in [(w 9,w 2),(.cellRef .word 999,.closure .word .word (.var 999) [w 7])] do
    for c in [false,true] do
      for text in ["(l,r,c)","(l,r,c,)","((l),(r),(c))","(((l,r,c)))"] do
        checked text left right c triple tripleType (.pair left (.pair right (.bool c))) 9
      checked "(l,r,c,l)" left right c (.pair (.var 0) (.pair (.var 1) (.pair (.var 2) (.var 0))))
        (.product .word (.product .word (.product .bool .word))) (.pair left (.pair right (.pair (.bool c) left))) 13
      checked "((l,r),c,l)" left right c (.pair (.pair (.var 0) (.var 1)) (.pair (.var 2) (.var 0)))
        (.product (.product .word .word) (.product .bool .word)) (.pair (.pair left right) (.pair (.bool c) left)) 13
      checked "(l,(c ? r : l),())" left right c (.pair (.var 0) (.pair (.ifE (.var 2) (.var 1) (.var 0)) .unit))
        (.product .word (.product .word .unit)) (.pair left (.pair (if c then right else left) .unit)) 12
  for c in [false,true] do
    checked "(l - r,c ? l : r,r)" (w 9) (w 2) c
      (.pair (.binary .wordSub (.var 0) (.var 1)) (.pair (.ifE (.var 2) (.var 0) (.var 1)) (.var 1)))
      (.product .word (.product .word .word)) (.pair (w 7) (.pair (if c then w 9 else w 2) (w 2))) 16
  for length in [3,4,6,9] do
    let text := "(" ++ String.intercalate "," (List.replicate length "l") ++ ")"
    let core := (List.range (length - 1)).foldl (fun inner _ => Core.Expr.pair (.var 0) inner) (.var 0)
    let type := (List.range (length - 1)).foldl (fun inner _ => Core.Ty.product .word inner) .word
    let value := (List.range (length - 1)).foldl (fun inner _ => Core.Value.pair (w 9) inner) (w 9)
    checked text (w 9) (w 2) true core type value (4 * length - 3)
  let source ← parsed "(l,r,c,)"
  assertTrue (match source.value with
    | .tuple ⟨s,[⟨a,.identifier x⟩,⟨b,.identifier y⟩,⟨c,.identifier z⟩]⟩ =>
        decide (s = source.span ∧ (x.value,y.value,z.value) = ("l","r","c") ∧
          (a.startByte,a.endByte,b.startByte,b.endByte,c.startByte,c.endByte) = (1,2,3,4,5,6))
    | _ => false) "flat original arity, written names or byte ranges were rewritten"
  for store in stores do
    let environment := (env (w 9) (w 2) true).values
    assertTrue (decide (Core.runStateful 2 (.initial triple environment store) = .outOfFuel
      ⟨.ret (w 9),[.pairRight (.pair (.var 1) (.var 2)) environment],store⟩ ∧
      Core.runStateful 5 (.initial triple environment store) = .outOfFuel
      ⟨.ret (w 2),[.pairRight (.var 2) environment,.pairApply (w 9)],store⟩ ∧
      Core.runStateful 8 (.initial triple environment store) = .outOfFuel
      ⟨.ret (.pair (w 2) (.bool true)),[.pairApply (w 9)],store⟩)) "actual nested pair frames or saved environment changed"
    let duplicateContext : Resolved.Context := [(id 7,.word),(id 7,.bool),(id 2,.word),(id 99,.bool)]
    let duplicateEnv : Resolved.Environment := [(id 7,w 9),(id 7,.bool false),(id 2,w 2),(id 99,.bool true)]
    let duplicate ← certify duplicateContext duplicateEnv rfl store source
    assertTrue (decide (duplicate.core = .pair (.var 0) (.pair (.var 2) (.var 3)) ∧
      duplicate.value = .pair (w 9) (.pair (w 2) (.bool true)) ∧ duplicate.cost = 9)) "first duplicate ID ceased to determine lookup/index"
    let rawSource ← parsed "(l,c ? r : missing,())"
    skipped rawSource store
    assertTrue ((elaborateLocalExpression? table (context .word .word) rawSource).isNone &&
      decide (evaluateLocalExpressionWithCost? table (env (w 9) (w 2) true) rawSource =
        some (.pair (w 9) (.pair (w 2) .unit),12))) "selected raw component bypassed whole written-arm checking"
  for text in ["(missing,l,r)","(l,missing,r)","(l,r,missing)","(l,r,c,missing)",
      "(l,r,~c)","(l,r,f(l))","(l,r,[c])","(l,r,c).x","(l,r,c)[0]"] do
    let invalid ← parsed text
    assertTrue ((elaborateLocalExpression? table (context .word .word) invalid).isNone &&
      (evaluateLocalExpressionWithCost? table (env (w 9) (w 2) true) invalid).isNone) "strict unsupported written component was skipped"
  let original ← parsed "(l,r,())"
  let unaligned : Resolved.Environment := [(id 2,w 2),(id 7,w 9),(id 99,.bool true)]
  match shape : original with
  | ⟨_,.tuple ⟨_,[⟨_,.identifier ln⟩,⟨_,.identifier rn⟩,⟨_,.tuple ⟨_,[]⟩⟩]⟩⟩ =>
      if l : ln.value = "l" then
        if r : rn.value = "r" then
          for store in stores do
            have raw : LocalExpressionEvaluatesWithCost table unaligned store original (.pair (w 9) (.pair (w 2) .unit)) store 9 := by
              rw [shape]; exact .many (.identifier (by rw [l]; exact .head) (.tail (by decide) .head))
                (.pair (.identifier (by rw [r]; exact .tail (by decide) (.tail (by decide) .head)) .head) .unit)
            have _ := evaluateLocalExpressionWithCost?_complete raw
            assertTrue (decide (unaligned.ids ≠ (context .word .word).ids ∧
              Core.runStateful 9 (.initial (.pair (.var 0) (.pair (.var 1) .unit)) unaligned.values store) =
                .done (.pair (w 2) (.pair (w 9) .unit)) store)) "raw named lookup was confused with unaligned positional Core execution"
        else throw (IO.userError "right original spelling changed")
      else throw (IO.userError "left original spelling changed")
  | _ => throw (IO.userError "original unaligned flat fixture changed")
end Tests

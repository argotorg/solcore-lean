import Solcore.Syntax.Parser.Term
import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Frontend.LocalExpressionFuelBound
import Solcore.Frontend.TypeName

/-! Original parsed binary tuples with independently constructed source evidence
and Core transition paths. Static types never manufacture or constrain raw values. -/
set_option autoImplicit false
namespace Tests
namespace BinaryTuples
open Solcore Solcore.Frontend
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"BinaryTuple", by decide⟩], by decide⟩⟩, 17⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def table : LocalNameTable := [("l", id 7), ("r", id 2), ("c", id 99)]
private def context (a b : Core.Ty) : Resolved.Context := [(id 7, a), (id 2, b), (id 99, .bool)]
private def env (a b : Core.Value) (c : Bool) : Resolved.Environment := [(id 7, a), (id 2, b), (id 99, .bool c)]
private def stores : List Core.Store := [[], [w 40, .cellRef .word 999, .bool false]]
private def file (content : String) : Syntax.SourceFile := ⟨⟨.main, "binary-tuples.sol"⟩, content⟩
private def parsed (content : String) : IO Syntax.Expr := do
  let .ok lexed := Syntax.Lexer.lex (file content) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "lexer diagnostics"
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial (file content) lexed)
    | throw (IO.userError "complete expression did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide
    (source.span = ⟨(file content).id, 0, content.utf8ByteSize⟩)) "original complete byte range changed"
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
private def checked (content : String) (a b : Core.Value) (c : Bool) (aType bType : Core.Ty)
    (expectedCore : Core.Expr) (expectedType : Core.Ty) (expectedValue : Core.Value) (expectedCost : Nat) : IO Unit := do
  let source ← parsed content
  for store in stores do
    let certificate ← certify (context aType bType) (env a b c) rfl store source
    assertTrue (decide (certificate.core = expectedCore ∧ certificate.type = expectedType ∧
      certificate.value = expectedValue ∧ certificate.cost = expectedCost)) "independent source certificate differs"
    let accepted := elaborateLocalExpression?_complete certificate.resolution certificate.lowered
      (certificate.resolution.preserves_type certificate.typing)
    let direct := evaluateLocalExpressionWithCost?_complete certificate.raw
    have _ := evaluateLocalExpressionWithCost?_sound direct store
    assertTrue (decide (elaborateLocalExpression? table (context aType bType) source = some (expectedCore, expectedType) ∧
      evaluateLocalExpressionWithCost? table (env a b c) source = some (expectedValue, expectedCost) ∧
      Core.infer? (context aType bType).values expectedCore = some expectedType ∧
      expectedCost ≤ localExpressionFuelBound source)) "fixed lowering/type/value/cost changed"
    for continuation in [[], [.letBody (.var 0) []], [.unaryApply .wordNot]] do
      have _ := certificate.paths continuation
      have _ := certificate.raw.toStepsWithContinuation certificate.resolution certificate.lowered continuation
      have _ := evaluateLocalExpressionWithCost?_checked_toStepsWithContinuation (store := store) direct accepted rfl continuation
      pure ()
    let start := Core.State.initial certificate.core (env a b c).values store
    for fuel in List.range (expectedCost + 3) do
      have _ := evaluateLocalExpressionWithCost?_checked_runStateful_done_iff (store := store) (fuel := fuel) direct accepted rfl
      assertTrue (match Core.runStateful fuel start with
        | .done value finalStore => decide (expectedCost ≤ fuel ∧ value = expectedValue ∧ finalStore = store)
        | .outOfFuel checkpoint => decide (fuel < expectedCost ∧ checkpoint.store = store)
        | _ => false) "independent threshold or own store changed"
    for spent in List.range expectedCost do
      match exhausted : Core.runStateful spent start with
      | .outOfFuel checkpoint =>
          have _ := (certificate.paths []).residual_of_outOfFuel exhausted
          have _ := certificate.raw.checked_residual_of_outOfFuel accepted rfl exhausted
          for additional in List.range (expectedCost - spent + 3) do
            have _ := Core.runStateful_resume exhausted additional
            assertTrue (decide (Core.runStateful additional checkpoint = Core.runStateful (spent + additional) start)) "resumption changed full state"
            assertTrue (match Core.runStateful additional checkpoint with
              | .done value finalStore => decide (expectedCost - spent ≤ additional ∧ value = expectedValue ∧ finalStore = store)
              | .outOfFuel next => decide (additional < expectedCost - spent ∧ next.store = store)
              | _ => false) "independent residual threshold changed"
          if spent > 0 then
            assertTrue (Core.runStateful (expectedCost - spent) start != .done expectedValue store) "restart paid no consumed prefix"
          if expectedCost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 checkpoint | throw (IO.userError "second chunk missing")
            assertTrue (decide (Core.runStateful (expectedCost - spent - 1) next = .done expectedValue store)) "third chunk did not finish"
      | _ => throw (IO.userError "genuine checkpoint absent")
    if expectedValue matches .pair _ _ then
      assertTrue (match Core.runStateful expectedCost ⟨.eval expectedCore (env a b c).values, [.unaryApply .wordNot], store⟩ with
        | .fault _ checkpoint => decide (checkpoint = ⟨.ret expectedValue, [.unaryApply .wordNot], store⟩)
        | _ => false) "arbitrary continuation endpoint was confused with exhaustion"
private def rejected (content : String) (expected : Option (Core.Value × Nat) := none) : IO Unit := do
  let source ← parsed content
  assertTrue ((elaborateLocalExpression? table (context .word .word) source).isNone &&
    decide (evaluateLocalExpressionWithCost? table (env (w 9) (w 2) true) source = expected)) "unsupported boundary changed"
  for store in stores do
    match outcome : evaluateLocalExpressionWithCost? table (env (w 9) (w 2) true) source with
    | none => have _ := (evaluateLocalExpressionWithCost?_eq_none_iff store).mp outcome; pure ()
    | some _ => have _ := evaluateLocalExpressionWithCost?_sound outcome store; pure ()
private def rawLogical (source : Syntax.Expr) (c : Bool) (store : Core.Store) : IO Unit := do
  match sourceAt : source with
  | ⟨span, .binary left ⟨operatorSpan, op⟩ right⟩ =>
      let a ← certify (context .word .word) (env (w 9) (w 2) c) rfl store left
      let b ← certify (context .word .word) (env (w 9) (w 2) c) rfl store right
      match opAt : op, guardValue : a.value with
      | .logicalAnd, .bool true =>
          let evidence := LocalExpressionEvaluatesWithCost.andTrue (span := span) (operatorSpan := operatorSpan) (guardValue ▸ a.raw) b.raw
          have _ : evaluateLocalExpressionWithCost? table (env (w 9) (w 2) c) source = some (b.value, a.cost + b.cost + 2) := by
            simpa only [sourceAt, opAt] using evaluateLocalExpressionWithCost?_complete evidence
          assertTrue (decide (a.cost + b.cost + 2 = 8 ∧ b.value = .pair (w 9) (w 2))) "independent and-forward certificate changed"
      | .logicalOr, .bool false =>
          let evidence := LocalExpressionEvaluatesWithCost.orFalse (span := span) (operatorSpan := operatorSpan) (guardValue ▸ a.raw) b.raw
          have _ : evaluateLocalExpressionWithCost? table (env (w 9) (w 2) c) source = some (b.value, a.cost + b.cost + 2) := by
            simpa only [sourceAt, opAt] using evaluateLocalExpressionWithCost?_complete evidence
          assertTrue (decide (a.cost + b.cost + 2 = 8 ∧ b.value = .pair (w 9) (w 2))) "independent or-forward certificate changed"
      | .logicalAnd, .bool false =>
          have _ := evaluateLocalExpressionWithCost?_complete (LocalExpressionEvaluatesWithCost.andFalse
            (span := span) (operatorSpan := operatorSpan) (right := right) (guardValue ▸ a.raw))
          assertTrue (a.cost + 3 == 4) "independent skipped and cost changed"
      | .logicalOr, .bool true =>
          have _ := evaluateLocalExpressionWithCost?_complete (LocalExpressionEvaluatesWithCost.orTrue
            (span := span) (operatorSpan := operatorSpan) (right := right) (guardValue ▸ a.raw))
          assertTrue (a.cost + 3 == 4) "independent skipped or cost changed"
      | _, _ => throw (IO.userError "logical certificate shape changed")
  | _ => throw (IO.userError "original binary shape changed")
end BinaryTuples
open BinaryTuples Solcore Solcore.Frontend
def frontendParsedBinaryTupleTests : IO Unit := do
  let pair : Core.Expr := .pair (.var 0) (.var 1); let product : Core.Ty := .product .word .word
  for (left, right) in [(w 9, w 2), (.cellRef .word 999, .closure .word .bool (.var 999) [w 12]),
      (.constructed ⟨⟨81⟩, 4⟩ (.pair .unit (w 8)), .unit)] do
    for text in ["(l,r)", "(l, r,)", "((l),(r))", "(((l,r)))"] do
      checked text left right true .word .word pair product (.pair left right) 5
    checked "(l,(r,l))" left right false .word .word (.pair (.var 0) (.pair (.var 1) (.var 0)))
      (.product .word product) (.pair left (.pair right left)) 9
    checked "((l,r),r)" left right false .word .word (.pair pair (.var 1))
      (.product product .word) (.pair (.pair left right) right) 9
    for c in [false, true] do
      checked "c ? (l,r) : (r,l)" left right c .word .word (.ifE (.var 2) pair (.pair (.var 1) (.var 0)))
        product (if c then .pair left right else .pair right left) 8
      checked "c ? (l,r) : (r,(c ? l : r))" left right c .word .word
        (.ifE (.var 2) pair (.pair (.var 1) (.ifE (.var 2) (.var 0) (.var 1))))
        product (if c then .pair left right else .pair right right) (if c then 8 else 11)
  for depth in [0, 1, 3, 6] do
    let content := (List.range depth).foldl (fun inner _ => "(l," ++ inner ++ ")") "r"
    let core := (List.range depth).foldl (fun inner _ => Core.Expr.pair (.var 0) inner) (.var 1)
    let type := (List.range depth).foldl (fun inner _ => Core.Ty.product .word inner) .word
    let value := (List.range depth).foldl (fun inner _ => Core.Value.pair (w 9) inner) (w 2)
    checked content (w 9) (w 2) true .word .word core type value (4 * depth + 1)
  checked "(l,c)" (w 9) (w 2) false .word .word (.pair (.var 0) (.var 2)) (.product .word .bool) (.pair (w 9) (.bool false)) 5
  checked "(c,r)" (w 9) (w 2) true .word .word (.pair (.var 2) (.var 1)) (.product .bool .word) (.pair (.bool true) (w 2)) 5
  for text in ["(l)", "(l,)"] do checked text (w 9) (w 2) true .word .word (.var 0) .word (w 9) 1
  checked "()" (w 9) (w 2) true .word .word .unit .unit .unit 1
  checked "(l,r)" (.cellRef .word 999) (.closure .word .word (.var 0) []) true (.cell .word) (.function .word .word)
    pair (.product (.cell .word) (.function .word .word)) (.pair (.cellRef .word 999) (.closure .word .word (.var 0) [])) 5
  let source ← parsed "(l,r,)"
  assertTrue (match source.value with
    | .tuple ⟨span, [⟨_, .identifier l⟩, ⟨_, .identifier r⟩]⟩ =>
        l.value == "l" && r.value == "r" && decide (span = source.span ∧ l.span.endByte < r.span.startByte)
    | _ => false) "parser changed binary arity, ranges or written order"
  for store in stores do
    let environment := (env (w 9) (w 2) true).values
    assertTrue (decide (Core.runStateful 2 (Core.State.initial pair environment store) = .outOfFuel
      ⟨.ret (w 9), [.pairRight (.var 1) environment], store⟩ ∧
      Core.runStateful 4 (Core.State.initial pair environment store) = .outOfFuel
      ⟨.ret (w 2), [.pairApply (w 9)], store⟩)) "actual ordered pair frames or captured environment changed"
    let duplicateContext : Resolved.Context := [(id 7, .word), (id 7, .bool), (id 2, .word), (id 99, .bool)]
    let duplicateEnvironment : Resolved.Environment := [(id 7, w 9), (id 7, .bool false), (id 2, w 2), (id 99, .bool true)]
    let duplicate ← certify duplicateContext duplicateEnvironment rfl store source
    have _ := evaluateLocalExpressionWithCost?_complete duplicate.raw
    assertTrue (decide (duplicate.core = .pair (.var 0) (.var 2) ∧ duplicate.type = product ∧
      duplicate.value = .pair (w 9) (w 2) ∧ duplicate.cost = 5 ∧
      Core.runStateful 5 (Core.State.initial (.pair (.var 0) (.var 2)) duplicateEnvironment.values store) = .done (.pair (w 9) (w 2)) store))
      "duplicate first-match identity changed ordered values or positions"
  for c in [false, true] do
    for op in [Syntax.BinaryOp.logicalAnd, .logicalOr] do
      let text := if op == .logicalAnd then "c && (l,r)" else "c || (l,r)"
      let expression ← parsed text
      let forwarded := if op == .logicalAnd then c else !c
      let value := if forwarded then Core.Value.pair (w 9) (w 2) else .bool c
      assertTrue (decide (evaluateLocalExpressionWithCost? table (env (w 9) (w 2) c) expression =
        some (value, if forwarded then 8 else 4)) && (elaborateLocalExpression? table (context .word .word) expression).isNone)
        "raw pair forwarding became a whole Bool rule"
      for store in stores do rawLogical expression c store
  checked "(l,r,c)" (w 9) (w 2) true .word .word (.pair (.var 0) (.pair (.var 1) (.var 2)))
    (.product .word (.product .word .bool)) (.pair (w 9) (.pair (w 2) (.bool true))) 9
  checked "(l,r,c,l)" (w 9) (w 2) true .word .word (.pair (.var 0) (.pair (.var 1) (.pair (.var 2) (.var 0))))
    (.product .word (.product .word (.product .bool .word))) (.pair (w 9) (.pair (w 2) (.pair (.bool true) (w 9)))) 13
  for text in ["[l,r]", "(l,r).x", "(l,r)[0]", "(missing,r)", "(l,missing)", "(l,f(r))", "(l,~c)"] do rejected text
  rejected "c ? (l,r) : (l,missing)" (some (.pair (w 9) (w 2), 8))
  rejected "c ? (l,r) : l" (some (.pair (w 9) (w 2), 8))
  let singleton : Syntax.Expr := ⟨source.span, .tuple ⟨source.span, [← parsed "l"]⟩⟩
  assertTrue ((resolveLocalExpression? table singleton).isNone &&
    (evaluateLocalExpressionWithCost? table (env (w 9) (w 2) true) singleton).isNone) "manual singleton tuple acquired grouping meaning"
  let .ok lexed := Syntax.Lexer.lex (file "(Word, Word)") | throw (IO.userError "type lexer invariant")
  let .ok tupleType next := Syntax.Parser.typeExpr (Syntax.Parser.State.initial (file "(Word, Word)") lexed)
    | throw (IO.userError "tuple type did not parse")
  assertTrue (next.atEnd && (interpretTypeName? [(["Word"], .word)] tupleType).isNone) "expression pairs enabled tuple type syntax"
  match sourceAt : source with
  | ⟨_, .tuple ⟨_, [⟨_, .identifier left⟩, ⟨_, .identifier right⟩]⟩⟩ =>
      if leftAt : left.value = "l" then
        if rightAt : right.value = "r" then
          let nominal : Core.Ty := .namedData ⟨83⟩
          have typing : LocalExpressionHasType table (context nominal .unit) source (.product nominal .unit) := by
            rw [sourceAt]
            exact .pair (.identifier (by rw [leftAt]; exact .head) .head)
              (.identifier (by rw [rightAt]; exact .tail (by decide) .head) (.tail (by decide) .head))
          have _ := localExpressionHasType_iff_elaborates.mp typing
          have noInhabitant : ∀ nominal : Core.DataTypeId, ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
            intro nominal
            rintro ⟨_, typed⟩
            cases typed with
            | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
          have _ := noInhabitant ⟨83⟩
          assertTrue (decide (elaborateLocalExpression? table (context nominal .unit) source =
            some (pair, .product nominal .unit))) "static nominal pair required actual values"
        else throw (IO.userError "nominal right spelling changed")
      else throw (IO.userError "nominal left spelling changed")
  | _ => throw (IO.userError "nominal original binary tuple changed")
end Tests

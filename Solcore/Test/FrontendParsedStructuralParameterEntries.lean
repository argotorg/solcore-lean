import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties

/-! Structural parameters enter the unchanged whole-function runtime. Original
annotation/raw-body evidence and hand-written Core paths fix each expectation. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace StructuralParameterEntries
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"StructuralParameterEntry", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool),
  (["Unit"], .unit), (["Pair"], .product .word .bool), (["Pkg", "Flag"], .bool),
  (["Cell"], .cell .word), (["Fn"], .function .word .word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "structural-parameter-entry.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  assertTrue lexed.diagnostics.isEmpty "unexpected lexing diagnostic"
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  assertTrue (next.atEnd && next.diagnostics.isEmpty && decide (source.span.source = file.id ∧
    source.span.startByte = 0 ∧ source.span.endByte = content.utf8ByteSize) && source.span.contains source.value.body.span)
    "original declaration range or completion changed"
  return source
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .unit⟩
  | ⟨_, .group inner⟩ =>
      let child ← expression table env store inner
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .group child.costed⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let first ← expression table env store left
      let second ← expression table env store right
      return ⟨.pair first.value second.value, first.cost + second.cost + 3, by
        rw [sourceAt]; exact .pair first.costed second.costed⟩
  | _ => throw (IO.userError "expression outside independent unit script")
termination_by sizeOf source
private structure Body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table env store source value store cost
private def body (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) : IO (Body table env store source) := do
  match sourceAt : source with
  | ⟨span, ⟨_, .letDecl name (some _) (some initializer)⟩ :: rest⟩ =>
      let first ← expression table env store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let second ← body ((name.value, id) :: table) ((id, first.value) :: env) store ⟨span, rest⟩
      return ⟨second.value, first.cost + second.cost + 2, by rw [sourceAt]; exact .binding first.costed second.costed⟩
  | ⟨_, [⟨_, .ifThen condition yes (some no)⟩]⟩ =>
      let guard ← expression table env store condition
      match selected : guard.value with
      | .bool true =>
          let child ← body table env store yes
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifTrue (selected ▸ guard.costed) child.costed⟩
      | .bool false =>
          let child ← body table env store no
          return ⟨child.value, guard.cost + child.cost + 2, by rw [sourceAt]; exact .ifFalse (selected ▸ guard.costed) child.costed⟩
      | _ => throw (IO.userError "independent guard not Boolean")
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ => return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | _ => throw (IO.userError "body outside independent unit script")
termination_by sizeOf source
private structure Annotation (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  meaning : StructuralTypeDenotes types source type
private def annotation (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Annotation types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | none => throw (IO.userError "independent return leaf missing")
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [atSource]; exact .unit⟩
  | ⟨_, .tuple [child]⟩ =>
      let inner ← annotation types child
      return ⟨inner.type, by rw [atSource]; exact .single inner.meaning⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let first ← annotation types left
      let second ← annotation types right
      return ⟨.product first.type second.type, by rw [atSource]; exact .pair first.meaning second.meaning⟩
  | _ => throw (IO.userError "return annotation outside independent script")
termination_by sizeOf source
private structure Return (types : TypeNameTable) (clause : Option Syntax.ReturnClause) where
  type : Core.Ty
  meaning : RuntimeReturnTypeDenotes types clause type
private def returns (types : TypeNameTable) (clause : Option Syntax.ReturnClause) : IO (Return types clause) := do
  match atClause : clause with
  | none => return ⟨.unit, by rw [atClause]; exact .absent⟩
  | some ⟨_, ⟨_, [source]⟩⟩ =>
      let child ← annotation types source
      return ⟨child.type, by rw [atClause]; exact .single child.meaning⟩
  | _ => throw (IO.userError "independent return clause is not singleton")
private def check (types : TypeNameTable) (content : String) (arguments : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat)
    (steps : ∀ store k, Core.Steps cost ⟨.eval core (arguments.reverse.map (·.value)), k, store⟩
      ⟨.ret value, k, store⟩) : IO Syntax.FunctionDecl := do
  let source ← parsed content
  let declared ← returns types source.value.signature.returnsClause
  assertTrue (decide (declared.type = type)) "independent structural return type differs from fixture"
  if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
      source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
    have header : RuntimeFunctionHeader types source.value.signature declared.type :=
      ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, declared.meaning⟩
    have _ := interpretRuntimeFunctionHeader?_iff.mpr header
    pure ()
  else throw (IO.userError "independent header policy rejected")
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError ("structural parameter entry did not compile: " ++ content))
  let original ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name sourceType := parameter.value | throw (IO.userError "original parameter shape changed")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains sourceType.span)
      "original parameter range changed"
    let meaning ← annotation types sourceType
    pure (name.value, meaning.type)
  let names := original.map Prod.fst
  assertTrue (decide (original.map Prod.snd = arguments.map (·.type))) "independent original parameter types changed"
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
    compiled.inputs.context.values = (original.map Prod.snd).reverse ∧ compiled.inputs.bindings.length = arguments.length))
    "fixed ordered Core/type or original parameter-only layout changed"
  match preparedAt : prepareRuntimeFunction? types owner source arguments with
  | none => throw (IO.userError "structural arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "adapter flattened arguments or leaked local bindings into parameter records"
      for store in stores do
        let raw ← body prepared.inputs.names prepared.inputs.environment store source.value.body
        assertTrue (decide (raw.value = value ∧ raw.cost = cost))
          "separate source/Core certificates disagreed with independent fixture"
        let independent := RuntimeFunctionEvaluatesWithCost.intro preparation raw.costed
        have direct := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp independent).2
        have _ := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store) (finalStore := store)).mpr ⟨rfl, direct⟩
        have _ := independent.cost_le_fuelBound
        have _ := (steps store []).runStateful_done_iff (fuel := cost)
        assertTrue (decide (evaluateRuntimeFunctionWithCost? types owner source arguments = some (type, value, cost))) "entry triple changed"
        let run := fun fuel => runRuntimeFunction? types owner source arguments fuel store
        let start := Core.State.initial core (arguments.reverse.map (·.value)) store
        for fuel in List.range (cost + 3) do
          have _ := independent.run_done_iff (fuel := fuel)
          have _ := independent.run_outOfFuel_iff (fuel := fuel)
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel start))) "entry changed fixed Core or full checkpoint"
          assertTrue (match run fuel with
            | some (t, .done v s) => decide (cost ≤ fuel ∧ t = type ∧ v = value ∧ s = store)
            | some (t, .outOfFuel checkpoint) => decide (fuel < cost ∧ t = type ∧ checkpoint.store = store)
            | _ => false) "entry threshold, ordered value or own store changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (t, .outOfFuel checkpoint) =>
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (t, Core.runStateful remaining checkpoint))) "entry residual path changed"
              assertTrue (decide (Core.runStateful (cost - spent) checkpoint = .done value store)) "actual remaining cost changed"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done value store))) "restart pretended to resume"
          | _ => throw (IO.userError "below-cost entry checkpoint missing")
  return source
private def rejected (types : TypeNameTable) (source : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid structural parameter gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid structural parameter gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid structural parameter gate exposed a checkpoint"
end StructuralParameterEntries
open StructuralParameterEntries

def frontendParsedStructuralParameterEntryTests : IO Unit := do
  let unitArg : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  for annotation in ["()", "(())", "((()))"] do
    let source ← check [] ("function unit(u: " ++ annotation ++ ") returns(()){return u;}") [unitArg]
      (.var 0) .unit .unit 1 (by intro store k; exact .cons (.var rfl) .refl)
    rejected [] source []
    rejected [] source [wordArg 0]
  let _ ← check [(["Unit"], .word)] "function spelling(u: (),x: Unit) returns(Unit){return x;}" [unitArg, wordArg 5]
    (.var 0) .word (w 5) 1 (by intro store k; exact .cons (.var rfl) .refl)
  for n in [0, 9, Core.wordModulus - 1] do
    for choice in [false, true] do
      let pair : TypedRuntimeArgument :=
        ⟨.product .word .bool, .pair (w n) (.bool choice), .pair .word .bool⟩
      for annotation in ["(Word,Bool)", "((Word),(Bool,))", "((Word,Bool),)"] do
        let source ← check types ("function retain(p: " ++ annotation ++ ",u: ()) returns((Word,Bool)){return p;}")
          [pair, unitArg] (.var 1) pair.type pair.value 1 (by intro store k; exact .cons (.var rfl) .refl)
        for wrong in [[pair], [wordArg n, boolArg choice, unitArg], [unitArg, pair],
            [pair, wordArg 0], [pair, unitArg, unitArg]] do rejected types source wrong
      let _ ← check types "function unused(p: (Word,Bool),u: ()){return ();}" [pair, unitArg]
        .unit .unit .unit 1 (by intro store k; exact .cons .unit .refl)
      let _ ← check types "function single(x: ((Word,)),u: ()) returns((Word)){return x;}" [wordArg n, unitArg]
        (.var 1) .word (w n) 1 (by intro store k; exact .cons (.var rfl) .refl)
      let second : TypedRuntimeArgument :=
        ⟨.product .word .bool, .pair (w (n + 1)) (.bool (!choice)), .pair .word .bool⟩
      let output := Core.Value.pair pair.value second.value
      let outputType := Core.Ty.product pair.type second.type
      let ordered ← check types "function ordered(p: (Word,Bool),q: (Word,Bool),u: ()) returns(((Word,Bool),(Word,Bool))){return (p,q);}"
        [pair, second, unitArg] (.pair (.var 2) (.var 1)) outputType output 5
        (by intro store k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner ordered [pair, second, unitArg] 2 store =
          some (outputType, .outOfFuel ⟨.ret pair.value, [.pairRight (.var 1) [.unit, second.value, pair.value]], store⟩)))
          "same-typed product parameters lost their original identities or order"
      let nested : TypedRuntimeArgument := ⟨.product pair.type .unit, .pair pair.value .unit, .pair pair.valueTyped .unit⟩
      let _ ← check types "function nested(p: ((Word,Bool),())) returns(((Word,Bool),())){return p;}" [nested]
        (.var 0) nested.type nested.value 1 (by intro store k; exact .cons (.var rfl) .refl)
      let bound ← check types "function bound(p: (Word,Bool),u: ()) returns(((Word,Bool),())){let copied: Pair=p;return (copied,u);}"
        [pair, unitArg] (.letE (.var 1) (.pair (.var 0) (.var 1))) nested.type nested.value 8
        (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet
          (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl))))))))
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner bound [pair, unitArg] 2 store = some (nested.type,
          .outOfFuel ⟨.ret pair.value, [.letBody (.pair (.var 0) (.var 1)) [.unit, pair.value]], store⟩)))
          "strict initializer no longer used the original structural parameter"
      let _ ← check types "function branches(p: (Word,Bool),c: (Bool)) returns((Word,Bool)){if(c){return p;}else{let x: Pair=p;return x;}}"
        [pair, boolArg choice] (.ifE (.var 0) (.var 1) (.letE (.var 1) (.var 0))) pair.type pair.value (if choice then 4 else 7)
        (by intro store k; cases choice <;> first
          | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) .refl)))
          | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons .enterLet
              (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))))))
      let migrated ← check types "function stillLet(p: (Word,Bool),c: (Bool)){let x: (Word,Bool)=p;return ();}"
        [pair, boolArg choice] (.letE (.var 1) .unit) .unit .unit 4
        (by intro store k; exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .unit .refl))))
      match migrated.value.body.value with
      | ⟨_, .letDecl _ (some original) (some _)⟩ :: _ =>
          let independent ← annotation types original
          assertTrue (decide (independent.type = pair.type)) "migrated original let annotation changed meaning"
          assertTrue (interpretTypeName? types original).isNone "old named-only annotation boundary changed"
      | _ => throw (IO.userError "migrated original structural let disappeared")
      for declaration in ["function unselected(p: (Word,Bool),c: (Bool)) returns((Word,Bool)){if(c){return p;}else{return missing;}}",
          "function unknown(p: (Word,Unknown),c: (Bool)){return ();}",
          "function unsupported(p: (Word,Bool,Word),c: (Bool)){return ();}",
          "function wrongOrder(p: (Bool,Word),c: (Bool)){return ();}",
          "function shadow(p: (Word,Bool),c: (Bool)){let p: Pair=p;return ();}",
          "function multiple(p: (Word,Bool),c: (Bool)) returns(Word,Bool){return p;}"] do
        rejected types (← parsed declaration) [pair, boolArg choice]
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 999, .cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩
  let opaqueArg : TypedRuntimeArgument := ⟨.product cell.type closure.type, .pair cell.value closure.value, .pair cell.valueTyped closure.valueTyped⟩
  let _ ← check types "function opaque(p: (Cell,Fn)) returns((Cell,Fn)){return p;}" [opaqueArg]
    (.var 0) opaqueArg.type opaqueArg.value 1 (by intro store k; exact .cons (.var rfl) .refl)
  let nominal ← parsed "function nominal(p: (N,()),u: ()) returns((N,())){return p;}"
  let nominalTypes := (["N"], Core.Ty.namedData ⟨91⟩) :: types
  assertTrue (decide ((compileRuntimeFunction? nominalTypes owner nominal).map (fun c => (c.core,c.returnType)) =
    some (.var 1, .product (.namedData ⟨91⟩) .unit))) "structural parameter required a nominal inhabitant to compile"
  rejected nominalTypes nominal [wordArg 9, unitArg]
end Tests

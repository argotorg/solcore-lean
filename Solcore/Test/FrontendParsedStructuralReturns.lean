import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeFunctionEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties

/-! Complete entries consume original structural return annotations. Independent
annotation/raw-body evidence and fixed Core transition scripts fix all expectations. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace StructuralReturns
private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"StructuralReturn", by decide⟩], by decide⟩⟩, 17⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool),
  (["Unit"], .unit), (["Pair"], .product .word .bool), (["Pkg", "Flag"], .bool),
  (["Cell"], .cell .word), (["Fn"], .function .word .word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, w n, .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := { id := ⟨.main, "structural-return.sol"⟩, content }
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
  have _ := (interpretRuntimeReturnType?_iff).mpr declared.meaning
  let some compiled := compileRuntimeFunction? types owner source | throw (IO.userError "unit entry did not compile")
  let names ← source.value.signature.parameters.elements.mapM fun parameter => do
    let .typed none name annotation := parameter.value | throw (IO.userError "original parameter shape changed")
    assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains annotation.span)
      "original parameter range changed"
    pure name.value
  assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧
    compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
    compiled.inputs.context.values = (arguments.map (·.type)).reverse ∧ compiled.inputs.bindings.length = arguments.length))
    "fixed ordered Core/type or original parameter-only layout changed"
  match preparedAt : prepareRuntimeFunction? types owner source arguments with
  | none => throw (IO.userError "unit arguments did not prepare")
  | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      assertTrue (decide (prepared.core = core ∧ prepared.returnType = type ∧ prepared.inputs.names = compiled.inputs.names ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value)))
        "unit flattened arguments or leaked local bindings into parameter records"
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
  assertTrue (prepareRuntimeFunction? types owner source arguments).isNone "invalid unit gate prepared"
  assertTrue (evaluateRuntimeFunctionWithCost? types owner source arguments).isNone "invalid unit gate produced a result"
  for store in stores do
    for fuel in [0, 1, 40] do assertTrue (runRuntimeFunction? types owner source arguments fuel store).isNone "invalid unit gate exposed a checkpoint"
end StructuralReturns
open StructuralReturns

def frontendParsedStructuralReturnTests : IO Unit := do
  for declaration in ["function unit() returns(()){return ();}",
      "function groupUnit() returns((())){return ();}", "function bare() returns(()){return;}"] do
    let _ ← check [] declaration [] .unit .unit .unit 1 (by intro store k; exact .cons .unit .refl)
  let _ ← check [(["Unit"], .word)] "function notReserved() returns(()){return ();}" [] .unit .unit .unit 1
    (by intro store k; exact .cons .unit .refl)
  for n in [0, 9, Core.wordModulus - 1] do
    for choice in [false, true] do
      let arguments := [wordArg n, boolArg choice]
      let pairType := Core.Ty.product .word .bool
      let value := Core.Value.pair (w n) (.bool choice)
      for annotation in ["(Word,Bool)", "((Word),(Bool,))", "(Word,Bool,)"] do
        let source ← check types ("function pair(x: Word,c: Bool) returns(" ++ annotation ++ "){return (x,c);}")
          arguments (.pair (.var 1) (.var 0)) pairType value 5
          (by intro store k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
            (.cons (.var rfl) (.cons .applyPair .refl)))))
        for store in stores do
          assertTrue (decide (runRuntimeFunction? types owner source arguments 2 store = some (pairType,
            .outOfFuel ⟨.ret (w n), [.pairRight (.var 0) [.bool choice, w n]], store⟩)))
            "structural annotation changed the original parameter environment checkpoint"
        for wrong in [[], [wordArg n], [boolArg choice, wordArg n], [wordArg n, boolArg choice, wordArg 0]] do
          rejected types source wrong
      let _ ← check types "function reversed(x: Word,c: Bool) returns((Bool,Word)){return (c,x);}" arguments
        (.pair (.var 0) (.var 1)) (.product .bool .word) (.pair (.bool choice) (w n)) 5
        (by intro store k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
          (.cons (.var rfl) (.cons .applyPair .refl)))))
      for annotation in ["(Word)", "((Word,))"] do
        let _ ← check types ("function single(x: Word,c: Bool) returns(" ++ annotation ++ "){return x;}") arguments
          (.var 1) .word (w n) 1 (by intro store k; exact .cons (.var rfl) .refl)
      let _ ← check types "function qualified(x: Word,c: Bool) returns((Pkg.Flag)){return c;}" arguments
        (.var 0) .bool (.bool choice) 1 (by intro store k; exact .cons (.var rfl) .refl)
      let _ ← check types "function nested(x: Word,c: Bool) returns(((Word,Bool),Word)){return ((x,c),x);}" arguments
        (.pair (.pair (.var 1) (.var 0)) (.var 1)) (.product pairType .word) (.pair value (w n)) 9
        (by intro store k; exact .cons .enterPair (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
          (.cons (.var rfl) (.cons .applyPair (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))))))
      let bound ← check types "function bound(x: Word,c: Bool) returns(((Word,Bool),Word)){let p: Pair=(x,c);return (p,x);}" arguments
        (.letE (.pair (.var 1) (.var 0)) (.pair (.var 0) (.var 2))) (.product pairType .word) (.pair value (w n)) 12
        (by intro store k; exact .cons .enterLet (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight
          (.cons (.var rfl) (.cons .applyPair (.cons .bindLet (.cons .enterPair (.cons (.var rfl)
            (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl))))))))))))
      for store in stores do
        assertTrue (decide (runRuntimeFunction? types owner bound arguments 6 store = some (.product pairType .word,
          .outOfFuel ⟨.ret value, [.letBody (.pair (.var 0) (.var 2)) [.bool choice, w n]], store⟩)))
          "named strict let stopped retaining its two binding steps"
      let _ ← check types "function branches(x: Word,c: Bool) returns((Word,Bool)){if(c){return (x,c);}else{let p: Pair=(x,c);return p;}}" arguments
        (.ifE (.var 0) (.pair (.var 1) (.var 0)) (.letE (.pair (.var 1) (.var 0)) (.var 0))) pairType value (if choice then 8 else 11)
        (by intro store k; cases choice <;> first
          | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .enterPair (.cons (.var rfl)
              (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))))
          | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons .enterLet (.cons .enterPair
              (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair
                (.cons .bindLet (.cons (.var rfl) .refl)))))))))))
      for declaration in ["function empty(x: Word,c: Bool) returns(){return (x,c);}",
          "function multiple(x: Word,c: Bool) returns(Word,Bool){return (x,c);}",
          "function wrongOrder(x: Word,c: Bool) returns((Bool,Word)){return (x,c);}",
          "function wrongAssociation(x: Word,c: Bool) returns((Word,(Bool,Word))){return ((x,c),x);}",
          "function unknown(x: Word,c: Bool) returns((Word,Unknown)){return (x,c);}",
          "function many(x: Word,c: Bool) returns((Word,Bool,Word)){return ((x,c),x);}",
          "function unselected(x: Word,c: Bool) returns((Word,Bool)){if(c){return (x,c);}else{return (missing,c);}}"] do
        let source ← parsed declaration
        rejected types source arguments
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 999, .cellRef⟩
  let closure : TypedRuntimeArgument := ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩
  let _ ← check types "function opaque(x: Cell,f: Fn) returns((Cell,Fn)){return (x,f);}" [cell, closure]
    (.pair (.var 1) (.var 0)) (.product cell.type closure.type) (.pair cell.value closure.value) 5
    (by intro store k; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))
  let nominal ← parsed "function nominal(x: N,c: Bool) returns((N,Bool)){return (x,c);}"
  let nominalTypes := (["N"], Core.Ty.namedData ⟨91⟩) :: types
  assertTrue (decide ((compileRuntimeFunction? nominalTypes owner nominal).map (fun c => (c.core,c.returnType)) =
    some (.pair (.var 1) (.var 0), .product (.namedData ⟨91⟩) .bool))) "static structural result required a nominal inhabitant"
  rejected nominalTypes nominal [wordArg 9, boolArg true]
end Tests

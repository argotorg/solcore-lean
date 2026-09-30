import Solcore.Syntax.Parser.Function
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Core.FuelResumptionProperties

/-! Original whole declarations still fail the old entry profile. Their root
call has independent static provenance; actual closure paths are Core-only. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace LocalFunctionApplicationEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"CallEntry", by decide⟩], by decide⟩⟩, 19⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "local-function-entry.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, content.utf8ByteSize⟩)) "complete original declaration range changed"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match original : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [original]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "missing independent annotation meaning")
  | _ => throw (IO.userError "outside fixture annotation grammar")
private structure Declared (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types owner initial params inputs
private def declare (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) : IO (Declared types initial params) := do
  match original : params with
  | [] => return ⟨initial, by rw [original]; exact .nil⟩
  | ⟨span, .typed none name annotation⟩ :: rest =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields changed"
      let m ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declare types (initial.bindFresh owner name.value m.type) rest
        return ⟨tail.inputs, by rw [original]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate original parameter")
  | _ => throw (IO.userError "unsupported original parameter")
private structure Bound (types : TypeNameTable) (initial : LocalInputs) (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial params args inputs
private def bindArgs (types : TypeNameTable) (initial : LocalInputs) (params : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Bound types initial params args) := do
  match original : params, actual : args with
  | [], [] => return ⟨initial, by rw [original, actual]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest, argument :: remaining =>
      let m ← meaning types annotation
      if same : m.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← bindArgs types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest remaining
          return ⟨tail.inputs, by rw [original, actual]; exact .cons (same ▸ m.evidence) unused tail.evidence⟩
        else throw (IO.userError "duplicate actual parameter")
      else throw (IO.userError "actual argument type differs")
  | _, _ => throw (IO.userError "actual argument count differs")
private structure Expression (s : LocalTypeInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers (Resolved.LocalScope.ids s.context) resolved core
  typing : Resolved.HasType s.context resolved type
private def expression (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Expression s source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? (Resolved.LocalScope.ids s.context) id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "original typed row missing")
      | none => throw (IO.userError "original local name missing")
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, .unit, .unit, by rw [original]; exact .unit, .unit, .unit⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← expression s left; let b ← expression s right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        by rw [original]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing⟩
  | _ => throw (IO.userError "outside independent pure children")
termination_by sizeOf source
private structure Application (s : LocalTypeInputs) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates s.names s.context source core type
private def application (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Application s source) := do
  match original : source with
  | ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ =>
      check (span.contains callee.span && span.contains argumentsSpan && argumentsSpan.contains argument.span &&
        decide (callee.span.endByte ≤ argumentsSpan.startByte)) "original one-argument ranges/order changed"
      let f ← expression s callee; let a ← expression s argument
      match shape : f.type with
      | .function parameterType resultType =>
          if same : a.type = parameterType then
            return ⟨.apply f.core a.core, resultType, by
              rw [original]; exact .call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)⟩
          else throw (IO.userError "original argument type differs")
      | _ => throw (IO.userError "original callee is not Function")
  | _ => throw (IO.userError "not exactly one original call argument")
private def table (input output : Core.Ty) : TypeNameTable :=
  [(["F"], .function input output), (["A"], input), (["R"], output), (["Word"], .word), (["Bool"], .bool)]
private def content := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def staticCase (types : TypeNameTable) (text : String) (expected : Core.Expr) (result : Core.Ty)
    (names : List String) (annotations : List Core.Ty) : IO (Syntax.FunctionDecl × LocalTypeInputs) := do
  let source ← parsed text
  let ps ← declare types .empty source.value.signature.parameters.elements
  have _ := RuntimeParametersDeclare.complete ps.evidence
  check (decide (ps.inputs.names = (names.zipIdx.map (fun (name, n) => (name, ⟨owner, n⟩))).reverse ∧
    ps.inputs.context.values = annotations.reverse)) "original static parameter layout changed"
  let ⟨_, [⟨returnSpan, .returnStmt (some returned)⟩]⟩ := source.value.body | throw (IO.userError "not original singleton return")
  check (source.value.body.span.contains returnSpan && returnSpan.contains returned.span) "original return range changed"
  let a ← application ps.inputs returned
  have accepted := a.evidence.complete
  have _ := elaborateLocalFunctionApplication?_sound accepted
  have _ := a.evidence.hasType
  have _ := a.evidence.core_hasType
  have _ := a.evidence.result_unique (elaborateLocalFunctionApplication?_sound accepted)
  have wrong : ¬ LocalFunctionApplicationElaborates ps.inputs.names ps.inputs.context returned
      (.letE .unit (expected.weakenAt 0)) result := by intro evidence; cases evidence
  check (decide (a.core = expected ∧ a.type = result ∧
    elaborateLocalFunctionApplication? ps.inputs.names ps.inputs.context returned = some (expected, result) ∧
    elaborateLocalExpression? ps.inputs.names ps.inputs.context returned = none)) "independent exact call or old pure rejection changed"
  check (decide (Core.infer? ps.inputs.context.values (.letE .unit (expected.weakenAt 0)) = some result))
    "wrong-Core rejection ceased to be a same-typed contrast"
  have _ := wrong
  match clause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.type = result then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          have _ : RuntimeFunctionHeader types source.value.signature result := ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2,
            by rw [clause]; exact .single (same ▸ m.evidence)⟩
          pure ()
        else throw (IO.userError "fixture header is not independently valid")
      else throw (IO.userError "fixture header disagrees")
  | _ => throw (IO.userError "fixture header shape changed")
  check ((compileRuntimeFunction? types owner source).isNone) "new root adapter leaked into old whole compiler"
  return (source, ps.inputs)
private def actualCase (types : TypeNameTable) (text : String) (expected : Core.Expr) (result : Core.Ty)
    (names : List String) (args : List TypedRuntimeArgument) : IO Core.Environment := do
  let (source, statics) ← staticCase types text expected result names (args.map (·.type))
  let actual ← bindArgs types .empty source.value.signature.parameters.elements args
  have _ := RuntimeParametersBind.complete actual.evidence
  have _ := RuntimeParametersBind.erase_values actual.evidence
  check (decide (actual.inputs.names = statics.names ∧ actual.inputs.toTypeInputs.context.values = statics.context.values ∧
    actual.inputs.environment.values = (args.map (·.value)).reverse))
    "same original parameter records did not retain actual values once"
  for fuel in List.range 13 do
    for store in [[], [w 91]] do
      check ((prepareRuntimeFunction? types owner source args).isNone && (runRuntimeFunction? types owner source args fuel store).isNone)
        "static root call was incorrectly integrated into old entry preparation/execution"
  return actual.inputs.environment.values
private theorem callPath {env captured : Core.Environment} {s t : Core.Store} {f a b : Core.Expr}
    {input output : Core.Ty} {v result : Core.Value} {fc ac bc : Nat} (k : List Core.Frame)
    (fp : ∀ k, Core.Steps fc ⟨.eval f env, k, s⟩ ⟨.ret (.closure input output b captured), k, s⟩)
    (ap : ∀ k, Core.Steps ac ⟨.eval a env, k, s⟩ ⟨.ret v, k, s⟩)
    (bp : ∀ k, Core.Steps bc ⟨.eval b (v :: captured), k, s⟩ ⟨.ret result, k, t⟩) :
    Core.Steps (fc + ac + bc + 3) ⟨.eval (.apply f a) env, k, s⟩ ⟨.ret result, k, t⟩ := by
  simpa only [Nat.add_assoc] using Core.Steps.cons .enterApply
    ((fp _).trans (.cons .beginArgument ((ap _).trans (.cons .invokeClosure (bp k)))))
private def runPath (core : Core.Expr) (env : Core.Environment) (s t : Core.Store) (result : Core.Value) (cost : Nat)
    (path : Core.Steps cost (.initial core env s) (.final result t)) : IO Unit := do
  have _ := path.runStateful_done_iff (fuel := cost)
  for fuel in List.range (cost + 3) do
    check (match Core.runStateful fuel (.initial core env s) with
      | .done value final => decide (cost ≤ fuel ∧ value = result ∧ final = t)
      | .outOfFuel _ => decide (fuel < cost)
      | .fault .. => false) "independent Core-only path threshold/value/store changed"
  for spent in List.range cost do
    match stopped : Core.runStateful spent (.initial core env s) with
    | .outOfFuel checkpoint =>
        have _ := path.residual_of_outOfFuel stopped
        have _ := Core.runStateful_resume stopped (cost - spent)
        check (decide (Core.runStateful (cost - spent) checkpoint = .done result t)) "genuine call residual changed"
    | _ => throw (IO.userError "genuine suspended call missing")
private def closure (type : Core.Ty) : TypedRuntimeArgument :=
  ⟨.function type type, .closure type type (.var 0) [], .closure .nil (.var rfl)⟩
private def identityCases : IO Unit := do
  for argument in [(⟨.word, w 9, .word⟩ : TypedRuntimeArgument), ⟨.unit, .unit, .unit⟩,
      ⟨.cell .word, .cellRef .word 700, .cellRef⟩, closure .word] do
    let f := closure argument.type
    let env ← actualCase (table argument.type argument.type) content (.apply (.var 1) (.var 0)) argument.type ["f", "x"] [f, argument]
    for s in [[], [w 91]] do
      if same : env = [argument.value, f.value] then
        have p (k) : Core.Steps 6 ⟨.eval (.apply (.var 1) (.var 0)) env, k, s⟩ ⟨.ret argument.value, k, s⟩ := by
          subst env
          exact callPath k (fun _ => .cons (.var rfl) .refl) (fun _ => .cons (.var rfl) .refl) (fun _ => .cons (.var rfl) .refl)
        runPath _ env s s argument.value 6 (p [])
        check (decide (Core.runStateful 2 (.initial (.apply (.var 1) (.var 0)) env s) =
          .outOfFuel ⟨.ret f.value, [.applyArgument (.var 0) env], s⟩ ∧
          Core.runStateful 4 (.initial (.apply (.var 1) (.var 0)) env s) =
          .outOfFuel ⟨.ret argument.value, [.applyClosure argument.type argument.type (.var 0) []], s⟩)) "caller/captured call frames changed"
        have _ := p [.unaryApply .wordNot]
        let k : List Core.Frame := [.unaryApply .wordNot]
        check (match Core.runStateful 6 ⟨.eval (.apply (.var 1) (.var 0)) env, k, s⟩ with
          | .outOfFuel endpoint => decide (argument.type = .word ∧ endpoint = ⟨.ret argument.value, k, s⟩)
          | .fault error endpoint => decide (error = .invalidUnaryOperand .wordNot argument.value ∧ endpoint = ⟨.ret argument.value, k, s⟩)
          | _ => false) "arbitrary continuation endpoint was mistaken for completion or unconditional exhaustion"
      else throw (IO.userError "original actual order differs")
private def delayed : Nat → Core.Expr | 0 => .word (Core.Word.ofNatModulo 7) | n + 1 => .letE .unit (delayed n)
private theorem delayedTyped (n : Nat) (ctx : Core.Context) : Core.HasType ctx (delayed n) .word := by
  induction n generalizing ctx with
  | zero => exact .word
  | succ n ih => exact .letE .unit (ih _)
private theorem delayedPath (n : Nat) (env : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (3 * n + 1) ⟨.eval (delayed n) env, k, s⟩ ⟨.ret (w 7), k, s⟩ := by
  induction n generalizing env with
  | zero => exact .cons .word .refl
  | succ n ih => simpa [delayed, Nat.mul_succ, Nat.add_assoc] using Core.Steps.cons .enterLet (.cons .unit (.cons .bindLet (ih (.unit :: env))))
private def capturedAndCosts : IO Unit := do
  for x in [9, 14] do
    let captured : TypedRuntimeArgument := ⟨.function .word .word, .closure .word .word (.var 1) [w 7],
      .closure (.cons .word .nil) (.var rfl)⟩
    let _ ← actualCase (table .word .word) content (.apply (.var 1) (.var 0)) .word ["f", "x"] [captured, ⟨.word, w x, .word⟩]
    for s in [[], [w 91]] do
      runPath (.apply (.var 1) (.var 0)) [w x, captured.value] s s (w 7) 6
        (callPath [] (fun _ => .cons (.var rfl) .refl) (fun _ => .cons (.var rfl) .refl) (fun _ => .cons (.var rfl) .refl))
      check (decide (Core.runStateful 4 (.initial (.apply (.var 1) (.var 0)) [w x, captured.value] s) =
        .outOfFuel ⟨.ret (w x), [.applyClosure .word .word (.var 1) [w 7]], s⟩)) "caller value replaced lexical capture"
    for n in [0, 1, 4, 9] do
      let f : TypedRuntimeArgument := ⟨.function .word .word, .closure .word .word (delayed n) [], .closure .nil (delayedTyped n _)⟩
      let _ ← actualCase (table .word .word) content (.apply (.var 1) (.var 0)) .word ["f", "x"] [f, ⟨.word, w x, .word⟩]
      have p : Core.Steps (3 * n + 6) (.initial (.apply (.var 1) (.var 0)) [w x, f.value] []) (.final (w 7) []) := by
        have raw := callPath (env := [w x, f.value]) (f := .var 1) (a := .var 0) []
          (fun _ => Core.Steps.cons (.var rfl) .refl) (fun _ => Core.Steps.cons (.var rfl) .refl) (delayedPath n [w x] [])
        have amount : 1 + 1 + (3 * n + 1) + 3 = 3 * n + 6 := by omega
        exact amount ▸ raw
      runPath _ _ [] [] (w 7) _ p
private def unitAndProduct : IO Unit := do
  let _ ← actualCase (table .unit .unit) "function invoke(f:F) returns(R){return f(());}"
    (.apply (.var 0) .unit) .unit ["f"] [closure .unit]
  let _ ← actualCase (table (.product .word .bool) (.product .word .bool)) "function invoke(f:F,x:Word,y:Bool) returns(R){return f((x,y));}"
    (.apply (.var 2) (.pair (.var 1) (.var 0))) (.product .word .bool) ["f", "x", "y"] [closure (.product .word .bool), ⟨.word, w 9, .word⟩, ⟨.bool, .bool true, .bool⟩]
  for s in [[], [w 91]] do
    runPath (.apply (.var 0) .unit) [(closure .unit).value] s s .unit 6
      (callPath [] (fun _ => .cons (.var rfl) .refl) (fun _ => .cons .unit .refl) (fun _ => .cons (.var rfl) .refl))
    runPath (.apply (.var 2) (.pair (.var 1) (.var 0))) [.bool true, w 9, (closure (.product .word .bool)).value] s s (.pair (w 9) (.bool true)) 10
      (callPath [] (fun _ => .cons (.var rfl) .refl) (fun _ => .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))
        (fun _ => .cons (.var rfl) .refl))
private def storeBoundaries : IO Unit := do
  let load : TypedRuntimeArgument := ⟨.function (.cell .word) .word, .closure (.cell .word) .word (.loadCell (.var 0)) [],
    .closure .nil (.loadCell (.var rfl))⟩
  let env ← actualCase (table (.cell .word) .word) content (.apply (.var 1) (.var 0)) .word ["f", "x"] [load, ⟨.cell .word, .cellRef .word 0, .cellRef⟩]
  check (decide (Core.runStateful 7 (.initial (.apply (.var 1) (.var 0)) env []) =
    .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩)) "structural typing falsely guaranteed allocated cells"
  runPath (.apply (.var 1) (.var 0)) [.cellRef .word 0, load.value] [w 23] [w 23] (w 23) 8
    (callPath [] (fun _ => .cons (.var rfl) .refl) (fun _ => .cons (.var rfl) .refl)
      (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))
  let alloc : TypedRuntimeArgument := ⟨.function .word (.cell .word), .closure .word (.cell .word) (.newCell .word (.var 0)) [],
    .closure .nil (.newCell (.var rfl))⟩
  let _ ← actualCase (table .word (.cell .word)) content (.apply (.var 1) (.var 0)) (.cell .word) ["f", "x"] [alloc, ⟨.word, w 9, .word⟩]
  for s in [[], [w 91]] do
    runPath (.apply (.var 1) (.var 0)) [w 9, alloc.value] s (s ++ [w 9]) (.cellRef .word s.length) 8
      (callPath [] (fun _ => .cons (.var rfl) .refl) (fun _ => .cons (.var rfl) .refl)
        (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))))
end LocalFunctionApplicationEntries
open LocalFunctionApplicationEntries
def frontendParsedLocalFunctionApplicationEntryTests : IO Unit := do
  identityCases; capturedAndCosts; unitAndProduct; storeBoundaries
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨99⟩) (.cell (.namedData ⟨17⟩))] do
    let _ ← staticCase (table type type) content (.apply (.var 1) (.var 0)) type ["f", "x"] [.function type type, type]
    pure ()
end Tests

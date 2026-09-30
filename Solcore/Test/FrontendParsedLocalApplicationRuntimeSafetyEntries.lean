import Solcore.Syntax.Parser.Function
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Core.FuelResumptionProperties

/-! The original parameter binding is checked against an actual runtime world.
Typed stores and typed outer frames justify safety, not structural values alone. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace LocalApplicationRuntimeSafetyEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"SafeActualCall", by decide⟩], by decide⟩⟩, 23⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def text := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def parsed : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "runtime-safe-local-call.sol"⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) "original declaration range changed"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match original : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [original]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside annotation fixture")
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
  | _ => throw (IO.userError "outside parameter fixture")
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
      else throw (IO.userError "actual type differs")
  | _, _ => throw (IO.userError "actual arity differs")
private structure Reference (s : LocalTypeInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.context.ids resolved core
  typing : Resolved.HasType s.context resolved type
private def reference (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Reference s source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "original typed row missing")
      | none => throw (IO.userError "original local name missing")
  | _ => throw (IO.userError "not original identifier")
private structure Call (s : LocalTypeInputs) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates s.names s.context source core type
private structure OriginalCall (source : Syntax.Expr) where
  span : Syntax.SourceSpan
  argumentsSpan : Syntax.SourceSpan
  callee : Syntax.Expr
  argument : Syntax.Expr
  shape : source = ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩
private def callShape (source : Syntax.Expr) : IO (OriginalCall source) := do
  match original : source with
  | ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ => return ⟨span, argumentsSpan, callee, argument, original⟩
  | _ => throw (IO.userError "not original singleton call")
private def application (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Call s source) := do
  let original ← callShape source
  let span := original.span; let argumentsSpan := original.argumentsSpan
  let callee := original.callee; let argument := original.argument
  check (span.contains callee.span && span.contains argumentsSpan && argumentsSpan.contains argument.span &&
    decide (callee.span.endByte ≤ argumentsSpan.startByte)) "call child ranges/order changed"
  let f ← reference s callee; let a ← reference s argument
  match shape : f.type with
  | .function input output =>
      if same : a.type = input then
        return ⟨.apply f.core a.core, output, by
          rw [original.shape]
          exact .call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)⟩
      else throw (IO.userError "argument type differs")
  | _ => throw (IO.userError "callee not Function")
private def table (input output : Core.Ty) : TypeNameTable :=
  [(["F"], .function input output), (["A"], input), (["R"], output)]
private def staticCase (input output : Core.Ty) : IO (Syntax.FunctionDecl × LocalTypeInputs) := do
  let source ← parsed; let types := table input output
  let ps ← declare types .empty source.value.signature.parameters.elements
  have _ := RuntimeParametersDeclare.complete ps.evidence
  check (decide (ps.inputs.names = [("x", ⟨owner, 1⟩), ("f", ⟨owner, 0⟩)] ∧
    ps.inputs.context.values = [input, .function input output])) "parameter-only static layout changed"
  let ⟨_, [⟨returnSpan, .returnStmt (some returned)⟩]⟩ := source.value.body | throw (IO.userError "not original return")
  check (source.value.body.span.contains returnSpan && returnSpan.contains returned.span) "return range changed"
  let a ← application ps.inputs returned
  check (decide (a.core = target ∧ a.type = output ∧
    elaborateLocalFunctionApplication? ps.inputs.names ps.inputs.context returned = some (target, output) ∧
    elaborateLocalExpression? ps.inputs.names ps.inputs.context returned = none)) "independent original call differs"
  match clause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.type = output then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          have _ : RuntimeFunctionHeader types source.value.signature output := ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2,
            by rw [clause]; exact .single (same ▸ m.evidence)⟩
          pure ()
        else throw (IO.userError "header policy changed")
      else throw (IO.userError "return type differs")
  | _ => throw (IO.userError "return clause differs")
  check ((compileRuntimeFunction? types owner source).isNone) "source call entered old compilation"
  return (source, ps.inputs)
private structure Observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : Type where
  evidence : ∀ store, LocalExpressionEvaluatesWithCost inputs.names inputs.environment store source value store 1
private def observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : IO (Observed inputs source value) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | some id =>
          if found : inputs.environment.lookup? id = some value then
            return ⟨fun _ => by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          else throw (IO.userError "actual row value changed")
      | none => throw (IO.userError "actual name missing")
  | _ => throw (IO.userError "raw child changed")
private def execute (argument : TypedRuntimeArgument) (output : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (world : Core.StoreTyping) (s t : Core.Store) (value : Core.Value) (bodyCost : Nat)
    (argumentTyped : Core.RuntimeValueHasType world argument.value argument.type)
    (closureTyped : Core.RuntimeValueHasType world (.closure argument.type output body captured) (.function argument.type output))
    (storeTyped : Core.StoreHasTypes world s)
    (bodyEvaluation : Core.Evaluates (argument.value :: captured) s body value t)
    (bodyPath : ∀ k, Core.Steps bodyCost ⟨.eval body (argument.value :: captured), k, s⟩ ⟨.ret value, k, t⟩)
    (k : List Core.Frame) (resultType : Core.Ty) (continuationTyped : Core.ContinuationHasType world k output resultType)
    (afterCost : Nat) (result : Core.Value)
    (afterPath : Core.Steps afterCost ⟨.ret value, k, t⟩ (.final result t)) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output, .closure argument.type output body captured, closureTyped.erase⟩
  let args := [f, argument]; let types := table argument.type output
  let (source, statics) ← staticCase argument.type output
  let actual ← bindArgs types .empty source.value.signature.parameters.elements args
  have _ := RuntimeParametersBind.complete actual.evidence
  have _ := RuntimeParametersBind.erase_values actual.evidence
  check (decide (actual.inputs.names = statics.names ∧ actual.inputs.context = statics.context ∧
    actual.inputs.bindings.map (fun b => (b.name, b.id, b.type, b.value)) =
      [("x", ⟨owner, 1⟩, argument.type, argument.value), ("f", ⟨owner, 0⟩, f.type, f.value)])) "original actual parameter records differ"
  let rows : PLift (actual.inputs.environment.values = (args.map (·.value)).reverse ∧
      actual.inputs.context.values = [argument.type, f.type]) ←
    if same : actual.inputs.environment.values = (args.map (·.value)).reverse ∧
        actual.inputs.context.values = [argument.type, f.type] then pure ⟨same⟩
    else throw (IO.userError "original projections lost their order")
  have runtimeTyped : Core.RuntimeEnvironmentHasTypes world actual.inputs.environment.values actual.inputs.context.values := by
    rw [rows.down.1, rows.down.2]; exact .cons argumentTyped (.cons closureTyped .nil)
  let ⟨_, [⟨_, .returnStmt (some returned)⟩]⟩ := source.value.body | throw (IO.userError "original return changed")
  let call ← application actual.inputs.toTypeInputs returned
  if acceptedCore : call.core = target ∧ call.type = output then
    have elaboration : LocalFunctionApplicationElaborates actual.inputs.names actual.inputs.context returned target output := by
      simpa only [acceptedCore.1, acceptedCore.2, LocalInputs.toTypeInputs_names, LocalInputs.toTypeInputs_context] using call.evidence
    let original ← callShape returned
    have elaboration := Eq.mp (congrArg (fun src =>
      LocalFunctionApplicationElaborates actual.inputs.names actual.inputs.context src target output) original.shape) elaboration
    let fp ← observed actual.inputs original.callee f.value
    let ap ← observed actual.inputs original.argument argument.value
    have raw := LocalFunctionApplicationEvaluates.call (span := original.span) (argumentsSpan := original.argumentsSpan)
      (fp.evidence s).erase (ap.evidence s).erase bodyEvaluation
    have costed := LocalFunctionApplicationEvaluatesWithCost.call (span := original.span) (argumentsSpan := original.argumentsSpan)
      (fp.evidence s) (ap.evidence s) (bodyPath [])
    have manual (continuation) : Core.Steps (bodyCost + 5)
        ⟨.eval target actual.inputs.environment.values, continuation, s⟩ ⟨.ret value, continuation, t⟩ := by
      rw [rows.down.1]
      exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (bodyPath continuation)))))
    have _ := raw.preserves_runtime_type elaboration actual.inputs.sameIds runtimeTyped storeTyped
    have _ := elaboration.hasType.runtime_evaluates actual.inputs.sameIds runtimeTyped storeTyped ⟨value, t, raw⟩
    have agreement : ∃ finalWorld, Core.WorldExtends world finalWorld ∧ Core.RuntimeStoreHasTypes finalWorld t ∧
        Core.RuntimeValueHasType finalWorld value output ∧ finalWorld.length = t.length := by
      obtain ⟨future, final, v, count, extension, typedStore, typedValue, evaluation, _⟩ :=
        elaboration.runtime_typed_execution actual.inputs.sameIds runtimeTyped storeTyped ⟨value, t, raw⟩
      obtain ⟨rfl, rfl, _⟩ := costed.deterministic evaluation
      exact ⟨future, extension, typedStore, typedValue, typedStore.length_eq⟩
    have _ := agreement
    have _ := elaboration.runtime_state_hasType runtimeTyped storeTyped continuationTyped
    let cost := bodyCost + 5
    for fuel in List.range (cost + afterCost + 3) do
      have _ := elaboration.runtime_run_never_faults runtimeTyped storeTyped continuationTyped fuel
      have _ := elaboration.runtime_run_never_faults runtimeTyped storeTyped (.nil : Core.ContinuationHasType world [] output output) fuel
      check ((prepareRuntimeFunction? types owner source args).isNone &&
        (runRuntimeFunction? types owner source args fuel s).isNone) "runtime-world proofs leaked into old entry"
      match done : Core.runStateful fuel (.initial target actual.inputs.environment.values s) with
      | .done v final =>
          have _ := elaborateLocalFunctionApplication?_runtime_run_done_sound elaboration.complete actual.inputs.sameIds runtimeTyped storeTyped done
          check (decide (cost ≤ fuel ∧ v = value ∧ final = t)) "closed runtime-safe call differs"
      | .outOfFuel _ => check (decide (fuel < cost)) "closed exact cost differs"
      | .fault .. => throw (IO.userError "runtime-world typed closed call faulted")
      check (match Core.runStateful fuel ⟨.eval target actual.inputs.environment.values, k, s⟩ with
        | .done v final => decide (cost + afterCost ≤ fuel ∧ v = result ∧ final = t)
        | .outOfFuel _ => decide (fuel < cost + afterCost)
        | .fault .. => false) "typed pending continuation differs"
    have _ := (manual k).trans afterPath
    check (decide (Core.runStateful cost ⟨.eval target actual.inputs.environment.values, k, s⟩ =
      .outOfFuel ⟨.ret value, k, t⟩)) "typed continuation did not retain actual final store"
    for spent in List.range (cost + afterCost) do
      match exhausted : Core.runStateful spent ⟨.eval target actual.inputs.environment.values, k, s⟩ with
      | .outOfFuel checkpoint =>
          have _ := elaboration.runtime_checkpoint_hasType runtimeTyped storeTyped continuationTyped exhausted
          for additional in [0, 1, cost + afterCost - spent, cost + afterCost + 2] do
            have _ := elaboration.runtime_checkpoint_never_faults runtimeTyped storeTyped continuationTyped exhausted additional
            have _ := Core.runStateful_resume exhausted additional
            check (decide (Core.runStateful additional checkpoint = Core.runStateful (spent + additional)
              ⟨.eval target actual.inputs.environment.values, k, s⟩)) "genuine typed checkpoint changed on resume"
          check (decide (Core.runStateful (cost + afterCost - spent) checkpoint = .done result t)) "typed residual did not complete"
      | _ => throw (IO.userError "genuine typed checkpoint missing")
  else throw (IO.userError "independent original call Core/type changed")
end LocalApplicationRuntimeSafetyEntries
open LocalApplicationRuntimeSafetyEntries
def frontendParsedLocalApplicationRuntimeSafetyEntryTests : IO Unit := do
  for x in [9, 14] do
    execute ⟨.word, w x, .word⟩ (.cell .word) (.newCell .word (.var 0)) [] [] [] [w x] (.cellRef .word 0) 3
      .word (.closure .nil (.newCell (.var rfl))) .nil (.newCell (.var rfl))
      (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
      [.loadCellApply] .word (.cons .loadCellApply .nil) 1 (w x) (.cons (.applyLoadCell rfl) .refl)
  for current in [3, 17] do
    have storeTyped : Core.StoreHasTypes [.word] [w current] := by
      simpa only [Core.Store.allocate, List.nil_append, w] using
        (Core.StoreHasTypes.nil.allocate Core.CellPayload.word (Core.ValueHasType.word (value := Core.Word.ofNatModulo current)))
    execute ⟨.unit, .unit, .unit⟩ (.cell .word) (.newCell .word (.loadCell (.var 1))) [.cellRef .word 0]
      [.word] [w current] [w current, w current] (.cellRef .word 1) 5
      .unit (.closure (.cons (.cellRef rfl) .nil) (.newCell (.loadCell (.var rfl)))) storeTyped
      (.newCell (.loadCell (.var rfl) rfl))
      (fun _ => .cons .enterNewCell (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) (.cons .applyNewCell .refl)))))
      [.loadCellApply] .word (.cons .loadCellApply .nil) 1 (w current) (.cons (.applyLoadCell rfl) .refl)
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨4⟩) (.namedData ⟨8⟩)] do
    let argument : TypedRuntimeArgument := ⟨.function type type, .closure type type (.var 0) [], .closure .nil (.var rfl)⟩
    execute argument argument.type (.var 0) [] [] [] [] argument.value 1
      (.closure .nil (.var rfl)) (.closure .nil (.var rfl)) .nil (.var rfl) (fun _ => .cons (.var rfl) .refl)
      [.letBody .unit []] .unit (.cons (.letBody .nil .unit) .nil) 2 .unit (.cons .bindLet (.cons .unit .refl))
end Tests

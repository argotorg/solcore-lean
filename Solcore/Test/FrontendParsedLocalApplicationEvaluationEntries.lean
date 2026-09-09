import Solcore.Syntax.Parser.Function
import Solcore.Frontend.LocalFunctionApplicationExecutionProperties
import Solcore.Frontend.RuntimeFunctionEntryProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties
import Solcore.Frontend.RuntimeParameterDeclarationBindingProperties
import Solcore.Frontend.LocalInputsProperties
import Solcore.Core.FuelResumptionProperties

/-! Original whole declarations retain their entry rejection. Independent
parameter records and actual closure bodies now feed the source-call laws. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace LocalApplicationEvaluationEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ActualCall", by decide⟩], by decide⟩⟩, 23⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def text := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def parsed : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "actual-local-call.sol"⟩, text⟩
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
  have wrong : ¬ LocalFunctionApplicationElaborates ps.inputs.names ps.inputs.context returned
      (.letE .unit (target.weakenAt 0)) output := by intro evidence; cases evidence
  have _ := wrong
  check (decide (Core.infer? ps.inputs.context.values (.letE .unit (target.weakenAt 0)) = some output)) "wrong Core not same typed"
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
    (closureTyped : Core.ValueHasType (.closure argument.type output body captured) (.function argument.type output))
    (value : Core.Store → Core.Value) (finalStore : Core.Store → Core.Store) (bodyCost : Nat)
    (bodyEvaluation : ∀ s, Core.Evaluates (argument.value :: captured) s body (value s) (finalStore s))
    (bodyPath : ∀ s k, Core.Steps bodyCost ⟨.eval body (argument.value :: captured), k, s⟩ ⟨.ret (value s), k, finalStore s⟩) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output, .closure argument.type output body captured, closureTyped⟩
  let args := [f, argument]; let types := table argument.type output
  let (source, statics) ← staticCase argument.type output
  let actual ← bindArgs types .empty source.value.signature.parameters.elements args
  have _ := RuntimeParametersBind.complete actual.evidence
  have _ := RuntimeParametersBind.erase_values actual.evidence
  check (decide (actual.inputs.names = statics.names ∧ actual.inputs.context = statics.context ∧
    actual.inputs.environment.values = (args.map (·.value)).reverse ∧
    actual.inputs.bindings.map (fun b => (b.name, b.id, b.type, b.value)) =
      [("x", ⟨owner, 1⟩, argument.type, argument.value), ("f", ⟨owner, 0⟩, f.type, f.value)])) "actual records/order changed"
  let ⟨_, [⟨_, .returnStmt (some returned)⟩]⟩ := source.value.body | throw (IO.userError "original body changed")
  let call ← application actual.inputs.toTypeInputs returned
  if originalCore : call.core = target then
    have elaboration : LocalFunctionApplicationElaborates actual.inputs.names actual.inputs.context returned target call.type := by
      simpa only [originalCore, LocalInputs.toTypeInputs_names, LocalInputs.toTypeInputs_context] using call.evidence
    let original ← callShape returned
    let span := original.span; let argumentsSpan := original.argumentsSpan
    let callee := original.callee; let arg := original.argument
    have elaboration := Eq.mp (congrArg (fun src =>
      LocalFunctionApplicationElaborates actual.inputs.names actual.inputs.context src target call.type) original.shape) elaboration
    let functionObserved ← observed actual.inputs callee f.value
    let argumentObserved ← observed actual.inputs arg argument.value
    let actualValues : PLift (actual.inputs.environment.values = [argument.value, f.value]) ←
      if same : actual.inputs.environment.values = [argument.value, f.value] then pure ⟨same⟩
      else throw (IO.userError "original runtime values not retained")
    for s in [[], [w 91, w 73]] do
      have manual (k) : Core.Steps (bodyCost + 5)
          ⟨.eval target actual.inputs.environment.values, k, s⟩ ⟨.ret (value s), k, finalStore s⟩ := by
        rw [actualValues.down]
        exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument
          (.cons (.var rfl) (.cons .invokeClosure (bodyPath s k)))))
      have raw : LocalFunctionApplicationEvaluates actual.inputs.names actual.inputs.environment s
          ⟨span, .call callee ⟨argumentsSpan, [arg]⟩⟩ (value s) (finalStore s) :=
        .call (functionObserved.evidence s).erase (argumentObserved.evidence s).erase (bodyEvaluation s)
      have costed := LocalFunctionApplicationEvaluatesWithCost.call (span := span) (argumentsSpan := argumentsSpan)
        (functionObserved.evidence s) (argumentObserved.evidence s) (bodyPath s [])
      have path := costed.toSteps elaboration actual.inputs.sameIds
      have _ := raw.deterministic costed.erase
      have _ := raw.exists_cost
      have _ := localFunctionApplicationEvaluates_iff_exists_cost.mpr ⟨_, costed⟩
      have reflected := elaboration.evaluatesWithCost_iff_steps actual.inputs.sameIds |>.mpr (manual [])
      have _ := costed.deterministic reflected
      have _ := costed.cost_unique reflected
      have _ := costed.cost_pos
      have _ := elaboration.evaluates_iff actual.inputs.sameIds |>.mpr ((elaboration.evaluates_iff actual.inputs.sameIds).mp raw)
      have _ := elaboration.evaluates_iff_exists_uniform_steps actual.inputs.sameIds |>.mp raw
      have _ := elaborateLocalFunctionApplication?_evaluates_iff elaboration.complete actual.inputs.sameIds |>.mp raw
      have _ := elaborateLocalFunctionApplication?_evaluatesWithCost_iff_steps elaboration.complete actual.inputs.sameIds |>.mp costed
      let cost := bodyCost + 5
      for fuel in List.range (cost + 3) do
        check ((prepareRuntimeFunction? types owner source args).isNone &&
          (runRuntimeFunction? types owner source args fuel s).isNone) "call leaked into old whole entry"
        check (match Core.runStateful fuel (.initial target actual.inputs.environment.values s) with
          | .done v t => decide (cost ≤ fuel ∧ v = value s ∧ t = finalStore s)
          | .outOfFuel _ => decide (fuel < cost)
          | .fault .. => false) "independent source call cost/value/store differs"
      check (decide (Core.runStateful 2 (.initial target actual.inputs.environment.values s) =
        .outOfFuel ⟨.ret f.value, [.applyArgument (.var 0) actual.inputs.environment.values], s⟩ ∧
        Core.runStateful 4 (.initial target actual.inputs.environment.values s) =
        .outOfFuel ⟨.ret argument.value, [.applyClosure argument.type output body captured], s⟩)) "actual caller/capture frames differ"
      for spent in List.range cost do
        match stopped : Core.runStateful spent (.initial target actual.inputs.environment.values s) with
        | .outOfFuel checkpoint =>
            have _ := path.residual_of_outOfFuel stopped
            for more in [0, 1, cost - spent, cost + 2] do
              have _ := Core.runStateful_resume stopped more
              check (decide (Core.runStateful more checkpoint = Core.runStateful (spent + more)
                (.initial target actual.inputs.environment.values s))) "genuine checkpoint did not resume full state"
            check (decide (Core.runStateful (cost - spent) checkpoint = .done (value s) (finalStore s))) "remaining fuel differs"
            if spent = 4 then
              match middle : Core.runStateful 1 checkpoint with
              | .outOfFuel next =>
                  have _ := Core.runStateful_resume middle (cost - 5)
                  check (decide (Core.runStateful (cost - 5) next = .done (value s) (finalStore s))) "actual three-chunk continuation differs"
              | _ => throw (IO.userError "actual body-entry checkpoint missing")
        | _ => throw (IO.userError "missing genuine call checkpoint")
      let k : List Core.Frame := [.unaryApply .wordNot]
      have _ := costed.toStepsWithContinuation elaboration actual.inputs.sameIds k
      check (match Core.UnaryOp.wordNot.apply (value s), Core.runStateful cost ⟨.eval target actual.inputs.environment.values, k, s⟩ with
        | some _, .outOfFuel endpoint => decide (endpoint = ⟨.ret (value s), k, finalStore s⟩)
        | none, .fault error endpoint => decide (error = .invalidUnaryOperand .wordNot (value s) ∧ endpoint = ⟨.ret (value s), k, finalStore s⟩)
        | _, _ => false) "pending continuation endpoint was confused with closed completion"
  else throw (IO.userError "actual static lowering changed")
private def delayed : Nat → Core.Expr | 0 => .word (Core.Word.ofNatModulo 7) | n + 1 => .letE .unit (delayed n)
private theorem delayedTyped (n : Nat) (ctx : Core.Context) : Core.HasType ctx (delayed n) .word := by
  induction n generalizing ctx with
  | zero => exact .word
  | succ n ih => exact .letE .unit (ih _)
private theorem delayedEvaluation (n : Nat) (env : Core.Environment) (s : Core.Store) :
    Core.Evaluates env s (delayed n) (w 7) s := by
  induction n generalizing env with
  | zero => exact .word
  | succ n ih => exact .letE .unit (ih _)
private theorem delayedPath (n : Nat) (env : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (3 * n + 1) ⟨.eval (delayed n) env, k, s⟩ ⟨.ret (w 7), k, s⟩ := by
  induction n generalizing env with
  | zero => exact .cons .word .refl
  | succ n ih => simpa [delayed, Nat.mul_succ, Nat.add_assoc] using Core.Steps.cons .enterLet (.cons .unit (.cons .bindLet (ih (.unit :: env))))
end LocalApplicationEvaluationEntries
open LocalApplicationEvaluationEntries
def frontendParsedLocalApplicationEvaluationEntryTests : IO Unit := do
  for argument in [(⟨.word, w 9, .word⟩ : TypedRuntimeArgument), ⟨.unit, .unit, .unit⟩,
      ⟨.cell .word, .cellRef .word 700, .cellRef⟩,
      ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩] do
    execute argument argument.type (.var 0) [] (.closure .nil (.var rfl)) (fun _ => argument.value) id 1
      (fun _ => .var rfl) (fun _ _ => .cons (.var rfl) .refl)
  for x in [9, 14] do
    let argument : TypedRuntimeArgument := ⟨.word, w x, .word⟩
    execute argument .word (.var 1) [w 7] (.closure (.cons .word .nil) (.var rfl)) (fun _ => w 7) id 1
      (fun _ => .var rfl) (fun _ _ => .cons (.var rfl) .refl)
    for n in [0, 1, 4, 9] do
      execute argument .word (delayed n) [] (.closure .nil (delayedTyped n _)) (fun _ => w 7) id (3 * n + 1)
        (delayedEvaluation n [w x]) (delayedPath n [w x])
    execute argument (.cell .word) (.newCell .word (.var 0)) [] (.closure .nil (.newCell (.var rfl) .word))
      (fun s => .cellRef .word s.length) (fun s => s ++ [w x]) 3
      (fun _ => .newCell (.var rfl)) (fun _ _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨99⟩) (.cell (.namedData ⟨17⟩))] do
    let _ ← staticCase type type
    pure ()
end Tests

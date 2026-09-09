import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeApplicationFunctionFactorizationProperties
import Solcore.Frontend.LocalApplicationReturnBodyRunnerProperties

/-! Value-free original declarations establish their own compilation evidence.
Only the separate Unit/Word smoke supplies actual arguments; nominal types do not. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRuntimeApplicationCompilation
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"CompileApplication", by decide⟩], by decide⟩⟩, n⟩
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def standard := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def parsed (text : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "compile-application.sol"⟩, text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing failed")
  let .ok source next := Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError s!"original declaration did not parse: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) s!"original full declaration range changed: {text}"
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
  | ⟨_, .tuple []⟩ => return ⟨.unit, by rw [original]; exact .unit⟩
  | ⟨_, .tuple [single]⟩ =>
      let m ← meaning types single
      return ⟨m.type, by rw [original]; exact .single m.evidence⟩
  | ⟨_, .tuple [left, right]⟩ =>
      let a ← meaning types left; let b ← meaning types right
      return ⟨.product a.type b.type, by rw [original]; exact .pair a.evidence b.evidence⟩
  | _ => throw (IO.userError "outside independent annotation fixture")
termination_by sizeOf source
private structure Declared (types : TypeNameTable) (o : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (params : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types o initial params inputs
private def declare (types : TypeNameTable) (o : Resolved.DeclarationId) (initial : LocalTypeInputs)
    (params : List Syntax.FunctionParameter) : IO (Declared types o initial params) := do
  match original : params with
  | [] => return ⟨initial, by rw [original]; exact .nil⟩
  | ⟨s, .typed none name annotation⟩ :: rest =>
      check (s.contains name.span && s.contains annotation.span) "original parameter fields changed"
      let m ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declare types o (initial.bindFresh o name.value m.type) rest
        return ⟨tail.inputs, by rw [original]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate original parameter")
  | _ => throw (IO.userError "outside declaration fixture")
private structure Header (types : TypeNameTable) (signature : Syntax.FunctionSignature) where
  type : Core.Ty
  evidence : RuntimeFunctionHeader types signature type
private def header (types : TypeNameTable) (signature : Syntax.FunctionSignature) : IO (Header types signature) := do
  if policy : signature.genericParameters = none ∧ signature.whereClause = none ∧
      signature.modifiers.publicMarker = none ∧ signature.modifiers.payableMarker = none then
    match clause : signature.returnsClause with
    | none => return ⟨.unit, ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, by rw [clause]; exact .absent⟩⟩
    | some ⟨_, ⟨_, [annotation]⟩⟩ =>
        let m ← meaning types annotation
        return ⟨m.type, ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2, by rw [clause]; exact .single m.evidence⟩⟩
    | _ => throw (IO.userError "not absent or exactly one return annotation")
  else throw (IO.userError "unsupported original header")
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
          | _, _ => throw (IO.userError "original context row missing")
      | none => throw (IO.userError "original name missing")
  | _ => throw (IO.userError "not original identifier")
private structure Body (s : LocalTypeInputs) (body : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalApplicationReturnBodyElaborates s.names s.context body core type
private def body (s : LocalTypeInputs) (body : Syntax.Block) : IO (Body s body) := do
  match original : body with
  | ⟨bs, [⟨rs, .returnStmt (some ⟨span, .call callee ⟨argsSpan, [argument]⟩⟩)⟩]⟩ =>
      check (bs.contains rs && rs.contains span && span.contains callee.span && span.contains argsSpan &&
        argsSpan.contains argument.span && decide (callee.span.endByte ≤ argsSpan.startByte)) "original body/call spans changed"
      let f ← reference s callee; let a ← reference s argument
      match shape : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core, output, by
            rw [original]; exact .application (.call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing))⟩
          else throw (IO.userError "original argument type differs")
      | _ => throw (IO.userError "original callee is not Function")
  | _ => throw (IO.userError "not original singleton application return")
private def table (input output : Core.Ty) : TypeNameTable :=
  [(["F"], .function input output), (["mod", "F"], .function input output), (["A"], input), (["R"], output), (["Unit"], .unit)]
private def fields (c : CompiledRuntimeFunction) := (c.inputs.names, c.inputs.context, c.core, c.returnType)
private structure Ready (types : TypeNameTable) (o : Resolved.DeclarationId) where
  source : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  evidence : RuntimeApplicationFunctionCompiles types o source compiled
private def positive (input output : Core.Ty) (o : Resolved.DeclarationId) (text : String) : IO (Ready (table input output) o) := do
  let types := table input output; let source ← parsed text
  let ps ← declare types o .empty source.value.signature.parameters.elements
  let h ← header types source.value.signature; let b ← body ps.inputs source.value.body
  if expected : h.type = output ∧ b.type = output ∧ b.core = target then
    let compiled : CompiledRuntimeFunction := ⟨ps.inputs, target, output⟩
    have compilation : RuntimeApplicationFunctionCompiles types o source compiled :=
      ⟨by simpa only [compiled, expected.1] using h.evidence, ps.evidence,
        by simpa only [compiled, expected.2.1, expected.2.2] using b.evidence⟩
    let expectedInputs := (LocalTypeInputs.empty.bindFresh o "f" (.function input output)).bindFresh o "x" input
    let expectedRecord : CompiledRuntimeFunction := ⟨expectedInputs, target, output⟩
    check (decide (fields compiled = fields expectedRecord ∧
      (compileRuntimeApplicationFunction? types o source).map fields = some (fields expectedRecord) ∧
      compileRuntimeFunction? types o source = none)) "independent original static record/Core/type differs"
    have accepted := compilation.complete
    have _ := compileRuntimeApplicationFunction?_iff.mpr compilation
    have _ := compilation.result_unique (compileRuntimeApplicationFunction?_sound accepted)
    have _ := (compileRuntimeApplicationFunction?_iff.mp accepted).core_hasType
    let wrongCore : Core.Expr := .letE .unit (.apply (.var 2) (.var 1))
    have _ : Core.HasType expectedInputs.context.values wrongCore output := .letE .unit (.apply (.var rfl) (.var rfl))
    have exactSource : ¬ RuntimeApplicationFunctionCompiles types o source ⟨expectedInputs, wrongCore, output⟩ := by
      intro other
      have impossible := congrArg CompiledRuntimeFunction.core (compilation.result_unique other)
      cases impossible
    have _ := exactSource
    return ⟨source, compiled, compilation⟩
  else throw (IO.userError "independent body does not match declared result")
private def actualSmoke (argument : TypedRuntimeArgument) (o : Resolved.DeclarationId) : IO Unit := do
  let ready ← positive argument.type argument.type o standard
  let types := table argument.type argument.type
  let f : TypedRuntimeArgument := ⟨.function argument.type argument.type,
    .closure argument.type argument.type (.var 0) [], .closure .nil (.var rfl)⟩
  let args := [f, argument]
  if aligned : args.map (·.type) = ready.compiled.inputs.context.values.reverse then
    have _ := ready.evidence.prepare_arguments args aligned
    have _ := runtimeApplicationFunctionPrepares_toCompiled_iff.mpr ⟨ready.evidence, aligned⟩
    match accepted : prepareRuntimeApplicationFunction? types o ready.source args with
    | none => throw (IO.userError "matching real arguments did not prepare")
    | some prepared =>
        have preparation := prepareRuntimeApplicationFunction?_sound accepted
        have erased := preparation.compiles.result_unique ready.evidence
        have _ := runtimeApplicationFunctionPrepares_toCompiled_iff.mp ⟨prepared, preparation, erased⟩
        have _ := preparation.result_unique (prepareRuntimeApplicationFunction?_iff.mp preparation.complete)
        have _ := preparation.core_hasType
        check (decide (fields prepared.toCompiled = fields ready.compiled ∧ prepared.core = target ∧
          prepared.returnType = argument.type ∧ prepared.inputs.environment.values = [argument.value, f.value] ∧
          prepared.inputs.bindings.map (fun b => (b.name, b.id, b.type, b.value)) =
            [("x", ⟨o, 1⟩, argument.type, argument.value), ("f", ⟨o, 0⟩, f.type, f.value)])) "actual complete record/order changed"
        have manual (store k) : Core.Steps 6 ⟨.eval target (args.reverse.map (·.value)), k, store⟩ ⟨.ret argument.value, k, store⟩ :=
          .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (.cons (.var rfl) .refl)))))
        for store in [[], [.bool true]] do
          for fuel in List.range 9 do
            have _ := ready.evidence.run_eq args aligned fuel store
            have _ := preparation.run_eq_body fuel store
            have _ := (manual store []).runStateful_done_iff (fuel := fuel)
            check (decide (runRuntimeApplicationFunction? types o ready.source args fuel store =
              some (argument.type, Core.runStateful fuel (.initial target [argument.value, f.value] store)))) "compiled execution changed actual values/store"
            match result : runRuntimeApplicationFunction? types o ready.source args fuel store with
            | some (_, .done v t) =>
                have _ := runRuntimeApplicationFunction?_eq_some_iff.mp result
                check (decide (6 ≤ fuel ∧ v = argument.value ∧ t = store)) "actual identity smoke differs"
            | some (_, .outOfFuel _) => check (decide (fuel < 6)) "actual smoke cost differs"
            | _ => throw (IO.userError "actual identity failed")
    for supplied in [args, [], [argument], args.reverse, args ++ [argument]] do
      have _ := prepareRuntimeApplicationFunction?_factorization types o ready.source supplied
      let projected := (prepareRuntimeApplicationFunction? types o ready.source supplied).map (fun p => fields p.toCompiled)
      check (decide (projected = if supplied.map (·.type) = args.map (·.type) then some (fields ready.compiled) else none)) "full Option or ordered type guard differs"
      have _ := prepareRuntimeApplicationFunction?_eq_none_iff (types := types) (owner := o) (declaration := ready.source) (arguments := supplied)
      have _ := runRuntimeApplicationFunction?_eq_none_iff (types := types) (owner := o) (declaration := ready.source) (arguments := supplied) 0 []
  else throw (IO.userError "original argument type ordering changed")
private def rejected (o : Resolved.DeclarationId) (text : String) (localSuccess : Bool)
    (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let types := table .word .word; let source ← parsed text location
  if localSuccess then
    let originalCaller := (LocalTypeInputs.empty.bindFresh o "f" (.function .word .word)).bindFresh o "x" .word
    let localBody ← body originalCaller source.value.body
    check (decide (localBody.core = target ∧ localBody.type = .word ∧ elaborateLocalApplicationReturnBody?
      originalCaller.names originalCaller.context source.value.body = some (target, .word))) "original body-only success was lost"
  if absent : compileRuntimeApplicationFunction? types o source = none then
    have _ := compileRuntimeApplicationFunction?_eq_none_iff.mp absent
    check ((compileRuntimeApplicationFunction? types o source).isNone) "whole rejection changed"
  else throw (IO.userError "invalid whole contract compiled")
end ParsedRuntimeApplicationCompilation
open ParsedRuntimeApplicationCompilation
def frontendParsedRuntimeApplicationCompilationTests : IO Unit := do
  let types : List Core.Ty := [.unit, .bool, .word, .cell .word, .product .word .unit,
    .namedData ⟨77⟩, .function (.namedData ⟨9⟩) (.namedData ⟨9⟩)]
  for o in [owner 0, owner 41] do
    for input in types do
      for output in types do
        let _ ← positive input output o standard
        let _ ← positive input output o "function invoke(f:mod.F,x:(A)) returns((R)){return f(x);}"
      let _ ← positive input .unit o "function invoke(f:F,x:A){return f(x);}"
      let _ ← positive input .unit o "function invoke(f:F,x:A) returns(()){return f(x);}"
    let _ ← positive (.product (.namedData ⟨1⟩) .unit) (.product (.namedData ⟨2⟩) .word) o
      "function invoke(f:F,x:A) returns(R){return f(x);}"
    let _ ← positive (.product .unit .unit) (.product .unit .unit) o
      "function invoke(f:F,x:((),())) returns(((),())){return f(x);}"
    let _ ← positive .unit .unit o "function invoke(f:F,x:()) returns(()){return f(x);}"
    actualSmoke ⟨.unit, .unit, .unit⟩ o
    actualSmoke ⟨.word, .word (Core.Word.ofNatModulo 14), .word⟩ o
    rejected o "function invoke(f:F,x:A) public returns(R){return f(x);}" true .contract
    rejected o "function invoke(f:F,x:A) payable returns(R){return f(x);}" true .contract
    for text in ["function invoke<T>(f:F,x:A) returns(R){return f(x);}",
        "function invoke(f:F,x:A) returns(R) where A: Eq {return f(x);}",
        "function invoke(f:F,x:A){return f(x);}", "function invoke(f:F,x:A) returns(Unit){return f(x);}",
        "function invoke(f:F,x:A) returns(){return f(x);}", "function invoke(f:F,x:A) returns(R,R){return f(x);}",
        "function invoke(f:F,x:A) returns(Missing){return f(x);}",
        "function invoke(comptime f:F,x:A) returns(R){return f(x);}",
        "function invoke(f:F,f:A) returns(R){return f(x);}", "function invoke(f:F,x:Missing) returns(R){return f(x);}"] do
      rejected o text true
    for text in ["function invoke(f:F,x:A) returns(R){return x;}",
        "function invoke(f:F,x:A) returns(R){return;}", "function invoke(f:F,x:A) returns(R){}",
        "function invoke(f:F,x:A) returns(R){return f(f(x));}",
        "function invoke(f:F,x:A) returns(R){return f(x);return x;}",
        "function invoke(f:F,x:A) returns(R){{return f(x);}}"] do rejected o text false
end Tests

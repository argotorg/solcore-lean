import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeComputationFunctionFactorizationProperties
import Solcore.Frontend.LocalComputationReturnTreeTypingProperties
import Solcore.Frontend.RuntimeApplicationFunctionCompilation
import Solcore.Core.ExactFuelProperties

/-! Whole original declarations have independent annotation, parameter and body
certificates. The nominal matrix supplies no values; only two actual smokes run. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRuntimeComputationCompilation
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"CompileMixed", by decide⟩], by decide⟩⟩, n⟩
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def text (body : String) := "function example(f:F,g:G,x:A) returns(R){" ++ body ++ "}"
private def parsed (text : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"compile-mixed.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing")
  let .ok source next := Syntax.Parser.functionDecl location (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError s!"original declaration parse: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "whole original span"
  check (source.span.contains source.value.signature.span && source.value.signature.span.contains source.value.signature.parameters.span &&
    decide (source.value.signature.span.endByte ≤ source.value.body.span.startByte)) "original header before body"
  return source
private structure Meaning (ts : TypeNameTable) (s : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes ts s type
private def meaning (ts : TypeNameTable) (s : Syntax.TypeExpr) : IO (Meaning ts s) := do
  match shape : s with
  | ⟨_,.named name none⟩ =>
      match found : ts.lookup? (qualifiedTypeNameKey name) with
      | some t => return ⟨t,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | _ => throw (IO.userError "missing annotation")
  | ⟨_,.tuple []⟩ => return ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [a]⟩ => let m ← meaning ts a; return ⟨m.type,by rw [shape]; exact .single m.evidence⟩
  | ⟨_,.tuple [a,b]⟩ =>
      let x ← meaning ts a; let y ← meaning ts b
      return ⟨.product x.type y.type,by rw [shape]; exact .pair x.evidence y.evidence⟩
  | _ => throw (IO.userError "outside annotation fixture")
termination_by sizeOf s
private structure Declared (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (ps : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom ts o i ps inputs
private def declare (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (ps : List Syntax.FunctionParameter) : IO (Declared ts o i ps) := do
  match shape : ps with
  | [] => return ⟨i,by rw [shape]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest =>
      check (span.contains name.span && span.contains annotation.span && decide (name.span.endByte ≤ annotation.span.startByte)) "parameter original order"
      let m ← meaning ts annotation
      if unused : name.value ∉ i.names.map Prod.fst then
        let tail ← declare ts o (i.bindFresh o name.value m.type) rest
        return ⟨tail.inputs,by rw [shape]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate parameter")
  | _ => throw (IO.userError "non-runtime parameter")
private structure Header (ts : TypeNameTable) (s : Syntax.FunctionSignature) where
  type : Core.Ty
  evidence : RuntimeFunctionHeader ts s type
private def header (ts : TypeNameTable) (s : Syntax.FunctionSignature) : IO (Header ts s) := do
  if policy : s.genericParameters = none ∧ s.whereClause = none ∧ s.modifiers.publicMarker = none ∧ s.modifiers.payableMarker = none then
    match shape : s.returnsClause with
    | none => return ⟨.unit,⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [shape]; exact .absent⟩⟩
    | some ⟨_,⟨_,[a]⟩⟩ =>
        let m ← meaning ts a
        return ⟨m.type,⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [shape]; exact .single m.evidence⟩⟩
    | _ => throw (IO.userError "return annotation shape")
  else throw (IO.userError "whole header policy")
private structure Atom (i : LocalTypeInputs) (s : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression i.names s resolved
  lowered : Resolved.Lowers i.context.ids resolved core
  typing : Resolved.HasType i.context resolved type
private def atom (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Atom i s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some id =>
          match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
          | some t,some n => return ⟨.var id,.var n,t,by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original row")
      | _ => throw (IO.userError "original name")
  | _ => throw (IO.userError "not fixture atom")
private structure Child (i : LocalTypeInputs) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalComputationElaborates i.names i.context s core type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Child i s) := do
  match shape : s with
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte ≤ argsSpan.startByte)) "call spans/order"
      let f ← atom i fn; let a ← atom i arg
      match ft : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,by
            rw [shape]; exact .application (.call f.resolution f.lowered (ft ▸ f.typing) a.resolution a.lowered (same ▸ a.typing))⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | _ => let a ← atom i s; return ⟨a.core,a.type,.pure a.resolution a.lowered a.typing⟩
private structure Body (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (b : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalComputationReturnTreeElaborates ts o i b core type
private def body (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (b : Syntax.Block) : IO (Body ts o i b) := do
  for s in b.value do check (b.span.contains s.span) "original statement span"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,.unit,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨rs,.returnStmt (some s)⟩]⟩ =>
      check (rs.contains s.span) "return span"; let c ← child i s
      return ⟨c.core,c.type,by rw [shape]; exact .expression c.evidence⟩
  | ⟨_,[⟨inner,.block statements⟩]⟩ =>
      let c ← body ts o i ⟨inner,statements⟩; return ⟨c.core,c.type,by rw [shape]; exact .block c.evidence⟩
  | ⟨bs,⟨ls,.letDecl name annotation (some init)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains init.span && decide (name.span.endByte ≤ init.span.startByte)) "binding spans/order"
      if unused : name.value ∉ i.names.map Prod.fst then
        let c ← child i init; let tail ← body ts o (i.bindFresh o name.value c.type) ⟨bs,rest⟩
        match ann : annotation with
        | none => return ⟨.letE c.core tail.core,tail.type,by rw [shape,ann]; exact .inferred unused c.evidence tail.evidence⟩
        | some a =>
            check (ls.contains a.span && decide (a.span.endByte ≤ init.span.startByte)) "annotation before initializer"
            let m ← meaning ts a
            if same : m.type = c.type then return ⟨.letE c.core tail.core,tail.type,by rw [shape,ann]; exact .binding (same ▸ m.evidence) unused c.evidence tail.evidence⟩
            else throw (IO.userError "initializer annotation mismatch")
      else throw (IO.userError "shadowing")
  | ⟨bs,⟨_,.expression s true⟩::rest⟩ =>
      let c ← child i s; let tail ← body ts o i ⟨bs,rest⟩
      return ⟨.letE c.core (tail.core.weakenAt 0),tail.type,by rw [shape]; exact .discard c.evidence tail.evidence⟩
  | ⟨_,[⟨_,.ifThen guard yes (some no)⟩]⟩ =>
      let c ← child i guard; let a ← body ts o i yes; let d ← body ts o i no
      if ct : c.type = .bool then
        if same : d.type = a.type then return ⟨.ifE c.core a.core d.core,a.type,by rw [shape]; exact .conditional (ct ▸ c.evidence) a.evidence (same ▸ d.evidence)⟩
        else throw (IO.userError "arm types")
      else throw (IO.userError "guard type")
  | _ => throw (IO.userError "outside body fixture")
termination_by sizeOf b
private def table (a b r : Core.Ty) : TypeNameTable := [(["F"],.function a b),(["F"],.bool),
  (["G"],.function a .bool),(["A"],a),(["B"],b),(["R"],r),(["Unit"],.unit),(["mod","F"],.function a b)]
private def fields (c : CompiledRuntimeFunction) := (c.inputs.names,c.inputs.context,c.core,c.returnType)
private structure Ready (ts : TypeNameTable) (o : Resolved.DeclarationId) where
  source : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  evidence : RuntimeComputationFunctionCompiles ts o source compiled
private def positive (a b r : Core.Ty) (o : Resolved.DeclarationId) (sourceText : String)
    (expectedCore : Core.Expr) (oldProfile : Nat := 0) : IO (Ready (table a b r) o) := do
  let ts := table a b r; let s ← parsed sourceText
  let ps ← declare ts o .empty s.value.signature.parameters.elements; let h ← header ts s.value.signature
  let c ← body ts o ps.inputs s.value.body
  if exactResult : h.type = r ∧ c.type = r ∧ c.core = expectedCore then
    let compiled : CompiledRuntimeFunction := ⟨ps.inputs,expectedCore,r⟩
    have e : RuntimeComputationFunctionCompiles ts o s compiled := ⟨by simpa only [compiled,exactResult.1] using h.evidence,
      ps.evidence,by simpa only [compiled,exactResult.2.1,exactResult.2.2] using c.evidence⟩
    let expectedInputs := ((LocalTypeInputs.empty.bindFresh o "f" (.function a b)).bindFresh o "g" (.function a .bool)).bindFresh o "x" a
    let expected : CompiledRuntimeFunction := ⟨expectedInputs,expectedCore,r⟩
    have accepted := compileRuntimeComputationFunction?_iff.mpr e
    have _ := (compileRuntimeComputationFunction?_iff.mp accepted).body.core_hasType
    check (decide (fields compiled = fields expected ∧ (compileRuntimeComputationFunction? ts o s).map fields = some (fields expected))) "independent full record/Core/return"
    check (decide ((compileRuntimeFunction? ts o s).map fields = (if oldProfile = 1 then some (fields expected) else none)) &&
      decide ((compileRuntimeApplicationFunction? ts o s).map fields = (if oldProfile = 2 then some (fields expected) else none))) "old success embedding or narrower boundary"
    let wrong : CompiledRuntimeFunction := ⟨ps.inputs,.letE .unit (expectedCore.weakenAt 0),r⟩
    have _ : Core.HasType ps.inputs.context.values wrong.core r := .letE .unit
      (by simpa only [Core.Context.insertAt] using e.body.core_hasType.weakenAt (inserted := .unit) 0)
    if different : (compileRuntimeComputationFunction? ts o s).map fields ≠ some (fields wrong) then
      have _ : ¬ RuntimeComputationFunctionCompiles ts o s wrong := by
        intro other; rw [compileRuntimeComputationFunction?_iff.mpr other] at different; exact different rfl
      pure ()
    else throw (IO.userError "same-typed wrong Core acquired exact provenance")
    return ⟨s,compiled,e⟩
  else throw (IO.userError "independent body/declared return differs")
private structure Bound (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom ts o i ps args inputs
private def bindActual (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Bound ts o i ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨i,by rw [shape,supplied]; exact .nil⟩
  | ⟨_,.typed none name annotation⟩::rest,arg::tail =>
      let m ← meaning ts annotation
      if same : m.type = arg.type then
        if unused : name.value ∉ i.names.map Prod.fst then
          let b ← bindActual ts o (i.bindFresh o name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨b.inputs,by rw [shape,supplied]; exact .cons (same ▸ m.evidence) unused b.evidence⟩
        else throw (IO.userError "actual duplicate")
      else throw (IO.userError "actual type")
  | _,_ => throw (IO.userError "actual arity")
private def smoke (x : TypedRuntimeArgument) (o : Resolved.DeclarationId) : IO Unit := do
  let core : Core.Expr := .letE (call 2 0) (.var 0)
  let ready ← positive x.type x.type x.type o (text "let r=f(x);return r;") core
  let ts := table x.type x.type x.type
  let f : TypedRuntimeArgument := ⟨.function x.type x.type,.closure x.type x.type (.var 0) [.unit],.closure (.cons .unit .nil) (.var rfl)⟩
  let g : TypedRuntimeArgument := ⟨.function x.type .bool,.closure x.type .bool (.bool true) [],.closure .nil .bool⟩
  let args := [f,g,x]; let actual ← bindActual ts o .empty ready.source.value.signature.parameters.elements args
  let c ← body ts o actual.inputs.toTypeInputs ready.source.value.body
  if exactResult : c.core = core ∧ c.type = x.type ∧ ready.compiled.returnType = x.type then
    let prepared : PreparedRuntimeFunction := ⟨actual.inputs,core,x.type⟩
    have e : RuntimeComputationFunctionPrepares ts o ready.source args prepared :=
      ⟨by simpa only [prepared,exactResult.2.2] using ready.evidence.header,actual.evidence,
      by simpa only [prepared,exactResult.1,exactResult.2.1] using c.evidence⟩
    have accepted := prepareRuntimeComputationFunction?_iff.mpr e
    have _ := prepareRuntimeComputationFunction?_iff.mp accepted
    check (decide (fields prepared.toCompiled = fields ready.compiled ∧ prepared.inputs.environment.values = [x.value,g.value,f.value] ∧
      prepared.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)) =
        [("x",⟨o,2⟩,x.type,x.value),("g",⟨o,1⟩,g.type,g.value),("f",⟨o,0⟩,f.type,f.value)])) "actual original rows/reverse once/no let locals"
    have manual (store k) : Core.Steps 9 ⟨.eval core [x.value,g.value,f.value],k,store⟩ ⟨.ret x.value,k,store⟩ :=
      .cons .enterLet (.cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl)
        (.cons .invokeClosure (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))))))))
    for store in [[],[.bool false]] do
      for fuel in List.range 11 do
        have _ := (manual store []).runStateful_done_iff (fuel := fuel)
        have _ := runRuntimeComputationFunction?_factorization ts o ready.source args fuel store
        check (decide (runRuntimeComputationFunction? ts o ready.source args fuel store =
          some (x.type,Core.runStateful fuel (.initial core [x.value,g.value,f.value] store)))) "full actual execution"
      check (decide (runRuntimeComputationFunction? ts o ready.source args 9 store = some (x.type,.done x.value store))) "literal actual value/cost/store"
      match runRuntimeComputationFunction? ts o ready.source args 8 store with
      | some (_, .outOfFuel checkpoint) =>
          check (decide (Core.runStateful 1 checkpoint = .done x.value store)) "genuine spent8 remaining1"
      | _ => throw (IO.userError "expected actual checkpoint before final variable")
    for supplied in [args,[],[f,x],args.reverse,args++[x]] do
      have _ := prepareRuntimeComputationFunction?_factorization ts o ready.source supplied
      check (decide ((prepareRuntimeComputationFunction? ts o ready.source supplied).map (fun p => fields p.toCompiled) =
        if supplied.map (·.type) = args.map (·.type) then some (fields ready.compiled) else none)) "full Option/type/arity guard"
  else throw (IO.userError "actual body differs")
private def rejected (sourceText : String) (localSuccess : Bool) (location : Syntax.Parser.FunctionLocation := .module) : IO Unit := do
  let ts := table .word .word .word; let o := owner 4; let s ← parsed sourceText location
  if localSuccess then
    let fixed := ((LocalTypeInputs.empty.bindFresh o "f" (.function .word .word)).bindFresh o "g" (.function .word .bool)).bindFresh o "x" .word
    let c ← body ts o fixed s.value.body
    check (decide (c.core = .letE (call 2 0) (.var 0) ∧ c.type = .word ∧
      elaborateLocalComputationReturnTree? ts o fixed s.value.body = some (c.core,c.type))) "body-only success under separate valid caller"
  check ((compileRuntimeComputationFunction? ts o s).isNone) "invalid whole declaration compiled"
end ParsedRuntimeComputationCompilation
open ParsedRuntimeComputationCompilation
def frontendParsedRuntimeComputationCompilationTests : IO Unit := do
  let types : List Core.Ty := [.unit,.bool,.word,.cell .word,.product .word .unit,.namedData ⟨77⟩,.function (.namedData ⟨9⟩) (.namedData ⟨9⟩)]
  for o in [owner 0,owner 41] do
    for a in types do
      for b in types do
        for (bodyText,core) in [("let r=f(x);return r;",.letE (call 2 0) (.var 0)),
            ("let r:B=f(x);return r;",.letE (call 2 0) (.var 0)),
            ("f(x);return f(x);",.letE (call 2 0) (call 3 1)),
            ("if(g(x)){{let r=f(x);return r;}}else{return f(x);}",.ifE (call 1 0) (.letE (call 2 0) (.var 0)) (call 2 0))] do
          let _ ← positive a b b o (text bodyText) core
        let _ ← positive a (.function a b) b o (text "let h=f(x);return h(x);") (.letE (call 2 0) (call 0 1))
        let _ ← positive a b a o (text "return x;") (.var 0) 1
        let _ ← positive a b b o (text "return f(x);") (call 2 0) 2
      let _ ← positive a .unit .unit o "function example(f:mod.F,g:G,x:(A)) returns(()){let r:B=f(x);{return r;}}" (.letE (call 2 0) (.var 0))
    let _ ← positive (.product .unit .unit) (.product .unit .unit) (.product .unit .unit) o
      "function example(f:F,g:G,x:((),())) returns(((),())){let r:((),())=f(x);return r;}" (.letE (call 2 0) (.var 0))
    smoke ⟨.unit,.unit,.unit⟩ o; smoke ⟨.word,.word (Core.Word.ofNatModulo 17),.word⟩ o
  let suffix := "{let r=f(x);return r;}"
  for head in ["function example<T>(f:F,g:G,x:A) returns(R)","function example(f:F,g:G,x:A) returns(R) where A: Eq",
      "function example(f:F,g:G,x:A)","function example(f:F,g:G,x:A) returns(Unit)",
      "function example(f:F,g:G,x:A) returns()","function example(f:F,g:G,x:A) returns(R,R)",
      "function example(f:F,g:G,x:A) returns(Missing)","function example(comptime f:F,g:G,x:A) returns(R)",
      "function example(f:F,g:G,x:Missing) returns(R)","function example(f:F,g:G,f:A) returns(R)"] do rejected (head++suffix) true
  for marker in ["public","payable"] do rejected ("function example(f:F,g:G,x:A) "++marker++" returns(R)"++suffix) true .contract
  for b in ["let x=f(x);return x;","let r;return x;","let r=f(f(x));return r;","let r=f(x);return f(r,x);",
      "if(g(x)){return f(x);}else{return Missing;}","{let r=f(x);}return r;","return f(x);return x;"] do rejected (text b) false
end Tests

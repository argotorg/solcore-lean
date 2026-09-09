import Solcore.Syntax.Parser.Function
import Solcore.Frontend.ComputationFunctionFactorizationProperties
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RuntimeComputationFunctionFactorizationProperties
import Solcore.Core.ExactFuelProperties
import Solcore.Frontend.WordLessCostStepComposition
import Solcore.Frontend.LocalFunctionApplicationStepComposition
/-! Whole original declarations have independent annotation, parameter and body
certificates. The nominal matrix supplies no values; three actual smokes run separately. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRecursiveComputationCompilation
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"CompileRecursive", by decide⟩], by decide⟩⟩, n⟩
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def text (body : String) := "function example(f:F,g:G,x:A) returns(R){" ++ body ++ "}"
private def parsed (text : String) (location : Syntax.Parser.FunctionLocation := .module) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"compile-recursive.sol"⟩,text⟩
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
  | ⟨_,.literal literal⟩ =>
      if spelling : literal.value=.decimal "1" then
        have denoted : WordLiteralDenotes literal (Core.Word.ofNatModulo 1) := by
          change NumericLiteralDenotes literal.value 1; rw [spelling]
          exact .decimal (by decide) (.cons (.decimal (digit := 1) (by decide) rfl) .nil)
        return ⟨.word (Core.Word.ofNatModulo 1),.word (Core.Word.ofNatModulo 1),.word,by rw [shape]; exact .wordLiteral denoted,.word,.word⟩
      else throw (IO.userError "migration literal")
  | _ => throw (IO.userError "not fixture atom")
private structure Child (i : LocalTypeInputs) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : RecursiveLocalComputationElaborates i.names i.context s core type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Child i s) := do
  match shape : s with
  | ⟨span,.group inner⟩ =>
      check (span.contains inner.span) "original group"; let c ← child i inner
      return ⟨c.core,c.type,by rw [shape]; exact .group c.evidence⟩
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte ≤ argsSpan.startByte)) "call spans/order"
      let f ← child i fn; let a ← child i arg
      match ft : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,by
            rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | ⟨_,.binary left ⟨_,.add⟩ right⟩ =>
      let a ← child i left; let b ← child i right
      if both : a.type=.word ∧ b.type=.word then return ⟨.binary .wordAdd a.core b.core,.word,
        by rw [shape]; exact .binary .add (by simpa only [Core.BinaryOp.leftType, both.1] using a.evidence) (by simpa only [Core.BinaryOp.rightType, both.2] using b.evidence)⟩
      else throw (IO.userError "migration Word operands")
  | _ => let a ← atom i s; return ⟨a.core,a.type,.pure a.resolution a.lowered a.typing⟩
termination_by sizeOf s
private structure Body (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (b : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : RecursiveComputationReturnTreeElaborates ts o i b core type
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
  (["G"],.function a a),(["A"],a),(["B"],b),(["R"],r),(["Unit"],.unit),(["Word"],.word),(["mod","F"],.function a b)]
private abbrev rowEq : DecidableEq LocalTypeBinding := fun a b =>
  decidable_of_iff ((a.name,a.id,a.type)=(b.name,b.id,b.type)) (by cases a; cases b; simp)
attribute [local instance] rowEq
private abbrev inputEq : DecidableEq LocalTypeInputs := fun a b =>
  decidable_of_iff (a.bindings=b.bindings) ⟨by cases a; cases b; intro h; cases h; rfl,fun h => congrArg LocalTypeInputs.bindings h⟩
attribute [local instance] inputEq
private abbrev compiledEq : DecidableEq CompiledRuntimeFunction := fun a b =>
  decidable_of_iff ((a.inputs,a.core,a.returnType)=(b.inputs,b.core,b.returnType)) (by cases a; cases b; simp)
attribute [local instance] compiledEq
private def fields (c : CompiledRuntimeFunction) := (c.inputs.names,c.inputs.context,c.core,c.returnType)
private structure Ready (ts : TypeNameTable) (o : Resolved.DeclarationId) where
  source : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  evidence : RecursiveComputationFunctionCompiles ts o source compiled
private def positive (a b r : Core.Ty) (o : Resolved.DeclarationId) (sourceText : String)
    (expectedCore : Core.Expr) (oldProfile : Bool := false) : IO (Ready (table a b r) o) := do
  let ts := table a b r; let s ← parsed sourceText
  let ps ← declare ts o .empty s.value.signature.parameters.elements; let h ← header ts s.value.signature
  let c ← body ts o ps.inputs s.value.body
  if exactResult : h.type = r ∧ c.type = r ∧ c.core = expectedCore then
    let compiled : CompiledRuntimeFunction := ⟨ps.inputs,expectedCore,r⟩
    have e : RecursiveComputationFunctionCompiles ts o s compiled := ⟨by simpa only [compiled,exactResult.1] using h.evidence,
      ps.evidence,by simpa only [compiled,exactResult.2.1,exactResult.2.2] using c.evidence⟩
    let expectedInputs := ((LocalTypeInputs.empty.bindFresh o "f" (.function a b)).bindFresh o "g" (.function a a)).bindFresh o "x" a
    let expected : CompiledRuntimeFunction := ⟨expectedInputs,expectedCore,r⟩
    have accepted := (compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?) (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr e
    have _ := ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType ((compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?) (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mp accepted).body
    check (decide (compiled = expected ∧ compileRecursiveComputationFunction? ts o s = some expected)) "independent full record/Core/return"
    check (decide (compileComputationFunction? elaborateLocalComputation? ts o s=(if oldProfile then some expected else none) ∧
      compileRuntimeComputationFunction? ts o s=(if oldProfile then some expected else none))) "old-child generic/old252 full Option"
    let wrong : CompiledRuntimeFunction := ⟨ps.inputs,.letE .unit (expectedCore.weakenAt 0),r⟩
    have _ : Core.HasType ps.inputs.context.values wrong.core r := .letE .unit
      (by simpa only [Core.Context.insertAt] using (ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType e.body).weakenAt (inserted := .unit) 0)
    if different : (compileRecursiveComputationFunction? ts o s).map fields ≠ some (fields wrong) then
      have _ : ¬ RecursiveComputationFunctionCompiles ts o s wrong := by
        intro other; exact different (congrArg (Option.map fields) ((compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?) (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr other))
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
private def smoke (x : TypedRuntimeArgument) (annotation : String) : IO Unit := do
  let o := owner 4; let core := Core.Expr.letE (.apply (.var 2) (call 1 0)) (.var 0)
  let ready ← positive x.type x.type x.type o ("function example(f:F,g:G,x:"++annotation++") returns("++annotation++"){let r=f(g(x));return r;}") core
  let ts := table x.type x.type x.type
  let f : TypedRuntimeArgument := ⟨.function x.type x.type,.closure x.type x.type (.var 0) [],.closure .nil (.var rfl)⟩
  let g := f; let args := [f,g,x]; let actual ← bindActual ts o .empty ready.source.value.signature.parameters.elements args
  let c ← body ts o actual.inputs.toTypeInputs ready.source.value.body
  if fixed : c.core=core ∧ c.type=x.type ∧ ready.compiled.returnType=x.type then
    let prepared : PreparedRuntimeFunction := ⟨actual.inputs,core,x.type⟩
    have e : RecursiveComputationFunctionPrepares ts o ready.source args prepared := ⟨by simpa only [prepared,fixed.2.2] using ready.evidence.header,
      actual.evidence,by simpa only [prepared,fixed.1,fixed.2.1] using c.evidence⟩
    have accepted := (prepareComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?) (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr e
    have _ := (prepareComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?) (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mp accepted
    check (decide (prepared.toCompiled=ready.compiled ∧ prepared.inputs.environment.values=[x.value,g.value,f.value] ∧
      prepared.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
        [("x",⟨o,2⟩,x.type,x.value),("g",⟨o,1⟩,g.type,g.value),("f",⟨o,0⟩,f.type,f.value)])) "same actual record/one reverse/parameter-only"
    have manual (s k) : Core.Steps 14 ⟨.eval core [x.value,g.value,f.value],k,s⟩ ⟨.ret x.value,k,s⟩ :=
      CostStepComposition.letE (CostStepComposition.apply (.cons (.var rfl) .refl)
        (CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl)
    for store in [[],[Core.Value.bool false]] do
      for fuel in List.range 16 do
        have _ := (manual store []).runStateful_done_iff (fuel := fuel)
        have _ := runComputationFunction?_factorization elaborateRecursiveLocalComputation? ts o ready.source args fuel store
        check (decide (runRecursiveComputationFunction? ts o ready.source args fuel store=some (x.type,Core.runStateful fuel (.initial core [x.value,g.value,f.value] store)) ∧
          runRuntimeComputationFunction? ts o ready.source args fuel store=none)) "new full result/old nested None"
      check (decide (runRecursiveComputationFunction? ts o ready.source args 14 store=some (x.type,.done x.value store))) "manual value/cost/store"
      match runRecursiveComputationFunction? ts o ready.source args 13 store with
      | some (_, .outOfFuel cp) => check (decide (Core.runStateful 1 cp=.done x.value store)) "genuine cp13/residual1"
      | _ => throw (IO.userError "missing genuine checkpoint")
    for supplied in [args,[],[f,g],[f,x,g],args++[⟨.unit,.unit,.unit⟩],[f,g,⟨.word,.word (Core.Word.ofNatModulo 17),.word⟩,⟨.unit,.unit,.unit⟩]] do
      have _ := prepareComputationFunction?_factorization elaborateRecursiveLocalComputation? ts o ready.source supplied
      check (decide ((prepareRecursiveComputationFunction? ts o ready.source supplied).map PreparedRuntimeFunction.toCompiled=
        if supplied.map (·.type)=args.map (·.type) then some ready.compiled else none)) "full Option/Unit not omitted/product not flattened"
  else throw (IO.userError "original actual body differs")
private def rejected (sourceText : String) (localSuccess : Bool) (location : Syntax.Parser.FunctionLocation := .module) (b : Core.Ty := .word) : IO Unit := do
  let ts := table .word b .word; let o := owner 4; let s ← parsed sourceText location
  if localSuccess then
    let fixed := ((LocalTypeInputs.empty.bindFresh o "f" (.function .word .word)).bindFresh o "g" (.function .word .word)).bindFresh o "x" .word
    let c ← body ts o fixed s.value.body
    check (decide (c.core = .letE (.apply (.var 2) (call 1 0)) (.var 0) ∧ c.type = .word ∧
      elaborateRecursiveComputationReturnTree? ts o fixed s.value.body = some (c.core,c.type))) "body-only success under separate valid caller"
  check ((compileRecursiveComputationFunction? ts o s).isNone) "invalid whole declaration compiled"
end ParsedRecursiveComputationCompilation
open ParsedRecursiveComputationCompilation
def frontendParsedRecursiveComputationCompilationTests : IO Unit := do
  let types : List Core.Ty := [.unit,.word,.cell .word,.product .word .unit,.namedData ⟨77⟩,.function (.namedData ⟨9⟩) (.namedData ⟨9⟩)]
  for o in [owner 0,owner 41] do
    for a in types do
      for b in types do
        let nested := Core.Expr.apply (.var 2) (call 1 0)
        for (bodyText,core,old) in [("let r=f(g(x));return r;",.letE nested (.var 0),false),
            ("let r:B=((f(g(x))));{return r;}",.letE nested (.var 0),false),
            ("f(g(x));return f(g(x));",.letE nested (.apply (.var 3) (call 2 1)),false),
            ("return f(x);",call 2 0,true),("let r=f(x);return r;",.letE (call 2 0) (.var 0),true)] do
          let _ ← positive a b b o (text bodyText) core old
        let _ ← positive a (.function a b) b o (text "let h=f(g(x));return h(g(x));") (.letE nested (.apply (.var 0) (call 2 1)))
        let _ ← positive a b a o (text "return x;") (.var 0) true
      let _ ← positive a .bool a o (text "if(f(g(x))){{let t=x;return t;}}else{return x;}") (.ifE (.apply (.var 2) (call 1 0)) (.letE (.var 0) (.var 0)) (.var 0))
      let _ ← positive a .unit .unit o "function example(f:mod.F,g:G,x:(A)) returns(()){let r:B=f(g(x));return r;}" (.letE (.apply (.var 2) (call 1 0)) (.var 0))
  smoke ⟨.unit,.unit,.unit⟩ "()"
  smoke ⟨.word,.word (Core.Word.ofNatModulo 17),.word⟩ "Word"
  smoke ⟨.product .word .unit,.pair (.word (Core.Word.ofNatModulo 17)) .unit,.pair .word .unit⟩ "(Word,())"
  let suffix := "{let r=f(g(x));return r;}"
  for head in ["function example<T>(f:F,g:G,x:A) returns(R)","function example(f:F,g:G,x:A) returns(R) where A: Eq",
      "function example(f:F,g:G,x:A)","function example(f:F,g:G,x:A) returns(Unit)",
      "function example(f:F,g:G,x:A) returns()","function example(f:F,g:G,x:A) returns(R,R)",
      "function example(f:F,g:G,x:A) returns(Missing)","function example(comptime f:F,g:G,x:A) returns(R)",
      "function example(f:F,g:G,x:Missing) returns(R)","function example(f:F,g:G,f:A) returns(R)"] do rejected (head++suffix) true
  for marker in ["public","payable"] do rejected ("function example(f:F,g:G,x:A) "++marker++" returns(R)"++suffix) true .contract
  let _ ← positive .word .word .word (owner 4) (text "return f(g(x))+1;") (.binary .wordAdd (.apply (.var 2) (call 1 0)) (.word (Core.Word.ofNatModulo 1)))
  for b in ["let x=f(g(x));return x;","let r;return x;","let r=f(g(x));return f(r,x);",
      "{let r=f(g(x));}return r;","return f(g(x));return x;","let r:Missing=f(g(x));return r;"] do rejected (text b) false
  rejected (text "if(f(g(x))){return x;}else{{let r:Missing=x;return r;}}") false .module .bool
end Tests

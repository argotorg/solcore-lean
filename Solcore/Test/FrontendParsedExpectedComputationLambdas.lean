import Solcore.Syntax.Parser.Function
import Solcore.Frontend.Expected
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.Computation
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.ExactFuelProperties
import Solcore.Core.FuelResumptionProperties

/-! Original header/body certificates precede the new standalone checker.
Creation and application are only existing Core consumers, not source evaluation.
Their arbitrary actual captures need not realize the static input types. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedExpectedComputationLambdas
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedComputationLambdas",by decide⟩],by decide⟩⟩,147⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def outer : LocalTypeInputs := ⟨[⟨"x",id 7,.bool⟩,⟨"saved",id 31,.word⟩,
  ⟨"f",foreign,.function .word .word⟩,⟨"g",id 20,.function .word .word⟩],by decide⟩
private def types : TypeNameTable := [(["A"],.word),(["B"],.bool),(["A"],.bool),
  (["C"],.cell (.function .word .word))]
private def file (text : String) : Syntax.SourceFile := ⟨⟨.main,"expected-computation-lambdas.sol"⟩,text⟩
private def parsed (text : String) (diagnostics : Nat := 0) : IO Syntax.Expr := do
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial (file text) lexed) with
  | .ok source next =>
      check (lexed.diagnostics.isEmpty && next.atEnd && decide (next.diagnostics.length=diagnostics ∧
        source.span=⟨(file text).id,0,text.utf8ByteSize⟩)) "full original source, ranges and explicit diagnostics"
      return source
  | .reject _ _ => throw (IO.userError "original lambda rejected")
  | .invariant _ => throw (IO.userError "parser invariant")
private structure Meaning (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (source : Syntax.TypeExpr) : IO (Meaning source) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
      | some t => return ⟨t,by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "annotation lookup")
  | ⟨_,.tuple []⟩ => return ⟨.unit,by rw [shape]; exact .unit⟩
  | ⟨_,.tuple [child]⟩ => let a ← meaning child; return ⟨a.type,by rw [shape]; exact .single a.evidence⟩
  | ⟨_,.tuple [left,right]⟩ =>
      let a ← meaning left; let b ← meaning right
      return ⟨.product a.type b.type,by rw [shape]; exact .pair a.evidence b.evidence⟩
  | ⟨_,.function _ ⟨_,[a]⟩ (some ⟨span,results⟩)⟩ =>
      let p ← meaning a; let r ← meaning ⟨span,.tuple results⟩
      return ⟨.function p.type r.type,by rw [shape]; exact .functionReturns p.evidence r.evidence⟩
  | _ => throw (IO.userError "independent annotation shape")
termination_by sizeOf source
private def wellFormed : (t : Core.Ty) → Option (PLift (Core.Ty.WellFormed [] t))
  | .unit => some ⟨.unit⟩ | .bool => some ⟨.bool⟩ | .word => some ⟨.word⟩ | .integer => some ⟨.integer⟩
  | .product a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.product p.down r.down⟩
  | .function a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.function p.down r.down⟩
  | .sum a b => do let p ← wellFormed a; let r ← wellFormed b; return ⟨.sum p.down r.down⟩
  | .cell a => do let p ← wellFormed a; return ⟨.cell p.down⟩
  | .namedData _ => none
private structure Header (source : Syntax.Expr) (a b : Core.Ty) where
  name : String
  body : Syntax.Block
  evidence : ExpectedUnaryLambdaHeaderDeclares types owner outer source (.function a b)
    ⟨outer.bindFresh owner name a,body,a,b⟩
private def header (source : Syntax.Expr) (a b : Core.Ty) : IO (Header source a b) := do
  match shape : source with
  | ⟨span,.lambda keyword ⟨ps,[p]⟩ returns body⟩ =>
      check (span.contains keyword && span.contains ps && ps.contains p.span && span.contains body.span &&
        decide (keyword.endByte≤ps.startByte ∧ ps.endByte≤body.span.startByte)) "original keyword, single parameter and body"
      let ⟨name,evidence⟩ : Σ name, PLift (ExpectedLambdaParameterDeclares types owner outer p a (outer.bindFresh owner name a)) ←
        match parameterShape : p with
        | ⟨_,.inferred name⟩ => pure ⟨name.value,⟨by rw [parameterShape]; exact .inferred⟩⟩
        | ⟨_,.typed none name ann⟩ => do
            let m ← meaning ann
            if same : m.type=a then pure ⟨name.value,⟨by rw [parameterShape]; exact .typed (same ▸ m.evidence)⟩⟩
            else throw (IO.userError "independent parameter mismatch")
        | _ => throw (IO.userError "original parameter profile")
      match present : returns with
      | none => return ⟨name,body,by rw [shape,present]; exact .lambda evidence.down .omitted⟩
      | some ann =>
          let m ← meaning ann
          if same : m.type=b then return ⟨name,body,by rw [shape,present]; exact .lambda evidence.down (.annotated (same ▸ m.evidence))⟩
          else throw (IO.userError "independent return mismatch")
  | _ => throw (IO.userError "original unary header")
private structure Child (inputs : LocalTypeInputs) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : RecursiveLocalComputationElaborates inputs.names inputs.context source core type
private def child (inputs : LocalTypeInputs) (source : Syntax.Expr) : IO (Child inputs source) := do
  match shape : source with
  | ⟨_,.identifier name⟩ => match named : inputs.names.lookup? name.value with
      | some i => match typed : inputs.context.lookup? i, position : Resolved.LocalScope.index? inputs.context.ids i with
          | some t,some n => return ⟨.var n,t,by
              rw [shape]
              exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
                (.var (Resolved.LocalScope.index?_iff.mp position)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | _,_ => throw (IO.userError "original typed row")
      | none => throw (IO.userError "original name")
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← child inputs fn; let a ← child inputs arg
      match ft : f.type with
      | .function p r =>
          if same : a.type=p then return ⟨.apply f.core a.core,r,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "child argument type")
      | _ => throw (IO.userError "child callee type")
  | _ => throw (IO.userError "independent child profile")
termination_by sizeOf source
private structure Body (inputs : LocalTypeInputs) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : ComputationReturnTreeElaborates RecursiveLocalComputationElaborates types owner inputs source core type
private def body (inputs : LocalTypeInputs) (source : Syntax.Block) : IO (Body inputs source) := do
  match shape : source with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,.unit,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some expr)⟩]⟩ =>
      let c ← child inputs expr; return ⟨c.core,c.type,by rw [shape]; exact .expression c.evidence⟩
  | ⟨span,⟨_,.letDecl name ann (some expr)⟩::rest⟩ =>
      let c ← child inputs expr
      let tail ← body (inputs.bindFresh owner name.value c.type) ⟨span,rest⟩
      match present : ann with
      | none => return ⟨.letE c.core tail.core,tail.type,by rw [shape,present]; exact .inferred c.evidence tail.evidence⟩
      | some sourceType =>
          let m ← meaning sourceType
          if same : m.type=c.type then return ⟨.letE c.core tail.core,tail.type,by rw [shape,present]; exact .binding (same ▸ m.evidence) c.evidence tail.evidence⟩
          else throw (IO.userError "original typed shadow")
  | ⟨span,⟨_,.expression expr true⟩::rest⟩ =>
      let c ← child inputs expr; let tail ← body inputs ⟨span,rest⟩
      return ⟨.letE c.core (tail.core.weakenAt 0),tail.type,by rw [shape]; exact .discard c.evidence tail.evidence⟩
  | _ => throw (IO.userError "independent body profile")
termination_by sizeOf source
private def accepted (text : String) (a b : Core.Ty) (literalBody : Core.Expr) (diagnostics : Nat := 0) : IO Unit := do
  let source ← parsed text diagnostics
  let h ← header source a b
  let inner := outer.bindFresh owner h.name a
  let original ← body inner h.body
  let some pa := wellFormed a | throw (IO.userError "domain WF")
  let some rb := wellFormed b | throw (IO.userError "codomain WF")
  if fixed : original.core=literalBody ∧ original.type=b then
    have independent : ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates types owner outer source (.lambda a b literalBody) (.function a b) :=
      .lambda h.evidence pa.down rb.down (by simpa only [fixed.1,fixed.2] using original.evidence)
    have typed := independent.core_hasType RecursiveLocalComputationElaborates.core_hasType
    have provenance := independent.provenance
    have complete := (elaborateExpectedComputationLambda?_iff elaborateRecursiveLocalComputation?_iff).mpr independent
    have restored := (elaborateExpectedComputationLambda?_iff elaborateRecursiveLocalComputation?_iff).mp complete
    have _ := typed; have _ := provenance; have _ := restored
    check (decide (elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner outer source (.function a b)=some (.lambda a b literalBody) ∧
      inner.names=(h.name,id 32)::outer.names ∧ inner.context=(id 32,a)::outer.context)) "literal lambda, unchanged outer rows and fresh inner input"
    check (elaborateRecursiveLocalComputation? outer.names outer.context source).isNone "old recursive checker still excludes the original lambda"
  else throw (IO.userError "independent original body versus fixed expected Core/type")
private def rejectedBody (text : String) (a b : Core.Ty) (diagnostics : Nat := 0) : IO Unit := do
  let source ← parsed text diagnostics; let h ← header source a b
  have _ := declareExpectedUnaryLambdaHeader?_iff.mpr h.evidence
  if rejected : elaborateExpectedComputationLambda? elaborateRecursiveLocalComputation? types owner outer source (.function a b)=none then
    have _ := (elaborateExpectedComputationLambda?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mp rejected
    check (declareExpectedUnaryLambdaHeader? types owner outer source (.function a b)).isSome "header is accepted but body is not"
  else throw (IO.userError "unsupported or mismatched body admitted")
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def allocator : Core.Value := .closure .word .word (.letE (.newCell .word (.var 0)) (.var 1)) [.bool false]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def literalBody : Core.Expr := .letE (.apply (.var 3) (.var 0)) (.letE (.apply (.var 5) (.var 0)) (.var 4))
private def lambda : Core.Expr := .lambda .word .word literalBody
private theorem creation (a b : Core.Ty) (e : Core.Expr) (env : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps 1 ⟨.eval (.lambda a b e) env,k,s⟩ ⟨.ret (.closure a b e env),k,s⟩ := .cons .lambda .refl
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual row")
    | .word v => return ⟨.word v,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .lambda a b inner => return ⟨.closure a b inner env,s,1,fun _ => by rw [shape]; exact creation a b inner env s _⟩
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ inner captured => let r ← path n inner (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual callable")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "allocation row")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell found) .refl))⟩ | none => throw (IO.userError "read location")
      | _ => throw (IO.userError "read reference")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match found : s.read? l, written : s.write? l v with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "write location")
      | _,_ => throw (IO.userError "write reference")
    | _ => throw (IO.userError "manual Core shape")
private def coreEffects (saved : Core.Value) (location : Nat) (expected : Core.Store) : IO Unit := do
  let env := [.bool true,saved,allocator,writer location,.closure .unit .unit (.var 99) [.cellRef .word 700]]
  let store := [w 99]
  let closed := Core.Value.closure .word .word literalBody env
  have made := creation .word .word literalBody env store []
  check (decide (Core.runStateful 0 (Core.State.initial lambda env store)=.outOfFuel (Core.State.initial lambda env store) ∧
    Core.runStateful 1 (Core.State.initial lambda env store)=.done closed store)) "Core creation captures all actual values, even unused invalid captures, without effects"
  have _ := made
  let originalPath ← path 40 literalBody (w 14::env) store
  let application := Core.Expr.apply lambda (.word (Core.Word.ofNatModulo 14))
  let applied ← path 50 application env store
  if fixed : originalPath.cost=31 ∧ applied.cost=36 ∧ originalPath.value=saved ∧ applied.value=saved ∧ originalPath.final=expected ∧ applied.final=expected then
    have exactPath (k) : Core.Steps 36 ⟨.eval application env,k,store⟩ ⟨.ret saved,k,expected⟩ := by simpa only [fixed.2.1,fixed.2.2.2.1,fixed.2.2.2.2.2] using applied.evidence k
    have allFuel (fuel : Nat) := (exactPath []).runStateful_done_iff (fuel:=fuel)
    for fuel in List.range 38 do
      let observed := Core.runStateful fuel (Core.State.initial application env store)
      if fuel<36 then
        match exhausted : Core.runStateful fuel (Core.State.initial application env store) with
        | .outOfFuel cp =>
            for more in [0,1,36] do check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (Core.State.initial application env store))) "genuine Core checkpoint resumes exactly"
            have _ := Core.runStateful_resume exhausted 36
        | _ => throw (IO.userError "early Core completion or fault")
      else check (decide (observed=.done saved expected)) "existing Core application alone performs allocation/write"
    have _ := allFuel
  else throw (IO.userError "fixed Core effects/cost independent of the source checker")
private def wholeRejected : IO Unit := do
  let text := "function wrap(f:function(A) returns(A),g:function(A) returns(A),saved:A) returns(function(A) returns(A)){return lam(x:A)->A{let x:A=f(x);g(x);return saved;};}"
  let .ok lexed := Syntax.Lexer.lex (file text) | throw (IO.userError "whole lexer")
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial (file text) lexed) with
  | .ok declaration next =>
      check (next.atEnd && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty &&
        decide (declaration.span=⟨(file text).id,0,text.utf8ByteSize⟩)) "original full function"
      let identity : TypedRuntimeArgument :=
        ⟨.function .word .word,.closure .word .word (.var 0) [],.closure .nil (.var rfl)⟩
      let arguments : List TypedRuntimeArgument := [identity,identity,⟨.word,w 41,.word⟩]
      check (decide (interpretRuntimeFunctionHeader? types declaration.value.signature=some (.function .word .word)) &&
        (declareRuntimeParameters? types owner declaration.value.signature.parameters.elements).isSome &&
        (bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments).isSome)
        "original named header and all three actual arguments are accepted before the lambda boundary"
      check (compileComputationFunction? elaborateRecursiveLocalComputation? types owner declaration).isNone "old whole function still rejects source lambda"
      check (prepareComputationFunction? elaborateRecursiveLocalComputation? types owner declaration arguments).isNone "no named-function admission was added"
      for fuel in [0,1,100] do
        check (runComputationFunction? elaborateRecursiveLocalComputation? types owner declaration arguments fuel []).isNone "old runner still rejects the original lambda"
  | .reject _ _ => throw (IO.userError "whole parser rejected")
  | .invariant _ => throw (IO.userError "whole parser invariant")
end ParsedExpectedComputationLambdas
open ParsedExpectedComputationLambdas
def frontendParsedExpectedComputationLambdaTests : IO Unit := do
  for text in ["lam(x){return x;}","lam(x:A)->A{return x;}","lam(x,)->A{return x;}"] do accepted text .word .word (.var 0)
  accepted "lam(x:A)->A{return saved;}" .word .word (.var 2)
  accepted "lam(x:A)->A{let x:A=f(x); g(x); return saved;}" .word .word literalBody
  accepted "lam(x){let x=f(x); g(x); return saved;}" .word .word literalBody
  accepted "lam(x:(A,B))->(A,B){return x;}" (.product .word .bool) (.product .word .bool) (.var 0)
  accepted "lam(x:function(A) returns(B))->function(A) returns(B){return x;}" (.function .word .bool) (.function .word .bool) (.var 0)
  accepted "lam(x:C)->A{return saved;}" (.cell (.function .word .word)) .word (.var 2)
  accepted "lam(x:A)->(){return;}" .word .unit .unit
  accepted "lam(comptime){return comptime;}" .word .word (.var 0) 1
  for text in ["lam(x){return x;}","lam(x:A)->B{return x;}","lam(x){return;}","lam(x){return Missing;}",
      "lam(x){let x:B=saved;return x;}","lam(x){return lam(y){return y;};}"] do rejectedBody text .word .bool
  rejectedBody "lam(x){let ;}" .word .word 1
  for saved in [w 41,.bool false] do
    coreEffects saved 0 [w 14,w 14]
    coreEffects saved 1 [w 99,w 14]
  wholeRejected
end Tests

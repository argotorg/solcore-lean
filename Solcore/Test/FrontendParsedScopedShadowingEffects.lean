import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Frontend.RuntimeInputValidation
import Solcore.Core.FuelResumptionProperties
/-! Old initializer x and fresh Word/Bool rows coexist; explicit blocks protect the outer scope. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedScopedShadowingEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ScopedShadowingEffects",by decide⟩],by decide⟩⟩,124⟩
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["Word"],.word),(["Bool"],.bool)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def output : Core.Ty := .product .bool .word
private def reader (l : Nat) : Core.Value := .closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def writer (l : Nat) (v : Core.Value) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.var 3)) [.cellRef .word l,v]
private def pairCore : Core.Expr := .pair (.var 0) (.var 2)
private def testCore (f : Nat) : Core.Expr := .binary .wordEq (.apply (.var f) (.var 0)) (.var 0)
private def branchCore (f : Nat) : Core.Expr := .letE (testCore f) pairCore
private def afterCore : Core.Expr := .ifE (.var 2) (branchCore 4) (branchCore 5)
private def tailCore : Core.Expr := .letE (.apply (.var 4) (.var 2)) afterCore
private def core : Core.Expr := .letE (.var 1) tailCore
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,x:Word,c:Bool) returns((Bool,Word)){let prior=x;let x:Word=f(x);if(c){{let x=w(x)==x;return(x,prior);}}else{{let x:Bool=f(x)==x;return(x,prior);}}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"scoped-shadowing-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original source and range"
  return source
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "original named leaf")
  | ⟨_,.tuple [a,b]⟩ => let x ← meaning a; let y ← meaning b; return ⟨.product x.1 y.1,⟨by rw [shape]; exact .pair x.2.down y.2.down⟩⟩
  | _ => throw (IO.userError "independent annotation profile")
termination_by sizeOf e
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "actual argument type")
  | _,_ => throw (IO.userError "original arity")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨.var n,t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨span,.call f ⟨argsSpan,[a]⟩⟩ =>
      check (span.contains f.span && span.contains argsSpan && argsSpan.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original unary call ranges/order"
      let l ← child i f; let r ← child i a
      match ft : l.type with
      | .function t u => if same : r.type=t then return ⟨.apply l.core r.core,u,by rw [shape]; exact .application (ft ▸ l.evidence) (same ▸ r.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | ⟨span,.tuple ⟨ts,[a,b]⟩⟩ =>
      check (span.contains ts && ts.contains a.span && ts.contains b.span && decide (a.span.endByte≤b.span.startByte)) "original pair order"
      let x ← child i a; let y ← child i b; return ⟨.pair x.core y.core,.product x.type y.type,by rw [shape]; exact .pair x.evidence y.evidence⟩
  | ⟨_,.binary a ⟨_,.equal⟩ b⟩ =>
      let x ← child i a; let y ← child i b
      if same : x.type=.word ∧ y.type=.word then return ⟨.binary .wordEq x.core y.core,.bool,by rw [shape]; exact .binary .equal (by simpa only [Core.BinaryOp.leftType,same.1] using x.evidence) (by simpa only [Core.BinaryOp.rightType,Core.BinaryOp.leftType,same.2] using y.evidence)⟩ else throw (IO.userError "old Word initializer operands")
  | _ => throw (IO.userError "static source child")
termination_by sizeOf e
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i b)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; return ⟨r.core,r.type,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← body i ⟨span,statements⟩; return ⟨r.core,r.type,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.length=i.ids.length+1 ∧ next.ids.head?=some ⟨owner,if name.value="prior" then 4 else if a.type=.word then 5 else 6⟩)) "scope-local fresh IDs retain every old name/type row"
      if name.value="x" then check (decide (i.names.lookup? "x"=some ⟨owner,if a.type=.word then 2 else 5⟩ ∧ next.names.lookup? "x"=next.ids.head?)) "initializer sees old x; tail selects the newly prepended x"
      let r ← body next ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some t => let m ← meaning t; if same : m.1=a.type then return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩ else throw (IO.userError "typed initializer")
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← child i c; let t ← body i yes; let e ← body i no
      match barrier : yes with
      | ⟨_,[⟨_,.block _⟩]⟩ =>
          have protection : ComputationNamesProtected (i.names.map Prod.fst) yes := by intro name exposed; rw [barrier] at exposed; cases exposed with | tail impossible => cases impossible
          if same : a.type=.bool ∧ t.type=e.type then return ⟨.ifE a.core t.core e.core,t.type,by rw [shape]; exact .conditional (same.1 ▸ a.evidence) protection t.evidence (same.2.symm ▸ e.evidence)⟩ else throw (IO.userError "branch type")
      | _ => throw (IO.userError "original explicit then scope barrier")
  | _ => throw (IO.userError "original body")
termination_by sizeOf b
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=core ∧ p.returnType=output)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=output ∧ b.core=core ∧ b.type=output then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature (output) := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core,output⟩ := ⟨h,ps.declared,by simpa only [erased,same.2.1,same.2.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("c",⟨owner,3⟩),("x",⟨owner,2⟩),("w",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original declarations and actual reverse once"
          return ⟨⟨ps.actual,core,output⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2.1,same.2.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "independent literal Core and outer single annotation")
  | _ => throw (IO.userError "outer single return policy")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .pair a b =>
        let l ← path n a env s; let r ← path n b env l.final
        return ⟨.pair l.value r.value,r.final,l.cost+r.cost+3,fun k => by rw [shape]; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (Core.Steps.cons .enterPair ((l.evidence _).trans (.cons .enterPairRight ((r.evidence _).trans (.cons .applyPair .refl)))))⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩ | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | .binary .wordEq a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : Core.BinaryOp.wordEq.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual equality fault")
    | .ifE c a b =>
        let condition ← path n c env s
        match cv : condition.value with
        | .bool true => let r ← path n a env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (cv ▸ condition.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (cv ▸ condition.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual condition")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩ | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | ⟨_,.tuple ⟨_,[a,b]⟩⟩ => let l ← rawChild table env s a; let r ← rawChild table env l.final b; return ⟨.pair l.value r.value,r.final,l.cost+r.cost+3,by rw [shape]; exact .pair l.evidence r.evidence⟩
  | ⟨_,.binary a ⟨_,.equal⟩ b⟩ =>
      let l ← rawChild table env s a; let r ← rawChild table env l.final b
      match applied : Core.BinaryOp.wordEq.apply l.value r.value with
      | some v => return ⟨v,r.final,l.cost+r.cost+3,by rw [shape]; exact .binary .equal l.evidence r.evidence applied⟩
      | none => throw (IO.userError "raw equality fault")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← rawBody table env s ⟨span,statements⟩; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some _ => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .binding a.evidence r.evidence⟩
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← rawChild table env s c
      match cv : a.value with
      | .bool true => let r ← rawBody table env a.final yes; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .ifTrue (cv ▸ a.evidence) r.evidence⟩
      | .bool false => let r ← rawBody table env a.final no; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .ifFalse (cv ▸ a.evidence) r.evidence⟩
      | _ => throw (IO.userError "raw condition")
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private theorem runtimeArguments {world : Core.StoreTyping} (args : List TypedRuntimeArgument) (typed : ∀ arg ∈ args, Core.RuntimeValueHasType world arg.value arg.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with | nil => exact .nil | cons a rest ih => exact .cons (typed a (by simp)) (ih (fun v member => typed v (by simp [member])))
private def verify (c : Bool) (s final : Core.Store) (value : Core.Value) : IO Unit := do
  let source ← parsed; let rawValues := [reader 0,writer 1 (w 73),w 14,.bool c]; let cost := 45
  let manual ← path 80 (core) rawValues.reverse s
  check (decide (manual.cost=cost ∧ manual.value=value ∧ manual.final=final)) "independent literal calls, captures, store and cost"
  let args ← rawValues.mapM fun value => do
    match built : buildRuntimeArgument? value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=value ∧ a.type=value.type)) "original constructed fields"; return a
    | none => throw (IO.userError "structural construction")
  let p ← prepare source args; let i := p.1.inputs; let env := i.environment.values
  if actualEnv : env=rawValues.reverse then
    have literal (k) : Core.Steps manual.cost ⟨.eval (core) env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩ := by rw [actualEnv]; exact manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body (core) (output) := by simpa only [p.2.down.2.1,p.2.down.2.2] using p.2.down.1.body
    have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,original⟩; have _ := original.core_hasType RecursiveLocalComputationElaborates.core_hasType
    let raw ← rawBody i.names i.environment s source.value.body
    have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
    have allK (k) : Core.Steps raw.cost ⟨.eval (core) env,k,s⟩ ⟨.ret raw.value,k,raw.final⟩ :=
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) original ids k
    have _ := (allK []).final_unique (literal [])
    check (decide (raw.cost=cost ∧ raw.value=value ∧ raw.final=final ∧ validateRuntimeInputs [.word,.word] args s=true)) "independent source cost and opt-in world boundary"
    have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
    have _ := prepareComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args
    have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original
    have whole (fuel) : runRecursiveComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial (core) env s)) := by simp only [runRecursiveComputationFunction?,runComputationFunction?,accepted,p.2.down.2.1,p.2.down.2.2,bind,Option.bind_some,pure]; rfl
    for fuel in List.range (cost+2) do
      have _ := runComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args fuel s
      have _ := whole fuel; have _ := (literal []).runStateful_done_iff (fuel := fuel)
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial (core) env s)))) "same prepared full entry result"
      match stopped : Core.runStateful fuel (.initial (core) env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "fixed completion threshold"
      | .fault _ _ => throw (IO.userError "successful raw path fault")
      | .outOfFuel cp =>
          for extra in [0,1,7,cost] do
            have _ := (literal []).residual_of_outOfFuel stopped; have _ := Core.runStateful_resume stopped extra
            check (decide (fuel<cost ∧ Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial (core) env s) ∧ Core.runStateful (cost-fuel) cp=.done value final)) "every genuine checkpoint and full resume"
    if validated : validateRuntimeInputs [.word,.word] args s=true then
      have runtime := validateRuntimeInputs_iff.mp validated
      have finitePath : Core.Steps manual.cost
          (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by
        rw [p.2.down.2.1]
        exact literal []
      have safe := p.2.down.1.runtime_typed_execution (F := RecursiveLocalComputationFragment) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
        RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation elaborateRecursiveLocalComputation?_iff runtime.1 runtime.2 ⟨manual.value, manual.final, Core.steps_from_initial_sound finitePath⟩
      have agreement : ∃ future, Core.WorldExtends [.word,.word] future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ Core.RuntimeValueHasType future manual.value (output) ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body manual.value manual.final manual.cost ∧
          ∀ fuel, (Core.runStateful fuel (.initial (core) env s)=.done manual.value manual.final ↔ manual.cost≤fuel) ∧ ((∃ cp, Core.runStateful fuel (.initial (core) env s)=.outOfFuel cp) ↔ fuel<manual.cost) := by
        obtain ⟨future,t,v,n,extension,stored,typed,sourceCost,paths,thresholds,_⟩ := safe.2
        have closed : Core.Steps manual.cost (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by rw [p.2.down.2.1]; exact literal []
        obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique closed
        exact ⟨future,extension,stored,by simpa only [p.2.down.2.2] using typed,sourceCost,by simpa only [p.2.down.2.1] using thresholds⟩
      have _ := agreement; have reversed := runtimeArguments args.reverse (fun a member => runtime.1 a (List.mem_reverse.mp member))
      have actual : Core.RuntimeEnvironmentHasTypes [.word,.word] env i.toTypeInputs.context.values := by simpa only [env,i,LocalInputs.environment,LocalInputs.context,LocalInputs.toTypeInputs_context,Resolved.LocalScope.values,List.map_map,Function.comp_def,p.2.down.1.parameters.argument_values,p.2.down.1.parameters.argument_types] using reversed
      for spent in List.range cost do
        match stopped : Core.runStateful spent (.initial (core) env s) with
        | .outOfFuel cp =>
            have saved := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 Core.ContinuationHasType.nil stopped
            have future : ∃ savedWorld finalWorld, Core.WorldExtends [.word,.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧ Core.WorldExtends savedWorld finalWorld ∧ Core.RuntimeStoreHasTypes finalWorld manual.final := by
              obtain ⟨savedWorld,ext,storeTyped,resumed⟩ := saved
              obtain ⟨future,growth,finalTyped⟩ := resumed ((literal []).residual_of_outOfFuel stopped).2
              exact ⟨savedWorld,future,ext,storeTyped,growth,finalTyped⟩
            have _ := future
        | _ => throw (IO.userError "genuine typed checkpoint")
    have _ := (literal [.pairApply .unit]).trans (.cons .applyPair .refl)
    check (decide (Core.runStateful cost ⟨.eval (core) env,[.pairApply .unit],s⟩=.outOfFuel ⟨.ret value,[.pairApply .unit],final⟩ ∧ Core.runStateful (cost+1) ⟨.eval (core) env,[.pairApply .unit],s⟩=.done (.pair .unit value) final)) "retained frame is outside original source cost"
    let outerEnv := w 41::w 14::env; let allocated := s++[w 14]; let left := if c then w 73 else w 41
    let checkpoints : List (Nat × Core.State) := [(2,⟨.ret (w 14),[.letBody tailCore env],s⟩),(17,⟨.ret (w 41),[.letBody afterCore (w 14::env)],allocated⟩),(20,⟨.ret (.bool c),[.ifBranches (branchCore 4) (branchCore 5) outerEnv],allocated⟩),(36,⟨.ret left,[.binaryRight .wordEq (.var 0) outerEnv,.letBody pairCore outerEnv],final⟩),(38,⟨.ret (w 41),[.binaryApply .wordEq left,.letBody pairCore outerEnv],final⟩),(39,⟨.ret (.bool (!c)),[.letBody pairCore outerEnv],final⟩)]
    for (spent,cp) in checkpoints do
      if genuine : Core.runStateful spent (.initial core env s)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        check (decide (Core.runStateful (cost-spent) cp=.done value final)) "actual old x, preserved captured callee, changed Bool x before fresh binding"
      else throw (IO.userError "literal checkpoint fields")
  else throw (IO.userError "actual reverse once")
private def fault (c : Bool) : IO Unit := do
  let source ← parsed; let rawValues := [reader 0,writer 1 (w 73),w 14,.bool c]
  let args ← rawValues.mapM fun v => match buildRuntimeArgument? v with | some a => pure a | none => throw (IO.userError "fault structural construction")
  let p ← prepare source args; let env := p.1.inputs.environment.values; let old := Core.Value.bool false
  let s := [old,w 99]; let t := if c then [old,old,w 14] else [old,w 99,w 14,old]
  let outerEnv := old::w 14::env; let left := if c then w 73 else old
  let frames := [.binaryApply .wordEq left,.letBody pairCore outerEnv]
  let failed : Core.StatefulRunResult := .fault (.invalidBinaryOperands .wordEq left old) ⟨.ret old,frames,t⟩
  let before : Core.State := ⟨.eval (.var 0) outerEnv,frames,t⟩
  check (decide (validateRuntimeInputs [.word,.word] args s=false ∧ Core.runStateful 37 (.initial core env s)=.outOfFuel before ∧ Core.runStateful 1 before=failed)) "initializer fault precedes new Bool shadow and retains selected effects"
  for fuel in List.range 40 do
    let result := Core.runStateful fuel (.initial core env s)
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output,result))) "same static shadow preparation is not a raw value guard"
    if fuel<38 then match stopped : result with
      | .outOfFuel cp => have _ := Core.runStateful_resume (by simpa only [result] using stopped) 38; check (decide (Core.runStateful 38 cp=failed)) "all genuine pre-fault states retain old rows and store effects"
      | _ => throw (IO.userError "first corrupt-store fault")
    else check (decide (result=failed)) "exact fault and later fuels"
end ParsedScopedShadowingEffects
open ParsedScopedShadowingEffects
def frontendParsedScopedShadowingEffectTests : IO Unit := do
  verify true [w 41,w 99] [w 41,w 41,w 14] (.pair (.bool false) (w 14)); verify false [w 41,w 99] [w 41,w 99,w 14,w 41] (.pair (.bool true) (w 14))
  fault true; fault false
end Tests

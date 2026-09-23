import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Core.FuelResumptionProperties
/-! Independent original header/parameters/body and actual raw/manual paths precede
owner transport. Actual closures, stores and full records retain their identity. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationFunctionOwnerEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ComputationFunctionOwnerEffects",by decide⟩],by decide⟩⟩,134⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex := o.declarationIndex+10}
private theorem injective : Function.Injective shift := by rintro ⟨lm,li⟩ ⟨rm,ri⟩ same; simpa [shift] using same
private theorem non_surjective : ¬ Function.Surjective shift := by
  intro h; obtain ⟨o,same⟩ := h {owner with declarationIndex := 0}
  have h := congrArg Resolved.DeclarationId.declarationIndex same; simp [shift] at h
private def relabel := ownerLocalIdMap shift
private theorem relabel_injective : Function.Injective relabel := ownerLocalIdMap_injective shift injective
private def types : TypeNameTable := [(["Word"],.word),(["Bool"],.bool),(["Word"],.bool)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def allocator : Core.Value := .closure .word .word
  (.letE (.newCell .word (.var 0)) (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1)))) [.bool false]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def checkedReader (l : Nat) : Core.Value := .closure .word .word (.binary .wordAdd (.loadCell (.var 1)) (.var 0)) [.cellRef .word l]
private def callCore : Core.Expr := .apply (.var 3) (.var 0)
private def branchCore : Core.Expr := .letE callCore (.var 0)
private def afterCore : Core.Expr := .ifE (.var 1) branchCore callCore
private def core : Core.Expr := .letE (.apply (.var 3) (.var 1)) afterCore
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:function(Word) returns(Word),g:function(Word) returns(Word),x:Word,c:Bool) returns(Word){let x:Word=f(x);if(c){{let x=g(x);return x;}}else{return g(x);}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-function-owner-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original source and range"
  return source
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "original named leaf")
  | ⟨_,.tuple [a]⟩ => let x ← meaning a; return ⟨x.1,⟨by rw [shape]; exact .single x.2.down⟩⟩
  | ⟨_,.function _ ⟨_,[a]⟩ (some ⟨span,results⟩)⟩ => let x ← meaning a; let y ← meaning ⟨span,.tuple results⟩; return ⟨.function x.1 y.1,⟨by rw [shape]; exact .functionReturns x.2.down y.2.down⟩⟩
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
  | _ => throw (IO.userError "static source child")
termination_by sizeOf e
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i b)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; return ⟨r.core,r.type,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← body i ⟨span,statements⟩; return ⟨r.core,r.type,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.length=i.ids.length+1 ∧ next.ids.head?=some ⟨owner,i.bindings.length⟩ ∧ i.names.lookup? "x"=some ⟨owner,if i.bindings.length=4 then 2 else 4⟩)) "fresh4/5 retains old x2/4 and every captured row"
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
private structure Preparation (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) where
  compiled : CompiledRuntimeFunction
  prepared : PreparedRuntimeFunction
  compilation : RecursiveComputationFunctionCompiles types owner source compiled
  preparation : RecursiveComputationFunctionPrepares types owner source args prepared
  coreFixed : prepared.core=core
  typeFixed : prepared.returnType=.word
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Preparation source args) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core ∧ b.type=.word then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2.1,same.2.2] using b.evidence⟩
          have preparation : RecursiveComputationFunctionPrepares types owner source args ⟨ps.actual,core,.word⟩ := ⟨h,ps.bound,by simpa only [same.2.1,same.2.2] using b.evidence⟩
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("c",⟨owner,3⟩),("x",⟨owner,2⟩),("g",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original declared rows and actual reverse exactly once"
          return ⟨⟨ps.statics,core,.word⟩,⟨ps.actual,core,.word⟩,compilation,preparation,rfl,rfl⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "literal Core and original outer return annotation")
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
    | .word w => return ⟨.word w,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell found) .refl))⟩ | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match found : s.read? l, written : s.write? l v with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual missing write")
      | _,_ => throw (IO.userError "manual write reference")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩ | none => throw (IO.userError "manual binary payload")
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


private def arguments (g : Core.Value) (c : Bool) : IO (List TypedRuntimeArgument) :=
  [allocator,g,w 14,.bool c].mapM fun v => do
    match built : buildRuntimeArgument? v with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=v ∧ a.type=v.type)) "unchanged actual closures/captures"; return a
    | none => throw (IO.userError "original actual argument")
private def compiledView (p : CompiledRuntimeFunction) := (p.inputs.bindings.map (fun b => (b.name,b.id,b.type)),p.core,p.returnType)
private def preparedView (p : PreparedRuntimeFunction) := (p.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)),p.core,p.returnType)
private def transport (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (p : Preparation source args) (s : Core.Store) (limit : Nat) : IO Unit := do
  have cc := (computationFunctionCompiles_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mpr p.compilation
  have pc := (computationFunctionPrepares_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mpr p.preparation
  have _ := (computationFunctionCompiles_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mp cc
  have _ := (computationFunctionPrepares_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mp pc
  have _ := compileComputationFunction?_mapOwner shift injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds relabel relabel_injective) types owner source
  have _ := prepareComputationFunction?_mapOwner shift injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds relabel relabel_injective) types owner source args
  check (decide ((compileRecursiveComputationFunction? types (shift owner) source).map compiledView=some (compiledView {p.compiled with inputs := p.compiled.inputs.mapIds relabel relabel_injective}))) "whole original compiled record, mapped IDs only"
  check (decide ((prepareRecursiveComputationFunction? types (shift owner) source args).map preparedView=some (preparedView {p.prepared with inputs := p.prepared.inputs.mapIds relabel relabel_injective}))) "whole actual preparation retains values/captures/core/tag"
  for fuel in List.range limit do
    have _ := runComputationFunction?_mapOwner shift injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds relabel relabel_injective) types owner source args fuel s
    check (decide (runRecursiveComputationFunction? types (shift owner) source args fuel s=runRecursiveComputationFunction? types owner source args fuel s ∧ runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core p.prepared.inputs.environment.values s)))) "complete original/mapped runner record"
private def verify (write : Bool) (l : Nat) (c : Bool) (s final : Core.Store) (value : Core.Value) : IO Unit := do
  let g := if write then writer l else reader l; let source ← parsed; let args ← arguments g c
  let manual ← path 80 core [.bool c,w 14,g,allocator] s; let p ← prepare source args
  let i := p.prepared.inputs; let env := i.environment.values; let cost := (if write then 35 else 28)+(if c then 3 else 0)
  let raw ← rawBody i.names i.environment s source.value.body
  if fixed : env=[.bool c,w 14,g,allocator] ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost ∧ raw.value=value ∧ raw.final=final ∧ raw.cost=cost then
    have ⟨ev,mv,ms,mc,rv,rs,rc⟩ := fixed
    have literal (k) : Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩ := by rw [ev]; simpa only [mv,ms,mc] using manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body core .word := by simpa only [p.coreFixed,p.typeFixed] using p.preparation.body
    have counted : RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body value final cost := by simpa only [rv,rs,rc] using raw.evidence
    have sourcePath (k) := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using counted) original (by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds) k
    have _ := (sourcePath []).final_unique (literal [])
    transport source args p s (cost+2)
    for fuel in List.range (cost+2) do
      have _ := (literal []).runStateful_done_iff (fuel := fuel)
      match genuine : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact actual result/store/fuel"
      | .outOfFuel cp =>
          have _ := (literal []).residual_of_outOfFuel genuine
          for more in [0,1,cost-fuel,cost+2] do
            have _ := Core.runStateful_resume genuine more
            check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core env s))) "all genuine full resumptions"
      | .fault _ _ => throw (IO.userError "successful example faulted")
    let bound := w 15::env; let allocated := s++[w 14]
    let gBody : Core.Expr := if write then .letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2)) else .loadCell (.var 1)
    let gK : List Core.Frame := if c then [.letBody (.var 0) bound] else []
    let cps : List (Nat × Core.State) := [(10,⟨.ret (.cellRef .word 2),[.letBody (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1))) [w 14,.bool false],.letBody afterCore env],allocated⟩),
      (17,⟨.eval afterCore bound,[],allocated⟩),(19,⟨.ret (.bool c),[.ifBranches branchCore callCore bound],allocated⟩),
      ((if c then 26 else 25),⟨.eval gBody [w 15,.cellRef .word l],gK,allocated⟩)] ++
      (if write then [((if c then 32 else 31),⟨.ret .unit,.letBody (.loadCell (.var 2)) [w 15,.cellRef .word l]::gK,final⟩)] else [])
    for (spent,cp) in cps do
      if genuine : Core.runStateful spent (.initial core env s)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        have _ := runComputationFunction?_mapOwner shift injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds relabel relabel_injective) types owner source args spent s
        check (decide (runRecursiveComputationFunction? types (shift owner) source args spent s=some (.word,.outOfFuel cp) ∧ Core.runStateful (cost-spent) cp=.done value final)) "genuine original caller/captures/allocation checkpoint"
      else throw (IO.userError "literal checkpoint")
    have _ := literal [.pairApply (.cellRef .word 700)]; have _ := sourcePath [.pairApply (.cellRef .word 700)]
    check (decide (Core.runStateful (cost+1) ⟨.eval core env,[.pairApply (.cellRef .word 700)],s⟩=.done (.pair (.cellRef .word 700) value) final)) "pending caller outside original body cost"
  else throw (IO.userError "independent original raw/manual fixed expectations")
private def fault (mode : Nat) (c : Bool) : IO Unit := do
  let g := if mode=0 then reader 700 else if mode=1 then writer 700 else checkedReader 0
  let s := if mode=2 then [Core.Value.bool false,w 99] else [w 41,w 99]
  let source ← parsed; let args ← arguments g c; let p ← prepare source args; let env := p.prepared.inputs.environment.values
  let bound := w 15::env; let l := if mode=2 then 0 else 700; let captured := [w 15,Core.Value.cellRef .word l]
  let outer : List Core.Frame := if c then [.letBody (.var 0) bound] else []
  let frames : List Core.Frame := (if mode=0 then [.loadCellApply] else if mode=1 then [.storeCellValue (.var 0) captured,.letBody (.loadCell (.var 2)) captured] else [.binaryApply .wordAdd (.bool false)])++outer
  let spent := (if mode=0 then 27 else if mode=1 then 28 else 31)+(if c then 1 else 0)
  let value := if mode=2 then w 15 else Core.Value.cellRef .word 700; let final := s++[w 14]
  let error := if mode=2 then Core.MachineFault.invalidBinaryOperands .wordAdd (.bool false) (w 15) else .invalidCellLocation 700
  let before : Core.State := ⟨.eval (.var (if mode=2 then 0 else 1)) captured,frames,final⟩
  let failed : Core.StatefulRunResult := .fault error ⟨.ret value,frames,final⟩
  check (decide (Core.runStateful (spent-1) (.initial core env s)=.outOfFuel before ∧ Core.runStateful 1 before=failed)) "actual missing reference or checked-reader payload fault preserves allocation"
  transport source args p s (spent+2)
  for fuel in List.range (spent+2) do
    match genuine : Core.runStateful fuel (.initial core env s) with
    | .outOfFuel cp => have _ := Core.runStateful_resume genuine spent; check (decide (fuel<spent ∧ Core.runStateful spent cp=failed)) "all genuine pre-fault resumptions"
    | result => check (decide (spent≤fuel ∧ result=failed)) "first fault and complete later result"
end ParsedComputationFunctionOwnerEffects
open ParsedComputationFunctionOwnerEffects in
def frontendParsedComputationFunctionOwnerEffectTests : IO Unit := do
  have _ := non_surjective
  for c in [false,true] do
    verify false 0 c [w 41,w 99] [w 41,w 99,w 14] (w 41)
    verify false 1 c [w 41,w 99] [w 41,w 99,w 14] (w 99)
    verify true 2 c [w 41,w 99] [w 41,w 99,w 15] (w 15)
    verify false 1 c [w 41,.bool false] [w 41,.bool false,w 14] (.bool false)
    verify true 0 c [.bool false,w 99] [w 15,w 99,w 14] (w 15)
    for mode in [0,1,2] do fault mode c
end Tests

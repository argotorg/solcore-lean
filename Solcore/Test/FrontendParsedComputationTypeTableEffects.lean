import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Frontend.RuntimeInputValidation
import Solcore.Core.FuelResumptionProperties
/-! Table transport preserves actual closures, allocation, faults and complete saved states. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationTypeTableEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ComputationTypeTableEffects",by decide⟩],by decide⟩⟩,125⟩
private def types : TypeNameTable := [(["Word"],.word),(["Bool"],.bool),(["Word"],.bool)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def reader (l : Nat) : Core.Value := .closure .word .word (.letE (.newCell .word (.var 0)) (.binary .wordAdd (.loadCell (.var 2)) (.var 1))) [.cellRef .word l]
private def branchCore : Core.Expr := .letE (.apply (.var 1) (.var 0)) (.var 0)
private def afterCore : Core.Expr := .ifE (.var 2) branchCore (.var 0)
private def tailCore : Core.Expr := .letE (.apply (.var 0) (.var 2)) afterCore
private def core : Core.Expr := .letE (.var 2) tailCore
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:function(Word) returns(Word),x:Word,c:Bool) returns(Word){let f:function(Word) returns(Word)=f;let x:Word=f(x);if(c){{let x:Word=f(x);return x;}}else{return x;}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-type-table-effects.sol"⟩,text⟩
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
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.length=i.ids.length+1 ∧ next.ids.head?=some (Resolved.freshLocalId owner i.ids))) "same fresh IDs retain every original row"
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
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=core ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core ∧ b.type=.word then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature (.word) := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2.1,same.2.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("c",⟨owner,2⟩),("x",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original declarations and actual reverse once"
          return ⟨⟨ps.actual,core,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2.1,same.2.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
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
    | .binary .wordAdd a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : Core.BinaryOp.wordAdd.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual Word addition fault")
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

private def duplicates : TypeNameTable := types++[(["Word"],.unit),(["Bool"],.word)]
private theorem backwards : TypeNameTable.Extends duplicates types := by
  intro key type found
  have same : duplicates.lookup? key=types.lookup? key := by
    by_cases a : ["Word"]=key <;> by_cases b : ["Bool"]=key <;> simp [duplicates,types,TypeNameTable.lookup?,a,b]
  exact TypeNameTable.lookup?_iff.mp (same ▸ TypeNameTable.lookup?_iff.mpr found)
private def variants : List (Σ next, PLift (TypeNameTable.Extends types next)) :=
  [⟨duplicates,⟨TypeNameTable.Extends.append_right _ _⟩⟩,
   ⟨(["Fresh"],Core.Ty.unit)::types,⟨TypeNameTable.Extends.cons_fresh _ _ _ (by decide)⟩⟩]
private def view (p : PreparedRuntimeFunction) :=
  (p.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)),p.core,p.returnType)
private def arguments (l : Nat) (c : Bool) : IO (List TypedRuntimeArgument) :=
  [reader l,w 14,.bool c].mapM fun v => do
    match built : buildRuntimeArgument? v with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=v ∧ a.type=v.type)) "same constructed closure/captures"; return a
    | none => throw (IO.userError "original actual argument")
private def transport (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (p : PreparedRuntimeFunction)
    (provenance : RecursiveComputationFunctionPrepares types owner source args p) (s : Core.Store) (limit : Nat) : IO Unit := do
  have old := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr provenance
  have compilation : RecursiveComputationFunctionCompiles types owner source p.toCompiled := ⟨provenance.header,provenance.parameters.erase_values,provenance.body⟩
  have oldCompile := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
  have oldBody := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr provenance.body
  have typing := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,provenance.body⟩
  have exactRun (fuel) : runRecursiveComputationFunction? types owner source args fuel s=some (p.returnType,Core.runStateful fuel (.initial p.core p.inputs.environment.values s)) := by simp only [runRecursiveComputationFunction?,runComputationFunction?,old,bind,Option.bind_some,pure]
  for ⟨next,extension⟩ in variants do
    have changed := provenance.extend_types extension.down; have _ := compilation.extend_types extension.down
    have _ := provenance.body.extend_types extension.down; have _ := typing.extend_types extension.down
    have _ := elaborateComputationReturnTree?_some_of_extends extension.down oldBody
    have _ := compileComputationFunction?_some_of_extends extension.down oldCompile
    have exactPrepared := prepareComputationFunction?_some_of_extends extension.down old
    have _ := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr changed
    check (decide ((prepareRecursiveComputationFunction? next owner source args).map view=some (view p))) "entire actual binding rows, captures, Core and return tag"
    for fuel in List.range limit do
      have _ := runComputationFunction?_some_of_extends extension.down (exactRun fuel)
      have _ := runComputationFunction?_eq_of_mutual_extends (checkChild := elaborateRecursiveLocalComputation?) (TypeNameTable.Extends.append_right _ _) backwards owner source args fuel s
      check (decide (runRecursiveComputationFunction? next owner source args fuel s=some (p.returnType,Core.runStateful fuel (.initial p.core p.inputs.environment.values s)))) "transport retains done/fault/complete genuine checkpoint"
    have _ := exactPrepared
  have _ := elaborateComputationReturnTree?_eq_of_mutual_extends (checkChild := elaborateRecursiveLocalComputation?) (TypeNameTable.Extends.append_right _ _) backwards owner p.inputs.toTypeInputs source.value.body
  have _ := compileComputationFunction?_eq_of_mutual_extends (checkChild := elaborateRecursiveLocalComputation?) (TypeNameTable.Extends.append_right _ _) backwards owner source
  for bad in [[],args.drop 1,args.reverse] do
    have _ := prepareComputationFunction?_eq_of_mutual_extends (checkChild := elaborateRecursiveLocalComputation?) (TypeNameTable.Extends.append_right _ _) backwards owner source bad
    check ((prepareRecursiveComputationFunction? types owner source bad).isNone && (prepareRecursiveComputationFunction? duplicates owner source bad).isNone) "mutual equality includes wrong-argument rejection"
private def verify (l base : Nat) (c : Bool) : IO Unit := do
  let source ← parsed; let s := [w 41,w 99]; let first := w (base+14); let value := if c then w (base+base+14) else first
  let final := s++[w 14]++(if c then [first] else []); let cost := if c then 45 else 26
  let manual ← path 80 core [.bool c,w 14,reader l] s
  check (decide (manual.cost=cost ∧ manual.value=value ∧ manual.final=final)) "independent literal Core cost/value and actual allocation"
  let args ← arguments l c; let p ← prepare source args; let i := p.1.inputs; let env := i.environment.values
  if actual : env=[.bool c,w 14,reader l] then
    have literal (k) : Core.Steps manual.cost ⟨.eval core env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩ := by rw [actual]; exact manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body core .word := by simpa only [p.2.down.2.1,p.2.down.2.2] using p.2.down.1.body
    let raw ← rawBody i.names i.environment s source.value.body
    have allK (k) : Core.Steps raw.cost ⟨.eval core env,k,s⟩ ⟨.ret raw.value,k,raw.final⟩ :=
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) original (by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds) k
    have _ := (allK []).final_unique (literal [])
    check (decide (raw.value=value ∧ raw.cost=cost ∧ raw.final=final ∧ validateRuntimeInputs [.word,.word] args s=true)) "independent original source cost and separate valid-world boundary"
    transport source args p.1 p.2.down.1 s (cost+2)
    for fuel in List.range (cost+2) do
      have _ := (literal []).runStateful_done_iff (fuel := fuel)
      match genuine : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "independent full fuel threshold"
      | .outOfFuel cp =>
          have _ := (literal []).residual_of_outOfFuel genuine
          for more in [0,1,cost] do
            have _ := Core.runStateful_resume genuine more
            check (decide (fuel<cost ∧ Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core env s) ∧ Core.runStateful (cost-fuel) cp=.done value final)) "same genuine checkpoint/full resumed state"
      | .fault _ _ => throw (IO.userError "successful path fault")
    let retained := reader l::env; let allocated := s++[w 14]
    let cps : List (Nat × Core.State) := [(20,⟨.ret (w 14),[.binaryApply .wordAdd (w base),.letBody afterCore retained],allocated⟩),(21,⟨.ret first,[.letBody afterCore retained],allocated⟩),(24,⟨.ret (.bool c),[.ifBranches branchCore (.var 0) (first::retained)],allocated⟩)]
    for (spent,cp) in cps do
      if genuine : Core.runStateful spent (.initial core env s)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        have ready := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
        have stopped : runComputationFunction? elaborateRecursiveLocalComputation? types owner source args spent s=some (.word,.outOfFuel cp) := by simp only [runComputationFunction?,ready,bind,Option.bind_some,pure,p.2.down.2.1,p.2.down.2.2]; exact congrArg (fun r => some (Core.Ty.word,r)) genuine
        for ⟨next,extension⟩ in variants do
          have _ := runComputationFunction?_some_of_extends extension.down stopped
          check (decide (runRecursiveComputationFunction? next owner source args spent s=some (.word,.outOfFuel cp))) "literal saved environment/capture/store transported without erasure"
        check (decide (Core.runStateful (cost-spent) cp=.done value final)) "literal actual operands/captured callee/old rows are retained"
      else throw (IO.userError "literal checkpoint")
    have _ := literal [.pairApply .unit]
    check (decide (Core.runStateful cost ⟨.eval core env,[.pairApply .unit],s⟩=.outOfFuel ⟨.ret value,[.pairApply .unit],final⟩)) "caller continuation is outside source cost"
  else throw (IO.userError "actual argument reverse once")
private def fault (missing c : Bool) : IO Unit := do
  let l := if missing then 700 else 0; let s := if missing then [w 41,w 99] else [Core.Value.bool false,w 99]
  let source ← parsed; let args ← arguments l c; let p ← prepare source args; let env := p.1.inputs.environment.values
  let caller := reader l::env; let captured : Core.Environment := [.cellRef .word s.length,w 14,.cellRef .word l]
  let allocated := s++[w 14]; let spent := if missing then 17 else 20
  let frames : List Core.Frame := if missing then [.loadCellApply,.binaryRight .wordAdd (.var 1) captured,.letBody afterCore caller] else [.binaryApply .wordAdd (.bool false),.letBody afterCore caller]
  let v := if missing then Core.Value.cellRef .word l else w 14
  let error := if missing then Core.MachineFault.invalidCellLocation l else .invalidBinaryOperands .wordAdd (.bool false) (w 14)
  let failed : Core.StatefulRunResult := .fault error ⟨.ret v,frames,allocated⟩
  let before : Core.State := ⟨.eval (.var (if missing then 2 else 1)) captured,frames,allocated⟩
  check (decide (validateRuntimeInputs [.word,.word] args s=false ∧ Core.runStateful (spent-1) (.initial core env s)=.outOfFuel before ∧ Core.runStateful 1 before=failed)) "missing/corrupt actual reference retains allocation before fault"
  transport source args p.1 p.2.down.1 s (spent+2)
  for fuel in List.range (spent+2) do
    match genuine : Core.runStateful fuel (.initial core env s) with
    | .outOfFuel cp => have _ := Core.runStateful_resume genuine spent; check (decide (fuel<spent ∧ Core.runStateful spent cp=failed)) "every pre-fault checkpoint and exact resumed fault"
    | result => check (decide (spent≤fuel ∧ result=failed)) "same first fault and all later fuels"
end ParsedComputationTypeTableEffects
open ParsedComputationTypeTableEffects
def frontendParsedComputationTypeTableEffectTests : IO Unit := do
  for (l,base) in [(0,41),(1,99)] do for c in [false,true] do verify l base c
  for missing in [false,true] do for c in [false,true] do fault missing c
end Tests

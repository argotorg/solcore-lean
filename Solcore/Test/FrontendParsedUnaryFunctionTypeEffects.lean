import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.ComputationFunctionFactorizationProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Frontend.RuntimeInputValidation
import Solcore.Frontend.ComputationFunctionRuntimeSafetyProperties
import Solcore.Frontend.ComputationReturnTreeRuntimeWorldProperties
import Solcore.Core.FuelResumptionProperties
/-! Original unary annotations supply no runtime closure. Independently supplied
factory/writer values allocate, capture, write, and return a closure or a triple. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedUnaryFunctionTypeEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"UnaryFunctionTypeEffects",by decide⟩],by decide⟩⟩,123⟩
private def types : TypeNameTable := [(["Word"],.word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def triple : Core.Ty := .product .word (.product .word .word)
private def output (invoke : Bool) : Core.Ty := if invoke then triple else .function .word triple
private def reads : Core.Expr := .pair (.loadCell (.var 3)) (.pair (.loadCell (.var 4)) (.loadCell (.var 1)))
private def factory (l r : Nat) : Core.Value := .closure .word (.function .word triple)
  (.letE (.newCell .word (.var 0)) (.lambda .word triple reads)) [.cellRef .word l,.cellRef .word r]
private def writer (l : Nat) : Core.Value := .closure .word .unit (.storeCell (.var 1) (.var 0)) [.cellRef .word l]
private def resultClosure (l r fresh : Nat) : Core.Value := .closure .word triple reads [.cellRef .word fresh,w 14,.cellRef .word l,.cellRef .word r]
private def lastCore (invoke : Bool) : Core.Expr := if invoke then .apply (.var 2) (.var 3) else .var 2
private def middle (invoke : Bool) : Core.Expr := .letE (.apply (.var 0) (.var 2)) (lastCore invoke)
private def tailCore (invoke : Bool) : Core.Expr := .letE (.var 2) (middle invoke)
private def core (invoke : Bool) : Core.Expr := .letE (.apply (.var 2) (.var 0)) (tailCore invoke)
private def parsed (invoke : Bool) (terminal : Option String := none) : IO Syntax.FunctionDecl := do
  let text := "function route(m:function(Word) returns(function(Word) returns(Word,Word,Word)),w:function(Word),x:Word) returns(" ++ (if invoke then "(Word,Word,Word)" else "function(Word) returns(Word,Word,Word)") ++ "){let f:function(Word) returns(Word,Word,Word)=m(x);let g:function(Word) returns()=w;g(x);return " ++ terminal.getD (if invoke then "f(x)" else "f") ++ ";}"
  let file : Syntax.SourceFile := ⟨⟨.main,"unary-function-type-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original source and range"
  return source
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "original named leaf")
  | ⟨_,.tuple []⟩ => return ⟨.unit,⟨by rw [shape]; exact .unit⟩⟩
  | ⟨_,.tuple [a]⟩ => let x ← meaning a; return ⟨x.1,⟨by rw [shape]; exact .single x.2.down⟩⟩
  | ⟨_,.tuple [a,b]⟩ => let x ← meaning a; let y ← meaning b; return ⟨.product x.1 y.1,⟨by rw [shape]; exact .pair x.2.down y.2.down⟩⟩
  | ⟨span,.tuple (a::b::c::rest)⟩ => let x ← meaning a; let y ← meaning ⟨span,.tuple (b::c::rest)⟩; return ⟨.product x.1 y.1,⟨by rw [shape]; exact .many x.2.down y.2.down⟩⟩
  | ⟨span,.function keyword ⟨ps,[a]⟩ none⟩ =>
      check (span.contains keyword && span.contains ps && ps.contains a.span) "original absent-return function ranges"
      let x ← meaning a; return ⟨.function x.1 .unit,⟨by rw [shape]; exact .functionDefault x.2.down⟩⟩
  | ⟨span,.function keyword ⟨ps,[a]⟩ (some ⟨rs,results⟩)⟩ =>
      check (span.contains keyword && span.contains ps && ps.contains a.span && span.contains rs && results.all (fun r => rs.contains r.span)) "original present return-list range and children"
      let x ← meaning a; let y ← meaning ⟨rs,.tuple results⟩
      return ⟨.function x.1 y.1,⟨by rw [shape]; exact .functionReturns x.2.down y.2.down⟩⟩
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
  | ⟨span,⟨_,.letDecl name (some annotation) (some e)⟩::rest⟩ =>
      let m ← meaning annotation; let a ← child i e
      if same : m.1=a.type then
        if unused : name.value ∉ i.names.map Prod.fst then
          let r ← body (i.bindFresh owner name.value a.type) ⟨span,rest⟩
          return ⟨.letE a.core r.core,r.type,by rw [shape]; exact .binding (same ▸ m.2.down) unused a.evidence r.evidence⟩
        else throw (IO.userError "fresh typed let")
      else throw (IO.userError "typed let annotation")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← child i e; let r ← body i ⟨span,rest⟩; return ⟨.letE a.core (r.core.weakenAt 0),r.type,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | _ => throw (IO.userError "original body")
termination_by sizeOf b
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (invoke : Bool) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=core invoke ∧ p.returnType=output invoke)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=output invoke ∧ b.core=core invoke ∧ b.type=output invoke then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature (output invoke) := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core invoke,output invoke⟩ := ⟨h,ps.declared,by simpa only [erased,same.2.1,same.2.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("x",⟨owner,2⟩),("w",⟨owner,1⟩),("m",⟨owner,0⟩)])) "original declarations and actual reverse once"
          return ⟨⟨ps.actual,core invoke,output invoke⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2.1,same.2.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
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
    | .var i => match found : env[i]? with
      | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "manual variable")
    | .lambda a b c => return ⟨.closure a b c env,s,1,fun _ => by rw [shape]; exact .cons .lambda .refl⟩
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
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with
      | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
      | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with
      | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "raw row")
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
  | ⟨span,⟨_,.letDecl name (some _) (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .binding a.evidence r.evidence⟩
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← rawChild table env s e; let r ← rawBody table env a.final ⟨span,rest⟩; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private theorem runtimeArguments {world : Core.StoreTyping} (args : List TypedRuntimeArgument)
    (typed : ∀ arg ∈ args, Core.RuntimeValueHasType world arg.value arg.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons a rest ih => exact .cons (typed a (by simp)) (ih (fun v member => typed v (by simp [member])))
private def verify (invoke : Bool) (l r location : Nat) (s final : Core.Store) (value : Core.Value) (valid : Bool) : IO Unit := do
  let source ← parsed invoke; let rawValues := [factory l r,writer location,w 14]; let cost := if invoke then 48 else 29
  let manual ← path 80 (core invoke) rawValues.reverse s
  check (decide (manual.cost=cost ∧ manual.value=value ∧ manual.final=final)) "independent literal calls, captures, store and cost"
  let args ← rawValues.mapM fun value => do
    match built : buildRuntimeArgument? value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=value ∧ a.type=value.type)) "original constructed fields"; return a
    | none => throw (IO.userError "structural construction")
  let p ← prepare source args invoke; let i := p.1.inputs; let env := i.environment.values
  if actualEnv : env=rawValues.reverse then
    have literal (k) : Core.Steps manual.cost ⟨.eval (core invoke) env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩ := by rw [actualEnv]; exact manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body (core invoke) (output invoke) := by simpa only [p.2.down.2.1,p.2.down.2.2] using p.2.down.1.body
    let raw ← rawBody i.names i.environment s source.value.body
    have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
    have allK (k) : Core.Steps raw.cost ⟨.eval (core invoke) env,k,s⟩ ⟨.ret raw.value,k,raw.final⟩ :=
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) original ids k
    have _ := (allK []).final_unique (literal [])
    check (decide (raw.cost=cost ∧ raw.value=value ∧ raw.final=final ∧ validateRuntimeInputs [.word,.word] args s=valid)) "independent source cost and opt-in world boundary"
    have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
    have _ := prepareComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args
    have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original
    have whole (fuel) : runRecursiveComputationFunction? types owner source args fuel s=some (output invoke,Core.runStateful fuel (.initial (core invoke) env s)) := by simp only [runRecursiveComputationFunction?,runComputationFunction?,accepted,p.2.down.2.1,p.2.down.2.2,bind,Option.bind_some,pure]; rfl
    for fuel in List.range (cost+2) do
      have _ := runComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args fuel s
      have _ := whole fuel; have _ := (literal []).runStateful_done_iff (fuel := fuel)
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output invoke,Core.runStateful fuel (.initial (core invoke) env s)))) "same prepared full entry result"
      match stopped : Core.runStateful fuel (.initial (core invoke) env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "fixed completion threshold"
      | .fault _ _ => throw (IO.userError "successful raw path fault")
      | .outOfFuel cp =>
          for extra in [0,1,7,cost] do
            have _ := (literal []).residual_of_outOfFuel stopped; have _ := Core.runStateful_resume stopped extra
            check (decide (fuel<cost ∧ Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial (core invoke) env s) ∧ Core.runStateful (cost-fuel) cp=.done value final)) "every genuine checkpoint and full resume"
    if validated : validateRuntimeInputs [.word,.word] args s=true then
      have runtime := validateRuntimeInputs_iff.mp validated
      have safe := p.2.down.1.runtime_typed_execution (F := RecursiveLocalComputationFragment) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
        RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation elaborateRecursiveLocalComputation?_iff runtime.1 runtime.2
      have agreement : ∃ future, Core.WorldExtends [.word,.word] future ∧ Core.StoreHasTypes future manual.final ∧ Core.RuntimeValueHasType future manual.value (output invoke) ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body manual.value manual.final manual.cost ∧
          ∀ fuel, (Core.runStateful fuel (.initial (core invoke) env s)=.done manual.value manual.final ↔ manual.cost≤fuel) ∧ ((∃ cp, Core.runStateful fuel (.initial (core invoke) env s)=.outOfFuel cp) ↔ fuel<manual.cost) := by
        obtain ⟨future,t,v,n,extension,stored,typed,sourceCost,paths,thresholds,_⟩ := safe.2
        have closed : Core.Steps manual.cost (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by rw [p.2.down.2.1]; exact literal []
        obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique closed
        exact ⟨future,extension,stored,by simpa only [p.2.down.2.2] using typed,sourceCost,by simpa only [p.2.down.2.1] using thresholds⟩
      have _ := agreement
      have reversed := runtimeArguments args.reverse (fun a member => runtime.1 a (List.mem_reverse.mp member))
      have actual : Core.RuntimeEnvironmentHasTypes [.word,.word] env i.toTypeInputs.context.values := by simpa only [env,i,LocalInputs.environment,LocalInputs.context,LocalInputs.toTypeInputs_context,Resolved.LocalScope.values,List.map_map,Function.comp_def,p.2.down.1.parameters.argument_values,p.2.down.1.parameters.argument_types] using reversed
      for spent in List.range cost do
        match stopped : Core.runStateful spent (.initial (core invoke) env s) with
        | .outOfFuel cp =>
            have saved := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 Core.ContinuationHasType.nil stopped
            have future : ∃ savedWorld finalWorld, Core.WorldExtends [.word,.word] savedWorld ∧ Core.StoreHasTypes savedWorld cp.store ∧ Core.WorldExtends savedWorld finalWorld ∧ Core.StoreHasTypes finalWorld manual.final := by
              obtain ⟨savedWorld,ext,storeTyped,resumed⟩ := saved
              obtain ⟨future,growth,finalTyped⟩ := resumed ((literal []).residual_of_outOfFuel stopped).2
              exact ⟨savedWorld,future,ext,storeTyped,growth,finalTyped⟩
            have _ := future
        | _ => throw (IO.userError "genuine typed checkpoint")
    have _ := (literal [.pairApply .unit]).trans (.cons .applyPair .refl)
    check (decide (Core.runStateful cost ⟨.eval (core invoke) env,[.pairApply .unit],s⟩=.outOfFuel ⟨.ret value,[.pairApply .unit],final⟩ ∧ Core.runStateful (cost+1) ⟨.eval (core invoke) env,[.pairApply .unit],s⟩=.done (.pair .unit value) final)) "retained frame is outside original source cost"
    if l=0 && r=1 && location=0 && s==[w 41,w 99] then
      let f := resultClosure 0 1 2; let allocated := s++[w 14]
      let checkpoints : List (Nat × Core.State) := [(12,⟨.ret f,[.letBody (tailCore invoke) env],allocated⟩),(15,⟨.ret (writer 0),[.letBody (middle invoke) (f::env)],allocated⟩),(27,⟨.ret .unit,[.letBody (lastCore invoke) (writer 0::f::env)],final⟩)] ++ if invoke then [(32,⟨.ret (w 14),[.applyClosure .word triple reads [.cellRef .word 2,w 14,.cellRef .word 0,.cellRef .word 1]],final⟩),(47,⟨.ret (.pair (w 99) (w 14)),[.pairApply (w 14)],final⟩)] else []
      for (spent,cp) in checkpoints do
        if genuine : Core.runStateful spent (.initial (core invoke) env s)=.outOfFuel cp then
          have _ := (literal []).residual_of_outOfFuel genuine
          check (decide (Core.runStateful (cost-spent) cp=.done value final)) "literal dynamic captures and pending typed/discard/apply/pair frames"
        else throw (IO.userError "literal checkpoint fields")
  else throw (IO.userError "actual reverse once")
private def fault (missingWriter : Bool) : IO Unit := do
  let source ← parsed true; let r := if missingWriter then 1 else 700; let location := if missingWriter then 700 else 0
  let rawValues := [factory 0 r,writer location,w 14]
  let args ← rawValues.mapM fun v => match buildRuntimeArgument? v with | some a => pure a | none => throw (IO.userError "fault structural construction")
  let p ← prepare source args true; let env := p.1.inputs.environment.values; let f := resultClosure 0 r 2
  let s := [w 41,w 99]; let t := if missingWriter then [w 41,w 99,w 14] else [w 14,w 99,w 14]
  let callEnv := [w 14,.cellRef .word 2,w 14,.cellRef .word 0,.cellRef .word r]
  let frames := if missingWriter then [.storeCellValue (.var 0) [w 14,.cellRef .word 700],.letBody (lastCore true) (writer location::f::env)] else [.loadCellApply,.pairRight (.loadCell (.var 1)) callEnv,.pairApply (w 14)]
  let failed : Core.StatefulRunResult := .fault (.invalidCellLocation 700) ⟨.ret (.cellRef .word 700),frames,t⟩
  let before : Core.State := ⟨.eval (.var (if missingWriter then 1 else 4)) (if missingWriter then [w 14,.cellRef .word 700] else callEnv),frames,t⟩
  let first := if missingWriter then 24 else 41
  check (decide (validateRuntimeInputs [.word,.word] args s=false ∧ Core.runStateful (first-1) (.initial (core true) env s)=.outOfFuel before ∧ Core.runStateful 1 before=failed)) "actual missing reference: precise first fault after earlier effects"
  for fuel in List.range (first+2) do
    let result := Core.runStateful fuel (.initial (core true) env s)
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (triple,result))) "annotation acceptance is not a raw execution guard"
    if fuel<first then match stopped : result with
      | .outOfFuel cp => have _ := Core.runStateful_resume (by simpa only [result] using stopped) first; check (decide (Core.runStateful first cp=failed)) "every pre-fault checkpoint preserves allocation/write"
      | _ => throw (IO.userError "first missing-reference fault")
    else check (decide (result=failed)) "exact fault state and all later fuels"
end ParsedUnaryFunctionTypeEffects
open ParsedUnaryFunctionTypeEffects
def frontendParsedUnaryFunctionTypeEffectTests : IO Unit := do
  verify true 0 1 0 [w 41,w 99] [w 14,w 99,w 14] (.pair (w 14) (.pair (w 99) (w 14))) true
  verify false 0 1 0 [w 41,w 99] [w 14,w 99,w 14] (resultClosure 0 1 2) true
  verify true 1 0 0 [w 41,w 99] [w 14,w 99,w 14] (.pair (w 99) (.pair (w 14) (w 14))) true
  verify true 0 1 1 [w 41,w 99] [w 41,w 14,w 14] (.pair (w 41) (.pair (w 14) (w 14))) true
  verify true 0 1 0 [w 41,.bool true] [w 14,.bool true,w 14] (.pair (w 14) (.pair (.bool true) (w 14))) false
  fault true; fault false
  for callText in ["f()","f(x,x)"] do
    let source ← parsed true (some callText)
    check (decide (compileRecursiveComputationFunction? types owner source=none)) "unary annotations do not broaden original call arity"
end Tests

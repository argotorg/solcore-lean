import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Core.FuelResumptionProperties
/-! Original value-free compilation is built before actual arguments. Independent
literal bindings identify the reconstructed proof witness without extracting Prop
data into IO. Same-typed closure permutations retain types, not values or effects. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationArgumentEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ComputationArgumentEffects",by decide⟩],by decide⟩⟩,140⟩
private def types : TypeNameTable := [(["Word"],.word),(["Word"],.bool)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def allocator : Core.Value := .closure .word .word
  (.letE (.newCell .word (.var 0)) (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1)))) [.bool false]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def checkedReader (l : Nat) : Core.Value := .closure .word .word (.binary .wordAdd (.loadCell (.var 1)) (.var 0)) [.cellRef .word l]
private def second : Core.Expr := .letE (.apply (.var 3) (.var 0)) (.var 0)
private def first : Core.Expr := .letE (.apply (.var 2) (.var 1)) second
private def core : Core.Expr := .letE (.apply (.var 2) (.var 0)) first
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:function(Word) returns(Word),g:function(Word) returns(Word),x:Word) returns(Word){f(x);let x:Word=g(x);let x=g(x);return x;}"
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-argument-effects.sol"⟩,text⟩
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
private def declare (i : LocalTypeInputs) (ps : List Syntax.FunctionParameter) : IO (Σ o, PLift (RuntimeParametersDeclareFrom types owner i ps o)) := do
  match shape : ps with
  | [] => return ⟨i,⟨by rw [shape]; exact .nil⟩⟩
  | ⟨span,.typed none name annotation⟩::rest =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if unused : name.value ∉ i.names.map Prod.fst then
        let r ← declare (i.bindFresh owner name.value m.1) rest
        return ⟨r.1,⟨by rw [shape]; exact .cons m.2.down unused r.2.down⟩⟩
      else throw (IO.userError "duplicate parameter")
  | _ => throw (IO.userError "source parameter")
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
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← child i e; let r ← body i ⟨span,rest⟩; return ⟨.letE a.core (r.core.weakenAt 0),r.type,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.head?=some ⟨owner,i.bindings.length⟩ ∧ i.names.lookup? "x"=some ⟨owner,if i.bindings.length=3 then 2 else 3⟩)) "fresh3/4 retains original x2/3; discard creates no source ID"
      let r ← body next ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some t => let m ← meaning t; if same : m.1=a.type then return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩ else throw (IO.userError "typed initializer")
  | _ => throw (IO.userError "original body")
termination_by sizeOf b
private structure Compilation (source : Syntax.FunctionDecl) where
  inputs : LocalTypeInputs
  evidence : RecursiveComputationFunctionCompiles types owner source ⟨inputs,core,.word⟩
private def compile (source : Syntax.FunctionDecl) : IO (Compilation source) := do
  let ps ← declare .empty source.value.signature.parameters.elements; let b ← body ps.1 source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core ∧ b.type=.word then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          return ⟨ps.1,⟨h,ps.2.down,by simpa only [same.2.1,same.2.2] using b.evidence⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "literal Core and original return annotation")
  | _ => throw (IO.userError "outer return")
private def bind (i : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Σ o, PLift (RuntimeParametersBindFrom types owner i ps args o)) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨i,⟨by rw [shape,supplied]; exact .nil⟩⟩
  | ⟨_,.typed none name annotation⟩::rest,arg::tail =>
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ i.names.map Prod.fst then
          let r ← bind (i.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨r.1,⟨by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused r.2.down⟩⟩
        else throw (IO.userError "duplicate actual binding")
      else throw (IO.userError "ordered actual type")
  | _,_ => throw (IO.userError "actual arity")
private structure Preparation (source : Syntax.FunctionDecl) (c : Compilation source) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RecursiveComputationFunctionPrepares types owner source args ⟨inputs,core,.word⟩
  projection : (PreparedRuntimeFunction.mk inputs core .word).toCompiled=⟨c.inputs,core,.word⟩
private def prepare (source : Syntax.FunctionDecl) (c : Compilation source) (args : List TypedRuntimeArgument) : IO (Preparation source c args) := do
  let rows ← bind .empty source.value.signature.parameters.elements args
  if matching : args.map (·.type)=c.inputs.context.values.reverse then
    have realized : ∃ candidate, RecursiveComputationFunctionPrepares types owner source args candidate ∧
        candidate.toCompiled=⟨c.inputs,core,.word⟩ ∧ candidate=⟨rows.1,core,.word⟩ := by
      obtain ⟨candidate,h,erased⟩ := c.evidence.prepare_arguments args matching
      have sameInputs := RuntimeParametersBindFrom.result_unique h.parameters rows.2.down
      have sameCore := congrArg CompiledRuntimeFunction.core erased
      have sameType := congrArg CompiledRuntimeFunction.returnType erased
      refine ⟨candidate,h,erased,?_⟩
      cases candidate; cases sameInputs; cases sameCore; cases sameType; rfl
    have proof : RecursiveComputationFunctionPrepares types owner source args ⟨rows.1,core,.word⟩ ∧
        (PreparedRuntimeFunction.mk rows.1 core .word).toCompiled=⟨c.inputs,core,.word⟩ := by
      obtain ⟨candidate,h,e,same⟩ := realized; simpa only [same] using And.intro h e
    have _ := proof.1.compiles
    have _ := (computationFunctionPrepares_toCompiled_iff.mpr ⟨c.evidence,matching⟩)
    have _ := computationFunctionPrepares_toCompiled_iff.mp ⟨_,proof.1,proof.2⟩
    have _ := proof.1.argument_values
    have unique : ∀ candidate, RecursiveComputationFunctionPrepares types owner source args candidate →
        candidate.toCompiled=⟨c.inputs,core,.word⟩ → candidate=⟨rows.1,core,.word⟩ := by
      intro candidate h erased; exact h.unique_of_toCompiled_eq proof.1 (erased.trans proof.2.symm)
    check (decide (rows.1.environment.values=args.reverse.map (·.value) ∧ rows.1.names=[("x",⟨owner,2⟩),("g",⟨owner,1⟩),("f",⟨owner,0⟩)])) "literal original actual rows, values and captures reversed once"
    return ⟨rows.1,proof.1,proof.2⟩
  else throw (IO.userError "independent compiled ordered type guard")
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
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← rawChild table env s e; let r ← rawBody table env a.final ⟨span,rest⟩; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some _ => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .binding a.evidence r.evidence⟩
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private def arguments (f g : Core.Value) : IO (List TypedRuntimeArgument) :=
  [f,g,w 14].mapM fun v => do
    match built : buildRuntimeArgument? v with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=v ∧ a.type=v.type)) "literal supplied values and captures"; return a
    | none => throw (IO.userError "structural actual argument")
private def view (p : PreparedRuntimeFunction) := (p.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)),p.core,p.returnType)
private def verify (source : Syntax.FunctionDecl) (c : Compilation source) (f g : Core.Value)
    (s middle next final : Core.Store) (discarded firstValue value : Core.Value) (gCost : Nat) : IO (Σ p : PreparedRuntimeFunction, PLift (p.toCompiled=⟨c.inputs,core,.word⟩)) := do
  let args ← arguments f g; let manual ← path 80 core [w 14,g,f] s; let p ← prepare source c args
  let i := p.inputs; let env := i.environment.values; let cost := 22+2*gCost; let raw ← rawBody i.names i.environment s source.value.body
  if fixed : env=[w 14,g,f] ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost ∧ raw.value=value ∧ raw.final=final ∧ raw.cost=cost then
    have ⟨ev,mv,ms,mc,rv,rs,rc⟩ := fixed
    have literal (k) : Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩ := by rw [ev]; simpa only [mv,ms,mc] using manual.evidence k
    have counted : RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body value final cost := by simpa only [rv,rs,rc] using raw.evidence
    have sourcePath (k) := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using counted) p.evidence.body (by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds) k
    have _ := (sourcePath []).final_unique (literal [])
    check (decide ((prepareRecursiveComputationFunction? types owner source args).map view=some (view ⟨i,core,.word⟩))) "complete literal prepared record identified by independent reconstruction"
    for fuel in List.range (cost+2) do
      have _ := (literal []).runStateful_done_iff (fuel := fuel)
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "complete prepared runner and declared tag"
      match genuine : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact cost and actual effects"
      | .outOfFuel cp =>
          have _ := (literal []).residual_of_outOfFuel genuine
          for more in [0,1,cost-fuel,cost+2] do
            have _ := Core.runStateful_resume genuine more
            check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core env s))) "all genuine full resumptions"
      | .fault _ _ => throw (IO.userError "successful example faulted")
    let hidden := discarded::env; let bound := firstValue::hidden
    let .closure _ _ gBody captured := g | throw (IO.userError "actual closure")
    let cps : List (Nat × Core.State) := [(17,⟨.eval first hidden,[],middle⟩),(23,⟨.eval gBody (w 14::captured),[.letBody second hidden],middle⟩),
      (18+gCost,⟨.ret firstValue,[.letBody second hidden],next⟩),(19+gCost,⟨.eval second bound,[],next⟩),(cost-2,⟨.ret value,[.letBody (.var 0) bound],final⟩)]++
      (if f=allocator then [(10,⟨.ret (.cellRef .word 2),[.letBody (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1))) [w 14,.bool false],.letBody first env],s++[w 14]⟩)] else [])
    for (spent,cp) in cps do
      if genuine : Core.runStateful spent (.initial core env s)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        check (decide (runRecursiveComputationFunction? types owner source args spent s=some (.word,.outOfFuel cp) ∧ Core.runStateful (cost-spent) cp=.done value final)) "genuine hidden discard slot, saved actual capture and latest store"
      else throw (IO.userError "literal checkpoint")
    have _ := literal [.pairApply (.cellRef .word 700)]; have _ := sourcePath [.pairApply (.cellRef .word 700)]
    check (decide (Core.runStateful (cost+1) ⟨.eval core env,[.pairApply (.cellRef .word 700)],s⟩=.done (.pair (.cellRef .word 700) value) final)) "pending caller outside source cost"
    return ⟨⟨i,core,.word⟩,⟨p.projection⟩⟩
  else throw (IO.userError "independent original raw/manual expectations")
private def fault (source : Syntax.FunctionDecl) (c : Compilation source) (mode : Nat) : IO Unit := do
  let f := if mode=0 then reader 700 else allocator
  let g := if mode=0 then writer 0 else if mode=1 then reader 700 else if mode=2 then writer 700 else checkedReader 0
  let s := if mode=3 then [Core.Value.bool false,w 99] else [w 41,w 99]
  let args ← arguments f g; let p ← prepare source c args; let env := p.inputs.environment.values
  let captured := [w 14,Core.Value.cellRef .word (if mode=3 then 0 else 700)]
  let outer := if mode=0 then Core.Frame.letBody first env else .letBody second (w 15::env)
  let frames := (if mode≤1 then [.loadCellApply] else if mode=2 then [.storeCellValue (.var 0) captured,.letBody (.loadCell (.var 2)) captured] else [.binaryApply .wordAdd (.bool false)])++[outer]
  let spent := if mode=0 then 8 else if mode=1 then 25 else if mode=2 then 26 else 29
  let final := if mode=0 then s else s++[w 14]; let v := if mode=3 then w 14 else Core.Value.cellRef .word 700
  let error := if mode=3 then Core.MachineFault.invalidBinaryOperands .wordAdd (.bool false) (w 14) else .invalidCellLocation 700
  let before : Core.State := ⟨.eval (.var (if mode=3 then 0 else 1)) captured,frames,final⟩
  let failed : Core.StatefulRunResult := .fault error ⟨.ret v,frames,final⟩
  check (decide (Core.runStateful (spent-1) (.initial core env s)=.outOfFuel before ∧ Core.runStateful 1 before=failed)) "discard fault skips later calls; later faults preserve earlier allocation"
  for fuel in List.range (spent+2) do
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "reconstruction is not a runtime-world guard"
    match genuine : Core.runStateful fuel (.initial core env s) with
    | .outOfFuel cp => have _ := Core.runStateful_resume genuine spent; check (decide (fuel<spent ∧ Core.runStateful spent cp=failed)) "all pre-fault resumptions"
    | result => check (decide (spent≤fuel ∧ result=failed)) "first fault and unchanged later results"
end ParsedComputationArgumentEffects
open ParsedComputationArgumentEffects in
def frontendParsedComputationArgumentEffectTests : IO Unit := do
  let source ← parsed; let c ← compile source
  for (location,value) in [(0,w 41),(1,w 99),(2,w 14)] do
    let _ ← verify source c allocator (reader location) [w 41,w 99] [w 41,w 99,w 14] [w 41,w 99,w 14] [w 41,w 99,w 14] (w 15) value value 8
  let original ← verify source c allocator (writer 0) [w 41,w 99] [w 41,w 99,w 14] [w 14,w 99,w 14] [w 14,w 99,w 14] (w 15) (w 14) (w 14) 15
  let permuted ← verify source c (writer 0) allocator [w 41,w 99] [w 14,w 99] [w 14,w 99,w 14] [w 14,w 99,w 14,w 15] (w 14) (w 15) (w 16) 15
  have _ : original.1.toCompiled=permuted.1.toCompiled := original.2.down.trans permuted.2.down.symm
  check (decide (original.1.inputs.environment.values≠permuted.1.inputs.environment.values)) "same compiled projection and same cost52 do not equate different same-typed supplied closures"
  let _ ← verify source c allocator (reader 0) [.bool false,w 99] [.bool false,w 99,w 14] [.bool false,w 99,w 14] [.bool false,w 99,w 14] (w 15) (.bool false) (.bool false) 8
  let _ ← verify source c allocator (writer 0) [.bool false,w 99] [.bool false,w 99,w 14] [w 14,w 99,w 14] [w 14,w 99,w 14] (w 15) (w 14) (w 14) 15
  for mode in [0,1,2,3] do fault source c mode
end Tests

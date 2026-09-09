import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.ComputationFunctionFactorizationProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Frontend.RuntimeComputationFunctionFactorizationProperties
import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Frontend.RuntimeInputValidation
import Solcore.Frontend.ComputationFunctionRuntimeSafetyProperties
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.ComputationReturnTreeRuntimeCheckpointProperties
import Solcore.Frontend.ComputationReturnTreeRuntimeWorldProperties
/-! Original named/discarded slots and nested literal matches retain their source
scopes. Literal Core paths separately expose both hidden scrutinee environments. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedWordMatchScopes
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WordMatchScopes",by decide⟩],by decide⟩⟩,103⟩
private def word (n : Nat) := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def innerTail : Core.Expr := .ifE (.binary .wordEq (.var 0) (.word (word 41))) (call 6 3) (.var 3)
private def inner : Core.Expr := .letE (call 4 2) innerTail
private def outerTail : Core.Expr := .ifE (.binary .wordEq (.var 0) (.word (word 0))) inner (call 4 2)
private def outer : Core.Expr := .letE (call 5 1) outerTail
private def tailCore : Core.Expr := .letE (call 2 0) outer
private def core : Core.Expr := .letE (.var 0) tailCore
private def pending : List Core.Frame := [.pairApply (.bool true)]
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,r:R,x:X) returns(X){let z=x;r(z);match(f(z)){case 0{match(r(z)){case 41{return w(z);}default{return z;}}}default{return r(z);}}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"word-match-scopes.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span && source.span.contains source.value.body.span) "complete original source ranges"
  return source
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["R"],.function .word .word),(["X"],.word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "annotation")
  | _ => throw (IO.userError "annotation shape")
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
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter arity")
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
    | .word v => return ⟨.word v,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual primitive")
    | .ifE c a b =>
        let g ← path n c env s
        match gv : g.value with
        | .bool true => let r ← path n a env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual guard")
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
private structure Static (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Σ t, Static (fun c => RecursiveLocalComputationElaborates i.names i.context e c t)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨t,.var n,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      check (e.span.contains f.span && e.span.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original callee/argument ranges"
      let l ← child i f; let r ← child i a
      match ft : l.1 with
      | .function t u => if same : r.1=t then return ⟨u,.apply l.2.core r.2.core,by rw [shape]; exact .application (by simpa only [ft] using l.2.evidence) (by simpa only [same] using r.2.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static child shape")
termination_by sizeOf e
private def pattern (p : Syntax.Pattern) : IO (Σ v, PLift (WordMatchPatternDenotes p v)) := do
  match shape : p.value with
  | .literal literal => match decoded : interpretWordLiteral? literal with
    | some v => return ⟨v,⟨⟨literal,shape,interpretWordLiteral?_sound decoded⟩⟩⟩
    | none => throw (IO.userError "strict Word literal")
  | _ => throw (IO.userError "literal pattern")
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.1=.word then return ⟨r.2.core,by rw [shape]; exact .expression (same ▸ r.2.evidence)⟩ else throw (IO.userError "return type")
  | ⟨span,⟨_,.letDecl name none (some e)⟩::rest⟩ =>
      let a ← child i e
      if unused : name.value ∉ i.names.map Prod.fst then
        let r ← body (i.bindFresh owner name.value a.1) ⟨span,rest⟩
        return ⟨.letE a.2.core r.core,by rw [shape]; exact .inferred unused a.2.evidence r.evidence⟩
      else throw (IO.userError "source binding freshness")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← child i e; let r ← body i ⟨span,rest⟩; return ⟨.letE a.2.core (r.core.weakenAt 0),by rw [shape]; exact .discard a.2.evidence r.evidence⟩
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨[arm],some d⟩⟩⟩]⟩ =>
      check (matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && armsSpan.contains arm.span && armsSpan.contains d.span && arm.span.contains arm.value.pattern.span && arm.span.contains arm.value.body.span && decide (e.span.endByte≤arm.span.startByte ∧ arm.span.endByte≤d.span.startByte)) "nested original scrutinee/case/default order"
      have smaller : sizeOf arm.value.body < sizeOf arm := by rcases arm with ⟨_,⟨_,_⟩⟩; simp; omega
      let sc ← child i e; let p ← pattern arm.value.pattern; let a ← body i arm.value.body; let dc ← body i d
      if same : sc.1=.word then return ⟨.letE sc.2.core (.ifE (.binary .wordEq (.var 0) (.word p.1)) (a.core.weakenAt 0) (dc.core.weakenAt 0)),by
        rw [shape]; exact .wordMatch (defaultEntry := some (d,dc.core)) (entries := [(arm,some p.1,a.core)]) (same ▸ sc.2.evidence) rfl
          (by intro entry h; cases List.mem_singleton.mp h; exact p.2.down)
          (by intro entry h; cases List.mem_singleton.mp h; exact a.evidence) rfl (by intro entry h; cases List.mem_singleton.mp h; exact dc.evidence) rfl⟩
      else throw (IO.userError "scrutinee type")
  | _ => throw (IO.userError "fixed original body shape")
termination_by sizeOf b
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=core ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("x",⟨owner,3⟩),("r",⟨owner,2⟩),("w",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original bindings and actual reverse once"
          return ⟨⟨ps.actual,core,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "independent literal Core/return annotation")
  | _ => throw (IO.userError "original return clause")
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
  | ⟨span,⟨_,.letDecl name none (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .inferred a.evidence r.evidence⟩
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← rawChild table env s e; let r ← rawBody table env a.final ⟨span,rest⟩; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨[arm],some d⟩⟩⟩]⟩ =>
      have smaller : sizeOf arm.value.body < sizeOf arm := by rcases arm with ⟨_,⟨_,_⟩⟩; simp; omega
      let sc ← rawChild table env s e; let p ← pattern arm.value.pattern
      match actual : sc.value with
      | .word v =>
          if same : v=p.1 then let r ← rawBody table env sc.final arm.value.body; return ⟨r.value,r.final,sc.cost+r.cost+2+7,by rw [shape]; exact .wordMatch (cases := [arm]) (defaultBody := some d) sc.evidence (by rw [actual]; exact .hit (same.symm ▸ p.2.down)) r.evidence⟩
          else let r ← rawBody table env sc.final d; return ⟨r.value,r.final,sc.cost+r.cost+2+7,by rw [shape]; exact .wordMatch (cases := [arm]) (defaultBody := some d) sc.evidence (by rw [actual]; exact .miss p.2.down same .fallback) r.evidence⟩
      | _ => throw (IO.userError "raw actual Word")
  | _ => throw (IO.userError "raw fixed body shape")
termination_by sizeOf b
private def allocator : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.newCell (.var rfl) .word) (.loadCell (.var rfl) .word))⟩
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word)⟩
private def writer (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word))⟩
private theorem runtimeArguments {world : Core.StoreTyping} (args : List TypedRuntimeArgument)
    (typed : ∀ arg ∈ args, Core.RuntimeValueHasType world arg.value arg.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons a rest ih => exact .cons (typed a (by simp)) (ih (fun v member => typed v (by simp [member])))
private def verify (source : Syntax.FunctionDecl) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let rawValues := [allocator.value,(writer 2).value,(reader 1).value,w 14]
  let manual ← path 80 core rawValues.reverse s
  check (decide (manual.cost=cost ∧ manual.value=value ∧ manual.final=final)) "independent literal indices/effects/cost"
  let args ← rawValues.mapM fun value => do
    match built : buildRuntimeArgument? value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=value ∧ a.type=value.type)) "original actual structural fields"; return a
    | none => throw (IO.userError "structural construction")
  let p ← prepare source args; let i := p.1.inputs; let env := i.environment.values
  if actualEnv : env=rawValues.reverse then
    have literal (k) : Core.Steps manual.cost ⟨.eval core env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩ := by rw [actualEnv]; exact manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body core .word := by simpa only [p.2.down.2.1,p.2.down.2.2] using p.2.down.1.body
    let raw ← rawBody i.names i.environment s source.value.body
    have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
    have allK (k) : Core.Steps raw.cost ⟨.eval core env,k,s⟩ ⟨.ret raw.value,k,raw.final⟩ :=
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
        (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) original ids k
    have correspondence := (allK []).final_unique (literal [])
    check (decide (raw.cost=cost ∧ raw.value=value ∧ raw.final=final)) "independent original cost agrees with literal path"
    have _ := correspondence; have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original
    have _ := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
    if validated : validateRuntimeInputs [.word,.word,.word] args s=true then
      have runtime := validateRuntimeInputs_iff.mp validated
      have reversed := runtimeArguments args.reverse (fun a member => runtime.1 a (List.mem_reverse.mp member))
      have actual : Core.RuntimeEnvironmentHasTypes [.word,.word,.word] env i.toTypeInputs.context.values := by
        dsimp only [env,i]
        simpa only [LocalInputs.environment,LocalInputs.context,LocalInputs.toTypeInputs_context,Resolved.LocalScope.values,List.map_map,Function.comp_def,p.2.down.1.parameters.argument_values,p.2.down.1.parameters.argument_types] using reversed
      have typedK : Core.ContinuationHasType [.word,.word,.word] pending .word (.product .bool .word) := .cons (.pairApply .bool) .nil
      have safe := original.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK
      let start : Core.State := ⟨.eval core env,pending,s⟩
      let result := Core.Value.pair (.bool true) value
      have whole : Core.Steps (manual.cost+1) start ⟨.ret (.pair (.bool true) manual.value),[],manual.final⟩ := (literal pending).trans (.cons .applyPair .refl)
      for fuel in List.range (cost+2) do
        check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "same prepared full entry outcome"
        match stopped : Core.runStateful fuel start with
        | .done v t => check (decide (cost+1≤fuel ∧ v=result ∧ t=final)) "body cost excludes retained typed frame"
        | .fault _ _ => throw (IO.userError "typed source continuation fault")
        | .outOfFuel cp =>
            have _ := safe.2.2 stopped
            have saved := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK stopped
            have retained : ∃ savedWorld future, Core.WorldExtends [.word,.word,.word] savedWorld ∧ Core.StoreHasTypes savedWorld cp.store ∧ Core.WorldExtends savedWorld future ∧ Core.StoreHasTypes future manual.final ∧ future[2]?=some .word := by
              obtain ⟨savedWorld,extension,stored,resumed⟩ := saved
              obtain ⟨future,growth,finalTyped⟩ := resumed (whole.residual_of_outOfFuel stopped).2
              exact ⟨savedWorld,future,extension,stored,growth,finalTyped,(extension.trans growth).lookup rfl⟩
            have _ := retained
            for extra in [0,1,7,cost+1] do
              have _ := Core.runStateful_resume stopped extra; have _ := whole.resumed_done_iff (additional := extra) stopped
              check (decide (Core.runStateful extra cp=Core.runStateful (fuel+extra) start ∧ Core.runStateful (cost+1-fuel) cp=.done result final)) "all genuine checkpoints and exact full resume"
      if s=[w 0,w 41,w 99] then
        let allocated := s++[w 14]
        let checkpoints : List (Nat × Core.State) := [(2,⟨.ret (w 14),.letBody tailCore env::pending,s⟩),(12,⟨.ret (w 41),.letBody outer (w 14::env)::pending,s⟩),(27,⟨.ret (w 0),.letBody outerTail (w 41::w 14::env)::pending,allocated⟩),(44,⟨.ret (w 41),.letBody innerTail (w 0::w 41::w 14::env)::pending,allocated⟩),(51,⟨.ret (.bool true),.ifBranches (call 6 3) (.var 3) (w 41::w 0::w 41::w 14::env)::pending,allocated⟩),(67,⟨.ret (w 14),pending,final⟩)]
        for (spent,cp) in checkpoints do
          if genuine : Core.runStateful spent start=.outOfFuel cp then
            have _ := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK genuine
            have _ := safe.2.2 genuine
            check (decide (Core.runStateful (68-spent) cp=.done result final)) "saved named/discarded/two hidden slots and literal original environments"
          else throw (IO.userError "literal checkpoint fields")
      check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old252 unchanged"
    else throw (IO.userError "same-world actual input validation")
  else throw (IO.userError "actual reverse-once environment")
end ParsedWordMatchScopes
open ParsedWordMatchScopes
def frontendParsedWordMatchScopeTests : IO Unit := do
  let source ← parsed
  verify source [w 0,w 41,w 99] [w 0,w 41,w 14,w 14] (w 14) 67
  verify source [w 0,w 42,w 99] [w 0,w 42,w 99,w 14] (w 14) 53
  verify source [w 7,w 41,w 99] [w 7,w 41,w 99,w 14] (w 41) 43
end Tests

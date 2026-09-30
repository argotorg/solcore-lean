import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RuntimeComputationFunction
import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Frontend.RuntimeInputValidation
import Solcore.Core.FuelResumptionProperties
/-! Ordered wildcard selection preserves original source and actual effects.
Independent literal Core paths distinguish direct selection from prior guards. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedWildcardMatchEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WordMatchEffects",by decide⟩],by decide⟩⟩,97⟩
private def word (n : Nat) := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def tailCore (mode : Nat) : Core.Expr := if mode<2 then call 2 1 else
  .ifE (.binary .wordEq (.var 0) (.word (word 0))) (call 2 1)
    (if mode=2 then call 3 1 else .ifE (.binary .wordEq (.var 0) (.word (word 1))) (call 2 1) (call 3 1))
private def core (mode : Nat) : Core.Expr := .letE (call 3 0) (tailCore mode)
private def sourceBody (mode : Nat) := match mode with
  | 0 => "match(f(x)){case _{return r(x);}default{return r(x);}}"
  | 1 => "match(f(x)){case _{return r(x);}case 0{return w(x);}case _{return w(x);}default{return r(x);}}"
  | 2 => "match(f(x)){case 0{return r(x);}case _{return w(x);}case 0{return r(x);}default{return r(x);}}"
  | _ => "match(f(x)){case 0{return r(x);}case 1{return r(x);}case _{return w(x);}case _{return r(x);}default{return r(x);}}"
private def parsed (body : String) : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,r:R,x:X) returns(X){"++body++"}"
  let file : Syntax.SourceFile := ⟨⟨.main,"word-match-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span && source.span.contains source.value.body.span) "original whole source ranges"
  return source
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["R"],.function .word .word),(["X"],.word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "annotation")
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
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
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
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
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
private def returned (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.1=.word then return ⟨r.2.core,by rw [shape]; exact .expression (same ▸ r.2.evidence)⟩ else throw (IO.userError "return type")
  | _ => throw (IO.userError "return body")
private def pattern (p : Syntax.Pattern) : IO (Σ tag : Option Core.Word, PLift (WordMatchPatternClassifies p tag)) := do
  match shape : p.value with
  | .wildcard marker => return ⟨none,⟨.wildcard (marker := marker) shape⟩⟩
  | .literal literal => match decoded : interpretWordLiteral? literal with | some v => return ⟨some v,⟨.literal ⟨literal,shape,interpretWordLiteral?_sound decoded⟩⟩⟩ | none => throw (IO.userError "strict Word literal")
  | _ => throw (IO.userError "literal or exact wildcard pattern")
private def arms (i : LocalTypeInputs) (cs : List Syntax.MatchCase) : IO (Σ entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)), PLift (entries.map Prod.fst=cs ∧ ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1 ∧ RecursiveComputationReturnTreeElaborates types owner i entry.1.value.body entry.2.2 .word)) := do
  match shape : cs with
  | [] => return ⟨[],⟨by rw [shape]; exact ⟨rfl,by simp⟩⟩⟩
  | c::rest =>
      check (c.span.contains c.value.pattern.span && c.span.contains c.value.body.span && decide (c.value.pattern.span.endByte≤c.value.body.span.startByte)) "original pattern/body order"
      let p ← pattern c.value.pattern; let b ← returned i c.value.body; let tail ← arms i rest
      return ⟨(c,p.1,b.core)::tail.1,⟨by rw [shape]; refine ⟨by simp [tail.2.down.1],?_⟩; intro entry member; rcases List.mem_cons.mp member with rfl|member; exact ⟨p.2.down,b.evidence⟩; exact tail.2.down.2 entry member⟩⟩
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨cs,some d⟩⟩⟩]⟩ =>
      check (b.span.contains matchSpan && matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && armsSpan.contains d.span && cs.all (fun c => armsSpan.contains c.span) && decide (scrutineeSpan.endByte≤armsSpan.startByte)) "original match scrutinee/arms/default spans"
      let sc ← child i e; let bs ← arms i cs; let dc ← returned i d
      if same : sc.1=.word then return ⟨.letE sc.2.core (bs.1.foldr (fun en t => match en.2.1 with | none => en.2.2.weakenAt 0 | some v => .ifE (.binary .wordEq (.var 0) (.word v)) (en.2.2.weakenAt 0) t) (dc.core.weakenAt 0)),by rw [shape]; exact .wordMatch (defaultEntry := some (d,dc.core)) (same ▸ sc.2.evidence) bs.2.down.1 (fun e h => (bs.2.down.2 e h).1) (.inl rfl) (fun e h => (bs.2.down.2 e h).2) rfl (by intro e h; cases List.mem_singleton.mp h; exact dc.evidence) (by simp only [Option.map_some]; induction bs.1 with | nil => rfl | cons e es ih => cases tag : e.2.1 <;> simp only [List.foldr_cons,tag,ih,Option.map_some])⟩
      else throw (IO.userError "scrutinee type")
  | _ => throw (IO.userError "original terminal match")
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (fixed : Core.Expr) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=fixed ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=fixed then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,fixed,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2] using b.evidence⟩
          have compiled := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          have prep : RecursiveComputationFunctionPrepares types owner source args ⟨ps.actual,fixed,.word⟩ := ⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩
          have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr prep
          have matching : args.map (·.type)=ps.statics.context.values.reverse := by
            have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
            simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
          have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some ⟨ps.statics,fixed,.word⟩ := by
            rw [prepareComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
          have whole (fuel) (s) : runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial fixed (args.reverse.map (·.value)) s)) := by
            rw [runRecursiveComputationFunction?,runComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
          have _ := accepted; have _ := whole
          check (decide (ps.actual.environment.values=args.reverse.map (·.value))) "original actual reverse once"
          return ⟨⟨ps.actual,fixed,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "literal Core/return annotation")
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
private def choose (v : Core.Value) (cs : List Syntax.MatchCase) (d : Syntax.Block) : IO (Σ selected : Syntax.Block × Nat, PLift (WordMatchChooses v cs (some d) selected.1 selected.2)) := do
  match shape : cs with
  | [] => return ⟨(d,0),⟨by rw [shape]; exact .fallback⟩⟩
  | c::rest =>
      let p ← pattern c.value.pattern
      match tag : p.1 with
      | none => return ⟨(c.value.body,0),⟨by rw [shape]; exact .wildcard (by simpa only [tag] using p.2.down)⟩⟩
      | some literal => match actual : v with
        | .word w =>
            have meaning : WordMatchPatternClassifies c.value.pattern (some literal) := by simpa only [tag] using p.2.down
            if same : w=literal then return ⟨(c.value.body,1),⟨by rw [shape,actual]; exact .hit (same.symm ▸ meaning)⟩⟩
            else let tail ← choose (.word w) rest d; return ⟨(tail.1.1,tail.1.2+1),⟨by rw [shape,actual]; exact .miss meaning same tail.2.down⟩⟩
        | _ => throw (IO.userError "actual non-Word comparison before wildcard")
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨cs,some d⟩⟩⟩]⟩ =>
      let sc ← rawChild table env s e; let c ← choose sc.value cs d
      match selected : c.1.1 with
      | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ => let r ← rawChild table env sc.final child; return ⟨r.value,r.final,sc.cost+r.cost+2+7*c.1.2,by rw [shape]; exact .wordMatch sc.evidence c.2.down (by rw [selected]; exact .expression r.evidence)⟩
      | _ => throw (IO.userError "selected return")
  | _ => throw (IO.userError "raw body")
private def allocator : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.newCell (.var rfl)) (.loadCell (.var rfl)))⟩
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def arguments (location : Nat := 2) : List TypedRuntimeArgument := [allocator,writer location,reader 1,⟨.word,w 14,.word⟩]
private def positive (mode : Nat) (s final : Core.Store) (value : Core.Value) (cost : Nat) (location : Nat := 2) : IO Unit := do
  let source ← parsed (sourceBody mode)
  let args ← (arguments location).mapM fun original => do
    match built : buildRuntimeArgument? original.value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=original.value ∧ a.type=original.type)) "raw construction preserves complete captures"; return a
    | none => throw (IO.userError "structural actual arguments")
  let p ← prepare source args (core mode)
  let i := p.1.inputs; let env := i.environment.values
  let raw ← rawBody i.names i.environment s source.value.body; let manual ← path 80 (core mode) env s
  check (decide (raw.value=value ∧ raw.final=final ∧ raw.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent original source and literal Core expectations"
  have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
  have _ := p.2.down.1.body.core_hasType RecursiveLocalComputationElaborates.core_hasType
  have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,p.2.down.1.body⟩
  have allK := fun k => ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) p.2.down.1.body ids k
  have _ := allK
  let world := List.replicate s.length Core.Ty.word
  check (validateRuntimeInputs world args s == (s.all (fun v => v.type==.word) && location != 700)) "same-world validation also inspects unused captured references"
  if validated : validateRuntimeInputs world args s=true then
    have runtime := validateRuntimeInputs_iff.mp validated
    have finitePath : Core.Steps manual.cost
        (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by
      rw [p.2.down.2.1]
      exact manual.evidence []
    have safe := ComputationFunctionPrepares.runtime_typed_execution (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
      RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation elaborateRecursiveLocalComputation?_iff p.2.down.1 runtime.1 runtime.2 ⟨manual.value, manual.final, Core.steps_from_initial_sound finitePath⟩
    have actualWorld : ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body manual.value manual.final manual.cost := by
      obtain ⟨future,t,v,n,ext,st,_,r,paths,_,_⟩ := safe.2
      have fixedPath : Core.Steps manual.cost (.initial p.1.core env s) (.final manual.value manual.final) := by rw [p.2.down.2.1]; exact manual.evidence []
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique fixedPath
      exact ⟨future,ext,st,r⟩
    have _ := actualWorld
  else check (!s.all (fun v => v.type==.word) || location==700) "opt-in rejection does not replace raw selected/default success"
  check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old252 remains None"
  for fuel in List.range (cost+2) do
    have _ := runComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args fuel s
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial (core mode) env s)) ∧ runRuntimeComputationFunction? types owner source args fuel s=none)) "full entry outcome and original tag"
    match stopped : Core.runStateful fuel (.initial (core mode) env s) with
    | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact threshold"
    | .outOfFuel cp =>
        have _ := (manual.evidence []).residual_of_outOfFuel stopped
        for more in [0,1,7,cost] do
          have _ := Core.runStateful_resume stopped more
          check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial (core mode) env s) ∧ Core.runStateful (cost-fuel) cp=.done value final)) "every genuine checkpoint and full resume"
    | .fault _ _ => throw (IO.userError "successful manual path faulted")
  let scr ← path 40 (call 3 0) env s
  let cp : Core.State := ⟨.ret scr.value,[.letBody (tailCore mode) env],scr.final⟩
  check (decide (scr.cost=13 ∧ Core.runStateful 14 (.initial (core mode) env s)=.outOfFuel cp ∧ Core.runStateful (cost-14) cp=.done value final)) "one allocation and actual hidden-let saved environment"
  if mode=2 then
    let cp : Core.State := ⟨.ret (.bool (scr.value==w 0)),[.ifBranches (call 2 1) (call 3 1) (scr.value::env)],scr.final⟩
    check (decide (Core.runStateful 21 (.initial (core mode) env s)=.outOfFuel cp ∧ Core.runStateful (cost-21) cp=.done value final)) "genuine ifBranches with actual saved scrutinee"
  check (decide (Core.runStateful cost ⟨.eval (core mode) env,[.pairApply (.bool true)],s⟩=.outOfFuel ⟨.ret value,[.pairApply (.bool true)],final⟩ ∧ Core.runStateful (cost+1) ⟨.eval (core mode) env,[.pairApply (.bool true)],s⟩=.done (.pair (.bool true) value) final)) "literal retained continuation outside source cost"
end ParsedWildcardMatchEffects
open ParsedWildcardMatchEffects
def frontendParsedWildcardMatchEffectTests : IO Unit := do
  positive 0 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 23
  positive 1 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 23
  positive 1 [.bool false,w 41,w 99] [.bool false,w 41,w 99,w 14] (w 41) 23
  positive 1 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 23 700
  positive 2 [w 7,w 41,w 99] [w 7,w 41,w 14,w 14] (w 14) 37
  positive 2 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 30
  positive 3 [w 7,w 41,w 99] [w 7,w 41,w 14,w 14] (w 14) 44
  let source ← parsed (sourceBody 2); let args := arguments; let p ← prepare source args (core 2); let env := p.1.inputs.environment.values
  let s := [.bool false,w 41,w 99]; let t := s++[w 14]
  let frames := [.binaryApply .wordEq (.bool false),.ifBranches (call 2 1) (call 3 1) (.bool false::env)]
  let fault : Core.StatefulRunResult := .fault (.invalidBinaryOperands .wordEq (.bool false) (w 0)) ⟨.ret (w 0),frames,t⟩
  let before : Core.State := ⟨.eval (.word (word 0)) (.bool false::env),frames,t⟩
  check (decide (Core.runStateful 19 (.initial (core 2) env s)=.outOfFuel before ∧ Core.runStateful 1 before=fault)) "literal before wildcard faults with allocation retained"
  for fuel in List.range 23 do
    let out := Core.runStateful fuel (.initial (core 2) env s)
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,out))) "same prepared prefix on corrupt actual store"
    if fuel<20 then match out with
      | .outOfFuel cp => check (decide (Core.runStateful 100 cp=fault)) "all genuine pre-fault resumes"
      | _ => throw (IO.userError "first literal fault threshold")
    else check (decide (out=fault)) "wildcard does not turn invalid literal operands into a miss"
  for text in ["match(f(x)){case _{return r(x);}case 0{return Missing;}default{return r(x);}}","match(f(x)){case _{return r(x);}default{return ();}}","match(f(x)){case _{return r(x);}case y{return w(x);}default{return r(x);}}"] do
    let unselected ← parsed text; let ps ← parameters .empty .empty unselected.value.signature.parameters.elements args
    let raw ← rawBody ps.actual.names ps.actual.environment [w 0,w 41,w 99] unselected.value.body
    check (decide (raw.value=w 41 ∧ raw.final=[w 0,w 41,w 99,w 14] ∧ raw.cost=23 ∧ compileRecursiveComputationFunction? types owner unselected=none)) "original raw wildcard skips tail but all static obligations remain"
end Tests

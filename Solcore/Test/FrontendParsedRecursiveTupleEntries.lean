import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RuntimeComputationFunction
import Solcore.Core.FuelResumptionProperties
/-! Independent original declaration certificates and manual paths retain actual captures, stores and whole results. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveTupleEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveTupleEntries",by decide⟩],by decide⟩⟩,67⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-tuple-entries.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original function did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) ("complete original bytes: "++text)
  check (source.span.contains source.value.signature.span && source.value.signature.span.contains source.value.signature.parameters.span && decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original header and parameter ranges"
  return source
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Σ type, PLift (StructuralTypeDenotes types source type)) := do
  match atSource : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation missing")
  | ⟨_,.tuple []⟩ => return ⟨.unit,⟨by rw [atSource]; exact .unit⟩⟩
  | ⟨_,.tuple [inner]⟩ => let a ← meaning types inner; return ⟨a.1,⟨by rw [atSource]; exact .single a.2.down⟩⟩
  | ⟨_,.tuple [left,right]⟩ =>
      let a ← meaning types left; let b ← meaning types right
      return ⟨.product a.1 b.1,⟨by rw [atSource]; exact .pair a.2.down b.2.down⟩⟩
  | ⟨span,.tuple (first::second::third::rest)⟩ =>
      let a ← meaning types first; let b ← meaning types ⟨span,.tuple (second::third::rest)⟩
      return ⟨.product a.1 b.1,⟨by rw [atSource]; exact .many a.2.down b.2.down⟩⟩
  | _ => throw (IO.userError "outside structural annotation fixture")
termination_by sizeOf source
private structure Parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters types s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span && decide (name.span.endByte≤annotation.span.startByte)) "original parameter fields/order"
      let m ← meaning types annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters types (s.bindFresh owner name.value arg.type)
            (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,
            by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate original parameter")
      else throw (IO.userError "original argument type mismatch")
  | _,_ => throw (IO.userError "original parameter arity")
private structure Path (core : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual script depth")
  | n+1,e,env,s => do
    match original : e with
    | .unit => return ⟨.unit,s,1,fun _ => by rw [original]; exact .cons .unit .refl⟩
    | .pair left right =>
        let a ← path n left env s; let b ← path n right env a.final
        return ⟨.pair a.value b.value,b.final,a.cost+b.cost+3,fun k => by
          rw [original]
          have p := Core.Steps.cons .enterPair ((a.evidence (.pairRight right env::k)).trans
            (.cons .enterPairRight ((b.evidence (.pairApply a.value::k)).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using p⟩
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [original]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual var missing")
    | .letE head tail =>
        let a ← path n head env s; let b ← path n tail (a.value::env) a.final
        return ⟨b.value,b.final,a.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.letE (a.evidence _) (b.evidence _)⟩
    | .apply fn arg =>
        let f ← path n fn env s; let a ← path n arg env f.final
        match fv : f.value with
        | .closure _ _ body captured =>
            let b ← path n body (a.value::captured) a.final
            return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,fun _ => by rw [original]; exact CostStepComposition.apply (fv ▸ f.evidence _) (a.evidence _) (b.evidence [])⟩
        | _ => throw (IO.userError "manual callee shape")
    | .loadCell (.var i) =>
        match found : env[i]? with
        | some (.cellRef t l) =>
            match read : s.read? l with
            | some v => return ⟨v,s,3,fun _ => by rw [original]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
            | none => throw (IO.userError "manual load missing")
        | _ => throw (IO.userError "manual reference shape")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [original]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write missing")
        | _,_ => throw (IO.userError "manual write shape")
    | _ => throw (IO.userError "outside explicit Core script")
private structure Certificate (Elaborates : Core.Expr → Core.Ty → Prop) (Evaluates : Core.Value → Core.Store → Nat → Prop) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : Elaborates core type
  raw : Evaluates value final cost
private abbrev Child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) :=
  Certificate (RecursiveLocalComputationElaborates s.names s.context source) (RecursiveLocalComputationEvaluatesWithCost s.names env store source)
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (source.span.contains fn.span && source.span.contains argsSpan && argsSpan.contains arg.span &&
        decide (fn.span.endByte ≤ argsSpan.startByte)) "original recursive child order"
      let f ← child s env store fn; let a ← child s env f.final arg
      match ft : f.type, fv : f.value with
      | .function input output,.closure _ _ body captured =>
          if same : a.type=input then
            let b ← path 100 body (a.value::captured) a.final
            return ⟨.apply f.core a.core,output,b.value,b.final,f.cost+a.cost+b.cost+3,
              by rw [original]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
              by rw [original]; exact .application (fv ▸ f.raw) a.raw (b.evidence [])⟩
          else throw (IO.userError "static argument differs")
      | _,_ => throw (IO.userError "static or actual Function differs")
  | ⟨_,.group inner⟩ =>
      let a ← child s env store inner
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .group a.elaboration,by rw [original]; exact .group a.raw⟩
  | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨.unit,.unit,.unit,store,1,by rw [original]; exact .pure .unit .unit .unit,by rw [original]; exact .pure .unit⟩
  | ⟨span,.tuple ⟨tupleSpan,[left,right]⟩⟩ =>
      check (decide (span=tupleSpan ∧ left.span.endByte<right.span.startByte) && tupleSpan.contains left.span && tupleSpan.contains right.span) "original binary tuple spans/order"
      let a ← child s env store left; let b ← child s env a.final right
      return ⟨.pair a.core b.core,.product a.type b.type,.pair a.value b.value,b.final,a.cost+b.cost+3,
        by rw [original]; exact .pair a.elaboration b.elaboration,by rw [original]; exact .pair a.raw b.raw⟩
  | ⟨span,.tuple ⟨tupleSpan,first::second::third::rest⟩⟩ =>
      check (decide (span=tupleSpan ∧ first.span.endByte<second.span.startByte) && tupleSpan.contains first.span) "original flat tuple head/range"
      let a ← child s env store first; let b ← child s env a.final ⟨span,.tuple ⟨tupleSpan,second::third::rest⟩⟩
      return ⟨.pair a.core b.core,.product a.type b.type,.pair a.value b.value,b.final,a.cost+b.cost+3,
        by rw [original]; exact .many a.elaboration b.elaboration,by rw [original]; exact .many a.raw b.raw⟩
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id, actual : env.lookup? id with
          | some t,some i,some v => return ⟨.var i,t,v,store,1,
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed)),
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | _,_,_ => throw (IO.userError "original row missing")
      | none => throw (IO.userError "original actual name missing")
  | _ => throw (IO.userError "outside fixture expression")
termination_by sizeOf source
private abbrev Tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) :=
  Certificate (RecursiveComputationReturnTreeElaborates types owner s source) (RecursiveComputationReturnTreeEvaluatesWithCost owner s.names env store source)
private def tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) : IO (Tree types s env store source) := do
  check (source.value.all fun statement => source.span.contains statement.span) "original statement spans"
  match original : source with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
      let a ← child s env store e
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .expression a.elaboration,by rw [original]; exact .expression a.raw⟩
  | _ => throw (IO.userError "outside original singleton return body")
private def header (types : TypeNameTable) (source : Syntax.FunctionDecl) (output : Core.Ty) : IO (PLift (RuntimeFunctionHeader types source.value.signature output)) := do
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.1=output then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧
            source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          return ⟨⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same ▸ m.2.down)⟩⟩
        else throw (IO.userError "original header policy")
      else throw (IO.userError "original return meaning")
  | _ => throw (IO.userError "original singleton return clause")
private def bodySource (body returns : String) : IO Syntax.FunctionDecl := parsed ("function tuple(f:F,g:G,x:X,y:Y) returns("++returns++"){return "++body++";}")
private def verify (source : Syntax.FunctionDecl) (f g x y : TypedRuntimeArgument) (output : Core.Ty) (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO PreparedRuntimeFunction := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["Y"],y.type),(["R"],output),(["Word"],.word),(["Cell"],.cell .word),(["Fn"],.function .word .word)]
  let args := [f,g,x,y]; let ps ← parameters types .empty .empty source.value.signature.parameters.elements args
  let inputs := ps.actual; let env := inputs.environment.values
  let h ← header types source output; let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body; let manual ← path 100 core env s
  have erased : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  check (decide (env=[y.value,x.value,g.value,f.value] ∧ inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("y",⟨owner,3⟩,y.type,y.value),("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original actual rows/reverse once"
  check (decide (b.value=value ∧ b.final=final ∧ b.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent raw/Core value/store/cost"
  if fixed : b.core=core ∧ b.type=output then
    let compiled : CompiledRuntimeFunction := ⟨ps.statics,core,output⟩; let prepared : PreparedRuntimeFunction := ⟨inputs,core,output⟩
    have preparation : RecursiveComputationFunctionPrepares types owner source args prepared := ⟨h.down,ps.bound,by simpa only [fixed.1,fixed.2] using b.elaboration⟩
    have compilation : RecursiveComputationFunctionCompiles types owner source compiled := ⟨h.down,ps.declared,by simpa only [compiled,prepared,erased] using preparation.body⟩
    have compiledSome := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
    have preparedSome := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr preparation
    have matching : args.map (·.type)=ps.statics.context.values.reverse := by
      have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
      simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
    have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some compiled := by
      rw [prepareComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte]
    have whole (fuel) (store) : runRecursiveComputationFunction? types owner source args fuel store = some (output,Core.runStateful fuel (.initial core [y.value,x.value,g.value,f.value] store)) := by
      rw [runRecursiveComputationFunction?,runComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte,args,List.reverse_cons,List.reverse_nil]; rfl
    have ids : inputs.environment.ids=inputs.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
    have _ := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation b.raw b.elaboration ids []
    check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old entry remains None"
    for fuel in List.range (cost+2) do
      have _ := whole fuel s
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial core env s)) ∧ runRuntimeComputationFunction? types owner source args fuel s=none)) "whole full result/tag"
      match exhausted : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact completion"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel exhausted; have _ := Core.runStateful_resume exhausted 2
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧ runRecursiveComputationFunction? types owner source args (fuel+2) s=some (output,Core.runStateful 2 cp))) "genuine saved state/residual/full resume"
      | .fault _ _ => throw (IO.userError "independent successful path faulted")
    return prepared
  else throw (IO.userError "independent exact Core/type")
private def reader (location : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word location],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (location : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word location],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def arg (value : Nat) : TypedRuntimeArgument := ⟨.word,w value,.word⟩
private def captured (a : TypedRuntimeArgument) : TypedRuntimeArgument :=
  ⟨.function .word a.type,.closure .word a.type (.var 1) [a.value],.closure (.cons a.valueTyped .nil) (.var rfl)⟩
end RecursiveTupleEntries
open RecursiveTupleEntries
def frontendParsedRecursiveTupleEntryTests : IO Unit := do
  let left := Core.Expr.apply (.var 3) (.var 1); let right := Core.Expr.apply (.var 2) (.var 0)
  let third := Core.Expr.apply (.var 3) (.var 0); let fourth := Core.Expr.apply (.var 2) (.var 1)
  let f := reader 0; let g := writer 0; let x := arg 11; let y := arg 14
  let pairType := Core.Ty.product .word .word; let pairCore := Core.Expr.pair left right
  let payloadClosure := Core.Value.closure .bool .unit (.var 99) [.cellRef .word 77]
  for (body,annotation,arity,core,type,value,cost) in [
      ("(f(x),g(y))","(Word,Word)",2,pairCore,pairType,Core.Value.pair (w 23) (w 14),26),
      ("(f(x),g(y),f(y))","(Word,Word,Word)",3,.pair left (.pair right third),.product .word pairType,.pair (w 23) (.pair (w 14) (w 14)),37),
      ("((f(x),),g(y),f(y),)","(Word,Word,Word)",3,.pair left (.pair right third),.product .word pairType,.pair (w 23) (.pair (w 14) (w 14)),37),
      ("(f(x),g(y),g(x),f(y))","(Word,Word,Word,Word)",4,.pair left (.pair right (.pair fourth third)),.product .word (.product .word pairType),.pair (w 23) (.pair (w 14) (.pair (w 11) (w 11))),55),
      ("(f(x),(g(y),f(y)))","(Word,(Word,Word))",2,.pair left (.pair right third),.product .word pairType,.pair (w 23) (.pair (w 14) (w 14)),37),
      ("(f(x),g(y),f(y),())","(Word,Word,Word,())",4,.pair left (.pair right (.pair third .unit)),.product .word (.product .word (.product .word .unit)),.pair (w 23) (.pair (w 14) (.pair (w 14) .unit)),41)] do
    let source ← bodySource body annotation; let final := if cost=55 then [w 11] else [w 14]
    check (match source.value.body.value with | [⟨_,.returnStmt (some ⟨_,.tuple ⟨_,elements⟩⟩)⟩] => decide (elements.length=arity) | _ => false) "original flat list versus explicit nested child count"
    let prepared ← verify source f g x y type core [w 23] final value cost
    let env := prepared.inputs.environment.values
    let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],.word),(["Y"],.word),(["Word"],.word)]
    let run := runRecursiveComputationFunction? types owner source [f,g,x,y]
    match core,value with
    | .pair _ tail,.pair _ tailValue =>
        let first : Core.State := ⟨.ret (w 23),[.pairRight tail env],[w 23]⟩
        let startTail : Core.State := ⟨.eval tail env,[.pairApply (w 23)],[w 23]⟩
        let apply : Core.State := ⟨.ret tailValue,[.pairApply (w 23)],final⟩
        check (decide (run 9 [w 23]=some (type,.outOfFuel first) ∧ run 10 [w 23]=some (type,.outOfFuel startTail) ∧ run (cost-1) [w 23]=some (type,.outOfFuel apply) ∧ Core.runStateful 1 apply=.done value final)) "saved original left survives every right update"
        for (spent,cp) in [(9,first),(10,startTail),(cost-1,apply)] do check (decide (Core.runStateful (cost-spent) cp=.done value final)) "fixed pair checkpoints resume exactly"
        match tail with
        | .pair _ rest =>
            let inner : Core.State := ⟨.ret (w 14),[.pairRight rest env,.pairApply (w 23)],[w 14]⟩
            check (decide (run 26 [w 23]=some (type,.outOfFuel inner) ∧ Core.runStateful (cost-26) inner=.done value final)) "flat tail keeps original env and latest store before its remaining calls"
        | _ => pure ()
    | _,_ => throw (IO.userError "literal pair expectation")
    for store in [[],[w 23],[.bool true],[.pair payloadClosure .unit],[payloadClosure],[w 23,.bool false]] do
      for fuel in List.range (cost+2) do
        check (decide (run fuel store=some (type,Core.runStateful fuel (.initial core env store)))) "same prepared arbitrary stores retain product tag and whole result"
        match exhausted : Core.runStateful fuel (.initial core env store) with
        | .outOfFuel cp =>
            have _ := Core.runStateful_resume exhausted 60
            check (decide (run (fuel+60) store=some (type,Core.runStateful 60 cp))) "all genuine checkpoints resume success or child fault"
        | _ => pure ()
  let source ← bodySource "(f(x),g(y))" "(Word,Word)"
  for old in [w 23,.bool true,.pair payloadClosure .unit,payloadClosure,.cellRef .word 71] do
    discard <| verify source f g x y pairType pairCore [old] [w 14] (.pair old (w 14)) 26
    discard <| verify source g (reader 1) x y pairType pairCore [w 23,old] [w 11,old] (.pair (w 11) old) 26
  discard <| verify source g f x y pairType pairCore [w 23] [w 11] (.pair (w 11) (w 11)) 26
  discard <| verify source f g y x pairType pairCore [w 23] [w 11] (.pair (w 23) (w 11)) 26
  discard <| verify source (reader 1) g x y pairType pairCore [w 23,w 7] [w 14,w 7] (.pair (w 7) (w 14)) 26
  let cell : TypedRuntimeArgument := ⟨.cell .word,.cellRef .word 77,.cellRef⟩
  let captures ← bodySource "(f(x),g(y))" "(Cell,Fn)"
  discard <| verify captures (captured cell) (captured f) x y (.product cell.type f.type) pairCore [] [] (.pair cell.value f.value) 15
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],.word),(["Y"],.word),(["Word"],.word)]
  for (a,b,store,firstFault) in [(reader 1,g,[w 23],8),(g,reader 1,[w 23],24)] do
    let env := [y.value,x.value,b.value,a.value]; let run := runRecursiveComputationFunction? types owner source [a,b,x,y]
    let (frames,actual,kept) := if firstFault=8 then ([Core.Frame.loadCellApply,.pairRight right env],x.value,[w 23])
      else ([Core.Frame.loadCellApply,.pairApply (w 11)],y.value,[w 11])
    let cp : Core.State := ⟨.eval (.var 1) [actual,.cellRef .word 1],frames,kept⟩
    let fault := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),frames,kept⟩
    check (decide (run (firstFault-1) store=some (pairType,.outOfFuel cp) ∧ run firstFault store=some (pairType,fault) ∧ Core.runStateful 1 cp=fault)) "left child fault skips writable right; right fault keeps actual left update"
    for fuel in List.range 30 do
      check (decide (run fuel store=some (pairType,Core.runStateful fuel (.initial pairCore env store)))) "fault threshold and full saved state"
      match exhausted : Core.runStateful fuel (.initial pairCore env store) with
      | .outOfFuel residual =>
          have _ := Core.runStateful_resume exhausted 30
          check (decide (fuel<firstFault ∧ run (fuel+30) store=some (pairType,Core.runStateful 30 residual))) "every pre-fault checkpoint resumes"
      | outcome => check (decide (firstFault≤fuel ∧ outcome=fault)) "first child fault threshold remains exact at every later fuel"
  for declaration in ["function tuple(f:F,g:G,x:X,y:Y) returns(Word,Word){return (f(x),g(y));}",
      "function tuple(f:F,g:G,x:X,y:Y) returns(((Word,Word),Word)){return (f(x),g(y),f(y));}",
      "function tuple(f:F,g:G,x:X,y:Y) returns((Word,Word)){return (f(x),missing);}"] do
    let bad ← parsed declaration
    check (decide (compileRecursiveComputationFunction? types owner bad=none ∧ prepareRecursiveComputationFunction? types owner bad [f,g,x,y]=none ∧ runRecursiveComputationFunction? types owner bad [f,g,x,y] 60 [w 23]=none)) "multiple returns, association and unknown names remain rejected"
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-tuple-entries.sol"⟩,"function tuple(f:F,g:G,x,y:Y) returns((Word,Word)){return (f(x),g(y));}"⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "untyped parameter lexer")
  check (match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) with | .ok _ next => !(tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) | .reject _ _ => true | .invariant _ => false) "missing parameter annotation remains a parser rejection"
end Tests

import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RuntimeComputationFunction
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.LocalFunctionApplication

/-!
# Recursive function tests

Recursive computation functions and their entries.
-/

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveComputationFunctionEntries
/-! Independent original declaration certificates and manual paths retain actual captures, stores and whole results. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveFunctionEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveFunctionEntries",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-function-entries.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original function did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "complete original bytes"
  check (source.span.contains source.value.signature.span && source.value.signature.span.contains source.value.signature.parameters.span && decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original header and parameter ranges"
  return source
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) :
    IO (Σ type, PLift (StructuralTypeDenotes types source type)) := do
  match atSource : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside named fixture")
private structure Parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters types s a ps args) := do
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
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [original]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual var missing")
    | .bool b => return ⟨.bool b,s,1,fun _ => by rw [original]; exact .cons .bool .refl⟩
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
    | .ifE condition yes no =>
        let c ← path n condition env s
        match cv : c.value with
        | .bool true =>
            let b ← path n yes env c.final
            return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.ifTrue (cv ▸ c.evidence _) (b.evidence _)⟩
        | .bool false =>
            let b ← path n no env c.final
            return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.ifFalse (cv ▸ c.evidence _) (b.evidence _)⟩
        | _ => throw (IO.userError "manual guard shape")
    | .loadCell (.var i) =>
        match found : env[i]? with
        | some (.cellRef t l) =>
            match read : s.read? l with
            | some v => return ⟨v,s,3,fun _ => by rw [original]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
            | none => throw (IO.userError "manual load missing")
        | _ => throw (IO.userError "manual reference shape")
    | .newCell t (.var i) =>
        match found : env[i]? with
        | some v => return ⟨.cellRef t s.length,s++[v],3,fun _ => by rw [original]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
        | none => throw (IO.userError "manual allocation value")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [original]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write missing")
        | _,_ => throw (IO.userError "manual write shape")
    | _ => throw (IO.userError "outside explicit Core script")
private structure Child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : RecursiveLocalComputationElaborates s.names s.context source core type
  raw : RecursiveLocalComputationEvaluatesWithCost s.names env store source value final cost
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.group inner⟩ =>
      check (source.span.contains inner.span) "original group range"
      let c ← child s env store inner
      return ⟨c.core,c.type,c.value,c.final,c.cost,by rw [original]; exact .group c.elaboration,by rw [original]; exact .group c.raw⟩
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
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id, actual : env.lookup? id with
          | some t,some i,some v => return ⟨.var i,t,v,store,1,
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed)),
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | _,_,_ => throw (IO.userError "original row missing")
      | none => throw (IO.userError "original name missing")
  | _ => throw (IO.userError "outside fixture expression")
termination_by sizeOf source
private structure Tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : RecursiveComputationReturnTreeElaborates types owner s source core type
  raw : RecursiveComputationReturnTreeEvaluatesWithCost owner s.names env store source value final cost
private def tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) : IO (Tree types s env store source) := do
  check (source.value.all fun statement => source.span.contains statement.span) "original statement spans"
  match original : source with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
      let a ← child s env store e
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .expression a.elaboration,by rw [original]; exact .expression a.raw⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ =>
      let b ← tree types s env store ⟨span,statements⟩
      return ⟨b.core,b.type,b.value,b.final,b.cost,by rw [original]; exact .block b.elaboration,by rw [original]; exact .block b.raw⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child s env store e
      if unused : name.value ∉ s.names.map Prod.fst then
        let id := Resolved.freshLocalId owner s.ids
        let b ← tree types (s.bindFresh owner name.value a.type) ((id,a.value)::env) a.final ⟨span,rest⟩
        have raw : RecursiveComputationReturnTreeEvaluatesWithCost owner s.names env store source b.value b.final (a.cost+b.cost+2) := by
          rw [original]; cases annotation <;> first | exact .inferred a.raw (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw) | exact .binding a.raw (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw)
        match annotationAt : annotation with
        | none => return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,by rw [original,annotationAt]; exact .inferred a.elaboration b.elaboration,raw⟩
        | some t =>
            let m ← meaning types t
            if same : m.1=a.type then return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,by rw [original,annotationAt]; exact .binding (same ▸ m.2.down) a.elaboration b.elaboration,raw⟩
            else throw (IO.userError "original binding annotation differs")
      else throw (IO.userError "shadowing is still excluded")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ =>
      let a ← child s env store e; let b ← tree types s env a.final ⟨span,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,b.value,b.final,a.cost+b.cost+2,by rw [original]; exact .discard a.elaboration b.elaboration,by rw [original]; exact .discard a.raw b.raw⟩
  | ⟨_,[⟨_,.ifThen e yes (some no)⟩]⟩ =>
      let protection ← if h : computationBlockPreservesNames (s.names.map Prod.fst) yes=true then pure (PLift.up (computationBlockPreservesNames_iff.mp h)) else throw (IO.userError "original then scope")
      let c ← child s env store e; if ct : c.type=.bool then
        let a ← tree types s env c.final yes; let b ← tree types s env c.final no
        if same : b.type=a.type then
          have el : RecursiveComputationReturnTreeElaborates types owner s source (.ifE c.core a.core b.core) a.type := by rw [original]; exact .conditional (ct ▸ c.elaboration) protection.down a.elaboration (same ▸ b.elaboration)
          match cv : c.value with
          | .bool true => return ⟨.ifE c.core a.core b.core,a.type,a.value,a.final,c.cost+a.cost+2,el,by rw [original]; exact .ifTrue (cv ▸ c.raw) a.raw⟩
          | .bool false => return ⟨.ifE c.core a.core b.core,a.type,b.value,b.final,c.cost+b.cost+2,el,by rw [original]; exact .ifFalse (cv ▸ c.raw) b.raw⟩
          | _ => throw (IO.userError "actual guard differs")
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "static guard differs")
  | _ => throw (IO.userError "outside original mixed body fixture")
termination_by sizeOf source
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
private def bodySource (body : String) : IO Syntax.FunctionDecl := parsed ("function recursive(f:F,g:G,x:X) returns(R){"++body++"}")
private structure Snapshot (source : Syntax.FunctionDecl) where
  types : TypeNameTable
  compiled : CompiledRuntimeFunction
  prepared : PreparedRuntimeFunction
  accepted : compileRecursiveComputationFunction? types owner source = some compiled
private def verify (source : Syntax.FunctionDecl) (f g x : TypedRuntimeArgument) (output : Core.Ty)
    (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) (missing := false) : IO (Snapshot source) := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["R"],output),(["Word"],.word)]
  let args := [f,g,x]
  let ps ← parameters types .empty .empty source.value.signature.parameters.elements args; let inputs := ps.actual
  let h ← header types source output; let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body
  let env := inputs.environment.values; let manual ← path 100 core env s
  have erased : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  check (decide (env=[x.value,g.value,f.value] ∧ inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original actual rows/reverse once"
  check (decide (b.value=value ∧ b.final=final ∧ b.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent raw/Core value/store/cost"
  if fixed : b.core=core ∧ b.type=output then
    let compiled : CompiledRuntimeFunction := ⟨ps.statics,core,output⟩
    let prepared : PreparedRuntimeFunction := ⟨inputs,core,output⟩
    have preparation : RecursiveComputationFunctionPrepares types owner source args prepared :=
      ⟨h.down,ps.bound,by simpa only [fixed.1,fixed.2] using b.elaboration⟩
    have compilation : RecursiveComputationFunctionCompiles types owner source compiled :=
      ⟨h.down,ps.declared,by simpa only [compiled,prepared,erased] using preparation.body⟩
    have compiledSome := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
    have preparedSome := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr preparation
    have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mp compiledSome
    have _ := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mp preparedSome
    have matching : args.map (·.type)=ps.statics.context.values.reverse := by
      have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
      simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
    have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some compiled := by
      rw [prepareComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte]
    have whole (fuel) (store) : runRecursiveComputationFunction? types owner source args fuel store =
        some (output,Core.runStateful fuel (.initial core [x.value,g.value,f.value] store)) := by
      rw [runRecursiveComputationFunction?,runComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte,args,List.reverse_cons,List.reverse_nil]; rfl
    have ids : inputs.environment.ids=inputs.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
    have _ := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation b.raw b.elaboration ids []
    check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old nested whole entry stays None"
    for fuel in List.range (cost+2) do
      have _ := whole fuel s
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial core env s)) ∧
        runRuntimeComputationFunction? types owner source args fuel s=none)) "new full actual result versus old None"
      match exhausted : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact declared tag/value/store completion"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel exhausted
          have _ := Core.runStateful_resume exhausted 2
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧
            runRecursiveComputationFunction? types owner source args (fuel+2) s=some (output,Core.runStateful 2 cp))) "entry genuine checkpoint/residual/full resume"
      | .fault _ _ => throw (IO.userError "independent successful path faulted")
    if missing then
      let cp : Core.State := ⟨.eval (.apply (.var 1) (.var 0)) env,[.applyClosure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.letBody (.var 0) env],[]⟩
      let fault := Core.StatefulRunResult.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply,.letBody (.var 0) env],[]⟩
      check (decide (runRecursiveComputationFunction? types owner source args 4 []=some (.word,.outOfFuel cp) ∧
        runRecursiveComputationFunction? types owner source args 13 []=some (.word,fault) ∧ Core.runStateful 9 cp=fault ∧
        runRecursiveComputationFunction? types owner source args 16 [w 23]=some (.word,.done (w 23) [w 23]))) "same prepared records preserve three store outcomes"
    return ⟨types,compiled,prepared,compiledSome⟩
  else throw (IO.userError "independent exact Core/type")
private def reader : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
end RecursiveFunctionEntries
open RecursiveFunctionEntries
def frontendParsedRecursiveComputationFunctionEntryTests : IO Unit := do
  let x : TypedRuntimeArgument := ⟨.word,w 14,.word⟩
  let identity : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 0) [],.closure .nil (.var rfl)⟩
  let nested (f g x : Nat) : Core.Expr := .apply (.var f) (.apply (.var g) (.var x))
  let source ← bodySource "let r:Word=f(g(x));return r;"; let core := Core.Expr.letE (nested 2 1 0) (.var 0)
  let left ← verify source reader writer x .word core [w 23] [w 14] (w 14) 25
  let right ← verify source writer reader x .word core [w 23] [w 23] (w 23) 25
  if same : left.types=right.types then
    have _ : left.compiled=right.compiled := Option.some.inj (left.accepted.symm.trans (by simpa only [same] using right.accepted))
    check (decide (left.prepared.inputs.environment.values≠right.prepared.inputs.environment.values)) "same compiled record/different actual supplied closures"
  else throw (IO.userError "same original source and type table")
  for old in [3,23] do
    let hiddenBody ← bodySource "f(g(x));{f(g(x));return x;}"; let hidden ← verify hiddenBody reader writer x .word (.letE (nested 2 1 0) (.letE (nested 3 2 1) (.var 2))) [w old] [w 14] (w 14) 49
    check (decide (runRecursiveComputationFunction? hidden.types owner hiddenBody [reader,writer,x] 24 [w old]=
      some (.word,.outOfFuel ⟨.eval (.letE (nested 3 2 1) (.var 2)) (w 14::hidden.prepared.inputs.environment.values),[],[w 14]⟩))) "entry hidden slot/captured reader/updated store"
    let alloc : TypedRuntimeArgument := ⟨.function .word (.cell .word),.closure .word (.cell .word) (.newCell .word (.var 0)) [],.closure .nil (.newCell (.var rfl))⟩
    let load : TypedRuntimeArgument := ⟨.function (.cell .word) .word,.closure (.cell .word) .word (.loadCell (.var 0)) [],.closure .nil (.loadCell (.var rfl))⟩
    discard <| verify (← bodySource "let r=f(g(x));return r;") load alloc x .word core [w old] [w old,w 14] (w 14) 18
    for choice in [false,true] do
      let guard : TypedRuntimeArgument := ⟨.function .word .bool,.closure .word .bool (.letE (.storeCell (.var 1) (.var 0)) (.bool choice)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) .bool)⟩
      discard <| verify (← bodySource "if(f(g(x))){g(x);return x;}else{return x;}") guard identity x .word (.ifE (nested 2 1 0) (.letE (.apply (.var 1) (.var 0)) (.var 1)) (.var 0)) [w old] [w 14] (w 14) (if choice then 29 else 21)
    let maker : TypedRuntimeArgument := ⟨.function .word reader.type,.closure .word reader.type (.var 1) [reader.value],.closure (.cons reader.valueTyped .nil) (.var rfl)⟩
    discard <| verify (← bodySource "let h=f(x);return h(g(x));") maker writer x .word (.letE (.apply (.var 2) (.var 0)) (nested 0 2 1)) [w old] [w 14] (w 14) 30
    discard <| verify (← bodySource "f(g(x));return f;") reader writer x reader.type (.letE (nested 2 1 0) (.var 3)) [w old] [w 14] reader.value 25
  discard <| verify (← bodySource "let r=f(g(x));return r;") reader identity x .word core [w 23] [w 23] (w 23) 16
  discard <| verify (← bodySource "let r=f(g(x));return r;") reader identity x .word core [.bool true] [.bool true] (.bool true) 16 true
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendRecursiveComputationFunctionProperties
/-! Original symbolic declarations, independent actual bindings and handwritten
paths. Operational factorization is tested separately from semantic provenance. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveComputationFunction
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RecursiveEntry", by decide⟩], by decide⟩⟩, 55⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "recursive-entry.sol"⟩, 255, 4⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (a : Core.Ty) : TypeNameTable := [(["Fn"], .function a a), (["Payload"], a)]
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def calls : Nat → Syntax.Expr
  | 0 => ref "x"
  | n + 1 => ⟨span, .call (ref "f") ⟨span, [calls n]⟩⟩
private def callCore : Nat → Core.Expr
  | 0 => .var 1
  | n + 1 => .apply (.var 2) (callCore n)
private def body (n : Nat) : Syntax.Block := ⟨span, [⟨span, .letDecl ⟨span, "r"⟩ none (some (calls n))⟩,
  ⟨span, .expression (ref "r") true⟩, ⟨span, .returnStmt (some (ref "r"))⟩]⟩
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (named type)⟩
private def parameters := [parameter "f" "Fn", parameter "x" "Payload", parameter "y" "Payload"]
private def entry (n : Nat) (original : Syntax.Block := body n) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "nested"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [named "Payload"]⟩⟩, none⟩, original⟩⟩
private def initial (a : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh owner "f" (.function a a)).bindFresh owner "x" a).bindFresh owner "y" a
private def tailCore : Core.Expr := .letE (.var 0) (.var 1)
private def core (n : Nat) : Core.Expr := .letE (callCore n) tailCore
private def compiled (n : Nat) (a : Core.Ty) : CompiledRuntimeFunction := ⟨initial a, core n, a⟩
private theorem header (n : Nat) (a : Core.Ty) : RuntimeFunctionHeader (types a) (entry n).value.signature a :=
  ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩
private theorem declared (a : Core.Ty) : RuntimeParametersDeclare (types a) owner parameters (initial a) :=
  .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "x" ∉ ["f"]; decide)
      (.cons (.named (.tail (by decide) .head)) (by change "y" ∉ ["x", "f"]; decide) .nil))
private theorem child (n : Nat) (a : Core.Ty) :
    RecursiveLocalComputationElaborates (initial a).names (initial a).context (calls n) (callCore n) a := by
  induction n with
  | zero =>
      exact .pure (.identifier (.tail (by change "y" ≠ "x"; decide) .head))
        (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head))
        (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head))
  | succ n ih =>
      exact .application (.pure (.identifier (.tail (by change "y" ≠ "f"; decide) (.tail (by change "x" ≠ "f"; decide) .head)))
        (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)))
        (.var (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)))) ih
private theorem provenance (n : Nat) (a : Core.Ty) :
    RecursiveComputationReturnTreeElaborates (types a) owner (initial a) (body n) (core n) a := by
  have shift : (Core.Expr.var 0).weakenAt 0 = .var 1 := by simp [Core.Expr.weakenAt]
  simp only [body, core, tailCore, ← shift]
  refine .inferred (child n a) ?_
  exact .discard (.pure (.identifier .head) (.var .head) (.var .head))
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem compilation (n : Nat) (a : Core.Ty) : RecursiveComputationFunctionCompiles (types a) owner (entry n) (compiled n a) :=
  ⟨header n a, declared a, provenance n a⟩
private abbrev Actual (a : Core.Ty) := {v : Core.Value // Core.ValueHasType v a}
private structure Capture where
  values : Core.Environment
  types : Core.Context
  typed : Core.EnvironmentHasTypes values types
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | m + 1, index => .letE (.var 0) (delay m (index + 1))
private theorem delayTyped (m index : Nat) (a : Core.Ty) (rest : Core.Context) (found : (a :: rest)[index]? = some a) :
    Core.HasType (a :: rest) (delay m index) a := by
  induction m generalizing index rest with
  | zero => exact .var found
  | succ m ih => exact .letE (.var rfl) (ih (index + 1) (a :: rest) (by simpa using found))
private def closure (m : Nat) (a : Core.Ty) (cap : Capture) : Core.Value := .closure a a (delay m 0) cap.values
private theorem closureTyped (m : Nat) (a : Core.Ty) (cap : Capture) : Core.ValueHasType (closure m a cap) (.function a a) :=
  .closure cap.typed (delayTyped m 0 a cap.types rfl)
private def arguments {a : Core.Ty} (m : Nat) (cap : Capture) (x y : Actual a) : List TypedRuntimeArgument :=
  [⟨.function a a, closure m a cap, closureTyped m a cap⟩, ⟨a, x.val, x.property⟩, ⟨a, y.val, y.property⟩]
private def inputs {a : Core.Ty} (m : Nat) (cap : Capture) (x y : Actual a) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "f" (.function a a) (closure m a cap) (closureTyped m a cap)).bindFresh owner "x" a x.val x.property).bindFresh owner "y" a y.val y.property
private def prepared {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) : PreparedRuntimeFunction := ⟨inputs m cap x y, core n, a⟩
private theorem bound {a : Core.Ty} (m : Nat) (cap : Capture) (x y : Actual a) :
    RuntimeParametersBind (types a) owner parameters (arguments m cap x y) (inputs m cap x y) :=
  .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "x" ∉ ["f"]; decide)
      (.cons (.named (.tail (by decide) .head)) (by change "y" ∉ ["x", "f"]; decide) .nil))
private theorem preparation {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) :
    RecursiveComputationFunctionPrepares (types a) owner (entry n) (arguments m cap x y) (prepared n m cap x y) :=
  ⟨header n a, bound m cap x y, provenance n a⟩
private theorem delayed (m index : Nat) (value : Core.Value) (rest : Core.Environment) (s : Core.Store) (k : List Core.Frame)
    (found : (value :: rest)[index]? = some value) :
    Core.Steps (3 * m + 1) ⟨.eval (delay m index) (value :: rest), k, s⟩ ⟨.ret value, k, s⟩ := by
  induction m generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (value :: rest) k (by simpa using found))))
private def charge (n m : Nat) := n * (3 * m + 5) + 1
private theorem childCost {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs m cap x y).names (inputs m cap x y).environment s (calls n) x.val s (charge n m) := by
  induction n with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .pure (.identifier (.tail (by change "y" ≠ "x"; decide) .head)
      (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head))
  | succ n ih =>
      have count : charge (n + 1) m = 1 + charge n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]
      exact .application (.pure (.identifier (.tail (by change "y" ≠ "f"; decide) (.tail (by change "x" ≠ "f"; decide) .head))
        (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head))))
        ih (delayed m 0 x.val cap.values s [] rfl)
private theorem childPath {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n m) ⟨.eval (callCore n) (inputs m cap x y).environment.values, k, s⟩ ⟨.ret x.val, k, s⟩ := by
  induction n generalizing k with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : charge (n + 1) m = 1 + charge n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var rfl) .refl) (ih _) (delayed m 0 x.val cap.values s [] rfl)
private theorem counted {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs m cap x y).names (inputs m cap x y).environment s (body n) x.val s (charge n m + 6) := by
  refine ComputationReturnTreeEvaluatesWithCost.inferred (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    (initializerCost := charge n m) (tailCost := 4) (childCost n m cap x y s) ?_
  exact ComputationReturnTreeEvaluatesWithCost.discard (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    (.pure (.identifier .head .head)) (.expression (.pure (.identifier .head .head)))
private theorem manual {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n m + 6) ⟨.eval (core n) (inputs m cap x y).environment.values, k, s⟩ ⟨.ret x.val, k, s⟩ := by
  simpa [core, Nat.add_assoc] using CostStepComposition.letE (childPath n m cap x y s _)
    (.cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))) :
      Core.Steps 4 ⟨.eval tailCore (x.val :: (inputs m cap x y).environment.values), k, s⟩ ⟨.ret x.val, k, s⟩)

private theorem compileSome (n : Nat) (a : Core.Ty) :
    compileRecursiveComputationFunction? (types a) owner (entry n) = some (compiled n a) :=
  (compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?)
    (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (compilation n a)
private theorem prepareSome {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) :
    prepareRecursiveComputationFunction? (types a) owner (entry n) (arguments m cap x y) = some (prepared n m cap x y) :=
  (prepareComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?)
    (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (preparation n m cap x y)

theorem exact_original_records_in_both_directions (n : Nat) (a : Core.Ty) :
    compileRecursiveComputationFunction? (types a) owner (entry n) = some (compiled n a) ∧
    RecursiveComputationFunctionCompiles (types a) owner (entry n) (compiled n a) ∧
    ∀ m cap (x y : Actual a), prepareRecursiveComputationFunction? (types a) owner (entry n) (arguments m cap x y) = some (prepared n m cap x y) ∧
      RecursiveComputationFunctionPrepares (types a) owner (entry n) (arguments m cap x y) (prepared n m cap x y) :=
  ⟨compileSome n a, (compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?)
    (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mp (compileSome n a),
    fun m cap x y => ⟨prepareSome n m cap x y, (prepareComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mp (prepareSome n m cap x y)⟩⟩

theorem full_option_projection_uses_original_order (n : Nat) (a : Core.Ty) (args : List TypedRuntimeArgument) :
    (prepareRecursiveComputationFunction? (types a) owner (entry n) args).map PreparedRuntimeFunction.toCompiled =
      if args.map (·.type) = [.function a a, a, a] then some (compiled n a) else none := by
  simpa only [compileSome n a, bind, Option.bind_some,
    show (compiled n a).inputs.context.values.reverse = [.function a a, a, a] from rfl] using
    prepareComputationFunction?_factorization elaborateRecursiveLocalComputation? (types a) owner (entry n) args
private theorem runEq {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) (fuel : Nat) (s : Core.Store) :
    runRecursiveComputationFunction? (types a) owner (entry n) (arguments m cap x y) fuel s =
      some (a, Core.runStateful fuel (.initial (core n) (inputs m cap x y).environment.values s)) := by
  simpa only [compileSome n a, bind, Option.bind_some,
    show (arguments m cap x y).map (·.type) = (compiled n a).inputs.context.values.reverse from rfl, ↓reduceIte,
    show (compiled n a).core = core n from rfl, show (compiled n a).returnType = a from rfl,
    show (arguments m cap x y).reverse.map (·.value) = (inputs m cap x y).environment.values from rfl] using
    runComputationFunction?_factorization elaborateRecursiveLocalComputation? (types a) owner (entry n) (arguments m cap x y) fuel s

theorem independent_cost_and_all_fuel_results {a : Core.Ty} (n m fuel : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs m cap x y).names (inputs m cap x y).environment s (body n) x.val s (charge n m + 6) ∧
    (∀ k, Core.Steps (charge n m + 6) ⟨.eval (core n) (inputs m cap x y).environment.values, k, s⟩ ⟨.ret x.val, k, s⟩) ∧
    (runRecursiveComputationFunction? (types a) owner (entry n) (arguments m cap x y) fuel s = some (a, .done x.val s) ↔ charge n m + 6 ≤ fuel) ∧
    runRecursiveComputationFunction? (types a) owner (entry n) (arguments m cap x y) fuel s =
      some (a, Core.runStateful fuel (.initial (core n) ((arguments m cap x y).reverse.map (·.value)) s)) := by
  refine ⟨counted n m cap x y s, manual n m cap x y s, ?_, runEq n m cap x y fuel s⟩
  rw [runEq, Option.some.injEq, Prod.mk.injEq]; simp only [true_and]
  exact (manual n m cap x y s []).runStateful_done_iff

private def checkpoint {a : Core.Ty} (n m : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) : Core.State :=
  ⟨.ret (closure m a cap), [.applyArgument (callCore n) (inputs m cap x y).environment.values,
    .letBody tailCore (inputs m cap x y).environment.values], s⟩
theorem actual_checkpoint_keeps_the_full_result_tag {a : Core.Ty} (n m additional : Nat) (cap : Capture) (x y : Actual a) (s : Core.Store) :
    runRecursiveComputationFunction? (types a) owner (entry (n + 1)) (arguments m cap x y) 3 s = some (a, .outOfFuel (checkpoint n m cap x y s)) ∧
    Core.Steps (charge (n + 1) m + 6 - 3) (checkpoint n m cap x y s) (.final x.val s) ∧
    runRecursiveComputationFunction? (types a) owner (entry (n + 1)) (arguments m cap x y) (3 + additional) s =
      some (a, Core.runStateful additional (checkpoint n m cap x y s)) := by
  have stopped : Core.runStateful 3 (.initial (core (n + 1)) (inputs m cap x y).environment.values s) = .outOfFuel (checkpoint n m cap x y s) := rfl
  refine ⟨(runEq (n + 1) m cap x y 3 s).trans (congrArg (fun result => some (a, result)) stopped),
    ((manual (n + 1) m cap x y s []).residual_of_outOfFuel stopped).2, ?_⟩
  rw [runEq, Core.runStateful_resume stopped additional]

private def emptyCapture : Capture := ⟨[], [], .nil⟩
private def word (n : Nat) : Actual .word := ⟨.word (Core.Word.ofNatModulo n), .word⟩
theorem same_typed_actual_swap_is_accepted_and_changes_the_result (s : Core.Store) :
    (prepared 2 0 emptyCapture (word 9) (word 14)).toCompiled = (prepared 2 0 emptyCapture (word 14) (word 9)).toCompiled ∧
    prepareRecursiveComputationFunction? (types .word) owner (entry 2) (arguments 0 emptyCapture (word 9) (word 14)) = some (prepared 2 0 emptyCapture (word 9) (word 14)) ∧
    prepareRecursiveComputationFunction? (types .word) owner (entry 2) (arguments 0 emptyCapture (word 14) (word 9)) = some (prepared 2 0 emptyCapture (word 14) (word 9)) ∧
    runRecursiveComputationFunction? (types .word) owner (entry 2) (arguments 0 emptyCapture (word 9) (word 14)) 17 s = some (.word, .done (word 9).val s) ∧
    runRecursiveComputationFunction? (types .word) owner (entry 2) (arguments 0 emptyCapture (word 14) (word 9)) 17 s = some (.word, .done (word 14).val s) ∧
    (word 9).val ≠ (word 14).val := by
  refine ⟨rfl, prepareSome _ _ _ _ _, prepareSome _ _ _ _ _,
    (independent_cost_and_all_fuel_results 2 0 17 _ _ _ s).2.2.1.mpr (by decide),
    (independent_cost_and_all_fuel_results 2 0 17 _ _ _ s).2.2.1.mpr (by decide), ?_⟩
  intro same; have numbers := congrArg Fin.val (Core.Value.word.inj same); change 9 = 14 at numbers; cases numbers

theorem nominal_compilation_is_value_free (n : Nat) (nominal : Core.DataTypeId) :
    compileRecursiveComputationFunction? (types (.namedData nominal)) owner (entry n) = some (compiled n (.namedData nominal)) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨compileSome n _, ?_⟩
  rintro ⟨value, typed⟩; cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem same_source_with_different_actual_body_costs (limit : Nat) (s : Core.Store) :
    ∃ m, RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs m emptyCapture (word 9) (word 14)).names
      (inputs m emptyCapture (word 9) (word 14)).environment s (body 2) (word 9).val s (charge 2 m + 6) ∧ limit < charge 2 m + 6 :=
  ⟨limit, counted 2 limit _ _ _ s, by simp [charge]; omega⟩

theorem independently_accepted_old_entry_embeds (a : Core.Ty) :
    compileRuntimeComputationFunction? (types a) owner (entry 0) = some (compiled 0 a) ∧
    compileRecursiveComputationFunction? (types a) owner (entry 0) = some (compiled 0 a) := by
  have oldChild : LocalComputationElaborates (initial a).names (initial a).context (calls 0) (callCore 0) a := by
    cases child 0 a with
    | pure resolution lowered typing => exact .pure resolution lowered typing
  have oldBody : LocalComputationReturnTreeElaborates (types a) owner (initial a) (body 0) (core 0) a := by
    have shift : (Core.Expr.var 0).weakenAt 0 = .var 1 := by simp [Core.Expr.weakenAt]
    simp only [body, core, tailCore, ← shift]
    refine .inferred (by change "r" ∉ ["y", "x", "f"]; decide) oldChild ?_
    exact .discard (.pure (.identifier .head) (.var .head) (.var .head))
      (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
  exact ⟨compileRuntimeComputationFunction?_iff.mpr ⟨header 0 a, declared a, oldBody⟩,
    (compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr
        ⟨header 0 a, declared a, oldBody.toRecursiveComputationReturnTree⟩⟩

theorem data_only_record_does_not_supply_provenance (n : Nat) (a : Core.Ty) :
    Core.HasType (initial a).context.values (.var 0) a ∧
    ¬ RecursiveComputationFunctionCompiles (types a) owner (entry n) { compiled n a with core := .var 0 } := by
  refine ⟨.var rfl, ?_⟩
  intro forged
  have accepted := (compileComputationFunction?_iff (checkChild := elaborateRecursiveLocalComputation?)
    (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr forged
  have impossible := congrArg CompiledRuntimeFunction.core (Option.some.inj (accepted.symm.trans (compileSome n a)))
  cases impossible

private def invalidChecker : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty) := fun _ _ _ => some (.var 999, .word)
private def invalidEntry := entry 0 ⟨span, [⟨span, .returnStmt (some (ref "x"))⟩]⟩
private def invalidCompiled : CompiledRuntimeFunction := ⟨initial .word, .var 999, .word⟩
private theorem invalidCompiledSome : compileComputationFunction? invalidChecker (types .word) owner invalidEntry = some invalidCompiled := by
  have h : interpretRuntimeFunctionHeader? (types .word) invalidEntry.value.signature = some .word := interpretRuntimeFunctionHeader?_iff.mpr (header 0 .word)
  simp only [compileComputationFunction?, h, bind, Option.bind_some]
  simp [invalidEntry, entry, (declared .word).complete, elaborateComputationReturnTree?, invalidChecker, invalidCompiled]
/-- These are operational equalities for a deliberately invalid checker, not source semantics. -/
theorem arbitrary_checker_factorization_keeps_faults (s : Core.Store) :
    (prepareComputationFunction? invalidChecker (types .word) owner invalidEntry (arguments 0 emptyCapture (word 9) (word 14))).map PreparedRuntimeFunction.toCompiled = some invalidCompiled ∧
    runComputationFunction? invalidChecker (types .word) owner invalidEntry (arguments 0 emptyCapture (word 9) (word 14)) 1 s =
      some (.word, .fault (.unboundVariable 999) (.initial (.var 999) (inputs 0 emptyCapture (word 9) (word 14)).environment.values s)) := by
  constructor
  · rw [prepareComputationFunction?_factorization, invalidCompiledSome]; rfl
  · rw [runComputationFunction?_factorization, invalidCompiledSome]; rfl

end Tests.FrontendRecursiveComputationFunction
end

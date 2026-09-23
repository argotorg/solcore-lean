import Solcore.Syntax.Parser.Function
import Solcore.Frontend.LocalComputation
import Solcore.Frontend.RuntimeComputationFunction
import Solcore.Frontend.RuntimeApplicationFunction
import Solcore.Core.FuelResumptionProperties
/-! Original declarations and actual records precede source certificates and independent fixed Core transition scripts. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RuntimeComputationEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"MixedActual",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def app (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"mixed-actual.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original function did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "complete original bytes"
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
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
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
-- A bounded fixture script constructs transitions; it never calls the machine runner.
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual script depth")
  | n+1,e,env,s => do
    match original : e with
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [original]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual var missing")
    | .unit => return ⟨.unit,s,1,fun _ => by rw [original]; exact .cons .unit .refl⟩
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
private structure Leaf (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  id : Resolved.LocalId
  index : Nat
  type : Core.Ty
  value : Core.Value
  resolution : ResolvesLocalExpression s.names source (.var id)
  lowered : Resolved.Lowers s.context.ids (.var id) (.var index)
  typing : Resolved.HasType s.context (.var id) type
  raw : LocalExpressionEvaluatesWithCost s.names env store source value store 1
private def leaf (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Leaf s env store source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id, actual : env.lookup? id with
          | some t,some i,some v => return ⟨id,i,t,v,by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed),
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual)⟩
          | _,_,_ => throw (IO.userError "independent original row missing")
      | none => throw (IO.userError "independent original name missing")
  | _ => throw (IO.userError "fixture leaf is not identifier")
private structure Child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : LocalComputationElaborates s.names s.context source core type
  raw : LocalComputationEvaluatesWithCost s.names env store source value final cost
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (source.span.contains fn.span && source.span.contains argsSpan && argsSpan.contains arg.span) "original call child spans"
      let f ← leaf s env store fn; let a ← leaf s env store arg
      match ft : f.type, fv : f.value with
      | .function input output,.closure _ _ body captured =>
          if same : a.type=input then
            let b ← path 100 body (a.value::captured) store
            return ⟨.apply (.var f.index) (.var a.index),output,b.value,b.final,b.cost+5,
              by rw [original]; exact .application (.call f.resolution f.lowered (ft ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)),
              by rw [original,←(show 1+1+b.cost+3=b.cost+5 by omega)]; exact .application (.call (fv ▸ f.raw) a.raw (b.evidence []))⟩
          else throw (IO.userError "static argument differs")
      | _,_ => throw (IO.userError "static or actual Function differs")
  | _ =>
      let a ← leaf s env store source
      return ⟨.var a.index,a.type,a.value,store,1,.pure a.resolution a.lowered a.typing,.pure a.raw⟩
private structure Tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : LocalComputationReturnTreeElaborates types owner s source core type
  raw : LocalComputationReturnTreeEvaluatesWithCost owner s.names env store source value final cost
private def tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) : IO (Tree types s env store source) := do
  match original : source with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ =>
      return ⟨.unit,.unit,.unit,store,1,by rw [original]; exact .bare,by rw [original]; exact .bare⟩
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
        have raw : LocalComputationReturnTreeEvaluatesWithCost owner s.names env store source b.value b.final (a.cost+b.cost+2) := by
          rw [original]; cases annotation <;> first | exact .inferred a.raw (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw) | exact .binding a.raw (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw)
        match annotationAt : annotation with
        | none => return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,by rw [original,annotationAt]; exact .inferred unused a.elaboration b.elaboration,raw⟩
        | some t =>
            let m ← meaning types t
            if same : m.1=a.type then return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,by rw [original,annotationAt]; exact .binding (same ▸ m.2.down) unused a.elaboration b.elaboration,raw⟩
            else throw (IO.userError "original binding annotation differs")
      else throw (IO.userError "shadowing is still excluded")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ =>
      let a ← child s env store e; let b ← tree types s env a.final ⟨span,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,b.value,b.final,a.cost+b.cost+2,by rw [original]; exact .discard a.elaboration b.elaboration,by rw [original]; exact .discard a.raw b.raw⟩
  | ⟨_,[⟨_,.ifThen e yes (some no)⟩]⟩ =>
      let c ← child s env store e
      if ct : c.type=.bool then
        let a ← tree types s env c.final yes; let b ← tree types s env c.final no
        if same : b.type=a.type then
          have el : LocalComputationReturnTreeElaborates types owner s source (.ifE c.core a.core b.core) a.type := by rw [original]; exact .conditional (ct ▸ c.elaboration) a.elaboration (same ▸ b.elaboration)
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
private def verify (body : String) (f g x : TypedRuntimeArgument) (output : Core.Ty)
    (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["R"],output),(["Cell"],.cell .word)]
  let source ← parsed ("function mixed(f:F,g:G,x:X) returns(R){"++body++"}"); let args := [f,g,x]
  let ps ← parameters types .empty .empty source.value.signature.parameters.elements args; let inputs := ps.actual
  let h ← header types source output; let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body
  let manual ← path 100 core [x.value,g.value,f.value] s
  have erased : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  check (decide (inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original one-time actual rows"
  if fixed : b.core=core ∧ b.type=output then
    have preparation : RuntimeComputationFunctionPrepares types owner source args ⟨inputs,core,output⟩ :=
      ⟨h.down,ps.bound,by simpa only [fixed.1,fixed.2] using b.elaboration⟩
    have compilation : RuntimeComputationFunctionCompiles types owner source ⟨ps.statics,core,output⟩ :=
      ⟨h.down,ps.declared,by rw [←erased]; exact preparation.body⟩
    have compiled := compileRuntimeComputationFunction?_iff.mpr compilation
    have prepared := prepareRuntimeComputationFunction?_iff.mpr preparation
    have _ := compileRuntimeComputationFunction?_iff.mp compiled
    have _ := prepareRuntimeComputationFunction?_iff.mp prepared
    have matching : args.map (·.type)=ps.statics.context.values.reverse := by
      have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
      simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
    have _ : (prepareRuntimeComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some ⟨ps.statics,core,output⟩ := by rw [prepareRuntimeComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
    have whole (fuel) : runRuntimeComputationFunction? types owner source args fuel s =
        some (output,Core.runStateful fuel (.initial core [x.value,g.value,f.value] s)) := by
      rw [runRuntimeComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte,args,List.reverse_cons,List.reverse_nil]; rfl
    have ids : inputs.environment.ids=inputs.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
    have _ := b.raw.toStepsWithContinuation b.elaboration ids [.letBody .unit []]
    check (decide (b.value=value ∧ b.final=final ∧ b.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent raw/Core value-store-cost"
    check (decide (compileRuntimeFunction? types owner source=none ∧ compileRuntimeApplicationFunction? types owner source=none)) "old whole profiles stay separate"
    for fuel in List.range (cost+2) do
      have _ := whole fuel
      check (decide (runRuntimeComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial core [x.value,g.value,f.value] s)) ∧ runRuntimeFunction? types owner source args fuel s=none ∧ runRuntimeApplicationFunction? types owner source args fuel s=none)) "new full result versus old entry rejection"
      match exhausted : Core.runStateful fuel (.initial core [x.value,g.value,f.value] s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact actual completion"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel exhausted
          have _ := Core.runStateful_resume exhausted (cost-fuel)
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧ runRuntimeComputationFunction? types owner source args (fuel+2) s=some (output,Core.runStateful 2 cp))) "entry retains genuine residual/full resume"
      | .fault _ _ => throw (IO.userError "independent successful path faulted")
  else throw (IO.userError "independent exact Core/type")
private def reader : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word)⟩
private def writer : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word))⟩
private def delay : Nat → Core.Expr | 0 => .var 0 | n+1 => .letE (.var 0) (delay n)
private theorem delayTyped (n : Nat) (ctx : Core.Context) (found : ctx[0]?=some .word) : Core.HasType ctx (delay n) .word := by
  induction n generalizing ctx with | zero => exact .var found | succ n ih => exact .letE (.var found) (ih _ rfl)
end RuntimeComputationEntries
open RuntimeComputationEntries
def frontendParsedRuntimeComputationEntryTests : IO Unit := do
  let x : TypedRuntimeArgument := ⟨.word,w 14,.word⟩
  for old in [3,23] do
    verify "f(x);return g(x);" writer reader x .word (.letE (app 2 0) (app 2 1)) [w old] [w 14] (w 14) 25
    verify "f(x);{g(x);return x;}" writer reader x .word (.letE (app 2 0) (.letE (app 2 1) (.var 2))) [w old] [w 14] (w 14) 28
    verify "f(x);return g;" writer reader x reader.type (.letE (app 2 0) (.var 2)) [w old] [w 14] reader.value 18
    let alloc : TypedRuntimeArgument := ⟨.function .word (.cell .word),.closure .word (.cell .word) (.newCell .word (.var 0)) [],.closure .nil (.newCell (.var rfl) .word)⟩
    let load : TypedRuntimeArgument := ⟨.function (.cell .word) .word,.closure (.cell .word) .word (.loadCell (.var 0)) [],.closure .nil (.loadCell (.var rfl) .word)⟩
    for annotation in ["",":Cell"] do
      verify ("let p"++annotation++"=f(x);return g(p);") alloc load x .word (.letE (app 2 0) (app 2 0)) [w old] [w old,w 14] (w 14) 18
    for choice in [false,true] do
      let guard : TypedRuntimeArgument := ⟨.function .word .bool,.closure .word .bool (.letE (.storeCell (.var 1) (.var 0)) (.bool choice)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) .bool)⟩
      verify "if(f(x)){return g(x);}else{return x;}" guard reader x .word (.ifE (app 2 0) (app 1 0) (.var 0)) [w old] [w 14] (w 14) (if choice then 23 else 16)
    let maker : TypedRuntimeArgument := ⟨.function .word reader.type,.closure .word reader.type (.var 1) [reader.value],.closure (.cons reader.valueTyped .nil) (.var rfl)⟩
    verify "let h=f(x);return h(x);" maker reader x .word (.letE (app 2 0) (app 0 1)) [w old] [w old] (w old) 16
  for n in [0,2,5,13] do
    let f : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (delay n) [],.closure .nil (delayTyped n _ rfl)⟩
    verify "let y=f(x);return y;" f reader x .word (.letE (app 2 0) (.var 0)) [] [] (w 14) (3*n+9)
  verify "f(x);return;" writer reader x .unit (.letE (app 2 0) .unit) [w 3] [w 14] .unit 18
  verify "let p=f(x);return p;" reader reader x .word (.letE (app 2 0) (.var 0)) [.bool true] [.bool true] (.bool true) 11
  for captured in [9,31] do
    let f : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w captured],.closure (.cons .word .nil) (.var rfl)⟩
    verify "let y=f(x);return y;" f reader x .word (.letE (app 2 0) (.var 0)) [] [] (w captured) 9
  let source ← parsed "function mixed(f:F,g:G,x:X) returns(R){let p=f(x);return p;}"
  let types : TypeNameTable := [(["F"],reader.type),(["G"],reader.type),(["X"],.word),(["R"],.word)]
  let args := [reader,reader,x]; let ps ← parameters types .empty .empty source.value.signature.parameters.elements args
  let h ← header types source .word; let b ← tree types ps.actual.toTypeInputs ps.actual.environment [.bool true] source.value.body
  let env := [x.value,reader.value,reader.value]; let core := Core.Expr.letE (app 2 0) (.var 0)
  if fixed : b.core=core ∧ b.type=.word then
    have p : RuntimeComputationFunctionPrepares types owner source args ⟨ps.actual,core,.word⟩ := ⟨h.down,ps.bound,by simpa only [fixed.1,fixed.2] using b.elaboration⟩
    have _ := prepareRuntimeComputationFunction?_iff.mpr p
    let cp : Core.State := ⟨.ret reader.value,[.applyArgument (.var 0) env,.letBody (.var 0) env],[]⟩
    let fault := Core.StatefulRunResult.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply,.letBody (.var 0) env],[]⟩
    check (decide (runRuntimeComputationFunction? types owner source args 3 []=some (.word,.outOfFuel cp) ∧ runRuntimeComputationFunction? types owner source args 8 []=some (.word,fault) ∧ Core.runStateful 5 cp=fault)) "prepared entry preserves exact missing-store fault"
  else throw (IO.userError "fault fixture exact static Core")
end Tests

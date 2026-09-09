import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Frontend.RuntimeComputationFunctionFactorizationProperties
import Solcore.Frontend.RuntimeApplicationFunctionEntry
import Solcore.Frontend.RuntimeApplicationFunctionCompilation
import Solcore.Core.FuelResumptionProperties
/-! Original declaration records feed a separate recursive expression profile.
No recursive whole entry is introduced; fixed Core paths are independent scripts. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveComputationEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveActual",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-actual.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original function did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "complete original bytes"
  check (source.span.contains source.value.signature.span && source.value.signature.span.contains source.value.signature.parameters.span &&
    decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original header and parameter ranges"
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
-- A bounded fixture script constructs transitions; it never calls the machine runner.
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual script depth")
  | n+1,e,env,s => do
    match original : e with
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
  | _ =>
      let a ← leaf s env store source
      return ⟨.var a.index,a.type,a.value,store,1,.pure a.resolution a.lowered a.typing,.pure a.raw⟩
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
private def verify (sourceText : String) (f g x : TypedRuntimeArgument) (output : Core.Ty)
    (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat)
    (legacy : Bool := false) (missing : Bool := false) : IO Unit := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["R"],output)]
  let source ← parsed ("function recursive(f:F,g:G,x:X) returns(R){return "++sourceText++";}"); let args := [f,g,x]
  let ps ← parameters types .empty .empty source.value.signature.parameters.elements args; let inputs := ps.actual
  let h ← header types source output
  let [⟨returnSpan,.returnStmt (some expression)⟩] := source.value.body.value | throw (IO.userError "original return shape")
  check (source.value.body.span.contains returnSpan && returnSpan.contains expression.span) "original expression inside return"
  let b ← child inputs.toTypeInputs inputs.environment s expression; let env := inputs.environment.values
  let manual ← path 100 core [x.value,g.value,f.value] s
  have _ : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  have _ := h.down
  have ids : inputs.environment.ids=inputs.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
  check (decide (env=[x.value,g.value,f.value] ∧ inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original actual rows/reverse once"
  check (decide (b.core=core ∧ b.type=output ∧ b.value=value ∧ b.final=final ∧ b.cost=cost ∧
    manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent Core/type/value/store/cost"
  have accepted := elaborateRecursiveLocalComputation?_iff.mpr b.elaboration
  have _ := elaborateRecursiveLocalComputation?_iff.mp accepted
  have typed := recursiveLocalComputationHasType_iff_elaborates.mpr ⟨_,b.elaboration⟩
  have _ := recursiveLocalComputationHasType_iff_elaborates.mp typed
  have _ := b.elaboration.core_hasType
  have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,b.raw⟩
  have _ := recursiveLocalComputationEvaluates_iff_exists_cost.mp raw
  have evaluated := (b.elaboration.evaluates_iff ids).mp raw
  have _ := (b.elaboration.evaluates_iff ids).mpr evaluated
  have closed := b.raw.toStepsWithContinuation b.elaboration ids []
  have _ := b.raw.toStepsWithContinuation b.elaboration ids [.letBody .unit []]
  have _ := b.raw.deterministic ((b.elaboration.evaluatesWithCost_iff_steps ids).mpr closed)
  have _ := (b.elaboration.evaluatesWithCost_iff_steps ids).mp b.raw
  let inserted : Core.Value := .cellRef (.namedData ⟨99⟩) 72
  let leading := env.take 1; let suffix := env.drop 1
  have splitEnv : leading++suffix=env := List.take_append_drop 1 env
  have fragment := b.elaboration.core_fragment
  have _ := fragment.weakenAt 1
  have evalSplit : Core.Evaluates (leading++suffix) s b.core b.value b.final := by rw [splitEnv]; exact evaluated
  have insertedEvaluation := (fragment.evaluates_insert_iff leading suffix inserted).mpr evalSplit
  have _ := (fragment.evaluates_insert_iff leading suffix inserted).mp insertedEvaluation
  have shifted : Core.Steps b.cost (.initial (b.core.weakenAt leading.length) (leading++inserted::suffix) s) (.final b.value b.final) := by
    obtain ⟨pairedCost,paired⟩ := fragment.insertion_paths leading suffix inserted evalSplit
    have sameCost : pairedCost=b.cost := (closed.final_unique (by simpa only [splitEnv,env,Core.State.final] using (paired []).1)).1.symm
    exact sameCost ▸ (paired []).2
  check (decide (elaborateRecursiveLocalComputation? inputs.names inputs.context expression=some (core,output))) "new expression only"
  unless legacy do check (decide (elaborateLocalComputation? inputs.names inputs.context expression=none ∧
    elaborateLocalComputationReturnTree? types owner inputs.toTypeInputs source.value.body=none ∧
    compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none ∧
    compileRuntimeApplicationFunction? types owner source=none)) "old child/body/whole entry remains narrow"
  for fuel in List.range (cost+2) do
    unless legacy do check (decide (runRuntimeComputationFunction? types owner source args fuel s=none)) "no new whole runner"
    for item in ([⟨Core.State.initial b.core env s,⟨closed⟩⟩,
        ⟨.initial (b.core.weakenAt leading.length) (leading++inserted::suffix) s,⟨shifted⟩⟩] :
        List (Σ start : Core.State, PLift (Core.Steps b.cost start (.final b.value b.final)))) do
      let start := item.1; have cert := item.2.down
      match exhausted : Core.runStateful fuel start with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "fixed completion threshold"
      | .outOfFuel cp =>
          have _ := cert.residual_of_outOfFuel exhausted
          have _ := Core.runStateful_resume exhausted 2
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧
            Core.runStateful 2 cp=Core.runStateful (fuel+2) start)) "each genuine checkpoint/full residual/resume"
      | .fault _ _ => throw (IO.userError "independently successful source faulted")
  if legacy then
    match shape : expression with
    | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
        let a ← leaf inputs.toTypeInputs inputs.environment s fn; let z ← leaf inputs.toTypeInputs inputs.environment s arg
        match ft : a.type, fv : a.value with
        | .function input result,.closure _ _ body captured =>
            if same : z.type=input then
              let p ← path 100 body (z.value::captured) s
              have old : LocalComputationElaborates inputs.toTypeInputs.names inputs.toTypeInputs.context expression (.apply (.var a.index) (.var z.index)) result := by rw [shape]; exact .application (.call a.resolution a.lowered (ft ▸ a.typing) z.resolution z.lowered (same ▸ z.typing))
              have oldCost : LocalComputationEvaluatesWithCost inputs.toTypeInputs.names inputs.environment s expression p.value p.final (1+1+p.cost+3) := by rw [shape]; exact .application (.call (fv ▸ a.raw) z.raw (p.evidence []))
              have _ := old.toRecursiveLocalComputation
              have _ := b.raw.deterministic oldCost.toRecursiveLocalComputation
            else throw (IO.userError "legacy argument")
        | _,_ => throw (IO.userError "legacy Function")
    | _ => throw (IO.userError "legacy root")
  if missing then
    let cp : Core.State := ⟨.eval (.apply (.var 1) (.var 0)) env,[.applyClosure .word .word (.loadCell (.var 1)) [.cellRef .word 0]],[]⟩
    let fault := Core.StatefulRunResult.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩
    check (decide (Core.runStateful 3 (.initial core env [])=.outOfFuel cp ∧ Core.runStateful 12 (.initial core env [])=fault ∧
      Core.runStateful 9 cp=fault)) "same original typed rows do not ensure allocated store"
private def reader : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word)⟩
private def writer : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word))⟩
private def delay : Nat → Core.Expr | 0 => .var 0 | n+1 => .letE (.var 0) (delay n)
private theorem delayTyped (n : Nat) (ctx : Core.Context) (found : ctx[0]?=some .word) : Core.HasType ctx (delay n) .word := by
  induction n generalizing ctx with | zero => exact .var found | succ n ih => exact .letE (.var found) (ih _ rfl)
end RecursiveComputationEntries
open RecursiveComputationEntries
def frontendParsedRecursiveComputationEntryTests : IO Unit := do
  let x : TypedRuntimeArgument := ⟨.word,w 14,.word⟩
  let identity : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 0) [],.closure .nil (.var rfl)⟩
  let nested : Core.Expr := .apply (.var 2) (.apply (.var 1) (.var 0))
  let computed : Core.Expr := .apply (.apply (.var 2) (.var 0)) (.apply (.var 1) (.var 0))
  for old in [3,23] do
    for expression in ["f(g(x))","((f))(((g(x))))","((f(g(x))))"] do
      verify expression reader writer x .word nested [w old] [w 14] (w 14) 22
    verify "f(g(x))" writer reader x .word nested [w old] [w old] (w old) 22
    let alloc : TypedRuntimeArgument := ⟨.function .word (.cell .word),.closure .word (.cell .word) (.newCell .word (.var 0)) [],.closure .nil (.newCell (.var rfl) .word)⟩
    let load : TypedRuntimeArgument := ⟨.function (.cell .word) .word,.closure (.cell .word) .word (.loadCell (.var 0)) [],.closure .nil (.loadCell (.var rfl) .word)⟩
    verify "f(g(x))" load alloc x .word nested [w old] [w old,w 14] (w 14) 15
    let maker : TypedRuntimeArgument := ⟨.function .word reader.type,.closure .word reader.type (.var 1) [reader.value],.closure (.cons reader.valueTyped .nil) (.var rfl)⟩
    verify "(f(x))(g(x))" maker writer x .word computed [w old] [w 14] (w 14) 27
    let effectMaker : TypedRuntimeArgument := ⟨.function .word reader.type,
      .closure .word reader.type (.letE (.storeCell (.var 1) (.var 2)) (.var 4)) [.cellRef .word 0,w 7,reader.value],
      .closure (.cons .cellRef (.cons .word (.cons reader.valueTyped .nil))) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.var rfl))⟩
    verify "((f(x)))((g(x)))" effectMaker writer x .word computed [w old] [w 14] (w 14) 34
    let env := [x.value,writer.value,effectMaker.value]
    check (decide (Core.runStateful 14 (.initial computed env [w old])=.outOfFuel ⟨.ret reader.value,[.applyArgument (.apply (.var 1) (.var 0)) env],[w 7]⟩ ∧
      Core.runStateful 30 (.initial computed env [w old])=.outOfFuel ⟨.ret (w 14),[.applyClosure .word .word (.loadCell (.var 1)) [.cellRef .word 0]],[w 14]⟩)) "observable callee then argument stores/captures"
  for n in [0,2,5,13] do
    let delayed : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (delay n) [],.closure .nil (delayTyped n _ rfl)⟩
    verify "f(g(x))" identity delayed x .word nested [] [] (w 14) (3*n+11)
  for captured in [9,31] do
    let constant : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 1) [w captured],.closure (.cons .word .nil) (.var rfl)⟩
    verify "f(g(x))" constant identity x .word nested [] [] (w captured) 11
  verify "f(g(x))" reader identity x .word nested [.bool true] [.bool true] (.bool true) 13 false true
  verify "f(x)" reader identity x .word (.apply (.var 2) (.var 0)) [w 23] [w 23] (w 23) 8 true
end Tests

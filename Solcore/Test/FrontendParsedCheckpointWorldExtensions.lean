import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Frontend.RuntimeInputValidation
import Solcore.Frontend.Computation
import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.FuelResumptionProperties
/-! Original allocation/write order and literal saved states precede the world
extension kernel. Raw construction and validation never guard the old entry. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedCheckpointWorldExtensions
private def check (b : Bool) (label : String) : IO Unit := do unless b do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"CheckpointWorlds",by decide⟩],by decide⟩⟩,89⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def reader : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word 0]
private def nested : Core.Value := .closure .word .word (.apply (.var 1) (.var 0)) [reader]
private def writer : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0]
private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
private def rawArgs : List Core.Value := [allocator,writer,nested,w 14]
private def env : Core.Environment := [w 14,nested,writer,allocator]
private def types : TypeNameTable :=
  [(["A"],allocator.type),(["W"],writer.type),(["R"],nested.type),(["X"],.word),(["P"],.cell .word)]
private def finalCall : Core.Expr := .apply (.var 4) (.var 3)
private def secondLet : Core.Expr := .letE (.apply (.var 5) (.apply (.var 3) (.var 2))) finalCall
private def tailCore : Core.Expr := .letE (.apply (.var 3) (.var 1)) secondLet
private def core : Core.Expr := .letE (.apply (.var 3) (.apply (.var 1) (.var 0))) tailCore
private def pending : List Core.Frame := [.pairApply (.bool true)]
private def finalStore : Core.Store := [w 14,w 23,w 14]
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function checkpoints(a:A,w:W,r:R,x:X) returns(X){let p:P=a(r(x));w(x);let q:P=a(r(x));return r(x);}"
  let file : Syntax.SourceFile := ⟨⟨.main,"checkpoint-world-extensions.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original declaration")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span &&
    source.span.contains source.value.body.span) "complete original header/body spans"
  return source
private def arguments : (raw : List Core.Value) → IO (Σ args : List TypedRuntimeArgument, PLift (args.map (·.value)=raw))
  | [] => return ⟨[],⟨rfl⟩⟩
  | value::rest => do
      match built : buildRuntimeArgument? value with
      | none => throw (IO.userError "raw structural construction")
      | some argument =>
          let tail ← arguments rest
          return ⟨argument::tail.1,⟨by simp only [List.map_cons,buildRuntimeArgument?_iff.mp built,tail.2.down]⟩⟩
private def meaning (table : TypeNameTable) (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes table source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : table.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "source annotation")
  | _ => throw (IO.userError "annotation shape")
private def parameters (table : TypeNameTable) (initial : LocalInputs) (ps : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Σ final, PLift (RuntimeParametersBindFrom table owner initial ps args final)) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨initial,⟨by rw [shape,supplied]; exact .nil⟩⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter ranges"
      let m ← meaning table annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let next ← parameters table (initial.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.1,⟨by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused next.2.down⟩⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter shape/arity")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (inputs : LocalTypeInputs) (source : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates inputs.names inputs.context source)) := do
  match shape : source with
  | ⟨_,.identifier name⟩ => match named : inputs.names.lookup? name.value with
    | some id => match typed : inputs.context.lookup? id, indexed : Resolved.LocalScope.index? inputs.context.ids id with
      | some t,some i => return ⟨.var i,t,by
          rw [shape]
          exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
            (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "source name")
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span) "original call children"
      let f ← child inputs fn; let a ← child inputs arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "call argument")
      | _ => throw (IO.userError "callee")
  | _ => throw (IO.userError "child shape")
termination_by sizeOf source
private def body (table : TypeNameTable) (inputs : LocalTypeInputs) (source : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates table owner inputs source)) := do
  check (source.value.all fun s => source.span.contains s.span) "original statement spans"
  match shape : source with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let a ← child inputs e; return ⟨a.core,a.type,by rw [shape]; exact .expression a.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      if unused : name.value ∉ inputs.names.map Prod.fst then
        let a ← child inputs e; let b ← body table (inputs.bindFresh owner name.value a.type) ⟨span,rest⟩
        match annotationAt : annotation with
        | none => return ⟨.letE a.core b.core,b.type,by rw [shape,annotationAt]; exact .inferred a.evidence b.evidence⟩
        | some t =>
            let m ← meaning table t
            if same : m.1=a.type then return ⟨.letE a.core b.core,b.type,by rw [shape,annotationAt]; exact .binding (same ▸ m.2.down) a.evidence b.evidence⟩
            else throw (IO.userError "binding annotation")
      else throw (IO.userError "fresh binding")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ =>
      let a ← child inputs e; let b ← body table inputs ⟨span,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,by rw [shape]; exact .discard a.evidence b.evidence⟩
  | _ => throw (IO.userError "body shape")
termination_by sizeOf source
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) :
    IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧
      p.core=core ∧ p.returnType=.word ∧ p.inputs.environment.values=env)) := do
  let ps ← parameters types .empty source.value.signature.parameters.elements args
  let b ← body types ps.1.toTypeInputs source.value.body
  if fixed : b.core=core ∧ b.type=.word ∧ ps.1.environment.values=env then
    check (decide (ps.1.names=[("x",⟨owner,3⟩),("r",⟨owner,2⟩),("w",⟨owner,1⟩),("a",⟨owner,0⟩)])) "actual reverse-once rows"
    match clause : source.value.signature.returnsClause with
    | some ⟨_,⟨_,[annotation]⟩⟩ =>
        let m ← meaning types annotation
        if same : m.1=.word then
          if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
            let p : PreparedRuntimeFunction := ⟨ps.1,core,.word⟩
            have annotationMeaning : StructuralTypeDenotes types annotation .word := by simpa only [same] using m.2.down
            have h : RuntimeFunctionHeader types source.value.signature .word :=
              ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single annotationMeaning⟩
            return ⟨p,⟨⟨⟨h,ps.2.down,by simpa only [fixed.1,fixed.2.1] using b.evidence⟩,rfl,rfl,fixed.2.2⟩⟩⟩
          else throw (IO.userError "header policy")
        else throw (IO.userError "declared return type")
    | _ => throw (IO.userError "single return type")
  else throw (IO.userError "independent literal Core/type/environment")
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
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured =>
            let r ← path n b (arg.value::captured) arg.final
            return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match found : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with
      | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
      | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual operands")
    | _ => throw (IO.userError "manual grammar")
private theorem runtimeArguments {world : Core.StoreTyping} (args : List TypedRuntimeArgument)
    (typed : ∀ arg ∈ args, Core.RuntimeValueHasType world arg.value arg.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons a rest ih => exact .cons (typed a (by simp)) (ih (fun v member => typed v (by simp [member])))
private theorem storeWorld {world : Core.StoreTyping} {store : Core.Store}
    (typed : Core.RuntimeStoreHasTypes world store) : world=store.map Core.Value.type :=
  typed.world_eq
private def verify (source : Syntax.FunctionDecl) : IO Unit := do
  let manual ← path 80 core env [w 23]
  check (decide (manual.cost=74 ∧ manual.value=w 14 ∧ manual.final=finalStore)) "independent literal raw path and effects"
  let args ← arguments rawArgs
  check (decide (args.1.map (·.value)=rawArgs)) "literal original raw values"
  let p ← prepare source args.1
  have original : RecursiveComputationReturnTreeElaborates types owner p.1.inputs.toTypeInputs source.value.body core .word := by
    simpa only [p.2.down.2.1,p.2.down.2.2.1] using p.2.down.1.body
  if validated : validateRuntimeInputs [.word] args.1 [w 23]=true then
    have runtime := validateRuntimeInputs_iff.mp validated
    have reversed := runtimeArguments args.1.reverse (fun a member => runtime.1 a (List.mem_reverse.mp member))
    have actual : Core.RuntimeEnvironmentHasTypes [.word] env p.1.inputs.toTypeInputs.context.values := by
      have bound : Core.RuntimeEnvironmentHasTypes [.word] p.1.inputs.environment.values p.1.inputs.context.values := by
        simpa only [LocalInputs.environment,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,
          p.2.down.1.parameters.argument_values,p.2.down.1.parameters.argument_types] using reversed
      simpa only [p.2.down.2.2.2,LocalInputs.toTypeInputs_context] using bound
    have typedK : Core.ContinuationHasType [.word] pending .word (.product .bool .word) := .cons (.pairApply .bool) .nil
    have safe := original.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK
    have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
    have _ := accepted
    let start : Core.State := ⟨.eval core env,pending,[w 23]⟩
    let result := Core.Value.pair (.bool true) (w 14)
    have wholePath : Core.Steps (manual.cost+1) start ⟨.ret (.pair (.bool true) manual.value),[],manual.final⟩ :=
      (manual.evidence pending).trans (.cons .applyPair .refl)
    for fuel in List.range 77 do
      check (decide (runRecursiveComputationFunction? types owner source args.1 fuel [w 23]=
        some (.word,Core.runStateful fuel (.initial core env [w 23])))) "unchanged full compiled entry result"
      match exhausted : Core.runStateful fuel start with
      | .done value store => check (decide (75≤fuel ∧ value=result ∧ store=finalStore)) "typed pending frame completes after original body"
      | .fault _ _ => throw (IO.userError "typed original pending frame fault")
      | .outOfFuel cp =>
          have saved := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK exhausted
          have _ := safe.2.2 exhausted
          have _ := wholePath.residual_of_outOfFuel exhausted
          have oldReference : ∃ savedWorld, Core.WorldExtends [.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧ savedWorld[0]?=some .word := by
            obtain ⟨savedWorld,extension,stored,_⟩ := saved
            exact ⟨savedWorld,extension,stored,extension.lookup rfl⟩
          have _ := oldReference
          have terminal : ∃ savedWorld future, Core.WorldExtends [.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧
              Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future manual.final := by
            obtain ⟨savedWorld,extension,stored,resumed⟩ := saved
            obtain ⟨future,growth,finalTyped⟩ := resumed (wholePath.residual_of_outOfFuel exhausted).2
            exact ⟨savedWorld,future,extension,stored,growth,finalTyped⟩
          have _ := terminal
          check (decide (fuel<75 ∧ Core.runStateful (75-fuel) cp=.done result finalStore)) "all genuine saved states retain exact remaining execution"
          for extra in [0,1,7,75] do
            check (decide (Core.runStateful extra cp=Core.runStateful (fuel+extra) start)) "full original/resumed state equality"
            match again : Core.runStateful extra cp with
            | .outOfFuel next =>
                have chain : ∃ saved future, Core.WorldExtends [.word] saved ∧ Core.RuntimeStoreHasTypes saved cp.store ∧
                    Core.WorldExtends saved future ∧ Core.RuntimeStoreHasTypes future next.store ∧ future[0]?=some .word := by
                  obtain ⟨savedWorld,extension,stored,resumed⟩ := saved
                  obtain ⟨future,growth,nextTyped⟩ := resumed (Core.runStateful_outOfFuel_sound again).1
                  exact ⟨savedWorld,future,extension,stored,growth,nextTyped,(extension.trans growth).lookup rfl⟩
                have _ := chain
            | .done _ _ => pure ()
            | .fault _ _ => throw (IO.userError "resumed typed checkpoint fault")
    let first : Core.State := ⟨.ret (.cellRef .word 1),.letBody tailCore env::pending,[w 23,w 23]⟩
    let written : Core.State := ⟨.ret (w 14),.letBody secondLet (.cellRef .word 1::env)::pending,[w 14,w 23]⟩
    let second : Core.State := ⟨.ret (.cellRef .word 2),.letBody finalCall (w 14::.cellRef .word 1::env)::pending,finalStore⟩
    for (spent,cp) in [(21,first),(38,written),(60,second)] do
      if genuine : Core.runStateful spent start=.outOfFuel cp then
        have identified : Core.WorldExtends [.word] (cp.store.map Core.Value.type) ∧ Core.RuntimeStoreHasTypes (cp.store.map Core.Value.type) cp.store := by
          obtain ⟨world,ext,stored,_⟩ := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK genuine
          simpa only [storeWorld stored] using And.intro ext stored
        have _ := identified
        check (decide (Core.runStateful (75-spent) cp=.done result finalStore)) "allocation/write/allocation preserve actual saved binders/captures"
      else throw (IO.userError "literal checkpoint mismatch")
    if chain : Core.runStateful 21 start=.outOfFuel first ∧ Core.runStateful 17 first=.outOfFuel written ∧ Core.runStateful 22 written=.outOfFuel second then
      have exactWorlds : Core.WorldExtends [.word] [.word,.word] ∧ Core.RuntimeStoreHasTypes [.word,.word] first.store ∧
          Core.RuntimeStoreHasTypes [.word,.word] written.store ∧ Core.WorldExtends [.word,.word] [.word,.word,.word] ∧
          Core.RuntimeStoreHasTypes [.word,.word,.word] second.store := by
        obtain ⟨saved,ext,stored,further⟩ := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK chain.1
        have writePath := (Core.runStateful_outOfFuel_sound chain.2.1).1
        obtain ⟨afterWrite,_,writeTyped⟩ := further writePath
        obtain ⟨afterAllocate,extended,allocationTyped⟩ := further (writePath.trans (Core.runStateful_outOfFuel_sound chain.2.2).1)
        have firstTypes : saved=[.word,.word] := storeWorld stored
        have writtenTypes : afterWrite=[.word,.word] := storeWorld writeTyped
        have secondTypes : afterAllocate=[.word,.word,.word] := storeWorld allocationTyped
        subst saved; subst afterWrite; subst afterAllocate
        exact ⟨ext,stored,writeTyped,extended,allocationTyped⟩
      have _ := exactWorlds
    else throw (IO.userError "independent 17/22-transition saved-state chain")
    check (decide (first.store.length=written.store.length ∧ first.store≠written.store ∧
      first.store.map Core.Value.type=written.store.map Core.Value.type ∧ second.store.length=written.store.length+1)) "typed write changes payload, second allocation extends locations"
  else throw (IO.userError "constructed input validation")
end ParsedCheckpointWorldExtensions
open ParsedCheckpointWorldExtensions
def frontendParsedCheckpointWorldExtensionTests : IO Unit := do verify (← parsed)
end Tests

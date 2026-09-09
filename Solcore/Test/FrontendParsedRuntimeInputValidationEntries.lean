import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeInputValidation
import Solcore.Frontend.ComputationFunctionRuntimeSafetyProperties
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.FuelResumptionProperties
/-! Original preparation and a separate literal Core path precede validation.
The opt-in Bool supplies runtime premises without guarding or rewriting entries. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRuntimeInputValidationEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ValidatedEntries",by decide⟩],by decide⟩⟩,74⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def x : TypedRuntimeArgument := ⟨.word,w 14,.word⟩
private def invocation : Core.Expr := .apply (.var 1) (.var 0)
private def tailCore : Core.Expr := .letE (.var 0) (.var 1)
private def core : Core.Expr := .letE invocation tailCore
private def types (f : TypedRuntimeArgument) (output : Core.Ty) : TypeNameTable :=
  [(["F"],f.type),(["X"],.word),(["R"],output)]
private def parsed (annotated : Bool) : IO Syntax.FunctionDecl := do
  let text := "function checked(f:F,x:X) returns(R){let r"++(if annotated then ":R" else "")++"=f(x);r;return r;}"
  let file : Syntax.SourceFile := ⟨⟨.main,"runtime-input-validation.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original declaration")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span &&
    source.span.contains source.value.body.span) "original complete header/body spans"
  return source
private def meaning (table : TypeNameTable) (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes table source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : table.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "annotation")
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
private def prepare (source : Syntax.FunctionDecl) (f : TypedRuntimeArgument) (output : Core.Ty) :
    IO (Σ p, PLift (RecursiveComputationFunctionPrepares (types f output) owner source [f,x] p ∧
      p.core=core ∧ p.returnType=output)) := do
  let ps ← parameters (types f output) .empty source.value.signature.parameters.elements [f,x]
  let b ← body (types f output) ps.1.toTypeInputs source.value.body
  check (decide (ps.1.environment.values=[x.value,f.value] ∧ ps.1.names=[("x",⟨owner,1⟩),("f",⟨owner,0⟩)])) "actual reverse-once records"
  if fixed : b.core=core ∧ b.type=output then
    match clause : source.value.signature.returnsClause with
    | some ⟨_,⟨_,[annotation]⟩⟩ =>
        let m ← meaning (types f output) annotation
        if same : m.1=output then
          if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
            let p : PreparedRuntimeFunction := ⟨ps.1,core,output⟩
            have annotationMeaning : StructuralTypeDenotes (types f output) annotation output := by
              simpa only [same] using m.2.down
            have h : RuntimeFunctionHeader (types f output) source.value.signature output :=
              ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single annotationMeaning⟩
            return ⟨p,⟨⟨⟨h,ps.2.down,by simpa only [fixed.1,fixed.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
          else throw (IO.userError "header policy")
        else throw (IO.userError "return annotation")
    | _ => throw (IO.userError "single return type")
  else throw (IO.userError "independent literal Core/type")
private structure Path (core : Core.Expr) (env : Core.Environment) (store : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,store⟩ ⟨.ret value,k,final⟩
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
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core grammar")
private def positive (source : Syntax.FunctionDecl) (f : TypedRuntimeArgument) (output : Core.Ty)
    (world : Core.StoreTyping) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let p ← prepare source f output; let env := p.1.inputs.environment.values
  let manual ← path 40 core env s
  check (decide (manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independently fixed value/store/cost"
  if validated : validateRuntimeInputs world [f,x] s=true then
    have runtime := validateRuntimeInputs_iff.mp validated
    have safe := ComputationFunctionPrepares.runtime_typed_execution (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
      RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost
      RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
      elaborateRecursiveLocalComputation?_iff p.2.down.1 runtime.1 runtime.2
    have agreement : ∃ future, Core.WorldExtends world future ∧ Core.StoreHasTypes future manual.final ∧
        Core.RuntimeValueHasType future manual.value output ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner p.1.inputs.names p.1.inputs.environment s source.value.body manual.value manual.final manual.cost ∧
        (∀ k, Core.Steps manual.cost ⟨.eval core env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩) ∧
        (∀ fuel, (Core.runStateful fuel (.initial core env s)=.done manual.value manual.final ↔ manual.cost≤fuel) ∧
          ((∃ cp, Core.runStateful fuel (.initial core env s)=.outOfFuel cp) ↔ fuel<manual.cost)) := by
      obtain ⟨future,t,v,n,ext,st,vt,raw,paths,thresholds,_⟩ := safe.2
      have closed : Core.Steps manual.cost (.initial p.1.core env s) ⟨.ret manual.value,[],manual.final⟩ := by
        rw [p.2.down.2.1]; exact manual.evidence []
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique closed
      refine ⟨future,ext,st,by simpa only [p.2.down.2.2] using vt,raw,?_,?_⟩
      · simpa only [p.2.down.2.1] using paths
      · simpa only [p.2.down.2.1] using thresholds
    if grows : s.length < manual.final.length then
      have extension : ∃ future, Core.WorldExtends world future ∧ world.length < future.length ∧ Core.StoreHasTypes future manual.final := by
        obtain ⟨future,ext,st,_,_⟩ := agreement
        exact ⟨future,ext,by simpa only [runtime.2.length_eq,st.length_eq] using grows,st⟩
      have _ := extension
      check (decide (s.length < final.length)) "allocation extends the validated world and actual store"
    have whole (fuel) : runRecursiveComputationFunction? (types f output) owner source [f,x] fuel s =
        some (output,Core.runStateful fuel (.initial core env s)) := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,runs⟩ := safe.2
      simpa only [p.2.down.2.1,p.2.down.2.2] using runs fuel
    have _ := safe.1
    let call ← path 40 invocation env s
    let first : Core.State := ⟨.ret call.value,[.letBody tailCore env],call.final⟩
    have firstPath : Core.Steps (call.cost+1) (.initial core env s) first := by
      simpa [core,first,Core.State.initial,Nat.add_comm] using Core.Steps.cons Core.Transition.enterLet
        (call.evidence [.letBody tailCore env])
    have _ := Core.runStateful_outOfFuel_complete firstPath (Core.advance_next_iff.mpr .bindLet)
    check (decide (call.cost+6=cost ∧ Core.runStateful (cost-5) (.initial core env s)=.outOfFuel first ∧
      Core.runStateful 5 first=.done value final)) "actual captured values/store and pending named-binding frame"
    for fuel in List.range (cost+2) do
      have _ := whole fuel
      check (decide (runRecursiveComputationFunction? (types f output) owner source [f,x] fuel s=some (output,Core.runStateful fuel (.initial core env s)))) "validation preserves prepared record and full runner"
      match stopped : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact done threshold"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel stopped
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧
            Core.runStateful 3 cp=Core.runStateful (fuel+3) (.initial core env s))) "every genuine checkpoint/full resumption"
      | .fault _ _ => throw (IO.userError "validated input fault")
    let cp : Core.State := ⟨.eval (.var 1) (value::value::env),[],final⟩
    check (decide (Core.runStateful (cost-1) (.initial core env s)=.outOfFuel cp ∧ Core.runStateful 1 cp=.done value final)) "actual named and discard hidden slots"
  else throw (IO.userError "valid input rejected")
private def rejected (source : Syntax.FunctionDecl) (f : TypedRuntimeArgument) (world : Core.StoreTyping)
    (s : Core.Store) (threshold : Nat) (expected : Core.Environment → Core.StatefulRunResult) : IO Unit := do
  let p ← prepare source f .word; let env := p.1.inputs.environment.values
  have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
  have _ := accepted
  check (!validateRuntimeInputs world [f,x] s) "invalid runtime input accepted"
  for fuel in List.range (threshold+2) do
    let actual := Core.runStateful fuel (.initial core env s)
    check (decide (runRecursiveComputationFunction? (types f .word) owner source [f,x] fuel s=some (.word,actual))) "rejection does not guard or repair the unchanged entry"
    if fuel<threshold then
      match actual with
      | .outOfFuel cp => check (decide (Core.runStateful 40 cp=expected env ∧ Core.runStateful 3 cp=Core.runStateful (fuel+3) (.initial core env s))) "rejected raw checkpoint remains resumable"
      | _ => throw (IO.userError "rejected raw first threshold")
    else check (decide (actual=expected env)) "rejection does not replace raw success/fault"
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word)⟩
private def writer : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word))⟩
private def identity : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.var 0) [],.closure .nil (.var rfl)⟩
private def nested (l : Nat) (used : Bool) : TypedRuntimeArgument :=
  ⟨.function .word .word,.closure .word .word (if used then invocation else .var 0) [(reader l).value],
    .closure (.cons (reader l).valueTyped .nil) (by split; exact .apply (.var rfl) (.var rfl); exact .var rfl)⟩
private def allocator : TypedRuntimeArgument := ⟨.function .word (.cell .word),.closure .word (.cell .word) (.newCell .word (.var 0)) [],.closure .nil (.newCell (.var rfl) .word)⟩
end ParsedRuntimeInputValidationEntries
open ParsedRuntimeInputValidationEntries
def frontendParsedRuntimeInputValidationEntryTests : IO Unit := do
  for annotated in [false,true] do
    let source ← parsed annotated
    positive source identity .word [] [] [] (w 14) 12
    positive source (reader 0) .word [.word] [w 23] [w 23] (w 23) 14
    positive source writer .word [.word] [w 23] [w 14] (w 14) 21
    positive source (nested 0 true) .word [.word] [w 23] [w 23] (w 23) 19
    positive source (nested 0 false) .word [.word] [w 23] [w 23] (w 14) 12
    positive source allocator (.cell .word) [.word] [w 23] [w 23,w 14] (.cellRef .word 1) 14
    rejected source (reader 0) [.word] [] 8 (fun env => .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply,.letBody tailCore env],[]⟩)
    rejected source (reader 0) [.word] [.bool true] 14 (fun _ => .done (.bool true) [.bool true])
    rejected source writer [.word] [.bool true] 21 (fun _ => .done (w 14) [w 14])
    rejected source identity [.word] [.bool true] 12 (fun _ => .done (w 14) [.bool true])
    rejected source (reader 0) [.bool] [.bool true] 14 (fun _ => .done (.bool true) [.bool true])
    rejected source (nested 7 false) [.word] [w 23] 12 (fun _ => .done (w 14) [w 23])
    rejected source (reader 0) [.word] [w 23,w 9] 14 (fun _ => .done (w 23) [w 23,w 9])
    rejected source (reader 0) [.word,.word] [w 23] 14 (fun _ => .done (w 23) [w 23])
end Tests

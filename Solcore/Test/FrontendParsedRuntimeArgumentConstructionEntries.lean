import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RuntimeArgumentConstruction
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
/-! Raw values, original preparation and literal Core paths are retained through
structural construction and the separate, opt-in same-world validation boundary. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedRuntimeArgumentConstructionEntries
private def check (b : Bool) (label : String) : IO Unit := do unless b do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ConstructedArguments",by decide⟩],by decide⟩⟩,81⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def core : Core.Expr := .apply (.var 1) (.var 0)
private def types (f x : TypedRuntimeArgument) (output : Core.Ty) : TypeNameTable :=
  [(["F"],f.type),(["X"],x.type),(["R"],output)]
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function invoke(f:F,x:X) returns(R){return f(x);}"
  let file : Syntax.SourceFile := ⟨⟨.main,"runtime-argument-construction.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original declaration")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span &&
    source.span.contains source.value.body.span) "complete original header/body spans"
  return source
private def construct (raw : Core.Value) : IO (Σ a : TypedRuntimeArgument, PLift (a.value=raw)) := do
  match built : buildRuntimeArgument? raw with
  | none => throw (IO.userError "raw structural construction")
  | some a =>
      have same := buildRuntimeArgument?_iff.mp built
      have tag : raw.type=a.type := by simpa only [same] using a.valueTyped.type_eq
      have _ := buildRuntimeArgument?_iff.mpr same
      check (decide (a.value=raw ∧ a.type=raw.type)) "exact raw value/type, no repaired payload"
      have _ := tag
      return ⟨a,⟨same⟩⟩
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
private def prepare (source : Syntax.FunctionDecl) (f x : TypedRuntimeArgument) (output : Core.Ty) :
    IO (Σ p, PLift (RecursiveComputationFunctionPrepares (types f x output) owner source [f,x] p ∧
      p.core=core ∧ p.returnType=output ∧ p.inputs.environment.values=[x.value,f.value])) := do
  let ps ← parameters (types f x output) .empty source.value.signature.parameters.elements [f,x]
  match bodyShape : source.value.body with
  | ⟨span,[⟨stmtSpan,.returnStmt (some e)⟩]⟩ =>
      check (span.contains stmtSpan && stmtSpan.contains e.span) "original return/body ranges"
      let b ← child ps.1.toTypeInputs e
      if fixed : b.core=core ∧ b.type=output ∧ ps.1.environment.values=[x.value,f.value] then
        check (decide (ps.1.names=[("x",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original reverse-once records"
        match clause : source.value.signature.returnsClause with
        | some ⟨_,⟨_,[annotation]⟩⟩ =>
            let m ← meaning (types f x output) annotation
            if same : m.1=output then
              if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
                let p : PreparedRuntimeFunction := ⟨ps.1,core,output⟩
                have annotationMeaning : StructuralTypeDenotes (types f x output) annotation output := by simpa only [same] using m.2.down
                have h : RuntimeFunctionHeader (types f x output) source.value.signature output :=
                  ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single annotationMeaning⟩
                have body : RecursiveComputationReturnTreeElaborates (types f x output) owner ps.1.toTypeInputs source.value.body core output := by
                  rw [bodyShape]; exact .expression (by simpa only [fixed.1,fixed.2.1] using b.evidence)
                return ⟨p,⟨⟨⟨h,ps.2.down,body⟩,rfl,rfl,fixed.2.2⟩⟩⟩
              else throw (IO.userError "header policy")
            else throw (IO.userError "return annotation")
        | _ => throw (IO.userError "single return type")
      else throw (IO.userError "independent Core/type/actual input order")
  | _ => throw (IO.userError "original return shape")
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
private def positive (source : Syntax.FunctionDecl) (rf rx : Core.Value) (output : Core.Ty)
    (world : Core.StoreTyping) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let manual ← path 40 core [rx,rf] s
  check (decide (manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "fixed raw Core observations before construction"
  let f ← construct rf; let x ← construct rx; let p ← prepare source f.1 x.1 output
  have envEq : p.1.inputs.environment.values=[rx,rf] := by rw [p.2.down.2.2.2,x.2.down,f.2.down]
  if validated : validateRuntimeInputs world [f.1,x.1] s=true then
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
        (∀ k, Core.Steps manual.cost ⟨.eval core [rx,rf],k,s⟩ ⟨.ret manual.value,k,manual.final⟩) ∧
        (∀ fuel, (Core.runStateful fuel (.initial core [rx,rf] s)=.done manual.value manual.final ↔ manual.cost≤fuel) ∧
          ((∃ cp, Core.runStateful fuel (.initial core [rx,rf] s)=.outOfFuel cp) ↔ fuel<manual.cost)) := by
      obtain ⟨future,t,v,n,ext,st,vt,raw,paths,thresholds,_⟩ := safe.2
      have closed : Core.Steps manual.cost (.initial p.1.core p.1.inputs.environment.values s) ⟨.ret manual.value,[],manual.final⟩ := by
        rw [p.2.down.2.1,envEq]; exact manual.evidence []
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique closed
      refine ⟨future,ext,st,by simpa only [p.2.down.2.2.1] using vt,raw,?_,?_⟩
      · simpa only [p.2.down.2.1,envEq] using paths
      · simpa only [p.2.down.2.1,envEq] using thresholds
    if grows : s.length < manual.final.length then
      have extension : ∃ future, Core.WorldExtends world future ∧ world.length < future.length ∧ Core.StoreHasTypes future manual.final := by
        obtain ⟨future,ext,st,_,_⟩ := agreement
        exact ⟨future,ext,by simpa only [runtime.2.length_eq,st.length_eq] using grows,st⟩
      have _ := extension
      check (decide (s.length < final.length)) "allocation extends the supplied world and literal store"
    have whole (fuel) : runRecursiveComputationFunction? (types f.1 x.1 output) owner source [f.1,x.1] fuel s =
        some (output,Core.runStateful fuel (.initial core [rx,rf] s)) := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,runs⟩ := safe.2
      simpa only [p.2.down.2.1,p.2.down.2.2.1,envEq] using runs fuel
    have _ := safe.1
    for fuel in List.range (cost+2) do
      have _ := whole fuel
      check (decide (runRecursiveComputationFunction? (types f.1 x.1 output) owner source [f.1,x.1] fuel s=some (output,Core.runStateful fuel (.initial core [rx,rf] s)))) "constructed literal records/full runner"
      match stopped : Core.runStateful fuel (.initial core [rx,rf] s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact source completion threshold"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel stopped
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧
            Core.runStateful 3 cp=Core.runStateful (fuel+3) (.initial core [rx,rf] s))) "every genuine raw checkpoint/full resumption"
      | .fault _ _ => throw (IO.userError "validated constructed input fault")
    match shape : rf with
    | .closure input output body captured =>
        let cp : Core.State := ⟨.ret rx,[.applyClosure input output body captured],s⟩
        have before : Core.Steps 4 (.initial core [rx,rf] s) cp := by
          rw [shape]; exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) .refl)))
        have _ := Core.runStateful_outOfFuel_complete before (Core.advance_next_iff.mpr .invokeClosure)
        let invoked : Core.State := ⟨.eval body (rx::captured),[],s⟩
        check (decide (Core.runStateful 4 (.initial core [rx,rf] s)=.outOfFuel cp ∧
          Core.runStateful 1 cp=.outOfFuel invoked ∧ Core.runStateful (cost-4) cp=.done value final ∧
          Core.runStateful (cost-5) invoked=.done value final)) "literal callee frame, actual argument/captures and body checkpoint"
    | _ => throw (IO.userError "original closure fixture")
  else throw (IO.userError "constructed safe input rejected")
private def rejected (source : Syntax.FunctionDecl) (rf rx : Core.Value) (world : Core.StoreTyping)
    (s : Core.Store) (threshold : Nat) (expected : Core.StatefulRunResult) : IO Unit := do
  let f ← construct rf; let x ← construct rx; let p ← prepare source f.1 x.1 .word
  have _ := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
  check (!validateRuntimeInputs world [f.1,x.1] s) "structural construction is not runtime safety"
  for fuel in List.range (threshold+2) do
    let actual := Core.runStateful fuel (.initial core [rx,rf] s)
    check (decide (runRecursiveComputationFunction? (types f.1 x.1 .word) owner source [f.1,x.1] fuel s=some (.word,actual))) "world rejection preserves source preparation and raw runner"
    if fuel<threshold then
      match actual with
      | .outOfFuel cp => check (decide (Core.runStateful 40 cp=expected ∧ Core.runStateful 3 cp=Core.runStateful (fuel+3) (.initial core [rx,rf] s))) "rejected-input raw resumption"
      | _ => throw (IO.userError "first raw threshold")
    else check (decide (actual=expected)) "rejection does not replace raw success/fault"
private def identity (t : Core.Ty) : Core.Value := .closure t t (.var 0) []
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def writer : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0]
private def nested (l : Nat) (used : Bool) : Core.Value := .closure .word .word (if used then core else .var 0) [reader l]
private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
end ParsedRuntimeArgumentConstructionEntries
open ParsedRuntimeArgumentConstructionEntries
def frontendParsedRuntimeArgumentConstructionEntryTests : IO Unit := do
  let source ← parsed
  positive source (identity .word) (w 14) .word [] [] [] (w 14) 6
  positive source (identity .bool) (.bool false) .bool [] [] [] (.bool false) 6
  positive source (reader 0) (w 14) .word [.word,.word] [w 23,w 41] [w 23,w 41] (w 23) 8
  positive source (reader 1) (w 14) .word [.word,.word] [w 23,w 41] [w 23,w 41] (w 41) 8
  positive source writer (w 14) .word [.word] [w 23] [w 14] (w 14) 15
  positive source (nested 0 true) (w 14) .word [.word] [w 23] [w 23] (w 23) 13
  positive source allocator (w 14) (.cell .word) [.word] [w 23] [w 23,w 14] (.cellRef .word 1) 8
  let nominal : Core.Ty := .namedData ⟨91⟩
  let sumType := Core.Ty.sum .word nominal
  positive source (identity sumType) (.inLeft nominal (w 14)) sumType [] [] [] (.inLeft nominal (w 14)) 6
  rejected source (reader 0) (w 14) [.word] [] 7 (.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩)
  rejected source (reader 0) (w 14) [.word] [.bool true] 8 (.done (.bool true) [.bool true])
  rejected source writer (w 14) [.word] [.bool true] 15 (.done (w 14) [w 14])
  rejected source (nested 700 false) (w 14) [.word] [w 23] 6 (.done (w 14) [w 23])
  let forged : Core.Value := .closure .word .word (.bool false) []
  for raw in [forged,.closure .word .word (.var 0) [forged],.closure .word .word (.var 1) [],
      .hostFunction .storageRead,.closure .word .word (.var 0) [.hostFunction .storageRead],.constructed ⟨⟨91⟩,0⟩ .unit] do
    check (buildRuntimeArgument? raw |>.isNone) "same tag does not bypass body/capture/nominal evidence"
  check (decide (forged.type=(identity .word).type ∧ Core.runStateful 6 (.initial core [w 14,forged] [])=.done (.bool false) [])) "failed construction does not rewrite raw execution"
  check (decide (Core.runStateful 6 (.initial core [w 14,.closure .word .word (.var 0) [forged]] [])=.done (w 14) [])) "unexecuted invalid captured closure still prevents construction"
  let nf ← construct (identity nominal); let wx ← construct (w 14)
  let table : TypeNameTable := [(["F"],nf.1.type),(["X"],nominal),(["R"],nominal)]
  check (decide ((compileRecursiveComputationFunction? table owner source).map (fun p => (p.core,p.returnType))=some (core,nominal)) &&
    (prepareRecursiveComputationFunction? table owner source [nf.1,wx.1]).isNone &&
    (compileRecursiveComputationFunction? [(["F"],nf.1.type),(["X"],nominal)] owner source).isNone) "nominal construction/value-free typing does not erase actual argument or annotation gates"
end Tests

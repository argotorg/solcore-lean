import Solcore.Syntax.Parser.Function
import Solcore.Frontend.ComputationFunctionRuntimeSafetyProperties
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.FuelResumptionProperties

/-! Original mixed declarations and actual argument worlds are independent of
checking. Literal Core scripts fix observations before the runtime theorem. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationRuntimeSafetyEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"SafeEntries",by decide⟩],by decide⟩⟩,68⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-runtime-safety.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original declaration")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) ("complete original parse: "++text)
  check (decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span &&
    source.span.contains source.value.signature.span) "original file/header/body spans"
  return source
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Σ type, PLift (StructuralTypeDenotes types source type)) := do
  match shape : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "named fixture annotation")
private def parameters (types : TypeNameTable) (initial : LocalInputs) (ps : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Σ final, PLift (RuntimeParametersBindFrom types owner initial ps args final)) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨initial,⟨by rw [shape,supplied]; exact .nil⟩⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter ranges"
      let m ← meaning types annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let next ← parameters types (initial.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.1,⟨by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused next.2.down⟩⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "actual argument type")
  | _,_ => throw (IO.userError "parameter arity/profile")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (inputs : LocalTypeInputs) (source : Syntax.Expr) :
    IO (Static (RecursiveLocalComputationElaborates inputs.names inputs.context source)) := do
  match shape : source with
  | ⟨_,.identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | some id =>
          match typed : inputs.context.lookup? id, indexed : Resolved.LocalScope.index? inputs.context.ids id with
          | some type,some index => return ⟨.var index,type,by
              rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
                (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | _,_ => throw (IO.userError "original static row")
      | none => throw (IO.userError "original name")
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span) "original call spans"
      let f ← child inputs fn; let a ← child inputs arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [shape]; exact .application (ft ▸ f.evidence) (same ▸ a.evidence)⟩
          else throw (IO.userError "call argument")
      | _ => throw (IO.userError "callee")
  | _ => throw (IO.userError "fixture child shape")
termination_by sizeOf source
private def body (types : TypeNameTable) (inputs : LocalTypeInputs) (source : Syntax.Block) :
    IO (Static (RecursiveComputationReturnTreeElaborates types owner inputs source)) := do
  check (source.value.all fun statement => source.span.contains statement.span) "original statement ranges"
  match shape : source with
  | ⟨_,[⟨_,.returnStmt (some expression)⟩]⟩ =>
      let a ← child inputs expression; return ⟨a.core,a.type,by rw [shape]; exact .expression a.evidence⟩
  | ⟨_,[⟨innerSpan,.block statements⟩]⟩ =>
      let a ← body types inputs ⟨innerSpan,statements⟩; return ⟨a.core,a.type,by rw [shape]; exact .block a.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some initializer)⟩::rest⟩ =>
      if unused : name.value ∉ inputs.names.map Prod.fst then
        let a ← child inputs initializer
        let b ← body types (inputs.bindFresh owner name.value a.type) ⟨span,rest⟩
        match annotationShape : annotation with
        | none => return ⟨.letE a.core b.core,b.type,by rw [shape,annotationShape]; exact .inferred a.evidence b.evidence⟩
        | some annotation =>
            let m ← meaning types annotation
            if same : m.1=a.type then return ⟨.letE a.core b.core,b.type,by rw [shape,annotationShape]; exact .binding (same ▸ m.2.down) a.evidence b.evidence⟩
            else throw (IO.userError "initializer annotation")
      else throw (IO.userError "fresh original binding")
  | ⟨span,⟨_,.expression expression true⟩::rest⟩ =>
      let a ← child inputs expression; let b ← body types inputs ⟨span,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,by rw [shape]; exact .discard a.evidence b.evidence⟩
  | ⟨_,[⟨_,.ifThen condition yes (some no)⟩]⟩ =>
      let protection ← if h : computationBlockPreservesNames (inputs.names.map Prod.fst) yes=true then pure (PLift.up (computationBlockPreservesNames_iff.mp h)) else throw (IO.userError "original then scope")
      let c ← child inputs condition; let a ← body types inputs yes; let b ← body types inputs no
      if valid : c.type=.bool ∧ b.type=a.type then return ⟨.ifE c.core a.core b.core,a.type,
        by rw [shape]; exact .conditional (valid.1 ▸ c.evidence) protection.down a.evidence (valid.2 ▸ b.evidence)⟩
      else throw (IO.userError "whole guard/branch types")
  | _ => throw (IO.userError "original mixed body")
termination_by sizeOf source
private structure Path (core : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual lookup")
    | .letE head tail =>
        let a ← path n head env s; let b ← path n tail (a.value::env) a.final
        return ⟨b.value,b.final,a.cost+b.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (a.evidence _) (b.evidence _)⟩
    | .ifE condition yes no =>
        let c ← path n condition env s
        match decision : c.value with
        | .bool true => let a ← path n yes env c.final; return ⟨a.value,a.final,c.cost+a.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (decision ▸ c.evidence _) (a.evidence _)⟩
        | .bool false => let b ← path n no env c.final; return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (decision ▸ c.evidence _) (b.evidence _)⟩
        | _ => throw (IO.userError "manual Bool")
    | .apply fn arg =>
        let f ← path n fn env s; let a ← path n arg env f.final
        match fv : f.value with
        | .closure _ _ body captured =>
            let b ← path n body (a.value::captured) a.final
            return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ f.evidence _) (a.evidence _) (b.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .newCell .word (.var i) =>
        match found : env[i]? with
        | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
        | none => throw (IO.userError "allocation operand")
    | .loadCell (.var i) =>
        match found : env[i]? with
        | some (.cellRef t l) =>
            match read : s.read? l with
            | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
            | none => throw (IO.userError "manual read")
        | _ => throw (IO.userError "manual reference")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write")
        | _,_ => throw (IO.userError "manual store operands")
    | _ => throw (IO.userError "literal Core script")
private def header (types : TypeNameTable) (source : Syntax.FunctionDecl) (output : Core.Ty) :
    IO (PLift (RuntimeFunctionHeader types source.value.signature output)) := do
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.1=output then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          return ⟨⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same ▸ m.2.down)⟩⟩
        else throw (IO.userError "header profile")
      else throw (IO.userError "return meaning")
  | _ => throw (IO.userError "singleton return clause")
private def verify (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (output : Core.Ty) (core : Core.Expr)
    (world : Core.StoreTyping) (s final : Core.Store) (value : Core.Value) (cost : Nat)
    (typed : ∀ a ∈ args, Core.RuntimeValueHasType world a.value a.type) (stored : Core.StoreHasTypes world s) : IO PreparedRuntimeFunction := do
  let f::g::_ := args | throw (IO.userError "fixture arguments")
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],.word),(["Y"],.word),(["C"],.bool),(["R"],output)]
  let ps ← parameters types .empty source.value.signature.parameters.elements args
  let inputs := ps.1; let env := inputs.environment.values
  let b ← body types inputs.toTypeInputs source.value.body
  let manual ← path 100 core env s
  check (decide (env=args.reverse.map (·.value) ∧ inputs.ids=(List.range args.length).reverse.map (fun i => ⟨owner,i⟩))) "exact actual rows/reverse once"
  check (decide (manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independently fixed observations"
  if fixed : b.core=core ∧ b.type=output then
    let prepared : PreparedRuntimeFunction := ⟨inputs,core,output⟩
    let h ← header types source output
    have preparation : RecursiveComputationFunctionPrepares types owner source args prepared :=
      ⟨h.down,ps.2.down,by simpa only [fixed.1,fixed.2] using b.evidence⟩
    have safe := ComputationFunctionPrepares.runtime_typed_execution (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
      RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost
      RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
      elaborateRecursiveLocalComputation?_iff preparation typed stored
    have agreement : ∃ future, Core.WorldExtends world future ∧ Core.StoreHasTypes future manual.final ∧
        Core.RuntimeValueHasType future manual.value output ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names inputs.environment s source.value.body manual.value manual.final manual.cost := by
      obtain ⟨future,final,value,cost,ext,st,vt,raw,paths,_⟩ := safe.2
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique (manual.evidence [])
      exact ⟨future,ext,st,vt,raw⟩
    if grows : s.length < manual.final.length then
      have allocationExtends : ∃ future, Core.WorldExtends world future ∧
          world.length < future.length ∧ Core.StoreHasTypes future manual.final := by
        obtain ⟨future,ext,st,_,_⟩ := agreement
        exact ⟨future,ext,by simpa only [stored.length_eq,st.length_eq] using grows,st⟩
      have _ := allocationExtends
      check (decide (s.length < final.length)) "allocation grows the actual store and runtime world"
    match shape : core with
    | .letE initializer (.letE discarded tail) =>
        let a ← path 100 initializer env s
        let d ← path 100 discarded (a.value::env) a.final
        let first : Core.State := ⟨.ret a.value,[.letBody (.letE discarded tail) env],a.final⟩
        let second : Core.State := ⟨.ret d.value,[.letBody tail (a.value::env)],d.final⟩
        have firstPath : Core.Steps (a.cost+1) (.initial core env s) first := by
          rw [shape]; simpa [first,Core.State.initial,Nat.add_comm] using Core.Steps.cons Core.Transition.enterLet (a.evidence [.letBody (.letE discarded tail) env])
        have secondPath : Core.Steps (a.cost+d.cost+3) (.initial core env s) second := by
          rw [shape]
          simpa [second,Core.State.initial,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Core.Steps.cons Core.Transition.enterLet
            ((a.evidence [.letBody (.letE discarded tail) env]).trans (.cons .bindLet (.cons .enterLet (d.evidence [.letBody tail (a.value::env)]))))
        have _ := Core.runStateful_outOfFuel_complete firstPath (Core.advance_next_iff.mpr .bindLet)
        have _ := Core.runStateful_outOfFuel_complete secondPath (Core.advance_next_iff.mpr .bindLet)
        for (spent,cp) in [(a.cost+1,first),(a.cost+d.cost+3,second)] do
          check (decide (Core.runStateful spent (.initial core env s)=.outOfFuel cp ∧
            Core.runStateful (cost-spent) cp=.done value final)) "named binding and discard retain actual saved environment/store"
    | _ => throw (IO.userError "literal named/discard let checkpoints")
    have whole (fuel) : runRecursiveComputationFunction? types owner source args fuel s =
        some (output,Core.runStateful fuel (.initial core env s)) := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,runs⟩ := safe.2
      exact runs fuel
    have _ := safe.1
    for fuel in List.range (cost+2) do
      have _ := whole fuel
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (output,Core.runStateful fuel (.initial core env s)))) "full result including actual checkpoints"
      match exhausted : Core.runStateful fuel (.initial core env s) with
      | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact successful threshold"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel exhausted
          have _ := Core.runStateful_resume exhausted 3
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧ runRecursiveComputationFunction? types owner source args (fuel+3) s=some (output,Core.runStateful 3 cp))) "every genuine checkpoint fully resumes"
      | .fault _ _ => throw (IO.userError "world/store typed execution faulted")
    return prepared
  else throw (IO.userError "independent exact Core/type")
private def reader (location : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word location],.closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word)⟩
private def writer : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word))⟩
private def allocator : TypedRuntimeArgument := ⟨.function .word (.cell .word),.closure .word (.cell .word) (.newCell .word (.var 0)) [],.closure .nil (.newCell (.var rfl) .word)⟩
private def arg (n : Nat) : TypedRuntimeArgument := ⟨.word,w n,.word⟩
private def choice (b : Bool) : TypedRuntimeArgument := ⟨.bool,.bool b,.bool⟩
private theorem readerTyped {world : Core.StoreTyping} {location : Nat} (found : world[location]?=some .word) :
    Core.RuntimeValueHasType world (reader location).value (reader location).type := .closure (.cons (.cellRef found) .nil) (.loadCell (.var rfl) .word)
private theorem writerTyped {world : Core.StoreTyping} (found : world[0]?=some .word) :
    Core.RuntimeValueHasType world writer.value writer.type :=
  .closure (.cons (.cellRef found) .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word))
private theorem wordStore (n : Nat) : Core.StoreHasTypes [.word] [w n] :=
  Core.StoreHasTypes.nil.allocate .word .word
private theorem argumentsTyped {world : Core.StoreTyping} {f g : TypedRuntimeArgument}
    (ft : Core.RuntimeValueHasType world f.value f.type) (gt : Core.RuntimeValueHasType world g.value g.type) (x y : Nat) (c : Bool) :
    ∀ a ∈ [f,g,arg x,arg y,choice c], Core.RuntimeValueHasType world a.value a.type := by
  intro a member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl; exact ft; exact gt; exact .word; exact .word; exact .bool
end ParsedComputationRuntimeSafetyEntries
open ParsedComputationRuntimeSafetyEntries
def frontendParsedComputationRuntimeSafetyEntryTests : IO Unit := do
  let core := Core.Expr.letE (.apply (.var 4) (.var 2))
    (.letE (.apply (.var 4) (.var 2)) (.ifE (.var 2) (.var 1) (.apply (.var 6) (.var 3))))
  for annotated in [false,true] do
    let binding := if annotated then "let a:R=f(x);" else "let a=f(x);"
    let source ← parsed ("function safe(f:F,g:G,x:X,y:Y,c:C) returns(R){"++binding++"g(y);{if(c){return a;}else{return f(y);}}}")
    for c in [true,false] do
      let args := [reader 0,writer,arg 11,arg 14,choice c]
      let one ← verify source args .word core [.word] [w 23] [w 14] (w (if c then 23 else 14)) (if c then 31 else 38)
        (argumentsTyped (readerTyped rfl) (writerTyped rfl) 11 14 c) (wordStore 23)
      let two ← verify source args .word core [.word] [w 7] [w 14] (w (if c then 7 else 14)) (if c then 31 else 38)
        (argumentsTyped (readerTyped rfl) (writerTyped rfl) 11 14 c) (wordStore 7)
      let three ← verify source args .word core [.word,.word] [w 23,w 7] [w 14,w 7] (w (if c then 23 else 14)) (if c then 31 else 38)
        (argumentsTyped (readerTyped rfl) (writerTyped rfl) 11 14 c) ((wordStore 23).allocate .word .word)
      check (decide (one.core=two.core ∧ one.returnType=two.returnType ∧
        one.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=two.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)) ∧
        one.core=three.core ∧ one.returnType=three.returnType ∧
        one.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=three.inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)))) "same prepared fields with distinct typed stores/worlds"
      discard <| verify source [writer,reader 0,arg 11,arg 14,choice c] .word core [.word] [w 23] [w (if c then 11 else 14)] (w (if c then 11 else 14)) (if c then 31 else 45)
        (argumentsTyped (writerTyped rfl) (readerTyped rfl) 11 14 c) (wordStore 23)
      discard <| verify source [reader 1,writer,arg 11,arg 14,choice c] .word core [.word,.word] [w 23,w 7] [w 14,w 7] (w 7) (if c then 31 else 38)
        (argumentsTyped (readerTyped rfl) (writerTyped rfl) 11 14 c) ((wordStore 23).allocate .word .word)
      discard <| verify source [allocator,writer,arg 11,arg 14,choice c] (.cell .word) core [.word] [w 23]
        (if c then [w 14,w 11] else [w 14,w 11,w 14]) (.cellRef .word (if c then 1 else 2)) (if c then 31 else 38)
        (argumentsTyped (.closure .nil (.newCell (.var rfl) .word)) (writerTyped rfl) 11 14 c) (wordStore 23)

end Tests

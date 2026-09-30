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
namespace RecursiveConditionalEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveConditionalEntries",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-conditional-entries.sol"⟩,text⟩
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
  | _ => throw (IO.userError "outside named fixture")
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
private structure Static (s : LocalTypeInputs) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : RecursiveLocalComputationElaborates s.names s.context source core type
private def branch (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Static s source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id with
          | some t,some i => return ⟨.var i,t,by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
          | _,_ => throw (IO.userError "original static row missing")
      | none => throw (IO.userError "original static name missing")
  | ⟨_,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (source.span.contains fn.span && source.span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte≤argsSpan.startByte)) "unselected branch original call ranges"
      let f ← branch s fn; let a ← branch s arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then return ⟨.apply f.core a.core,output,by rw [original]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration)⟩
          else throw (IO.userError "static branch argument differs")
      | _ => throw (IO.userError "static branch function differs")
  | _ => throw (IO.userError "outside independent static branch")
termination_by sizeOf source
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.group inner⟩ =>
      check (source.span.contains inner.span) "original group span"
      let a ← child s env store inner
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .group a.elaboration,by rw [original]; exact .group a.raw⟩
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
  | ⟨_,.conditional condition question yes colon no⟩ =>
      check (source.span.contains question && source.span.contains colon && source.span.contains condition.span && source.span.contains yes.span && source.span.contains no.span &&
        decide (condition.span.endByte≤question.startByte ∧ question.endByte≤yes.span.startByte ∧ yes.span.endByte≤colon.startByte ∧ colon.endByte≤no.span.startByte)) "original question/colon and three child order"
      let c ← child s env store condition; let a ← branch s yes; let b ← branch s no
      if typed : c.type=.bool ∧ b.type=a.type then
        have el : RecursiveLocalComputationElaborates s.names s.context source (.ifE c.core a.core b.core) a.type := by
          rw [original]; exact .conditional (typed.1 ▸ c.elaboration) a.elaboration (typed.2 ▸ b.elaboration)
        match cv : c.value with
        | .bool true =>
            let selected ← child s env c.final yes
            return ⟨.ifE c.core a.core b.core,a.type,selected.value,selected.final,c.cost+selected.cost+2,el,by rw [original]; exact .ifTrue (cv ▸ c.raw) selected.raw⟩
        | .bool false =>
            let selected ← child s env c.final no
            return ⟨.ifE c.core a.core b.core,a.type,selected.value,selected.final,c.cost+selected.cost+2,el,by rw [original]; exact .ifFalse (cv ▸ c.raw) selected.raw⟩
        | _ => throw (IO.userError "actual guard has no successful raw cost")
      else throw (IO.userError "static conditional types differ")
  | ⟨_,.identifier name⟩ =>
      let e ← branch s source
      match named : s.names.lookup? name.value with
      | some id =>
          match actual : env.lookup? id with
          | some v => return ⟨e.core,e.type,v,store,1,e.elaboration,by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | none => throw (IO.userError "original actual row missing")
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
private def bodySource (body : String) : IO Syntax.FunctionDecl := parsed ("function conditional(f:F,g:G,x:X,y:Y) returns(R){"++body++"}")
private def verify (source : Syntax.FunctionDecl) (f g x y : TypedRuntimeArgument) (output : Core.Ty) (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO PreparedRuntimeFunction := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["Y"],y.type),(["R"],output),(["Word"],.word)]
  let args := [f,g,x,y]; let ps ← parameters types .empty .empty source.value.signature.parameters.elements args
  let inputs := ps.actual; let env := inputs.environment.values
  let h ← header types source output; let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body
  let manual ← path 100 core env s
  have erased : inputs.toTypeInputs=ps.statics := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  check (decide (env=[y.value,x.value,g.value,f.value] ∧ inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("y",⟨owner,3⟩,y.type,y.value),("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original actual rows/reverse once"
  check (decide (b.value=value ∧ b.final=final ∧ b.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent raw/Core value/store/cost"
  if fixed : b.core=core ∧ b.type=output then
    let compiled : CompiledRuntimeFunction := ⟨ps.statics,core,output⟩; let prepared : PreparedRuntimeFunction := ⟨inputs,core,output⟩
    have preparation : RecursiveComputationFunctionPrepares types owner source args prepared :=
      ⟨h.down,ps.bound,by simpa only [fixed.1,fixed.2] using b.elaboration⟩
    have compilation : RecursiveComputationFunctionCompiles types owner source compiled :=
      ⟨h.down,ps.declared,by simpa only [compiled,prepared,erased] using preparation.body⟩
    have compiledSome := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
    have preparedSome := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr preparation
    have matching : args.map (·.type)=ps.statics.context.values.reverse := by
      have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
      simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
    have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some compiled := by
      rw [prepareComputationFunction?_factorization,compiledSome]; simp only [compiled,bind,Option.bind_some,matching,↓reduceIte]
    have whole (fuel) (store) : runRecursiveComputationFunction? types owner source args fuel store =
        some (output,Core.runStateful fuel (.initial core [y.value,x.value,g.value,f.value] store)) := by
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
private def guardReader : TypedRuntimeArgument := ⟨.function .bool .bool,.closure .bool .bool (.loadCell (.var 1)) [.cellRef .bool 0],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def guardWriter : TypedRuntimeArgument := ⟨.function .bool .bool,.closure .bool .bool (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .bool 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def writer : TypedRuntimeArgument := ⟨.function .bool .word,.closure .bool .word (.letE (.storeCell (.var 1) (.var 2)) (.loadCell (.var 2))) [.cellRef .word 1,w 14],
  .closure (.cons .cellRef (.cons .word .nil)) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
end RecursiveConditionalEntries
open RecursiveConditionalEntries
def frontendParsedRecursiveConditionalFunctionEntryTests : IO Unit := do
  let x : TypedRuntimeArgument := ⟨.bool,.bool true,.bool⟩; let y : TypedRuntimeArgument := ⟨.word,w 23,.word⟩
  let call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
  let core := Core.Expr.ifE (call 3 1) (call 2 1) (.var 0)
  let source ← bodySource "return f(x)?g(x):y;"
  let prepared ← verify source guardReader writer x y .word core [.bool true,w 99] [.bool true,w 14] (w 14) 25
  discard <| verify source guardReader writer x y .word core [.bool false,w 99] [.bool false,w 99] (w 23) 11
  discard <| verify source guardReader writer x y .word core [.bool false] [.bool false] (w 23) 11
  for choice in [false,true] do
    let arg : TypedRuntimeArgument := ⟨.bool,.bool choice,.bool⟩
    discard <| verify source guardWriter writer arg y .word core [.bool (!choice),w 99] [.bool choice,if choice then w 14 else w 99] (if choice then w 14 else w 23) (if choice then 32 else 18)
  let alternate : TypedRuntimeArgument := ⟨writer.type,.closure .bool .word (.letE (.storeCell (.var 1) (.var 2)) (.loadCell (.var 2))) [.cellRef .word 1,w 23],.closure (.cons .cellRef (.cons .word .nil)) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
  for choice in [false,true] do
    let selected := if choice then writer.value else alternate.value; let word := if choice then w 14 else w 23
    discard <| verify (← bodySource "return f(x)?g:y;") guardReader writer x alternate writer.type (.ifE (call 3 1) (.var 2) (.var 0)) [.bool choice] [.bool choice] selected 11
    discard <| verify (← bodySource "return (f(x)?g:y)(x);") guardReader writer x alternate .word (.apply (.ifE (call 3 1) (.var 2) (.var 0)) (.var 1)) [.bool choice,w 99] [.bool choice,word] word 25
  let env := prepared.inputs.environment.values
  let types : TypeNameTable := [(["F"],guardReader.type),(["G"],writer.type),(["X"],.bool),(["Y"],.word),(["R"],.word),(["Word"],.word)]
  let run := runRecursiveComputationFunction? types owner source [guardReader,writer,x,y]
  let frames := [Core.Frame.ifBranches (call 2 1) (.var 0) env]
  for choice in [false,true] do
    let store := [.bool choice,w 99]; let cp : Core.State := ⟨.ret (.bool choice),frames,store⟩
    let selected : Core.State := ⟨.eval (if choice then call 2 1 else .var 0) env,[],store⟩
    check (decide (run 9 store=some (.word,.outOfFuel cp) ∧ run 10 store=some (.word,.outOfFuel selected) ∧ Core.runStateful 1 cp=.outOfFuel selected)) "genuine ifBranches and exact selection after resumption"
  let wrong := Core.StatefulRunResult.fault (.expectedBool (w 99)) ⟨.ret (w 99),frames,[w 99,w 23]⟩
  let wrongCp : Core.State := ⟨.ret (.cellRef .bool 0),.loadCellApply::frames,[w 99,w 23]⟩
  let empty := Core.StatefulRunResult.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .bool 0),.loadCellApply::frames,[]⟩
  let emptyCp : Core.State := ⟨.eval (.var 1) env,.applyClosure .bool .bool (.loadCell (.var 1)) [.cellRef .bool 0]::frames,[]⟩
  let selectedEnv := [.bool true,.cellRef .word 1,w 14]
  let selectedFrames := [Core.Frame.storeCellValue (.var 2) selectedEnv,.letBody (.loadCell (.var 2)) selectedEnv]
  let branchFault := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),selectedFrames,[.bool true]⟩
  let branchCp : Core.State := ⟨.eval (.var 1) selectedEnv,selectedFrames,[.bool true]⟩
  check (decide (run 8 [w 99,w 23]=some (.word,.outOfFuel wrongCp) ∧ run 9 [w 99,w 23]=some (.word,wrong) ∧ Core.runStateful 1 wrongCp=wrong ∧ run 4 []=some (.word,.outOfFuel emptyCp) ∧ run 8 []=some (.word,empty) ∧ Core.runStateful 4 emptyCp=empty)) "wrong or missing guard blocks both branches"
  check (decide (run 17 [.bool true]=some (.word,.outOfFuel branchCp) ∧ run 18 [.bool true]=some (.word,branchFault) ∧ Core.runStateful 1 branchCp=branchFault ∧ run 11 [.bool false]=some (.word,.done (w 23) [.bool false]))) "selected branch fault versus unselected missing-cell success"
  let effectCp : Core.State := ⟨.ret (.bool true),[.ifBranches (call 2 1) (.var 0) [y.value,x.value,writer.value,guardWriter.value]],[.bool true]⟩
  check (decide (runRecursiveComputationFunction? types owner source [guardWriter,writer,x,y] 16 [.bool false]=some (.word,.outOfFuel effectCp) ∧ runRecursiveComputationFunction? types owner source [guardWriter,writer,x,y] 25 [.bool false]=some (.word,branchFault) ∧ Core.runStateful 9 effectCp=branchFault)) "guard update survives resumed selected-branch fault"
  for s in [[.bool true,w 99],[.bool false],[w 99,w 23],[],[.bool true]] do
    for fuel in List.range 34 do
      check (decide (run fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "same prepared record full values/stores/fault tags"
      match exhausted : Core.runStateful fuel (.initial core env s) with
      | .outOfFuel cp =>
          have _ := Core.runStateful_resume exhausted 40
          check (decide (run (fuel+40) s=some (.word,Core.runStateful 40 cp))) "all genuine residual states resume whole outcomes"
      | _ => pure ()
  for body in ["return f(x)?g(x):missing;","return f(x)?g(x):x;","return y?g(x):y;"] do
    let bad ← bodySource body
    check (decide (compileRecursiveComputationFunction? types owner bad=none ∧ prepareRecursiveComputationFunction? types owner bad [guardReader,writer,x,y]=none ∧ runRecursiveComputationFunction? types owner bad [guardReader,writer,x,y] 50 [.bool true,w 99]=none)) "whole unselected-name/branch-type/guard-type gates"
  let wrongReturn ← parsed "function conditional(f:F,g:G,x:X,y:Y) returns(X){return f(x)?g(x):y;}"
  check (decide (elaborateRecursiveComputationReturnTree? types owner prepared.inputs.toTypeInputs wrongReturn.value.body=some (core,.word) ∧ compileRecursiveComputationFunction? types owner wrongReturn=none)) "independent Word body versus declared Bool"
end Tests

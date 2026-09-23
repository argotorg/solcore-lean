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
namespace RecursiveLazyEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveLazyEntries",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-lazy-entries.sol"⟩,text⟩
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
    | .bool b => return ⟨.bool b,s,1,fun _ => by rw [original]; exact .cons .bool .refl⟩
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
  | ⟨_,.binary left ⟨opSpan,op⟩ right⟩ =>
      check (source.span.contains left.span && source.span.contains right.span && source.span.contains opSpan &&
        decide (left.span.endByte≤opSpan.startByte ∧ opSpan.endByte≤right.span.startByte)) "original logical children/operator order"
      let l ← child s env store left; let r ← branch s right
      if typed : l.type=.bool ∧ r.type=.bool then
        match which : op with
        | .logicalAnd =>
            have el : RecursiveLocalComputationElaborates s.names s.context source (.ifE l.core r.core (.bool false)) .bool := by
              rw [original,which]; exact .logicalAnd (typed.1 ▸ l.elaboration) (typed.2 ▸ r.elaboration)
            match actual : l.value with
            | .bool true =>
                let rhs ← child s env l.final right
                return ⟨.ifE l.core r.core (.bool false),.bool,rhs.value,rhs.final,l.cost+rhs.cost+2,el,by rw [original,which]; exact .andTrue (actual ▸ l.raw) rhs.raw⟩
            | .bool false => return ⟨.ifE l.core r.core (.bool false),.bool,.bool false,l.final,l.cost+3,el,by rw [original,which]; exact .andFalse (actual ▸ l.raw)⟩
            | _ => throw (IO.userError "non-Bool actual left")
        | .logicalOr =>
            have el : RecursiveLocalComputationElaborates s.names s.context source (.ifE l.core (.bool true) r.core) .bool := by
              rw [original,which]; exact .logicalOr (typed.1 ▸ l.elaboration) (typed.2 ▸ r.elaboration)
            match actual : l.value with
            | .bool true => return ⟨.ifE l.core (.bool true) r.core,.bool,.bool true,l.final,l.cost+3,el,by rw [original,which]; exact .orTrue (actual ▸ l.raw)⟩
            | .bool false =>
                let rhs ← child s env l.final right
                return ⟨.ifE l.core (.bool true) r.core,.bool,rhs.value,rhs.final,l.cost+rhs.cost+2,el,by rw [original,which]; exact .orFalse (actual ▸ l.raw) rhs.raw⟩
            | _ => throw (IO.userError "non-Bool actual left")
        | _ => throw (IO.userError "outside fixed lazy fixture")
      else throw (IO.userError "original logical operands are not Bool")
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
private def bodySource (body : String) : IO Syntax.FunctionDecl := parsed ("function lazy(f:F,g:G,x:X,y:Y) returns(R){"++body++"}")
private def verify (source : Syntax.FunctionDecl) (f g x y : TypedRuntimeArgument) (output : Core.Ty) (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO PreparedRuntimeFunction := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["Y"],y.type),(["R"],output),(["Word"],.word)]
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
private def reader : TypedRuntimeArgument := ⟨.function .bool .bool,.closure .bool .bool (.loadCell (.var 1)) [.cellRef .bool 1],.closure (.cons .cellRef .nil) (.loadCell (.var rfl) .bool)⟩
private def writer (location : Nat) : TypedRuntimeArgument := ⟨.function .bool .bool,.closure .bool .bool (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .bool location],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) .bool) (.loadCell (.var rfl) .bool))⟩
private def arg (value : Bool) : TypedRuntimeArgument := ⟨.bool,.bool value,.bool⟩
end RecursiveLazyEntries
open RecursiveLazyEntries
def frontendParsedRecursiveLazyFunctionEntryTests : IO Unit := do
  let left := Core.Expr.apply (.var 3) (.var 1); let right := Core.Expr.apply (.var 2) (.var 0)
  let f := writer 0; let g := writer 1
  for disjunction in [false,true] do
    let source ← bodySource (if disjunction then "return f(x) || g(y);" else "return f(x) && g(y);"); let core := if disjunction then Core.Expr.ifE left (.bool true) right else .ifE left right (.bool false)
    for flag in [false,true] do
      let selected := flag != disjunction; let x := arg flag
      for rhs in [false,true] do
        discard <| verify source f g x (arg rhs) .bool core [.bool (!flag),.bool (!rhs)] [.bool flag,.bool (if selected then rhs else !rhs)] (.bool (if selected then rhs else flag)) (if selected then 32 else 18)
      discard <| verify source f reader x (arg false) .bool core [.bool (!flag),w 23] [.bool flag,w 23] (if selected then w 23 else .bool flag) (if selected then 25 else 18)
      unless selected do
        discard <| verify source f reader x (arg false) .bool core [.bool (!flag)] [.bool flag] (.bool flag) 18
    let selected := !disjunction
    discard <| verify source g f (arg selected) (arg disjunction) .bool core [.bool disjunction,.bool selected] [.bool disjunction,.bool selected] (.bool disjunction) 32
  let source ← bodySource "return f(x) && g(y);"; let core := Core.Expr.ifE left right (.bool false)
  let x := arg true; let y := arg false
  let prepared ← verify source f reader x y .bool core [.bool false,w 23] [.bool true,w 23] (w 23) 25
  let env := prepared.inputs.environment.values
  let types : TypeNameTable := [(["F"],f.type),(["G"],reader.type),(["X"],.bool),(["Y"],.bool),(["R"],.bool),(["Word"],.word)]
  let run := runRecursiveComputationFunction? types owner source [f,reader,x,y]
  let frames := [Core.Frame.ifBranches right (.bool false) env]
  let cp : Core.State := ⟨.ret (.bool true),frames,[.bool true,w 23]⟩
  check (decide (run 16 [.bool false,w 23]=some (.bool,.outOfFuel cp) ∧ Core.runStateful 9 cp=.done (w 23) [.bool true,w 23] ∧ run 25 [.bool false,w 23]=some (.bool,.done (w 23) [.bool true,w 23]))) "actual Word RHS success retains Bool entry tag after genuine ifBranches"
  let rightEnv := [y.value,.cellRef .bool 1]
  let missingCp : Core.State := ⟨.eval (.var 1) rightEnv,[.loadCellApply],[.bool true]⟩
  let missing := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .bool 1),[.loadCellApply],[.bool true]⟩
  check (decide (run 23 [.bool false]=some (.bool,.outOfFuel missingCp) ∧ run 24 [.bool false]=some (.bool,missing) ∧ Core.runStateful 1 missingCp=missing ∧ runRecursiveComputationFunction? types owner source [f,reader,arg false,y] 18 [.bool true]=some (.bool,.done (.bool false) [.bool false]))) "selected missing RHS versus skipped missing RHS preserves left update"
  let badLeft : TypedRuntimeArgument := ⟨f.type,.closure .bool .bool (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 3))) [.cellRef .bool 0,.cellRef .bool 2],
    .closure (.cons .cellRef (.cons .cellRef .nil)) (.letE (.storeCell (.var rfl) (.var rfl) .bool) (.loadCell (.var rfl) .bool))⟩
  let badEnv := [(arg true).value,x.value,g.value,badLeft.value]
  let badFrames := [Core.Frame.ifBranches right (.bool false) badEnv]; let updated := [.bool true,.bool false,w 99]
  let badCp : Core.State := ⟨.ret (.cellRef .bool 2),.loadCellApply::badFrames,updated⟩
  let bad := Core.StatefulRunResult.fault (.expectedBool (w 99)) ⟨.ret (w 99),badFrames,updated⟩
  check (decide (runRecursiveComputationFunction? types owner source [badLeft,g,x,arg true] 15 [.bool false,.bool false,w 99]=some (.bool,.outOfFuel badCp) ∧ runRecursiveComputationFunction? types owner source [badLeft,g,x,arg true] 16 [.bool false,.bool false,w 99]=some (.bool,bad) ∧ Core.runStateful 1 badCp=bad)) "non-Bool left preserves left effects and never executes right writer"
  for store in [[.bool false,w 23],[.bool false,.bool true],[.bool false],[]] do
    for fuel in List.range 34 do
      check (decide (run fuel store=some (.bool,Core.runStateful fuel (.initial core env store)))) "same prepared record retains arbitrary stores and whole tag"
      match exhausted : Core.runStateful fuel (.initial core env store) with
      | .outOfFuel residual =>
          have _ := Core.runStateful_resume exhausted 40
          check (decide (run (fuel+40) store=some (.bool,Core.runStateful 40 residual))) "all genuine checkpoints resume full outcomes"
      | _ => pure ()
  for body in ["return f(x) && missing;","return f(x) || missing;","return f(x) && 1;","return 1 || g(y);"] do
    let bad ← bodySource body
    check (decide (compileRecursiveComputationFunction? types owner bad=none ∧ prepareRecursiveComputationFunction? types owner bad [f,reader,x,y]=none ∧ runRecursiveComputationFunction? types owner bad [f,reader,x,y] 50 [.bool false,w 23]=none)) "whole unselected-name and logical operand type gates"
  let wrongReturn ← parsed "function lazy(f:F,g:G,x:X,y:Y) returns(Word){return f(x) && g(y);}"
  check (decide (elaborateRecursiveComputationReturnTree? types owner prepared.inputs.toTypeInputs wrongReturn.value.body=some (core,.bool) ∧ compileRecursiveComputationFunction? types owner wrongReturn=none)) "original Bool body versus declared Word"
end Tests

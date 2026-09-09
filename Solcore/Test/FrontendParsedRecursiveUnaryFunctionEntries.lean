import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.ComputationFunctionFactorizationProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Frontend.RuntimeComputationFunctionFactorizationProperties
import Solcore.Core.FuelResumptionProperties
/-! Independent original declaration certificates and manual paths retain actual captures, stores and whole results. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace RecursiveUnaryEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveUnaryEntries",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-unary-entries.sol"⟩,text⟩
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
    | .unary op operand =>
        let a ← path n operand env s
        match applied : op.apply a.value with
        | some value => return ⟨value,a.final,a.cost+2,fun _ => by rw [original]; exact CostStepComposition.unary (a.evidence _) applied⟩
        | none => throw (IO.userError "manual unary payload")
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
  | _ => throw (IO.userError "outside independent static identifier")
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
  | ⟨_,.unary ⟨opSpan,.logicalNot⟩ operand⟩ =>
      check (source.span.contains opSpan && source.span.contains operand.span && decide (opSpan.endByte≤operand.span.startByte)) "original ! prefix/operand ranges"
      let a ← child s env store operand
      if typed : a.type=.bool then
        match actual : a.value with
        | .bool b => return ⟨.unary .boolNot a.core,.bool,.bool (!b),a.final,a.cost+2,
            by rw [original]; exact .logicalNot (typed ▸ a.elaboration),by rw [original]; exact .logicalNot (actual ▸ a.raw)⟩
        | _ => throw (IO.userError "wrong actual ! payload")
      else throw (IO.userError "wrong original ! type")
  | ⟨_,.unary ⟨opSpan,.bitNot⟩ operand⟩ =>
      check (source.span.contains opSpan && source.span.contains operand.span && decide (opSpan.endByte≤operand.span.startByte)) "original ~ prefix/operand ranges"
      let a ← child s env store operand
      if typed : a.type=.word then
        match actual : a.value with
        | .word v => return ⟨.unary .wordNot a.core,.word,.word v.bitNot,a.final,a.cost+2,
            by rw [original]; exact .bitNot (typed ▸ a.elaboration),by rw [original]; exact .bitNot (actual ▸ a.raw)⟩
        | _ => throw (IO.userError "wrong actual ~ payload")
      else throw (IO.userError "wrong original ~ type")
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
private def bodySource (body : String) : IO Syntax.FunctionDecl := parsed ("function unary(f:F,g:G,x:X,y:Y) returns(R){"++body++"}")
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
private def reader (t : Core.Ty) (payload : Core.CellPayload t) (location : Nat) : TypedRuntimeArgument :=
  ⟨.function t t,.closure t t (.loadCell (.var 1)) [.cellRef t location],.closure (.cons .cellRef .nil) (.loadCell (.var rfl) payload)⟩
private def writer (t : Core.Ty) (payload : Core.CellPayload t) (location : Nat) : TypedRuntimeArgument :=
  ⟨.function t t,.closure t t (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef t location],
    .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) payload) (.loadCell (.var rfl) payload))⟩
end RecursiveUnaryEntries
open RecursiveUnaryEntries
def frontendParsedRecursiveUnaryFunctionEntryTests : IO Unit := do
  let f := reader .word .word 0; let g := writer .word .word 1
  let x : TypedRuntimeArgument := ⟨.word,w 14,.word⟩; let y : TypedRuntimeArgument := ⟨.bool,.bool false,.bool⟩
  let inner := Core.Expr.apply (.var 3) (.apply (.var 2) (.var 1))
  let core := Core.Expr.unary .wordNot inner
  let source ← bodySource "return ~f(g(x));"
  let prepared ← verify source f g x y .word core [w 23,w 99] [w 23,w 14] (.word (Core.Word.ofNatModulo 23).bitNot) 24
  for value in [Core.Word.zero,Core.Word.maximum,Core.Word.ofNatModulo 47] do
    discard <| verify source f g x y .word core [.word value,w 99] [.word value,w 14] (.word value.bitNot) 24
    discard <| verify (← bodySource "return ~~f(g(x));") f g x y .word (.unary .wordNot core) [.word value,w 99] [.word value,w 14] (.word value.bitNot.bitNot) 26
  discard <| verify source (reader .word .word 1) g x y .word core [w 23,w 99] [w 23,w 14] (.word (Core.Word.ofNatModulo 14).bitNot) 24
  discard <| verify source g f x y .word core [w 23,w 99] [w 23,w 23] (.word (Core.Word.ofNatModulo 23).bitNot) 24
  for flag in [false,true] do
    let arg : TypedRuntimeArgument := ⟨.bool,.bool (!flag),.bool⟩
    let bf := reader .bool .bool 0; let bg := writer .bool .bool 1
    discard <| verify (← bodySource "return !f(g(x));") bf bg arg y .bool (.unary .boolNot inner) [.bool flag,.bool flag] [.bool flag,.bool (!flag)] (.bool (!flag)) 24
    discard <| verify (← bodySource "return !!(f(g(x)));") bf bg arg y .bool (.unary .boolNot (.unary .boolNot inner)) [.bool flag,.bool flag] [.bool flag,.bool (!flag)] (.bool flag) 26
  let env := prepared.inputs.environment.values
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["Y"],y.type),(["R"],.word),(["Word"],.word)]
  let run := runRecursiveComputationFunction? types owner source [f,g,x,y]
  let updated := [w 23,w 14]; let wrongStore := [.bool true,w 14]
  let cp : Core.State := ⟨.ret (w 23),[.unaryApply .wordNot],updated⟩
  let wrong := Core.StatefulRunResult.fault (.invalidUnaryOperand .wordNot (.bool true)) ⟨.ret (.bool true),[.unaryApply .wordNot],wrongStore⟩
  let wrongCp : Core.State := ⟨.ret (.cellRef .word 0),[.loadCellApply,.unaryApply .wordNot],wrongStore⟩
  check (decide (run 23 [w 23,w 99]=some (.word,.outOfFuel cp) ∧ run 24 [w 23,w 99]=some (.word,.done (.word (Core.Word.ofNatModulo 23).bitNot) updated) ∧ Core.runStateful 1 cp=.done (.word (Core.Word.ofNatModulo 23).bitNot) updated)) "genuine unaryApply and one remaining transition"
  check (decide (run 22 [.bool true,w 99]=some (.word,.outOfFuel wrongCp) ∧ run 23 [.bool true,w 99]=some (.word,wrong) ∧ Core.runStateful 1 wrongCp=wrong)) "operand effects survive exact wrong-payload fault"
  let gEnv := [x.value,.cellRef .word 1]
  let suspended := [Core.Frame.storeCellValue (.var 0) gEnv,.letBody (.loadCell (.var 2)) gEnv,.applyClosure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.unaryApply .wordNot]
  let missing := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),suspended,[]⟩
  let missingCp : Core.State := ⟨.eval (.var 1) gEnv,suspended,[]⟩
  check (decide (run 11 []=some (.word,.outOfFuel missingCp) ∧ run 12 []=some (.word,missing) ∧ Core.runStateful 1 missingCp=missing)) "child missing-cell fault precedes unary application"
  let absentReader := reader .word .word 2
  let lateCp : Core.State := ⟨.eval (.var 1) [x.value,.cellRef .word 2],[.loadCellApply,.unaryApply .wordNot],updated⟩
  let late := Core.StatefulRunResult.fault (.invalidCellLocation 2) ⟨.ret (.cellRef .word 2),[.loadCellApply,.unaryApply .wordNot],updated⟩
  check (decide (runRecursiveComputationFunction? types owner source [absentReader,g,x,y] 21 [w 23,w 99]=some (.word,.outOfFuel lateCp) ∧ runRecursiveComputationFunction? types owner source [absentReader,g,x,y] 22 [w 23,w 99]=some (.word,late) ∧ Core.runStateful 1 lateCp=late)) "actual capture missing after argument effects keeps updated store"
  let boolSource ← bodySource "return !f(g(x));"
  let bf := reader .bool .bool 0; let bg := writer .bool .bool 1; let bx : TypedRuntimeArgument := ⟨.bool,.bool true,.bool⟩
  let bt : TypeNameTable := [(["F"],bf.type),(["G"],bg.type),(["X"],.bool),(["Y"],.bool),(["R"],.bool)]
  let boolCp : Core.State := ⟨.ret (.cellRef .bool 0),[.loadCellApply,.unaryApply .boolNot],[w 99,.bool true]⟩
  let boolFault := Core.StatefulRunResult.fault (.invalidUnaryOperand .boolNot (w 99)) ⟨.ret (w 99),[.unaryApply .boolNot],[w 99,.bool true]⟩
  check (decide (runRecursiveComputationFunction? bt owner boolSource [bf,bg,bx,y] 22 [w 99,.bool false]=some (.bool,.outOfFuel boolCp) ∧ runRecursiveComputationFunction? bt owner boolSource [bf,bg,bx,y] 23 [w 99,.bool false]=some (.bool,boolFault) ∧ Core.runStateful 1 boolCp=boolFault)) "Bool entry tag and prior effects survive actual Word payload"
  for store in [[w 23,w 99],[.bool true,w 99],[],[w 23]] do
    for fuel in List.range 27 do
      check (decide (run fuel store=some (.word,Core.runStateful fuel (.initial core env store)))) "same prepared Word/Bool/empty store preserves whole return tag"
      match exhausted : Core.runStateful fuel (.initial core env store) with
      | .outOfFuel residual =>
          have _ := Core.runStateful_resume exhausted 30
          check (decide (run (fuel+30) store=some (.word,Core.runStateful 30 residual))) "every genuine checkpoint resumes exact whole outcome"
      | _ => pure ()
  for body in ["return !f(g(x));","return ~y;","return ~missing;"] do
    let bad ← bodySource body
    check (decide (compileRecursiveComputationFunction? types owner bad=none ∧ prepareRecursiveComputationFunction? types owner bad [f,g,x,y]=none ∧ runRecursiveComputationFunction? types owner bad [f,g,x,y] 40 [w 23,w 99]=none)) "whole unary operand type/name gates"
  let wrongReturn ← parsed "function unary(f:F,g:G,x:X,y:Y) returns(Y){return ~f(g(x));}"
  check (decide (elaborateRecursiveComputationReturnTree? types owner prepared.inputs.toTypeInputs wrongReturn.value.body=some (core,.word) ∧ compileRecursiveComputationFunction? types owner wrongReturn=none)) "original Word body versus declared Bool"
end Tests

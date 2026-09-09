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
namespace RecursiveNegatedComparisonEntries
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveNegatedComparisonEntries",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"recursive-negated-comparison-entries.sol"⟩,text⟩
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
        | some v => return ⟨v,a.final,a.cost+2,fun _ => by rw [original]; exact CostStepComposition.unary (a.evidence _) applied⟩
        | none => throw (IO.userError "manual unary shape")
    | .binary op left right =>
        let a ← path n left env s; let b ← path n right env a.final
        match applied : op.apply a.value b.value with
        | some v => return ⟨v,b.final,a.cost+b.cost+3,fun _ => by rw [original]; exact CostStepComposition.binary (a.evidence _) (b.evidence _) applied⟩
        | none => throw (IO.userError "manual binary shape")
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
        decide (left.span.endByte≤opSpan.startByte ∧ opSpan.endByte≤right.span.startByte)) "original comparison child/operator order"
      let l ← child s env store left; let r ← child s env l.final right
      if typed : l.type=.word ∧ r.type=.word then
        match lv : l.value, rv : r.value with
        | .word a,.word b =>
            match which : op with
            | .notEqual => return ⟨.unary .boolNot (.binary .wordEq l.core r.core),.bool,.bool (!(a==b)),r.final,l.cost+r.cost+5,
                by rw [original,which]; exact .notEqual (typed.1 ▸ l.elaboration) (typed.2 ▸ r.elaboration),
                by rw [original,which]; exact .notEqual (lv ▸ l.raw) (rv ▸ r.raw)⟩
            | .lessEqual => return ⟨.unary .boolNot (.binary .wordGt l.core r.core),.bool,.bool (!(decide (a>b))),r.final,l.cost+r.cost+5,
                by rw [original,which]; exact .lessEqual (typed.1 ▸ l.elaboration) (typed.2 ▸ r.elaboration),
                by rw [original,which]; exact .lessEqual (lv ▸ l.raw) (rv ▸ r.raw)⟩
            | _ => throw (IO.userError "outside two negated comparisons")
        | _,_ => throw (IO.userError "actual comparison operands are not Word")
      else throw (IO.userError "original comparison operands are not Word")
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id, actual : env.lookup? id with
          | some t,some i,some v => return ⟨.var i,t,v,store,1,
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed)),
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | _,_,_ => throw (IO.userError "original row missing")
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
private def bodySource (body : String) : IO Syntax.FunctionDecl := parsed ("function comparison(f:F,g:G,x:X,y:Y) returns(R){"++body++"}")
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
private def reader (location : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word location],.closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word)⟩
private def writer (location : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word location],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word))⟩
private def arg (value : Nat) : TypedRuntimeArgument := ⟨.word,w value,.word⟩
end RecursiveNegatedComparisonEntries
open RecursiveNegatedComparisonEntries
def frontendParsedRecursiveNegatedComparisonEntryTests : IO Unit := do
  let left := Core.Expr.apply (.var 3) (.var 1); let right := Core.Expr.apply (.var 2) (.var 0)
  let f := reader 0; let g := writer 0; let x := arg 11; let y := arg 14
  for le in [false,true] do
    let source ← bodySource (if le then "return f(x) <= g(y);" else "return f(x) != g(y);")
    let op := if le then Core.BinaryOp.wordGt else .wordEq
    let core := Core.Expr.unary .boolNot (.binary op left right)
    for (old,rhs) in [(23,14),(14,23),(14,14),(0,2^256-1),(2^256-1,0),(2^255,2^255),(2^256-1,2^255)] do
      discard <| verify source f g x (arg rhs) .bool core [w old] [w rhs] (.bool (if le then old≤rhs else old≠rhs)) 28
    discard <| verify source g f x y .bool core [w 23] [w 11] (.bool le) 28
    discard <| verify source (reader 1) g x y .bool core [w 23,w 7] [w 14,w 7] (.bool true) 28
    discard <| verify source g (reader 1) y x .bool core [w 23,w 7] [w 14,w 7] (.bool (!le)) 28
    discard <| verify source f g y x .bool core [w 23] [w 11] (.bool (!le)) 28
  let source ← bodySource "return f(x) != g(y);"
  let core := Core.Expr.unary .boolNot (.binary .wordEq left right)
  let prepared ← verify source f g x y .bool core [w 23] [w 14] (.bool true) 28
  let env := prepared.inputs.environment.values
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],.word),(["Y"],.word),(["R"],.bool),(["Word"],.word)]
  let run := runRecursiveComputationFunction? types owner source [f,g,x,y]
  let unary : List Core.Frame := [.unaryApply .boolNot]
  let between : Core.State := ⟨.ret (w 23),.binaryRight .wordEq right env::unary,[w 23]⟩
  let last : Core.State := ⟨.ret (w 14),.binaryApply .wordEq (w 23)::unary,[w 14]⟩
  let negation : Core.State := ⟨.ret (.bool false),unary,[w 14]⟩
  check (decide (run 10 [w 23]=some (.bool,.outOfFuel between) ∧ run 26 [w 23]=some (.bool,.outOfFuel last) ∧ run 27 [w 23]=some (.bool,.outOfFuel negation) ∧ Core.runStateful 18 between=.done (.bool true) [w 14] ∧ Core.runStateful 2 last=.done (.bool true) [w 14] ∧ Core.runStateful 1 negation=.done (.bool true) [w 14])) "genuine binaryRight/binaryApply/unaryApply with original captures and intermediate store"
  let badState : Core.State := ⟨.ret (w 14),.binaryApply .wordEq (.bool true)::unary,[w 14]⟩
  let bad := Core.StatefulRunResult.fault (.invalidBinaryOperands .wordEq (.bool true) (w 14)) badState
  let badCp : Core.State := ⟨.ret (.cellRef .word 0),.loadCellApply::.binaryApply .wordEq (.bool true)::unary,[w 14]⟩
  let emptyCp : Core.State := ⟨.eval (.var 1) env,.applyClosure .word .word (.loadCell (.var 1)) [.cellRef .word 0]::.binaryRight .wordEq right env::unary,[]⟩
  let empty := Core.StatefulRunResult.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),.loadCellApply::.binaryRight .wordEq right env::unary,[]⟩
  check (decide (run 25 [.bool true]=some (.bool,.outOfFuel badCp) ∧ run 26 [.bool true]=some (.bool,bad) ∧ Core.runStateful 1 badCp=bad ∧ run 5 []=some (.bool,.outOfFuel emptyCp) ∧ run 9 []=some (.bool,empty) ∧ Core.runStateful 4 emptyCp=empty)) "right write survives invalid left comparison; left child fault prevents right"
  let leftMissingEnv := [y.value,x.value,g.value,(reader 1).value]
  let leftMissingRun := runRecursiveComputationFunction? types owner source [reader 1,g,x,y]
  let leftMissingCp : Core.State := ⟨.eval (.var 1) [x.value,.cellRef .word 1],.loadCellApply::.binaryRight .wordEq right leftMissingEnv::unary,[w 23]⟩
  let leftMissing := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),.loadCellApply::.binaryRight .wordEq right leftMissingEnv::unary,[w 23]⟩
  check (decide (leftMissingRun 8 [w 23]=some (.bool,.outOfFuel leftMissingCp) ∧ leftMissingRun 9 [w 23]=some (.bool,leftMissing) ∧ Core.runStateful 1 leftMissingCp=leftMissing)) "missing left cell leaves writable right cell untouched"
  let rf := writer 0; let rg := reader 1
  let changed ← verify source rf rg x y .bool core [w 23,w 14] [w 11,w 14] (.bool true) 28
  let changedEnv := changed.inputs.environment.values
  let changedRun := runRecursiveComputationFunction? types owner source [rf,rg,x,y]
  let missingCp : Core.State := ⟨.eval (.var 1) [y.value,.cellRef .word 1],.loadCellApply::.binaryApply .wordEq (w 11)::unary,[w 11]⟩
  let missing := Core.StatefulRunResult.fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),.loadCellApply::.binaryApply .wordEq (w 11)::unary,[w 11]⟩
  check (decide (changedRun 24 [w 23]=some (.bool,.outOfFuel missingCp) ∧ changedRun 25 [w 23]=some (.bool,missing) ∧ Core.runStateful 1 missingCp=missing)) "missing right preserves earlier left write and pending negation"
  let wrongRightCp : Core.State := ⟨.ret (.cellRef .word 1),.loadCellApply::.binaryApply .wordEq (w 11)::unary,[w 11,.bool false]⟩
  let wrongRight := Core.StatefulRunResult.fault (.invalidBinaryOperands .wordEq (w 11) (.bool false)) ⟨.ret (.bool false),.binaryApply .wordEq (w 11)::unary,[w 11,.bool false]⟩
  check (decide (changedRun 25 [w 23,.bool false]=some (.bool,.outOfFuel wrongRightCp) ∧ changedRun 26 [w 23,.bool false]=some (.bool,wrongRight) ∧ Core.runStateful 1 wrongRightCp=wrongRight)) "wrong actual right Word payload retains left write and unapplied negation"
  for (actualEnv,actualRun) in [(env,run),(changedEnv,changedRun)] do
    for store in [[w 23],[.bool true],[],[w 23,.bool false],[w 23,w 14]] do
      for fuel in List.range 30 do
        check (decide (actualRun fuel store=some (.bool,Core.runStateful fuel (.initial core actualEnv store)))) "same prepared actual values retain arbitrary stores and declared Bool tag"
        match exhausted : Core.runStateful fuel (.initial core actualEnv store) with
        | .outOfFuel residual =>
            have _ := Core.runStateful_resume exhausted 40
            check (decide (actualRun (fuel+40) store=some (.bool,Core.runStateful 40 residual))) "all genuine checkpoints resume complete success or fault"
        | _ => pure ()
  for body in ["return f(x) != missing;","return missing <= g(y);","return f(x) != (x==y);","return (x==y) <= g(y);","return f(x) < g(y);","return f(x) >= g(y);"] do
    let rejected ← bodySource body
    check (decide (compileRecursiveComputationFunction? types owner rejected=none ∧ prepareRecursiveComputationFunction? types owner rejected [f,g,x,y]=none ∧ runRecursiveComputationFunction? types owner rejected [f,g,x,y] 50 [w 23]=none)) "whole Word gates, unknown names and excluded ordered expansions"
  let wrongReturn ← parsed "function comparison(f:F,g:G,x:X,y:Y) returns(Word){return f(x) != g(y);}"
  check (decide (elaborateRecursiveComputationReturnTree? types owner prepared.inputs.toTypeInputs wrongReturn.value.body=some (core,.bool) ∧ compileRecursiveComputationFunction? types owner wrongReturn=none ∧ prepareRecursiveComputationFunction? types owner wrongReturn [f,g,x,y]=none)) "original Bool comparison body versus declared Word"
  for body in ["f(x)<=g(y)<=x","f(x)!=g(y)!=x"] do
    let file : Syntax.SourceFile := ⟨⟨.main,"nonassociative-comparison-entry.sol"⟩,"function comparison(f:F,g:G,x:X,y:Y) returns(R){return "++body++";}"⟩
    let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "non-associative fixture lexer")
    check tokens.diagnostics.isEmpty "original chained comparison lexes"
    match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) with
    | .ok _ next => check (!next.diagnostics.isEmpty || !next.atEnd) "comparison grammar remains non-associative"
    | .reject _ _ => pure ()
    | .invariant _ => throw (IO.userError "non-associative parser invariant")
end Tests

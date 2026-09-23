import Solcore.Syntax.Parser.Function
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RuntimeComputationFunction
import Solcore.Core.FuelResumptionProperties

/-! Three exact old rejections become positives without replacing their original
owners, source files, caller rows or annotations. Store invariance below belongs
only to the original identity/constant closure fixture, not arbitrary callees. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
open RecursiveLocalComputationElaborates RecursiveLocalComputationFragment RecursiveLocalComputationEvaluatesWithCost
namespace ParsedScopedShadowingMigrations
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def shared : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Shared",by decide⟩],by decide⟩⟩,54⟩
private def compileOwner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"CompileRecursive",by decide⟩],by decide⟩⟩,4⟩
private def id (n : Nat) : Resolved.LocalId := ⟨shared,n⟩
private def foreign : Resolved.LocalId := ⟨{shared with declarationIndex := 91},302⟩
private def inputs : LocalTypeInputs := ⟨[⟨"x",id 4,.word⟩,⟨"f",foreign,.function .word .word⟩,
  ⟨"g",id 9,.function .word .word⟩,⟨"h",id 12,.function .word .word⟩,⟨"k",id 15,.function .word .word⟩,
  ⟨"p",id 20,.function .word .bool⟩,⟨"f",id 25,.bool⟩],by change [id 4,foreign,id 9,id 12,id 15,id 20,id 25].Nodup; decide⟩
private def types : TypeNameTable := [(["Word"],.word),(["A"],.word),(["A"],.bool)]
private def value : Core.Value := .word (Core.Word.ofNatModulo 17)
private def identity : Core.Value := .closure .word .word (.var 0) [.bool false]
private def environment : Resolved.Environment := [(id 4,value),(foreign,identity),(id 9,identity),
  (id 12,identity),(id 15,identity),(id 20,.closure .word .bool (.bool true) [.unit]),(id 25,.bool false)]
private def parsed (fileName text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,fileName⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "parser")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span &&
    source.span.contains source.value.signature.span && decide (source.value.signature.span.endByte≤source.value.body.span.startByte)) "original declaration ranges"
  return source
private structure Child (i : LocalTypeInputs) (e : Resolved.Environment) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  elaboration : RecursiveLocalComputationElaborates i.names i.context source core type
  counted : ∀ store, RecursiveLocalComputationEvaluatesWithCost i.names e store source value store cost
private def child (i : LocalTypeInputs) (e : Resolved.Environment) (source : Syntax.Expr) : IO (Child i e source) := do
  match shape : source with
  | ⟨_,.identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some localId =>
          match typed : i.context.lookup? localId, indexed : Resolved.LocalScope.index? i.context.ids localId, actual : e.lookup? localId with
          | some type,some index,some value =>
              return ⟨.var index,type,value,1,by
                rw [shape]
                exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named))
                  (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed)),
                fun _ => by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | _,_,_ => throw (IO.userError "original static/actual row")
      | none => throw (IO.userError "original name")
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span &&
        decide (fn.span.endByte≤argsSpan.startByte)) "original call order/ranges"
      let f ← child i e fn; let a ← child i e arg
      match ft : f.type with
      | .function input output =>
          if same : a.type=input then
            have el : RecursiveLocalComputationElaborates i.names i.context source (.apply f.core a.core) output := by
              rw [shape]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration)
            match actual : f.value with
            | .closure _ _ (.var 0) captures =>
                return ⟨.apply f.core a.core,output,a.value,f.cost+a.cost+4,el,fun s => by
                  rw [shape]
                  exact .application (actual ▸ f.counted s) (a.counted s) (.cons (.var rfl) .refl)⟩
            | .closure _ _ (.bool flag) captures =>
                return ⟨.apply f.core a.core,output,.bool flag,f.cost+a.cost+4,el,fun s => by
                  rw [shape]
                  exact .application (actual ▸ f.counted s) (a.counted s) (.cons .bool .refl)⟩
            | _ => throw (IO.userError "original closure body")
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | _ => throw (IO.userError "original child shape")
termination_by sizeOf source
private structure Body (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (e : Resolved.Environment) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  elaboration : RecursiveComputationReturnTreeElaborates ts o i source core type
  counted : ∀ store, RecursiveComputationReturnTreeEvaluatesWithCost o i.names e store source value store cost
private def body (ts : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (e : Resolved.Environment) (source : Syntax.Block) : IO (Body ts o i e source) := do
  for statement in source.value do check (source.span.contains statement.span) "original statement ranges"
  match shape : source with
  | ⟨_,[⟨rs,.returnStmt (some expression)⟩]⟩ =>
      check (rs.contains expression.span) "original return range"; let a ← child i e expression
      return ⟨a.core,a.type,a.value,a.cost,by rw [shape]; exact .expression a.elaboration,
        fun s => by rw [shape]; exact .expression (a.counted s)⟩
  | ⟨span,⟨ls,.letDecl name none (some initializer)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains initializer.span && decide (name.span.endByte≤initializer.span.startByte)) "original initializer before new binding"
      let a ← child i e initializer; let fresh := Resolved.freshLocalId o i.ids
      let b ← body ts o (i.bindFresh o name.value a.type) ((fresh,a.value)::e) ⟨span,rest⟩
      return ⟨.letE a.core b.core,b.type,b.value,a.cost+b.cost+2,by rw [shape]; exact .inferred a.elaboration b.elaboration,
        fun s => by rw [shape]; exact .inferred (a.counted s) (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.counted s)⟩
  | ⟨_,[⟨_,.ifThen guard yes (some no)⟩]⟩ =>
      let protection ← if h : computationBlockPreservesNames (i.names.map Prod.fst) yes=true then
        pure (PLift.up (computationBlockPreservesNames_iff.mp h)) else throw (IO.userError "original then scope")
      let c ← child i e guard; let a ← body ts o i e yes; let b ← body ts o i e no
      if same : c.type=.bool ∧ b.type=a.type then
        have el : RecursiveComputationReturnTreeElaborates ts o i source (.ifE c.core a.core b.core) a.type := by
          rw [shape]; exact .conditional (same.1 ▸ c.elaboration) protection.down a.elaboration (same.2 ▸ b.elaboration)
        match actual : c.value with
        | .bool true => return ⟨.ifE c.core a.core b.core,a.type,a.value,c.cost+a.cost+2,el,
            fun s => by rw [shape]; exact .ifTrue (actual ▸ c.counted s) (a.counted s)⟩
        | .bool false => return ⟨.ifE c.core a.core b.core,a.type,b.value,c.cost+b.cost+2,el,
            fun s => by rw [shape]; exact .ifFalse (actual ▸ c.counted s) (b.counted s)⟩
        | _ => throw (IO.userError "actual guard")
      else throw (IO.userError "both original branch types")
  | _ => throw (IO.userError "original body shape")
termination_by sizeOf source
private def nested (f g : Nat) : Core.Expr := .apply (.var f) (.apply (.var g) (.var 0))
private def core (branch : Bool) : Core.Expr := if branch then
  .ifE (nested 5 2) (.var 0) (.letE (.var 0) (.var 0)) else .letE (nested 1 2) (.var 0)
private theorem invoke {e : Core.Environment} {s : Core.Store} {k : List Core.Frame} {f n : Nat}
    {arg : Core.Expr} {a b : Core.Ty} {actual : Core.Expr} {captures : Core.Environment} {x v : Core.Value}
    (found : e[f]?=some (.closure a b actual captures))
    (argument : Core.Steps n ⟨.eval arg e,.applyClosure a b actual captures::k,s⟩ ⟨.ret x,.applyClosure a b actual captures::k,s⟩)
    (closure : Core.Steps 1 (.initial actual (x::captures) s) (.final v s)) :
    Core.Steps (1+n+1+3) ⟨.eval (.apply (.var f) arg) e,k,s⟩ ⟨.ret v,k,s⟩ :=
  CostStepComposition.apply (.cons (.var found) .refl) argument closure
private theorem manual (branch : Bool) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps 14 ⟨.eval (core branch) environment.values,k,s⟩ ⟨.ret value,k,s⟩ := by
  cases branch
  · exact CostStepComposition.letE (invoke rfl (invoke rfl (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl)
  · exact CostStepComposition.ifTrue (invoke rfl (invoke rfl (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)) (.cons .bool .refl)) (.cons (.var rfl) .refl)
private def originalBody (branch : Bool) := if branch then
  "if(p(g(x))){return x;}else{let x=x;return x;}" else "let x=f(g(x));return x;"
private def exercise (branch : Bool) : IO Unit := do
  let declaration ← parsed "shared-body.sol" ("function original(){"++originalBody branch++"}")
  let source := declaration.value.body; let b ← body types shared inputs environment source
  if fixed : b.core=core branch ∧ b.type=.word ∧ b.value=value ∧ b.cost=14 then
    have el : RecursiveComputationReturnTreeElaborates types shared inputs source (core branch) .word := by
      simpa only [fixed.1,fixed.2.1] using b.elaboration
    have _ := ComputationReturnTreeElaborates.core_hasType core_hasType el
    have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,el⟩
    have accepted := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr el
    check (decide (elaborateRecursiveComputationReturnTree? types shared inputs source=some (core branch,.word) ∧
      (inputs.bindFresh shared "x" .word).names.lookup? "x"=some (id 26) ∧ inputs.names.lookup? "f"=some foreign ∧
      types.lookup? ["A"]=some .word)) "same sparse duplicate tables/new exact binder"
    for store in [[],[Core.Value.bool true,.unit]] do
      have raw : RecursiveComputationReturnTreeEvaluatesWithCost shared inputs.names environment store source value store 14 := by
        simpa only [fixed.2.2.1,fixed.2.2.2] using b.counted store
      have _ := (computationReturnTreeEvaluates_iff_exists_cost (ChildEval := RecursiveLocalComputationEvaluates)
        (ChildCost := RecursiveLocalComputationEvaluatesWithCost) recursiveLocalComputationEvaluates_iff_exists_cost).mpr ⟨_,raw⟩
      have costLaw := ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps (F := RecursiveLocalComputationFragment)
        (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
        core_fragment weakenAt evaluates_insert_iff evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost insertion_paths toStepsWithContinuation el (environment := environment) rfl
      have _ := ComputationReturnTreeEvaluatesWithCost.deterministic (ChildCost := RecursiveLocalComputationEvaluatesWithCost) deterministic raw (costLaw.mpr (manual branch store []))
      have _ := costLaw.mp raw
      have fragment := ComputationReturnTreeElaborates.core_fragment (ChildElab := RecursiveLocalComputationElaborates)
        (F := RecursiveLocalComputationFragment) core_fragment weakenAt el
      let inserted := Core.Value.cellRef (.namedData ⟨99⟩) 404
      have paired : ∀ k, Core.Steps 14 ⟨.eval (core branch) environment.values,k,store⟩ ⟨.ret value,k,store⟩ ∧
          Core.Steps 14 ⟨.eval ((core branch).weakenAt 0) (inserted::environment.values),k,store⟩ ⟨.ret value,k,store⟩ := by
        obtain ⟨n,paths⟩ := ComputationBodyFragment.insertion_paths (F := RecursiveLocalComputationFragment)
          insertion_paths fragment [] environment.values inserted (Core.steps_from_initial_sound (manual branch store []))
        have same := ((manual branch store []).final_unique (paths []).1).1
        exact same.symm ▸ paths
      have _ := (paired []).2.runStateful_done_iff (fuel := 14)
      let cp : Core.State := if branch then ⟨.ret (.bool true),[.ifBranches (.var 0) (.letE (.var 0) (.var 0)) environment.values],store⟩
        else ⟨.ret value,[.letBody (.var 0) environment.values],store⟩
      check (decide (Core.runStateful 12 (.initial (core branch) environment.values store)=.outOfFuel cp ∧
        Core.runStateful 1 cp=.outOfFuel ⟨.eval (.var 0) (if branch then environment.values else value::environment.values),[],store⟩ ∧
        Core.runStateful 2 cp=.done value store)) "literal genuine guard/binder checkpoint and old/new environment"
      for k in [[],[Core.Frame.letBody .unit []]] do
        have _ := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
          (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
          core_fragment weakenAt insertion_paths toStepsWithContinuation raw el rfl k
        check (decide (Core.runStateful 14 ⟨.eval (core branch) environment.values,k,store⟩=
          if k=[] then .done value store else .outOfFuel ⟨.ret value,k,store⟩)) "manual same cost/pending actual endpoint"
      for fuel in List.range 16 do
        have _ := (manual branch store []).runStateful_done_iff (fuel := fuel)
        let start := Core.State.initial (core branch) environment.values store
        match genuine : Core.runStateful fuel start with
        | .done result final => check (decide (14≤fuel ∧ result=value ∧ final=store)) "original value/store/full fuel"
        | .outOfFuel cp =>
            have _ := (manual branch store []).residual_of_outOfFuel genuine
            for more in List.range 16 do
              have _ := Core.runStateful_resume genuine more
              check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) start)) "genuine full resumption"
            check (decide (fuel<14 ∧ Core.runStateful (14-fuel) cp=.done value store)) "exact residual"
        | .fault _ _ => throw (IO.userError "original success faulted")
  else throw (IO.userError "independent original static/raw differs")
private def compileTypes : TypeNameTable := [(["F"],.function .word .word),(["F"],.bool),
  (["G"],.function .word .word),(["A"],.word),(["B"],.word),(["R"],.word),
  (["Unit"],.unit),(["Word"],.word),(["mod","F"],.function .word .word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ type, PLift (StructuralTypeDenotes compileTypes source type)) := do
  match shape : source with
  | ⟨_,.named name none⟩ =>
      match found : compileTypes.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation lookup")
  | _ => throw (IO.userError "original annotation shape")
private def declare (i : LocalTypeInputs) (ps : List Syntax.FunctionParameter) :
    IO (Σ result, PLift (RuntimeParametersDeclareFrom compileTypes compileOwner i ps result)) := do
  match shape : ps with
  | [] => return ⟨i,⟨by rw [shape]; exact .nil⟩⟩
  | ⟨span,.typed none name annotation⟩::rest =>
      check (span.contains name.span && span.contains annotation.span && decide (name.span.endByte≤annotation.span.startByte)) "original parameter ranges/order"
      let m ← meaning annotation
      if unused : name.value ∉ i.names.map Prod.fst then
        let tail ← declare (i.bindFresh compileOwner name.value m.1) rest
        return ⟨tail.1,⟨by rw [shape]; exact .cons m.2.down unused tail.2.down⟩⟩
      else throw (IO.userError "duplicate parameters remain excluded")
  | _ => throw (IO.userError "original parameter shape")
private def compilation : IO Unit := do
  let source ← parsed "compile-recursive.sol" "function example(f:F,g:G,x:A) returns(R){let x=f(g(x));return x;}"
  let sig := source.value.signature; let declared ← declare .empty sig.parameters.elements
  let expectedInputs := ((LocalTypeInputs.empty.bindFresh compileOwner "f" (.function .word .word)).bindFresh compileOwner "g" (.function .word .word)).bindFresh compileOwner "x" .word
  if original : declared.1.names=expectedInputs.names ∧ declared.1.context=expectedInputs.context then
    let env : Resolved.Environment := [(⟨compileOwner,2⟩,value),(⟨compileOwner,1⟩,identity),(⟨compileOwner,0⟩,identity)]
    let b ← body compileTypes compileOwner declared.1 env source.value.body
    if policy : sig.genericParameters=none ∧ sig.whereClause=none ∧ sig.modifiers.publicMarker=none ∧ sig.modifiers.payableMarker=none then
      match returns : sig.returnsClause with
      | some ⟨_,⟨_,[annotation]⟩⟩ =>
          let m ← meaning annotation
          if fixed : m.1=.word ∧ b.type=.word ∧ b.core=.letE (nested 2 1) (.var 0) then
            have header : RuntimeFunctionHeader compileTypes sig .word :=
              ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [returns]; exact .single (fixed.1 ▸ m.2.down)⟩
            let compiled : CompiledRuntimeFunction := ⟨declared.1,.letE (nested 2 1) (.var 0),.word⟩
            have certificate : RecursiveComputationFunctionCompiles compileTypes compileOwner source compiled :=
              ⟨header,declared.2.down,by simpa only [compiled,fixed.2.1,fixed.2.2] using b.elaboration⟩
            have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr certificate
            check (decide ((compileRecursiveComputationFunction? compileTypes compileOwner source).map (fun c => (c.inputs.names,c.inputs.context,c.core,c.returnType))=
              some (expectedInputs.names,expectedInputs.context,.letE (nested 2 1) (.var 0),.word) ∧
              (declared.1.bindFresh compileOwner "x" .word).names.lookup? "x"=some ⟨compileOwner,3⟩ ∧
              compileRuntimeComputationFunction? compileTypes compileOwner source=none ∧
              compileComputationFunction? elaborateLocalComputation? compileTypes compileOwner source=none)) "original full declaration/exact compile/old endpoints"
          else throw (IO.userError "independent original compile differs")
      | _ => throw (IO.userError "original returns clause")
    else throw (IO.userError "original whole header")
  else throw (IO.userError "original parameters reverse once")
end ParsedScopedShadowingMigrations
open ParsedScopedShadowingMigrations
def frontendParsedScopedShadowingMigrationTests : IO Unit := do
  exercise true
  exercise false
  compilation
end Tests

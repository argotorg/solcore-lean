import Solcore.Syntax.Parser.Function
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.TypeNameProperties
import Solcore.Frontend.RecursiveLocalComputationTypingProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Frontend.ComputationReturnTreeRuntimeSafetyProperties
import Solcore.Frontend.ComputationBindingScopeProperties
import Solcore.Frontend.ComputationReturnTreeRuntimeCheckpointProperties
import Solcore.Core.FuelResumptionProperties
/-! Original mixed bodies, sparse caller rows, independently counted source rules
and literal Core scripts connect actual effects to same-world runtime safety. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationRuntimeSafety
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RuntimeMixed",by decide⟩],by decide⟩⟩,68⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 91},302⟩
private def inputs : LocalTypeInputs := ⟨[
  ⟨"x",id 4,.word⟩,⟨"f",foreign,.function .word .word⟩,⟨"g",id 9,.function .word .word⟩,
  ⟨"a",id 12,.function .word (.cell .word)⟩,⟨"c",id 15,.bool⟩,⟨"f",id 30,.bool⟩],
  by change [id 4,foreign,id 9,id 12,id 15,id 30].Nodup; decide⟩
private def types : TypeNameTable := [(["W"],.word),(["C"],.cell .word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def reader : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word 0]
private def writer : Core.Value := .closure .word .word
  (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0]
private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
private def env (x : Nat) (choice swap : Bool) : Resolved.Environment :=
  [(id 4,w x),(foreign,if swap then writer else reader),(id 9,if swap then reader else writer),
    (id 12,allocator),(id 15,.bool choice),(id 30,.bool false)]
private theorem envTyped (x : Nat) (choice swap : Bool) :
    Core.RuntimeEnvironmentHasTypes [.word] (env x choice swap).values inputs.context.values := by
  have r : Core.RuntimeValueHasType [.word] reader (.function .word .word) :=
    .closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl) .word)
  have g : Core.RuntimeValueHasType [.word] writer (.function .word .word) :=
    .closure (.cons (.cellRef rfl) .nil) (.letE (.storeCell (.var rfl) (.var rfl) .word) (.loadCell (.var rfl) .word))
  have a : Core.RuntimeValueHasType [.word] allocator (.function .word (.cell .word)) :=
    .closure .nil (.newCell (.var rfl) .word)
  cases swap
  · exact .cons .word (.cons r (.cons g (.cons a (.cons .bool (.cons .bool .nil)))))
  · exact .cons .word (.cons g (.cons r (.cons a (.cons .bool (.cons .bool .nil)))))
private def parsed (body : String) : IO Syntax.Block := do
  let text := "function mixed(){" ++ body ++ "}"
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-runtime-safety.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "original function parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "original full bytes"
  return source.value.body
private structure Path (core : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual script depth")
  | n+1,e,env,s => do
    match original : e with
    | .unit => return ⟨.unit,s,1,fun _ => by rw [original]; exact .cons .unit .refl⟩
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
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [original]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write missing")
        | _,_ => throw (IO.userError "manual write shape")
    | .newCell .word (.var i) =>
        match found : env[i]? with
        | some v => return ⟨.cellRef .word s.length,s ++ [v],3,fun _ => by rw [original]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
        | none => throw (IO.userError "manual allocation argument")
    | .ifE condition yes no =>
        let c ← path n condition env s
        match choice : c.value with
        | .bool true => let b ← path n yes env c.final; return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.ifTrue (choice ▸ c.evidence _) (b.evidence _)⟩
        | .bool false => let b ← path n no env c.final; return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.ifFalse (choice ▸ c.evidence _) (b.evidence _)⟩
        | _ => throw (IO.userError "manual Bool guard")
    | _ => throw (IO.userError "outside explicit Core script")
private structure Certificate (Elaborates : Core.Expr → Core.Ty → Prop) (Evaluates : Core.Value → Core.Store → Nat → Prop) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : Elaborates core type
  raw : Evaluates value final cost
private abbrev Child (i : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) :=
  Certificate (RecursiveLocalComputationElaborates i.names i.context source) (RecursiveLocalComputationEvaluatesWithCost i.names e s source)
private def child (i : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) : IO (Child i e s source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some id =>
          match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id, actual : e.lookup? id with
          | some t,some n,some v => return ⟨.var n,t,v,s,1,
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed)),
              by rw [original]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual))⟩
          | _,_,_ => throw (IO.userError "original row")
      | none => throw (IO.userError "original first name")
  | ⟨_,.group inner⟩ =>
      let a ← child i e s inner
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .group a.elaboration,by rw [original]; exact .group a.raw⟩
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte≤argsSpan.startByte)) "original child ranges/order"
      let f ← child i e s fn; let a ← child i e f.final arg
      match ft : f.type, fv : f.value with
      | .function input output,.closure _ _ body captured =>
          if same : a.type=input then
            let b ← path 100 body (a.value::captured) a.final
            return ⟨.apply f.core a.core,output,b.value,b.final,f.cost+a.cost+b.cost+3,
              by rw [original]; exact .application (ft ▸ f.elaboration) (same ▸ a.elaboration),
              by rw [original]; exact .application (fv ▸ f.raw) a.raw (b.evidence [])⟩
          else throw (IO.userError "original argument type")
      | _,_ => throw (IO.userError "original/actual Function")
  | _ => throw (IO.userError "outside independent child")
termination_by sizeOf source
private abbrev Tree (i : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (source : Syntax.Block) :=
  Certificate (RecursiveComputationReturnTreeElaborates types owner i source) (RecursiveComputationReturnTreeEvaluatesWithCost owner i.names e s source)
private def tree (i : LocalTypeInputs) (e : Resolved.Environment) (s : Core.Store) (source : Syntax.Block) : IO (Tree i e s source) := do
  check (source.value.all fun statement => source.span.contains statement.span) "original statement ranges"
  match original : source with
  | ⟨_,[⟨rs,.returnStmt (some expression)⟩]⟩ =>
      check (rs.contains expression.span) "original return range"; let a ← child i e s expression
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .expression a.elaboration,by rw [original]; exact .expression a.raw⟩
  | ⟨_,[⟨bs,.block statements⟩]⟩ =>
      let a ← tree i e s ⟨bs,statements⟩
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .block a.elaboration,by rw [original]; exact .block a.raw⟩
  | ⟨bs,⟨ls,.letDecl name annotation (some initializer)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains initializer.span && decide (name.span.endByte≤initializer.span.startByte)) "original binding ranges/order"
      if unused : name.value ∉ i.names.map Prod.fst then
        let a ← child i e s initializer; let fresh := Resolved.freshLocalId owner i.ids
        let b ← tree (i.bindFresh owner name.value a.type) ((fresh,a.value)::e) a.final ⟨bs,rest⟩
        have tail : RecursiveComputationReturnTreeEvaluatesWithCost owner
            ((name.value,Resolved.freshLocalId owner (i.names.map Prod.snd))::i.names)
            ((Resolved.freshLocalId owner (i.names.map Prod.snd),a.value)::e) a.final ⟨bs,rest⟩ b.value b.final b.cost := by
          simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw
        match ann : annotation with
        | none => return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,
            by rw [original,ann]; exact .inferred a.elaboration b.elaboration,
            by rw [original,ann]; exact .inferred a.raw tail⟩
        | some written =>
            check (ls.contains written.span) "original type range"
            match atType : written with
            | ⟨_,.named name none⟩ =>
                if found : types.lookup? (qualifiedTypeNameKey name)=some a.type then
                  have meaning : StructuralTypeDenotes types written a.type := by rw [atType]; exact .named (TypeNameTable.lookup?_iff.mp found)
                  return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,
                    by rw [original,ann]; exact .binding meaning a.elaboration b.elaboration,
                    by rw [original,ann]; exact .binding a.raw tail⟩
                else throw (IO.userError "original annotation")
            | _ => throw (IO.userError "annotation shape")
      else throw (IO.userError "original shadow")
  | ⟨bs,⟨_,.expression expression true⟩::rest⟩ =>
      let a ← child i e s expression; let b ← tree i e a.final ⟨bs,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,b.value,b.final,a.cost+b.cost+2,
        by rw [original]; exact .discard a.elaboration b.elaboration,by rw [original]; exact .discard a.raw b.raw⟩
  | ⟨_,[⟨_,.ifThen guard yes (some no)⟩]⟩ =>
      let protection ← if h : computationBlockPreservesNames (i.names.map Prod.fst) yes=true then pure (PLift.up (computationBlockPreservesNames_iff.mp h)) else throw (IO.userError "original then scope")
      let c ← child i e s guard; let a ← tree i e c.final yes; let b ← tree i e c.final no
      if ct : c.type=.bool then
        if same : b.type=a.type then
          match cv : c.value with
          | .bool true => return ⟨.ifE c.core a.core b.core,a.type,a.value,a.final,c.cost+a.cost+2,
              by rw [original]; exact .conditional (ct ▸ c.elaboration) protection.down a.elaboration (same ▸ b.elaboration),
              by rw [original]; exact .ifTrue (cv ▸ c.raw) a.raw⟩
          | .bool false => return ⟨.ifE c.core a.core b.core,a.type,b.value,b.final,c.cost+b.cost+2,
              by rw [original]; exact .conditional (ct ▸ c.elaboration) protection.down a.elaboration (same ▸ b.elaboration),
              by rw [original]; exact .ifFalse (cv ▸ c.raw) b.raw⟩
          | _ => throw (IO.userError "actual Bool")
        else throw (IO.userError "both original branches")
      else throw (IO.userError "original Bool")
  | _ => throw (IO.userError "outside original mixed body")
termination_by sizeOf source
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def fixed : Core.Expr := .letE (call 1 0) (.letE (call 3 1)
  (.ifE (.var 6) (.letE (call 5 1) (.apply (.var 4) (call 5 2))) (call 3 2)))
private def verify (text : String) (x old : Nat) (choice swap : Bool) : IO Unit := do
  let source ← parsed text; let e := env x choice swap; let s := [w old]
  let a ← tree inputs e s source; let manual ← path 100 fixed e.values s
  let value := w (if swap || !choice then x else old)
  let final := if choice then [value,value] else [w x]
  let cost := if choice then 62 else if swap then 45 else 38
  if shape : a.core=fixed ∧ a.type=.word then
    have elaboration : RecursiveComputationReturnTreeElaborates types owner inputs source fixed .word := by simpa only [shape.1,shape.2] using a.elaboration
    have ids : e.ids=inputs.context.ids := rfl
    have st : Core.StoreHasTypes [.word] s := Core.StoreHasTypes.nil.allocate .word .word
    have et := envTyped x choice swap
    check (decide (a.value=value ∧ a.final=final ∧ a.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent exact values/stores/costs"
    check (decide (elaborateRecursiveComputationReturnTree? types owner inputs source=some (fixed,.word) ∧
      inputs.names.lookup? "f"=some foreign ∧ (inputs.bindFresh owner "r" .word).names.lookup? "r"=some (id 31) ∧
      ((inputs.bindFresh owner "r" .word).bindFresh owner "p" (.cell .word)).names.lookup? "p"=some (id 32))) "exact checker, first match and owner-filtered freshness"
    have identified : ∃ fw, Core.WorldExtends [.word] fw ∧ Core.StoreHasTypes fw manual.final ∧ Core.RuntimeValueHasType fw manual.value .word ∧
        RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names e s source manual.value manual.final manual.cost := by
      obtain ⟨fw,fs,v,n,extension,storeTyped,valueTyped,originalCost,paths,_⟩ :=
        ComputationReturnTreeElaborates.runtime_typed_execution (F := RecursiveLocalComputationFragment)
          (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates)
          (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
          RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment
          RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
          RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost
          RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation elaboration ids et st
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique (manual.evidence [])
      exact ⟨fw,extension,storeTyped,valueTyped,originalCost⟩
    have counted := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
      RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation a.raw a.elaboration ids
    have _ := (by simpa only [shape.1,Core.State.initial,Core.State.final] using counted [] : Core.Steps a.cost (.initial fixed e.values s) (.final a.value a.final)).final_unique (manual.evidence [])
    let k := [Core.Frame.pairApply (w 7)]
    have kt : Core.ContinuationHasType [.word] k .word (.product .word .word) := .cons (.pairApply .word) .nil
    have safety := ComputationReturnTreeElaborates.runtime_checkpoint_safety (ChildElab := RecursiveLocalComputationElaborates)
      RecursiveLocalComputationElaborates.core_hasType elaboration et st kt
    if choice then
      let bound := w (if swap then x else old)
      let saved := w x::bound::e.values
      let after := [w x,bound]
      check (decide (Core.runStateful 39 ⟨.eval fixed e.values,k,s⟩=
        .outOfFuel ⟨.ret (.cellRef .word 1),.letBody (.apply (.var 4) (call 5 2)) saved::k,after⟩ ∧
        Core.runStateful 40 ⟨.eval fixed e.values,k,s⟩=
        .outOfFuel ⟨.eval (.apply (.var 4) (call 5 2)) (.cellRef .word 1::saved),k,after⟩)) "allocation and hidden discard slot literal checkpoints"
    for fuel in List.range (cost+2) do
      match closed : Core.runStateful fuel (.initial fixed e.values s) with
      | .done v fs => check (decide (cost≤fuel ∧ v=value ∧ fs=final)) "exact closed result"
      | .outOfFuel cp =>
          have _ := (manual.evidence []).residual_of_outOfFuel closed
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final)) "exact closed residual"
      | .fault _ _ => throw (IO.userError "independent manual path faulted")
      match stopped : Core.runStateful fuel ⟨.eval fixed e.values,k,s⟩ with
      | .done v fs => check (decide (cost+1≤fuel ∧ v=.pair (w 7) value ∧ fs=final)) "typed pending completion"
      | .outOfFuel cp =>
          have _ := safety.2.2 stopped
          have _ := Core.runStateful_resume stopped (cost+1-fuel)
          check (decide (fuel≤cost ∧ Core.runStateful (cost+1-fuel) cp=.done (.pair (w 7) value) final ∧
            Core.runStateful 1 cp=Core.runStateful (fuel+1) ⟨.eval fixed e.values,k,s⟩)) "exact typed saved state/full resume"
      | .fault error state => False.elim (safety.2.1 fuel error state stopped)
    check (decide (Core.runStateful cost ⟨.eval fixed e.values,k,s⟩=.outOfFuel ⟨.ret value,k,final⟩)) "actual endpoint not closed completion"
  else throw (IO.userError "original lowering differs from literal Core")
end ParsedComputationRuntimeSafety
open ParsedComputationRuntimeSafety
def frontendParsedComputationRuntimeSafetyTests : IO Unit := do
  for choice in [true,false] do
    for swap in [true,false] do
      for x in [11,14] do
        for old in [23,91] do
          for annotation in ["",":W"] do
            for wrapper in [false,true] do
              let body := "let r"++annotation++"=f(x);g(x);if(c){{let p:C=a(r);return f(g(r));}}else{return f(x);}"
              verify (if wrapper then "{"++body++"}" else body) x old choice swap
end Tests

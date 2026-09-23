import Solcore.Syntax.Parser.Term
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Core.FuelResumptionProperties
/-! Original allocation/write/read and literal-to-grouped-wildcard selection have
independent raw and cost witnesses before owner transport or Core observations. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationRawOwnerEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ComputationRawOwnerEffects",by decide⟩],by decide⟩⟩,132⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex := 903}
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex := o.declarationIndex+10}
private theorem injective : Function.Injective shift := by rintro ⟨lm,li⟩ ⟨rm,ri⟩ same; simpa [shift] using same
private theorem non_surjective : ¬ Function.Surjective shift := by
  intro h; obtain ⟨o,same⟩ := h {owner with declarationIndex := 0}
  have h := congrArg Resolved.DeclarationId.declarationIndex same; simp [shift] at h
private def relabel := ownerLocalIdMap shift
private theorem relabel_injective : Function.Injective relabel := ownerLocalIdMap_injective shift injective
private def inputs : LocalTypeInputs := ⟨[
  ⟨"x",⟨owner,7⟩,.word⟩,⟨"a",⟨owner,31⟩,.function .word .word⟩,
  ⟨"w",⟨foreign,700⟩,.function .word .word⟩,⟨"r",⟨owner,3⟩,.function .word .word⟩,⟨"x",⟨foreign,21⟩,.bool⟩],by decide⟩
private def mapped := inputs.mapIds relabel relabel_injective
private def types : TypeNameTable := [(["Word"],.word),(["Word"],.bool)]
private def word (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def allocator : Core.Value := .closure .word .word
  (.letE (.newCell .word (.var 0)) (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1)))) [.bool false]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def environment (w r : Nat) (x : Core.Value := word 14) : Resolved.Environment :=
  [(⟨owner,7⟩,x),(⟨owner,31⟩,allocator),(⟨foreign,700⟩,writer w),(⟨owner,3⟩,reader r),(⟨foreign,21⟩,.bool true)]
private def compareCore : Core.Expr := .binary .wordEq (.var 0) (.word (Core.Word.ofNatModulo 15))
private def chooseCore : Core.Expr := .ifE compareCore (.var 1) (.apply (.var 6) (.var 1))
private def matchCore : Core.Expr := .letE (.apply (.var 5) (.var 0)) chooseCore
private def tailCore : Core.Expr := .letE (.apply (.var 3) (.var 0)) matchCore
private def core : Core.Expr := .letE (.apply (.var 1) (.var 0)) tailCore
private def parsed : IO Syntax.Block := do
  let text := "{let x:Word=a(x);let x=w(x);match(r(x)){case 15{return x;}case ((_)){return r(x);}default{return w(x);}}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-raw-owner-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok b next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original block")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (b.span=⟨file.id,0,text.utf8ByteSize⟩)) "whole original block/range"
  return b
private def meaning (e : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types e t)) := do
  match shape : e with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "original named leaf")
  | _ => throw (IO.userError "annotation shape")
private structure Static (J : Core.Expr → Core.Ty → Prop) where
  core : Core.Expr
  type : Core.Ty
  evidence : J core type
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Static (RecursiveLocalComputationElaborates i.names i.context e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨.var n,t,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨span,.call f ⟨argsSpan,[a]⟩⟩ =>
      check (span.contains f.span && span.contains argsSpan && argsSpan.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original unary call ranges/order"
      let l ← child i f; let r ← child i a
      match ft : l.type with
      | .function t u => if same : r.type=t then return ⟨.apply l.core r.core,u,by rw [shape]; exact .application (ft ▸ l.evidence) (same ▸ r.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static source child")
termination_by sizeOf e
private structure Returned (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def returned (i : LocalTypeInputs) (b : Syntax.Block) : IO (Returned (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.type=.word then return ⟨r.core,by rw [shape]; exact .expression (same ▸ r.evidence)⟩ else throw (IO.userError "return type")
  | _ => throw (IO.userError "return body")
private def pattern (p : Syntax.Pattern) : IO (Σ tag : Option Core.Word, PLift (WordMatchPatternClassifies p tag)) := do
  match shape : p with
  | ⟨_,.wildcard _⟩ => return ⟨none,⟨by rw [shape]; exact .wildcard rfl⟩⟩
  | ⟨_,.literal literal⟩ => match decoded : interpretWordLiteral? literal with | some v => return ⟨some v,⟨by rw [shape]; exact .literal ⟨literal,rfl,interpretWordLiteral?_sound decoded⟩⟩⟩ | none => throw (IO.userError "strict Word literal")
  | ⟨_,.group inner⟩ => check (p.span.contains inner.span && decide (p.span.startByte<inner.span.startByte ∧ inner.span.endByte<p.span.endByte)) "original nested group ranges"; let c ← pattern inner; return ⟨c.1,⟨by rw [shape]; exact .group c.2.down⟩⟩
  | _ => throw (IO.userError "unsupported grouped or bare leaf")
termination_by sizeOf p
private def arms (i : LocalTypeInputs) (cs : List Syntax.MatchCase) : IO (Σ entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)), PLift (entries.map Prod.fst=cs ∧ ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1 ∧ RecursiveComputationReturnTreeElaborates types owner i entry.1.value.body entry.2.2 .word)) := do
  match shape : cs with
  | [] => return ⟨[],⟨by rw [shape]; exact ⟨rfl,by simp⟩⟩⟩
  | c::rest =>
      check (c.span.contains c.value.pattern.span && c.span.contains c.value.body.span && decide (c.value.pattern.span.endByte≤c.value.body.span.startByte)) "original pattern/body order"
      let p ← pattern c.value.pattern; let b ← returned i c.value.body; let tail ← arms i rest
      return ⟨(c,p.1,b.core)::tail.1,⟨by rw [shape]; refine ⟨by simp [tail.2.down.1],?_⟩; intro entry member; rcases List.mem_cons.mp member with rfl|member; exact ⟨p.2.down,b.evidence⟩; exact tail.2.down.2 entry member⟩⟩
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i b)) := do
  match shape : b with
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨cs,d⟩⟩⟩]⟩ =>
      check (b.span.contains matchSpan && matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && cs.all (fun c => armsSpan.contains c.span) && d.toList.all (fun b => armsSpan.contains b.span) && decide (scrutineeSpan.endByte≤armsSpan.startByte)) "original match and optional default ranges"
      let sc ← child i e; let bs ← arms i cs
      let dc : Σ de : Option (Syntax.Block × Core.Expr), PLift (de.map Prod.fst=d ∧ ∀ en ∈ de.toList, RecursiveComputationReturnTreeElaborates types owner i en.1 en.2 .word) ← match present : d with | none => pure ⟨none,⟨by simp [present]⟩⟩ | some b => do let c ← returned i b; pure ⟨some (b,c.core),⟨by refine ⟨present.symm,?_⟩; intro en h; cases List.mem_singleton.mp h; exact c.evidence⟩⟩
      match lowered : bs.1.foldr (fun en t => match en.2.1 with | none => some (en.2.2.weakenAt 0) | some v => t.map (fun t => .ifE (.binary .wordEq (.var 0) (.word v)) (en.2.2.weakenAt 0) t)) (dc.1.map (fun en => en.2.weakenAt 0)) with
      | some t => if same : sc.type=.word then return ⟨.letE sc.core t,.word,by rw [shape]; exact .wordMatch (defaultEntry := dc.1) (same ▸ sc.evidence) bs.2.down.1 (fun e h => (bs.2.down.2 e h).1) (.inl rfl) (fun e h => (bs.2.down.2 e h).2) dc.2.down.1 dc.2.down.2 lowered⟩ else throw (IO.userError "scrutinee type")
      | none => throw (IO.userError "uncovered original arms")
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      let fresh := 32+(i.bindings.length-inputs.bindings.length)
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.head?=some ⟨owner,fresh⟩ ∧ i.names.lookup? "x"=some ⟨owner,if fresh=32 then 7 else fresh-1⟩)) "old initializer and fresh32/33 tail row"
      check (decide (((i.mapIds relabel relabel_injective).bindFresh (shift owner) name.value a.type).ids.head?=some ⟨shift owner,fresh⟩)) "foreign binder700 ignored; same fresh index after owner map"
      let r ← body next ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some t => let m ← meaning t; if same : m.1=a.type then return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩ else throw (IO.userError "typed initializer")
  | _ => throw (IO.userError "original typed/inferred/match body")
termination_by sizeOf b
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .word w => return ⟨.word w,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b => let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match found : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell found) .refl))⟩ | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match found : s.read? l, written : s.write? l v with
        | some _,some final => return ⟨.unit,final,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue found) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual missing write")
      | _,_ => throw (IO.userError "manual write reference")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩ | none => throw (IO.userError "manual binary payload")
    | .ifE c a b =>
        let condition ← path n c env s
        match cv : condition.value with
        | .bool true => let r ← path n a env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (cv ▸ condition.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env condition.final; return ⟨r.value,r.final,condition.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (cv ▸ condition.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual condition")
    | _ => throw (IO.userError "manual Core shape")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) (U : Core.Value → Core.Store → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
  uncosted : U value final
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e) (RecursiveLocalComputationEvaluates table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)),by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩ | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence []),by rw [shape]; exact .application (fv ▸ l.uncosted) r.uncosted (Core.steps_from_initial_sound (p.evidence []))⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def choose (v : Core.Value) (cs : List Syntax.MatchCase) (d : Option Syntax.Block) : IO (Σ selected : Syntax.Block × Nat, PLift (WordMatchChooses v cs d selected.1 selected.2)) := do
  match shape : cs with
  | [] => match present : d with | some fallback => return ⟨(fallback,0),⟨by rw [shape,present]; exact .fallback⟩⟩ | none => throw (IO.userError "no raw fallback")
  | c::rest =>
      let p ← pattern c.value.pattern
      match tag : p.1 with
      | none => return ⟨(c.value.body,0),⟨by rw [shape]; exact .wildcard (by simpa only [tag] using p.2.down)⟩⟩
      | some literal => match actual : v with
        | .word w =>
            have meaning : WordMatchPatternClassifies c.value.pattern (some literal) := by simpa only [tag] using p.2.down
            if same : w=literal then return ⟨(c.value.body,1),⟨by rw [shape,actual]; exact .hit (same.symm ▸ meaning)⟩⟩
            else let tail ← choose (.word w) rest d; return ⟨(tail.1.1,tail.1.2+1),⟨by rw [shape,actual]; exact .miss meaning same tail.2.down⟩⟩
        | _ => throw (IO.userError "actual non-Word comparison before wildcard")
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b) (RecursiveComputationReturnTreeEvaluates owner table env s b)) := do
  match shape : b with
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .inferred a.evidence r.evidence,by rw [shape,ann]; exact .inferred a.uncosted r.uncosted⟩
      | some _ => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .binding a.evidence r.evidence,by rw [shape,ann]; exact .binding a.uncosted r.uncosted⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨cs,d⟩⟩⟩]⟩ =>
      let sc ← rawChild table env s e; let c ← choose sc.value cs d
      check (decide (c.1.2=1)) "original selected match visits exactly one literal"
      match selected : c.1.1 with
      | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ =>
          let r ← rawChild table env sc.final child
          return ⟨r.value,r.final,sc.cost+r.cost+2+7*c.1.2,by rw [shape]; exact .wordMatch sc.evidence c.2.down (by rw [selected]; exact .expression r.evidence),
            by rw [shape]; exact .wordMatch sc.uncosted c.2.down (by rw [selected]; exact .expression r.uncosted)⟩
      | _ => throw (IO.userError "selected original return")
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b
private def exercise (w r : Nat) (store final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let b ← parsed; let p ← body inputs b; let env := environment w r
  let a ← rawBody inputs.names env store b; let m ← path 70 core env.values store
  if fixed : p.core=core ∧ p.type=.word ∧ m.value=value ∧ m.final=final ∧ m.cost=cost ∧ a.value=value ∧ a.final=final ∧ a.cost=cost then
    have ⟨pc,pt,mv,ms,mc,av,ast,ac⟩ := fixed
    have counted : RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names env store b value final cost := by simpa only [av,ast,ac] using a.evidence
    have evaluated : RecursiveComputationReturnTreeEvaluates owner inputs.names env store b value final := by simpa only [av,ast] using a.uncosted
    have renamedCost := (computationReturnTreeEvaluatesWithCost_mapOwner_iff shift injective (recursiveLocalComputationEvaluatesWithCost_mapIds_iff relabel relabel_injective)).mpr counted
    have renamedRaw := (computationReturnTreeEvaluates_mapOwner_iff shift injective (recursiveLocalComputationEvaluates_mapIds_iff relabel relabel_injective)).mpr evaluated
    have _ := (computationReturnTreeEvaluatesWithCost_mapOwner_iff shift injective (recursiveLocalComputationEvaluatesWithCost_mapIds_iff relabel relabel_injective)).mp renamedCost
    have _ := (computationReturnTreeEvaluates_mapOwner_iff shift injective (recursiveLocalComputationEvaluates_mapIds_iff relabel relabel_injective)).mp renamedRaw
    have original : RecursiveComputationReturnTreeElaborates types owner inputs b core .word := by simpa only [pc,pt] using p.evidence
    have mappedElab := (computationReturnTreeElaborates_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mpr original
    have accepted : elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b=some (core,.word) := by simpa only [mapped,relabel] using (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr mappedElab
    have literal : ∀ k, Core.Steps cost ⟨.eval core env.values,k,store⟩ ⟨.ret value,k,final⟩ := by simpa only [mv,ms,mc] using m.evidence
    have sourcePath (k : List Core.Frame) := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation counted original (by rfl) k
    have mappedPath (k : List Core.Frame) := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation renamedCost mappedElab (by rfl) k
    have _ := (sourcePath []).final_unique (literal [])
    have records : ∀ fuel, (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b).map
        (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel env).values store))) =
        some (.word,Core.runStateful fuel (.initial core env.values store)) := by
      intro fuel; rw [accepted,Option.map_some,Resolved.LocalScope.values_mapIds]
    let e1 := word 15::env.values; let e2 := word 15::e1
    let scr := if cost=52 then word 15 else value; let e3 := scr::e2
    let cps : List (Nat × Core.State) := [
      (10,⟨.ret (.cellRef .word 2),[.letBody (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1))) [word 14,.bool false],.letBody tailCore env.values],store++[word 14]⟩),
      (17,⟨.eval tailCore e1,[],store++[word 14]⟩),(29,⟨.ret .unit,[.letBody (.loadCell (.var 2)) [word 15,.cellRef .word w],.letBody matchCore e1],final⟩),
      (34,⟨.eval matchCore e2,[],final⟩),(43,⟨.ret scr,[.letBody chooseCore e2],final⟩),
      (49,⟨.ret (word 15),[.binaryApply .wordEq scr,.ifBranches (.var 1) (.apply (.var 6) (.var 1)) e3],final⟩),
      (51,⟨.eval (if cost=52 then .var 1 else .apply (.var 6) (.var 1)) e3,[],final⟩)]
    for (spent,cp) in cps do
      if genuine : Core.runStateful spent (.initial core env.values store)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        have _ := (records spent).trans (congrArg (fun result => some (Core.Ty.word,result)) genuine)
        check (decide (Core.runStateful (cost-spent) cp=.done value final)) "original saved allocator/writer/scrutinee/comparison/selected body"
      else throw (IO.userError "literal checkpoint")
    for fuel in List.range (cost+2) do
      have _ := records fuel; have _ := (literal []).runStateful_done_iff (fuel := fuel)
      check (decide ((elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b).map
        (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel env).values store)))=some (.word,Core.runStateful fuel (.initial core env.values store)))) "same complete code/tag/store/checkpoint"
      match stopped : Core.runStateful fuel (.initial core env.values store) with
      | .done v s => check (decide (cost≤fuel ∧ v=value ∧ s=final)) "fixed original value/store/exact cost"
      | .outOfFuel cp =>
          have _ := (literal []).residual_of_outOfFuel stopped
          for more in [0,1,cost-fuel,cost+2] do
            check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core (Resolved.LocalScope.mapIds relabel env).values store))) "all genuine full resumptions"
      | .fault _ _ => throw (IO.userError "success fault")
    let k := [Core.Frame.pairApply (.cellRef .word 700)]
    have _ := literal k; have _ := sourcePath k; have _ := mappedPath k
    check (decide (Core.runStateful (cost+1) ⟨.eval core (Resolved.LocalScope.mapIds relabel env).values,k,store⟩=.done (.pair (.cellRef .word 700) value) final)) "unchanged actual pending caller"
  else throw (IO.userError "independent original source and literal Core expectations")
private def faults : IO Unit := do
  let b ← parsed; let p ← body inputs b
  for mode in List.range 4 do
    let w := if mode=0 then 700 else if mode=2 then 0 else 2; let r := if mode=1 then 700 else if mode=2 then 1 else 2
    let x := if mode=3 then Core.Value.bool false else word 14; let env := environment w r x
    let store := if mode=2 then [word 41,.bool false] else [word 41,word 99]
    let e1 := word 15::env.values; let e2 := word 15::e1; let e3 := Core.Value.bool false::e2
    let final := if mode=0 ∨ mode=3 then store++[x] else if mode=2 then [word 15,.bool false,word 14] else [word 41,word 99,word 15]
    let (threshold,cp,failed,error) : Nat × Core.State × Core.State × Core.MachineFault :=
      if mode=0 then
        let k := [Core.Frame.storeCellValue (.var 0) [word 15,.cellRef .word w],.letBody (.loadCell (.var 2)) [word 15,.cellRef .word w],.letBody matchCore e1]
        (26,⟨.eval (.var 1) [word 15,.cellRef .word w],k,final⟩,⟨.ret (.cellRef .word w),k,final⟩,.invalidCellLocation 700)
      else if mode=1 then
        let k := [Core.Frame.loadCellApply,.letBody chooseCore e2]
        (42,⟨.eval (.var 1) [word 15,.cellRef .word r],k,final⟩,⟨.ret (.cellRef .word r),k,final⟩,.invalidCellLocation 700)
      else if mode=2 then
        let k := [Core.Frame.binaryApply .wordEq (.bool false),.ifBranches (.var 1) (.apply (.var 6) (.var 1)) e3]
        (49,⟨.eval (.word (Core.Word.ofNatModulo 15)) e3,k,final⟩,⟨.ret (word 15),k,final⟩,.invalidBinaryOperands .wordEq (.bool false) (word 15))
      else
        let k := [Core.Frame.binaryApply .wordAdd (.bool false),.letBody tailCore env.values]
        (15,⟨.eval (.word (Core.Word.ofNatModulo 1)) [.cellRef .word 2,x,.bool false],k,final⟩,⟨.ret (word 1),k,final⟩,.invalidBinaryOperands .wordAdd x (word 1))
    if fixed : p.core=core ∧ p.type=.word then
      have original : RecursiveComputationReturnTreeElaborates types owner inputs b core .word := by simpa only [fixed.1,fixed.2] using p.evidence
      have _ := (computationReturnTreeElaborates_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mpr original
      check (decide (Core.runStateful (threshold-1) (.initial core env.values store)=.outOfFuel cp ∧ Core.runStateful 1 cp=.fault error failed)) "independently fixed first fault and preserved earlier effects"
      for fuel in List.range (threshold+2) do
        check (decide ((elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b).map (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel env).values store)))=some (.word,Core.runStateful fuel (.initial core env.values store)))) "same mapped code/tag/full fault records"
        match Core.runStateful fuel (.initial core env.values store) with
        | .fault err st => check (decide (threshold≤fuel ∧ err=error ∧ st=failed)) "fixed first fault and entire saved state"
        | .outOfFuel saved => check (decide (fuel<threshold ∧ Core.runStateful (threshold-fuel) saved=.fault error failed)) "all fault checkpoint resumptions"
        | .done _ _ => throw (IO.userError "invalid actual input completed")
    else throw (IO.userError "actual inputs changed original static evidence")
end ParsedComputationRawOwnerEffects
open ParsedComputationRawOwnerEffects in
def frontendParsedComputationRawOwnerEffectTests : IO Unit := do
  have _ := non_surjective
  exercise 2 2 [word 41,word 99] [word 41,word 99,word 15] (word 15) 52
  exercise 0 1 [word 41,word 99] [word 15,word 99,word 14] (word 99) 59
  exercise 0 1 [word 41,word 15] [word 15,word 15,word 14] (word 15) 52
  exercise 2 2 [.bool true,word 99] [.bool true,word 99,word 15] (word 15) 52
  faults
end Tests

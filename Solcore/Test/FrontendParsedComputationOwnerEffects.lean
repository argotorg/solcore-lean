import Solcore.Syntax.Parser.Term
import Solcore.Frontend.ComputationReturnTreeOwnerProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationRenamingProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.FuelResumptionProperties
/-! Original repeated-name lets retain old-input initializers and fresh indices
under owner-only relabeling. Actual cells and captures are never mapped. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedComputationOwnerEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ComputationOwnerEffects",by decide⟩],by decide⟩⟩,128⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex := 903}
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex := o.declarationIndex+10}
private theorem injective : Function.Injective shift := by rintro ⟨lm,li⟩ ⟨rm,ri⟩ same; simpa [shift] using same
private theorem non_surjective : ¬ Function.Surjective shift := by
  intro h; obtain ⟨o,same⟩ := h {owner with declarationIndex := 0}
  have h := congrArg Resolved.DeclarationId.declarationIndex same; simp [shift] at h
private def relabel := ownerLocalIdMap shift
private theorem relabel_injective : Function.Injective relabel := ownerLocalIdMap_injective shift injective
private def inputs : LocalTypeInputs := ⟨[
  ⟨"x",⟨owner,7⟩,.word⟩,⟨"c",⟨foreign,4⟩,.bool⟩,⟨"a",⟨owner,31⟩,.function .word .word⟩,
  ⟨"w",⟨foreign,700⟩,.function .word .word⟩,⟨"r",⟨owner,3⟩,.function .word .word⟩,⟨"x",⟨foreign,21⟩,.bool⟩],by decide⟩
private def mapped := inputs.mapIds relabel relabel_injective
private def types : TypeNameTable := [(["Word"],.word),(["Word"],.bool)]
private def word (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def allocator : Core.Value := .closure .word .word
  (.letE (.newCell .word (.var 0)) (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1)))) [.bool false]
private def writer (l : Nat) : Core.Value := .closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l]
private def reader (l : Nat) : Core.Value := .closure .word .word (.loadCell (.var 1)) [.cellRef .word l]
private def environment (c : Core.Value) (w r : Nat) (x : Core.Value := word 14) : Resolved.Environment :=
  [(⟨owner,7⟩,x),(⟨foreign,4⟩,c),(⟨owner,31⟩,allocator),(⟨foreign,700⟩,writer w),(⟨owner,3⟩,reader r),(⟨foreign,21⟩,.bool true)]
private def yesCore : Core.Expr := .letE (.apply (.var 6) (.var 0)) (.var 0)
private def noCore : Core.Expr := .letE (.apply (.var 5) (.apply (.var 6) (.var 0))) (.var 0)
private def afterCore : Core.Expr := .ifE (.var 3) yesCore noCore
private def tailCore : Core.Expr := .letE (.apply (.var 4) (.var 0)) afterCore
private def core : Core.Expr := .letE (.apply (.var 2) (.var 0)) tailCore
private def parsed : IO Syntax.Block := do
  let text := "{let x:Word=a(x);let x=w(x);if(c){{let x:Word=r(x);return x;}}else{{let x=w(r(x));return x;}}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"computation-owner-effects.sol"⟩,text⟩
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
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (RecursiveComputationReturnTreeElaborates types owner i b)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; return ⟨r.core,r.type,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← body i ⟨span,statements⟩; return ⟨r.core,r.type,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child i e; let next := i.bindFresh owner name.value a.type
      let fresh := 32+(i.bindings.length-inputs.bindings.length)
      check (decide (next.names.tail=i.names ∧ next.context.tail=i.context ∧ next.ids.head?=some ⟨owner,fresh⟩ ∧ i.names.lookup? "x"=some ⟨owner,if fresh=32 then 7 else fresh-1⟩)) "old initializer and fresh32/33/34 tail row"
      have commutes := LocalTypeInputs.bindFresh_mapOwner i owner shift injective name.value a.type
      check (decide (((i.mapIds relabel relabel_injective).bindFresh (shift owner) name.value a.type).ids.head?=some ⟨shift owner,fresh⟩)) "foreign binder700 ignored; same fresh index after owner map"
      let r ← body next ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some t => let m ← meaning t; if same : m.1=a.type then return ⟨.letE a.core r.core,r.type,by rw [shape,ann]; exact .binding (same ▸ m.2.down) a.evidence r.evidence⟩ else throw (IO.userError "typed initializer")
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← child i c; let t ← body i yes; let e ← body i no
      match barrier : yes with
      | ⟨_,[⟨_,.block _⟩]⟩ =>
          have protection : ComputationNamesProtected (i.names.map Prod.fst) yes := by intro name exposed; rw [barrier] at exposed; cases exposed with | tail impossible => cases impossible
          if same : a.type=.bool ∧ t.type=e.type then return ⟨.ifE a.core t.core e.core,t.type,by rw [shape]; exact .conditional (same.1 ▸ a.evidence) protection t.evidence (same.2.symm ▸ e.evidence)⟩ else throw (IO.userError "branch type")
      | _ => throw (IO.userError "original explicit then scope barrier")
  | _ => throw (IO.userError "original body")
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
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩ | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ => let r ← rawBody table env s ⟨span,statements⟩; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .block r.evidence⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      match ann : annotation with
      | none => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .inferred a.evidence r.evidence⟩
      | some _ => return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape,ann]; exact .binding a.evidence r.evidence⟩
  | ⟨_,[⟨_,.ifThen c yes (some no)⟩]⟩ =>
      let a ← rawChild table env s c
      match cv : a.value with
      | .bool true => let r ← rawBody table env a.final yes; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .ifTrue (cv ▸ a.evidence) r.evidence⟩
      | .bool false => let r ← rawBody table env a.final no; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .ifFalse (cv ▸ a.evidence) r.evidence⟩
      | _ => throw (IO.userError "raw condition")
  | _ => throw (IO.userError "raw body")
termination_by sizeOf b

private def exercise (c : Bool) (w r : Nat) (store middle final : Core.Store) (value : Core.Value) : IO Unit := do
  let b ← parsed; let p ← body inputs b; let env := environment (.bool c) w r
  let m ← path 70 core env.values store; let a ← rawBody inputs.names env store b
  let cost := if c then 48 else 62
  if fixed : p.core=core ∧ p.type=.word ∧ m.value=value ∧ m.final=final ∧ m.cost=cost ∧ a.value=value ∧ a.final=final ∧ a.cost=cost then
    have original : RecursiveComputationReturnTreeElaborates types owner inputs b core .word := by simpa only [fixed.1,fixed.2.1] using p.evidence
    have typed := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,original⟩
    have renamed := (computationReturnTreeElaborates_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mpr original
    have _ := (computationReturnTreeElaborates_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mp renamed
    have _ := (computationReturnTreeHasType_mapOwner_iff shift injective (recursiveLocalComputationHasType_mapIds_iff relabel relabel_injective)).mpr typed
    have old := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original
    have accepted := (elaborateComputationReturnTree?_mapOwner shift injective elaborateRecursiveLocalComputation?
      (elaborateRecursiveLocalComputation?_mapIds relabel relabel_injective) types owner inputs b).trans old
    have mappedAccepted : elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b=some (core,.word) := by simpa only [mapped,relabel] using accepted
    have values : (Resolved.LocalScope.mapIds relabel env).values=env.values := Resolved.LocalScope.values_mapIds relabel env
    have literal : ∀ k, Core.Steps cost ⟨.eval core env.values,k,store⟩ ⟨.ret value,k,final⟩ := by simpa only [fixed.2.2.1,fixed.2.2.2.1,fixed.2.2.2.2.1] using m.evidence
    have counted : RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names env store b value final cost := by simpa only [fixed.2.2.2.2.2.1,fixed.2.2.2.2.2.2.1,fixed.2.2.2.2.2.2.2] using a.evidence
    have sourcePath (k : List Core.Frame) := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation counted original (by rfl) k
    have _ := (sourcePath []).final_unique (literal [])
    have records : ∀ fuel, (elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b).map
        (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel env).values store))) =
        some (.word,Core.runStateful fuel (.initial core env.values store)) := by intro fuel; rw [mappedAccepted,Option.map_some,values]
    let e1 := word 15::env.values; let e2 := word 15::e1
    let cps : List (Nat × Core.State) := [
      (10,⟨.ret (.cellRef .word 2),[.letBody (.binary .wordAdd (.var 1) (.word (Core.Word.ofNatModulo 1))) [word 14,.bool false],.letBody tailCore env.values],store++[word 14]⟩),
      (17,⟨.eval tailCore e1,[],store++[word 14]⟩),(29,⟨.ret .unit,[.letBody (.loadCell (.var 2)) [word 15,.cellRef .word w],.letBody afterCore e1],middle⟩),
      (34,⟨.eval afterCore e2,[],middle⟩),
      (36,⟨.ret (.bool c),[.ifBranches yesCore noCore e2],middle⟩),(cost-1,⟨.eval (.var 0) (value::e2),[],final⟩)]
    for (spent,cp) in cps do
      if genuine : Core.runStateful spent (.initial core env.values store)=.outOfFuel cp then
        have _ := (literal []).residual_of_outOfFuel genuine
        have mappedCheckpoint := (records spent).trans (congrArg (fun result => some (Core.Ty.word,result)) genuine)
        check (decide (Core.runStateful spent (.initial core (Resolved.LocalScope.mapIds relabel env).values store)=.outOfFuel cp ∧ Core.runStateful (cost-spent) cp=.done value final)) "same literal fresh-tail/conditional/final-let checkpoint"
      else throw (IO.userError "literal checkpoint")
    for fuel in List.range (cost+2) do
      have _ := records fuel; have _ := (literal []).runStateful_done_iff (fuel := fuel)
      check (decide ((elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b).map
        (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel env).values store)))=some (.word,Core.runStateful fuel (.initial core env.values store)))) "same full checker/code/tag/run"
      match stopped : Core.runStateful fuel (.initial core env.values store) with
      | .done v s => check (decide (cost≤fuel ∧ v=value ∧ s=final)) "fixed actual value/store/threshold"
      | .outOfFuel cp =>
          have _ := (literal []).residual_of_outOfFuel stopped
          for more in [0,1,cost-fuel,cost+2] do
            check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial core (Resolved.LocalScope.mapIds relabel env).values store))) "genuine full saved/resumed state"
      | .fault _ _ => throw (IO.userError "success fault")
    let k := [Core.Frame.pairApply (.cellRef .word 700)]
    have _ := literal k; have _ := sourcePath k
    check (decide (Core.runStateful (cost+1) ⟨.eval core (Resolved.LocalScope.mapIds relabel env).values,k,store⟩=.done (.pair (.cellRef .word 700) value) final)) "literal pending caller untouched"
  else throw (IO.userError "original raw/static/manual fixed expectations")
private def faults : IO Unit := do
  let b ← parsed; let p ← body inputs b
  for mode in List.range 4 do
    let w := if mode=0 then 700 else 2; let r := if mode=1 then 700 else 2
    let c := if mode=2 then word 14 else Core.Value.bool true; let x := if mode=3 then Core.Value.bool false else word 14
    let env := environment c w r x; let store := [word 41,word 99]
    let e1 := word 15::env.values; let e2 := word 15::e1
    let written := [word 41,word 99,word 15]; let allocated := store++[x]
    let writeK : List Core.Frame := [.storeCellValue (.var 0) [word 15,.cellRef .word w],.letBody (.loadCell (.var 2)) [word 15,.cellRef .word w],.letBody afterCore e1]
    let loadK : List Core.Frame := [.loadCellApply,.letBody (.var 0) e2]
    let ifK : List Core.Frame := [.ifBranches yesCore noCore e2]
    let addK : List Core.Frame := [.binaryApply .wordAdd (.bool false),.letBody tailCore env.values]
    let (threshold,cp,failed,error) : Nat × Core.State × Core.State × Core.MachineFault :=
      if mode=0 then (26,⟨.eval (.var 1) [word 15,.cellRef .word w],writeK,allocated⟩,⟨.ret (.cellRef .word w),writeK,allocated⟩,.invalidCellLocation 700)
      else if mode=1 then (45,⟨.eval (.var 1) [word 15,.cellRef .word r],loadK,written⟩,⟨.ret (.cellRef .word r),loadK,written⟩,.invalidCellLocation 700)
      else if mode=2 then (36,⟨.eval (.var 3) e2,ifK,written⟩,⟨.ret c,ifK,written⟩,.expectedBool c)
      else (15,⟨.eval (.word (Core.Word.ofNatModulo 1)) [.cellRef .word 2,x,.bool false],addK,allocated⟩,⟨.ret (word 1),addK,allocated⟩,.invalidBinaryOperands .wordAdd x (word 1))
    if fixed : p.core=core ∧ p.type=.word then
      have original : RecursiveComputationReturnTreeElaborates types owner inputs b core .word := by simpa only [fixed.1,fixed.2] using p.evidence
      have _ := (computationReturnTreeElaborates_mapOwner_iff shift injective (recursiveLocalComputationElaborates_mapIds_iff relabel relabel_injective)).mpr original
      have _ := elaborateComputationReturnTree?_mapOwner shift injective elaborateRecursiveLocalComputation? (elaborateRecursiveLocalComputation?_mapIds relabel relabel_injective) types owner inputs b
      check (decide (Core.runStateful (threshold-1) (.initial core env.values store)=.outOfFuel cp ∧ Core.runStateful 1 cp=.fault error failed)) "original malformed actual values/captures fault after preserved effects"
      for fuel in List.range (threshold+3) do
        let actual := Core.runStateful fuel (.initial core env.values store)
        check (decide ((elaborateComputationReturnTree? elaborateRecursiveLocalComputation? types (shift owner) mapped b).map
          (fun (ce,ty) => (ty,Core.runStateful fuel (.initial ce (Resolved.LocalScope.mapIds relabel env).values store)))=some (.word,actual))) "same complete mapped fault/absence/checkpoint record"
        match actual with
        | .fault err st => check (decide (threshold≤fuel ∧ err=error ∧ st=failed)) "first fault cost/full state"
        | .outOfFuel saved => check (decide (fuel<threshold ∧ Core.runStateful (threshold-fuel) saved=.fault error failed ∧
            Core.runStateful 1 saved=Core.runStateful (fuel+1) (.initial core (Resolved.LocalScope.mapIds relabel env).values store))) "all genuine fault resumptions"
        | .done _ _ => throw (IO.userError "malformed actual input completed")
    else throw (IO.userError "actual input changed original body typing")
end ParsedComputationOwnerEffects
open ParsedComputationOwnerEffects in
def frontendParsedComputationOwnerEffectTests : IO Unit := do
  have _ := non_surjective
  for c in [false,true] do
    exercise c 0 1 [word 41,word 99] [word 15,word 99,word 14] (if c then [word 15,word 99,word 14] else [word 99,word 99,word 14]) (word 99)
    exercise c 2 2 [word 41,word 99] [word 41,word 99,word 15] [word 41,word 99,word 15] (word 15)
    -- Raw reads/writes may carry Bool under a static Word tag; no runtime-world premise is supplied.
    exercise c 0 1 [word 41,.bool false] [word 15,.bool false,word 14] (if c then [word 15,.bool false,word 14] else [.bool false,.bool false,word 14]) (.bool false)
  faults
end Tests

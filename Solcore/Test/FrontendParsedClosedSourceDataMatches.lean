import Solcore.Frontend.ClosedSourceDataBodyProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.LocalExpressionCostErasureProperties
import Solcore.Frontend.ComputationReturnTreeEvaluationProperties
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalExpressionCostProperties
import Solcore.Syntax.Parser.Term
/- Original arms, pattern proofs and two body derivations precede search.
The selected body is read from the AST; image witnesses are eliminated only in Prop. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceDataMatches
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"DataMatches",by decide⟩],by decide⟩⟩,174⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=901},700⟩
private def up (e : Resolved.Environment) := e.map (fun row => (row.1,RuntimeValue.ofCore row.2))
private structure EC (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (src : Syntax.Expr) (v : Core.Value) (cost : Nat) : Type where
  gate : ClosedSourceDataExpression src
  closed : ClosedSourceExpressionEvaluates owner t (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore v) (s.map RuntimeValue.ofCore)
  old : LocalExpressionEvaluatesWithCost t e s src v s cost
private structure BC (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store)
    (src : Syntax.Block) (v : Core.Value) (cost : Nat) : Type where
  gate : ClosedSourceDataBody src
  closed : ClosedSourceBodyEvaluates owner t (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore v) (s.map RuntimeValue.ofCore)
  old : ComputationReturnTreeEvaluatesWithCost LocalExpressionEvaluatesWithCost owner t e s src v s cost
private theorem mapped {e : Resolved.Environment} {i : Resolved.LocalId} {v : Core.Value}
    (h : Resolved.LocalScope.Lookup e i v) : Resolved.LocalScope.Lookup (up e) i (RuntimeValue.ofCore v) := by
  induction h with | head => exact .head | tail different _ ih => exact .tail different ih
private def ref (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr)
    (name : String) (i : Resolved.LocalId) (v : Core.Value)
    (n : LocalNameTable.Lookup t name i) (f : Resolved.LocalScope.Lookup e i v) : IO (EC t e s src v 1) := do
  match shape : src with
  | ⟨_,.identifier actual⟩ =>
    if h : actual.value=name then return by rw [shape]; exact ⟨.reference,.reference (h ▸ n) (mapped f),.identifier (h ▸ n) f⟩
    else throw (IO.userError "original identifier spelling")
  | _ => throw (IO.userError "original identifier shape")
private def ret (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block)
    (name : String) (i : Resolved.LocalId) (v : Core.Value)
    (n : LocalNameTable.Lookup t name i) (f : Resolved.LocalScope.Lookup e i v) : IO (BC t e s src v 1) := do
  match shape : src with
  | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ =>
    let h ← ref t e s child name i v n f
    return by rw [shape]; exact ⟨.expression h.gate,.expression h.closed,.expression h.old⟩
  | _ => throw (IO.userError "original expression return")
private def inputs : LocalTypeInputs := ⟨[
  ⟨"x",sid 7,.unit⟩,⟨"saved",sid 3,.unit⟩,⟨"c",sid 31,.bool⟩,
  ⟨"d",sid 11,.bool⟩,⟨"tag",foreign,.word⟩],by decide⟩
private def environment (x saved : Core.Value) (c d : Bool) (tag : Core.Value) : Resolved.Environment :=
  [(sid 7,x),(sid 3,saved),(sid 31,.bool c),(sid 11,.bool d),(foreign,tag)]
private def parsed (text : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main,"data-matches.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.block .require (Syntax.Parser.State.initial file lexed) with
  | .ok body next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && body.span==Syntax.SourceSpan.fullFile file) "original whole block/EOF/spans"
    return body
  | _ => throw (IO.userError "original block parser")
private def zero : Core.Word := ⟨0,by decide⟩
private def literal (p : Syntax.Pattern) : IO (PLift (WordMatchPatternClassifies p (some zero))) := do
  match shape : p with
  | ⟨_,.literal ⟨ls,.decimal spelling⟩⟩ =>
    if h : spelling="0" then
      return by
        apply PLift.up; rw [shape]; refine .literal ⟨_,rfl,?_⟩; subst spelling
        exact .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) (by decide)) .nil)
    else throw (IO.userError "original zero spelling")
  | _ => throw (IO.userError "original literal pattern")
private def wildcard (p : Syntax.Pattern) : IO (PLift (WordMatchPatternClassifies p none)) := do
  match shape : p with
  | ⟨a,.group ⟨b,.group ⟨c,.wildcard marker⟩⟩⟩ =>
    check (a.endByte-a.startByte==5 && b.startByte==a.startByte+1 && b.endByte+1==a.endByte && c==marker && c.startByte==b.startByte+1 && c.endByte+1==b.endByte) "original double-group wildcard spans"
    return by apply PLift.up; rw [shape]; exact .group (.group (.wildcard rfl))
  | _ => throw (IO.userError "original grouped wildcard")
private structure Tail (e : Resolved.Environment) (s : Core.Store) (v : Core.Value) (w : Core.Word)
    (rest : List Syntax.MatchCase) (fallback : Option Syntax.Block) : Type where
  body : Syntax.Block
  cert : BC inputs.names e s body v 1
  gates : ∀ arm ∈ rest, ClosedSourceDataBody arm.value.body
  defaults : ∀ b ∈ fallback.toList, ClosedSourceDataBody b
  old : WordMatchChooses (.word w) rest fallback body 0
  closed : RuntimeWordMatchChooses (.word w) rest fallback body 0
private def originalTail (e : Resolved.Environment) (s : Core.Store) (v : Core.Value) (w : Core.Word)
    (rest : List Syntax.MatchCase) (fallback : Option Syntax.Block)
    (found : Resolved.LocalScope.Lookup e (sid 3) v) : IO (Tail e s v w rest fallback) := do
  match shape : (rest,fallback) with
  | ([arm],none) =>
    let hg := (← wildcard arm.value.pattern).down
    let hb ← ret inputs.names e s arm.value.body "saved" (sid 3) v (.tail (by decide) .head) found
    return by cases shape; exact ⟨arm.value.body,hb,by intro a ha; simp only [List.mem_singleton] at ha; exact ha ▸ hb.gate,by simp,.wildcard hg,.wildcard hg⟩
  | ([],some body) =>
    let hb ← ret inputs.names e s body "saved" (sid 3) v (.tail (by decide) .head) found
    return by cases shape; exact ⟨body,hb,by simp,by intro b hb'; simp only [Option.toList,List.mem_singleton] at hb'; exact hb' ▸ hb.gate,.fallback,.fallback⟩
  | _ => throw (IO.userError "original wildcard or default tail")
private def compared (src : Syntax.Block) (x saved : Core.Value) (w : Core.Word) (s : Core.Store) :
    IO (BC inputs.names (environment x saved true true (.word w)) s src (if w=zero then x else saved) 11) := do
  let e := environment x saved true true (.word w)
  match shape : src with
  | ⟨_,[⟨_,.matchWith ⟨_,⟨guard,[]⟩⟩ ⟨_,⟨first::rest,fallback⟩⟩⟩]⟩ =>
    let hg ← ref inputs.names e s guard "tag" foreign (.word w)
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    let meaning := (← literal first.value.pattern).down
    let ht ← ret inputs.names e s first.value.body "x" (sid 7) x .head .head
    let hf ← originalTail e s saved w rest fallback (.tail (by decide) .head)
    return by
      rw [shape]; refine ⟨.wordMatch hg.gate ?_ hf.defaults,?_,?_⟩
      · intro arm member; rcases List.mem_cons.mp member with rfl|member; exact ht.gate; exact hf.gates _ member
      · by_cases eq : w=zero
        · subst w; simp only [↓reduceIte]; exact .wordMatch (by simpa only [RuntimeValue.ofCore] using hg.closed) (.hit meaning) ht.closed
        · simp only [eq,↓reduceIte]; exact .wordMatch (by simpa only [RuntimeValue.ofCore] using hg.closed) (.miss meaning eq hf.closed) hf.cert.closed
      · by_cases eq : w=zero
        · subst w; simp only [↓reduceIte]; exact ComputationReturnTreeEvaluatesWithCost.wordMatch hg.old (.hit meaning) ht.old
        · simp only [eq,↓reduceIte]; exact ComputationReturnTreeEvaluatesWithCost.wordMatch hg.old (.miss meaning eq hf.old) hf.cert.old
  | _ => throw (IO.userError "original literal-headed match")
private def immediate (src : Syntax.Block) (x saved tag : Core.Value) (s : Core.Store) (bare : Bool) :
    IO (BC inputs.names (environment x saved true true tag) s src (if bare then .unit else x) 4) := do
  let e := environment x saved true true tag
  match shape : src with
  | ⟨_,[⟨_,.matchWith ⟨_,⟨guard,[]⟩⟩ ⟨_,⟨cases,fallback⟩⟩⟩]⟩ =>
    let hg ← ref inputs.names e s guard "tag" foreign tag
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    if hb : bare then
      match arms : (cases,fallback) with
      | ([],some ⟨bs,[⟨rs,.returnStmt none⟩]⟩) =>
        return by
          rw [shape]; cases arms; simp only [hb,↓reduceIte]; refine ⟨.wordMatch hg.gate (by simp) ?_,?_,?_⟩
          · intro b member; simp only [Option.toList,List.mem_singleton] at member; subst b; exact .bare
          · simp only [RuntimeValue.ofCore]; exact .wordMatch hg.closed .fallback .bare
          · exact ComputationReturnTreeEvaluatesWithCost.wordMatch hg.old .fallback .bare
      | _ => throw (IO.userError "original default bare return")
    else
      match arms : (cases,fallback) with
      | ([first,second],none) =>
        let meaning := (← wildcard first.value.pattern).down
        let ht ← ret inputs.names e s first.value.body "x" (sid 7) x .head .head
        let hf ← ret inputs.names e s second.value.body "saved" (sid 3) saved (.tail (by decide) .head) (.tail (by decide) .head)
        return by
          rw [shape]; cases arms; simp only [hb]; refine ⟨.wordMatch hg.gate ?_ (by simp),.wordMatch hg.closed (.wildcard meaning) ht.closed,?_⟩
          · intro arm member; rcases List.mem_cons.mp member with rfl|member; exact ht.gate; simp only [List.mem_singleton] at member; exact member ▸ hf.gate
          · exact ComputationReturnTreeEvaluatesWithCost.wordMatch hg.old (.wildcard meaning) ht.old
      | _ => throw (IO.userError "original ignored suffix match")
  | _ => throw (IO.userError "original immediate match")
private def exercise (t : LocalNameTable) (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Block)
    (v : Core.Value) (cost depth : Nat) (h : BC t e s src v cost) (withCore : Bool) : IO Unit := do
  let old := (computationReturnTreeEvaluates_iff_exists_cost localExpressionEvaluates_iff_exists_cost).mpr ⟨cost,h.old⟩
  for budget in [0,depth-1,depth,depth+2] do
    match ran : evaluateClosedSourceBody? budget owner t (up e) (s.map RuntimeValue.ofCore) src with
    | none => check (budget<depth) "closed depth exhaustion"
    | some (mv,ms) =>
      have actual := evaluateClosedSourceBody?_sound ran
      have rawImage := h.gate.local_evaluates_iff.mp actual
      proof (show mv=RuntimeValue.ofCore v ∧ ms=s.map RuntimeValue.ofCore from by
        obtain ⟨a,b,hv,hs,ev⟩ := rawImage
        obtain ⟨k,hk⟩ := (computationReturnTreeEvaluates_iff_exists_cost localExpressionEvaluates_iff_exists_cost).mp ev
        obtain ⟨vv,ss,_⟩ := hk.deterministic (fun aa bb => aa.deterministic bb) h.old
        exact ⟨hv.trans (congrArg _ vv),hs.trans (congrArg _ ss)⟩)
      proof (h.gate.local_evaluates_iff.mpr rawImage)
      proof ((h.gate.local_evaluates_iff.mpr ⟨v,s,rfl,rfl,old⟩).deterministic h.closed)
      if withCore then
        if ht : t=inputs.names then
          if aligned : e.ids=inputs.context.ids then
            match accepted : elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner inputs src with
            | none => throw (IO.userError "whole checker")
            | some (core,ty) =>
              have image := (h.gate.core_evaluates_iff accepted aligned).mp (ht ▸ actual)
              proof image
              check (ty==.unit) "actual whole checked type"
              for fuel in [0,cost-1,cost,cost+1] do
                match runCore : Core.runStateful fuel (.initial core e.values s) with
                | .done a b =>
                  have ev := Core.runStateful_evaluation_sound runCore
                  proof (show ClosedSourceBodyEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) src mv ms from by
                    obtain ⟨x,y,hx,hy,oldCore⟩ := image
                    have ⟨vx,vs⟩ := Core.evaluation_deterministic oldCore ev
                    exact (h.gate.core_evaluates_iff accepted aligned).mpr ⟨a,b,hx.trans (congrArg _ vx),hy.trans (congrArg _ vs),ev⟩)
                  check (a==v && b==s && cost<=fuel && mv.toCore?==some a && ms.mapM RuntimeValue.toCore?==some b) "actual whole payload/store and transition cost"
                | .outOfFuel _ => check (fuel<cost) "Core transition exhaustion"
                | .fault _ _ => throw (IO.userError "unexpected Core fault")
          else throw (IO.userError "full runtime ID order")
        else throw (IO.userError "unique static names")
      check (mv.toCore?==some v && ms.mapM RuntimeValue.toCore?==some s && depth<=budget) "actual raw full image"
end ParsedClosedSourceDataMatches
open Solcore Solcore.Frontend ParsedClosedSourceDataMatches
def frontendParsedClosedSourceDataMatchTests : IO Unit := do
  let x : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let saved : Core.Value := .hostFunction .storageWrite
  let cell : Core.Value := .cellRef (.function .unit .word) 700
  for withDefault in [true,false] do
    let src ← parsed (if withDefault then "{match(tag){case 0{return x;}default{return saved;}}}" else
      "{match(tag){case 0{return x;}case ((_)){return saved;}}}")
    for w in [zero,⟨1,by decide⟩] do
      for s in [[],[x,cell]] do
        let h ← compared src x saved w s
        exercise inputs.names (environment x saved true true (.word w)) s src (if w=zero then x else saved) 11 3 h true
    let bad := environment x saved true true cell
    check ((evaluateClosedSourceBody? 40 owner inputs.names (up bad) [] src).isNone &&
      (elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner inputs src).isSome) "non-Word before literal is actual None despite whole checker success"
  for kind in [2,3,4] do
    let src ← parsed (if kind==2 then "{match(tag){case ((_)){return x;}case 0{return saved;}}}" else if kind==3 then
      "{match(tag){default{return;}}}" else "{match(tag){case ((_)){return x;}case \"bad\"{return saved;}}}")
    for tag in [x,saved,cell,.word zero] do
      for s in [[],[x,cell]] do
        let bare := kind==3
        let h ← immediate src x saved tag s bare
        exercise inputs.names (environment x saved true true tag) s src (if bare then .unit else x) 4 (if bare then 2 else 3) h (kind != 4)
        check ((elaborateComputationReturnTree? elaborateLocalExpression? [(["Unit"],.unit)] owner inputs src).isSome==(kind != 4)) "all original patterns checked despite wildcard short-circuit"
  IO.println "ADR0294 parsed ordered literal/wildcard/default image and whole-pattern boundaries GREEN"
end Tests

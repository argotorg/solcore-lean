import Solcore.Frontend.ClosedSourceDataBodyDepthDecisionProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Syntax.Parser.Term

/- Actual parsed bodies retain independent whole AST/ranges and original raw
witnesses before the depth laws. Typed/inferred fresh rows, ordered match choice,
arbitrary mixed payloads and full stores remain literal. Comparison counts are
not source-search depths or Core transition costs; source calls are not covered. -/
set_option autoImplicit false
namespace Tests.ParsedDataBodyDepthBridge
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedBodyDepth",by decide⟩],by decide⟩⟩,303⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=904},700⟩
private def names : LocalNameTable := [("x",sid 7),("y",sid 8),("tag",foreign),("x",sid 99),("y",sid 99)]
private def rows (tag p q : V) (tail : Resolved.LocalScope V) :=
  [(sid 8,q),(sid 7,p),(foreign,tag),(sid 7,.unit),(foreign,.unit)]++tail
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (n : String) : Syntax.Expr :=
  ⟨span f a b,.identifier ⟨span f a b,n⟩⟩
private def ret (f : Syntax.SourceFile) (a b c d e : Nat) (n : String) : Syntax.Block :=
  ⟨span f a e,[⟨span f b (d+1),.returnStmt (some (ref f c d n))⟩]⟩
private def bindingAST (f : Syntax.SourceFile) : Syntax.Block :=
  ⟨span f 0 36,[⟨span f 1 14,.letDecl ⟨span f 5 6,"x"⟩
    (some ⟨span f 7 11,.named ⟨span f 7 11,⟨⟨⟨span f 7 11,"Unit"⟩,[]⟩⟩⟩ none⟩) (some (ref f 12 13 "x"))⟩,
    ⟨span f 14 22,.letDecl ⟨span f 18 19,"x"⟩ none (some (ref f 20 21 "x"))⟩,
    ⟨span f 22 24,.expression (ref f 22 23 "x") true⟩,
    ⟨span f 24 35,.block (ret f 24 25 32 33 35 "x").value⟩]⟩
private def matchAST (fallback : Bool) (f : Syntax.SourceFile) : Syntax.Block :=
  let endByte := if fallback then 49 else 48
  let first : Syntax.MatchCase := ⟨span f 12 29,⟨⟨span f 17 18,.literal ⟨span f 17 18,.decimal "0"⟩⟩,
    ret f 18 19 26 27 29 "x"⟩⟩
  let second : Syntax.MatchCase := ⟨span f 29 46,⟨⟨span f 34 35,.wildcard (span f 34 35)⟩,
    ret f 35 36 43 44 46 "y"⟩⟩
  ⟨span f 0 endByte,[⟨span f 1 (endByte-1),.matchWith ⟨span f 6 11,⟨ref f 7 10 "tag",[]⟩⟩
    ⟨span f 11 (endByte-1),⟨if fallback then [first] else [first,second],
      if fallback then some (ret f 36 37 44 45 47 "y") else none⟩⟩⟩]⟩
private def refSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier ⟨n,_⟩⟩ => [s,n] | _ => []
private def retSpans : Syntax.Block → List Syntax.SourceSpan
  | ⟨b,[⟨s,.returnStmt (some e)⟩]⟩ => [b,s]++refSpans e | _ => []
private def patternSpans : Syntax.Pattern → List Syntax.SourceSpan
  | ⟨s,.literal ⟨t,_⟩⟩ => [s,t] | ⟨s,.wildcard t⟩ => [s,t] | _ => []
private def actualSpans : Syntax.Block → List Syntax.SourceSpan
  | ⟨b,[⟨a,.letDecl ⟨n,_⟩ (some ⟨t,.named ⟨q,⟨⟨⟨i,_⟩,[]⟩⟩⟩ none⟩) (some x)⟩,
      ⟨c,.letDecl ⟨m,_⟩ none (some y)⟩,⟨d,.expression z true⟩,⟨inner,.block rest⟩]⟩ =>
      [b,a,n,t,q,i]++refSpans x++[c,m]++refSpans y++[d]++refSpans z++[inner]++retSpans ⟨inner,rest⟩
  | ⟨b,[⟨s,.matchWith ⟨g,⟨e,[]⟩⟩ ⟨a,⟨cases,fallback⟩⟩⟩]⟩ =>
      [b,s,g]++refSpans e++[a]++cases.flatMap (fun c =>
        [c.span]++patternSpans c.value.pattern++retSpans c.value.body)++fallback.toList.flatMap retSpans
  | _ => []
private def parsed (text : String) (expected : Syntax.SourceFile → Syntax.Block)
    (ranges : List (Nat × Nat)) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-data-body-depth.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "body depth lexer")
  match Syntax.Parser.block .require (Syntax.Parser.State.initial file lexed) with
  | .ok body next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      body.span==Syntax.SourceSpan.fullFile file && body==expected file) "whole handwritten body AST / EOF / diagnostics zero"
    check ((actualSpans body).all (fun s => s.isValidFor file) &&
      (actualSpans body).map (fun s => (s.startByte,s.endByte))==ranges) "every actual node/name/type/pattern/delimiter range"
    return body
  | _ => throw (IO.userError "body depth parser")
private structure EC (t : LocalNameTable) (e : Resolved.LocalScope V) (s : List V) (src : Syntax.Expr) (v : V) : Type where
  gate : ClosedSourceDataExpression src
  original : ClosedSourceExpressionEvaluates owner t e s src v s
private structure BC (t : LocalNameTable) (e : Resolved.LocalScope V) (s : List V) (src : Syntax.Block) (v : V) : Type where
  gate : ClosedSourceDataBody src
  original : ClosedSourceBodyEvaluates owner t e s src v s
private def reference (t : LocalNameTable) (e : Resolved.LocalScope V) (s : List V) (src : Syntax.Expr)
    (spelling : String) (id : Resolved.LocalId) (v : V)
    (named : LocalNameTable.Lookup t spelling id) (found : Resolved.LocalScope.Lookup e id v) : IO (EC t e s src v) := do
  match shape : src with
  | ⟨_,.identifier name⟩ =>
    if h : name.value=spelling then return by rw [shape]; exact ⟨.reference,.reference (h ▸ named) found⟩
    else throw (IO.userError "actual reference spelling")
  | _ => throw (IO.userError "actual reference shape")
private def returned (t : LocalNameTable) (e : Resolved.LocalScope V) (s : List V) (src : Syntax.Block)
    (spelling : String) (id : Resolved.LocalId) (v : V)
    (named : LocalNameTable.Lookup t spelling id) (found : Resolved.LocalScope.Lookup e id v) : IO (BC t e s src v) := do
  match shape : src with
  | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ =>
    let h ← reference t e s child spelling id v named found
    return by rw [shape]; exact ⟨.expression h.gate,.expression h.original⟩
  | _ => throw (IO.userError "actual expression return")
private def bindingWitness (src : Syntax.Block) (tag p q : V) (tail : Resolved.LocalScope V) (store : List V) :
    IO (BC names (rows tag p q tail) store src p) := do
  match shape : src with
  | ⟨bs,[⟨ls,.letDecl ⟨xs,"x"⟩ (some _) (some init)⟩,⟨ls2,.letDecl ⟨xs2,"x"⟩ none (some init2)⟩,
      ⟨ds,.expression discarded true⟩,⟨inner,.block rest⟩]⟩ =>
    let e := rows tag p q tail
    let i := Resolved.freshLocalId owner (names.map Prod.snd)
    let t1 := ("x",i)::names; let e1 := (i,p)::e
    let j := Resolved.freshLocalId owner (t1.map Prod.snd)
    let t2 := ("x",j)::t1; let e2 := (j,p)::e1
    let h1 ← reference names e store init "x" (sid 7) p .head (.tail (by decide) .head)
    let h2 ← reference t1 e1 store init2 "x" i p .head .head
    let hd ← reference t2 e2 store discarded "x" j p .head .head
    let hr ← returned t2 e2 store ⟨inner,rest⟩ "x" j p .head .head
    return by rw [shape]; exact ⟨.binding h1.gate (.binding h2.gate (.discard hd.gate (.block hr.gate))),
      .binding h1.original (.inferred h2.original (.discard hd.original (.block hr.original)))⟩
  | _ => throw (IO.userError "actual typed/inferred fresh shadow/discard/nested block")
private def zero : Core.Word := ⟨0,by decide⟩
private def literal (p : Syntax.Pattern) : IO (PLift (WordMatchPatternClassifies p (some zero))) := do
  match shape : p with
  | ⟨_,.literal ⟨_,.decimal "0"⟩⟩ =>
    return by apply PLift.up; rw [shape]; exact .literal ⟨_,rfl,
      .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) (by decide)) .nil)⟩
  | _ => throw (IO.userError "actual original zero pattern")
private structure Tail (e : Resolved.LocalScope V) (s : List V) (v : V) (w : Core.Word)
    (cases : List Syntax.MatchCase) (fallback : Option Syntax.Block) where
  body : Syntax.Block
  cert : BC names e s body v
  branches : ∀ arm ∈ cases, ClosedSourceDataBody arm.value.body
  defaults : ∀ body ∈ fallback.toList, ClosedSourceDataBody body
  choice : RuntimeWordMatchChooses (.word w) cases fallback body 0
private def tailWitness (e : Resolved.LocalScope V) (s : List V) (q : V) (w : Core.Word)
    (cases : List Syntax.MatchCase) (fallback : Option Syntax.Block)
    (found : Resolved.LocalScope.Lookup e (sid 8) q) : IO (Tail e s q w cases fallback) := do
  match shape : (cases,fallback) with
  | ([⟨a,⟨⟨ps,.wildcard marker⟩,body⟩⟩],none) =>
    let h ← returned names e s body "y" (sid 8) q (.tail (by decide) .head) found
    return by cases shape; exact ⟨body,h,by intro arm ha; simp only [List.mem_singleton] at ha; exact ha ▸ h.gate,
      by simp,.wildcard (.wildcard rfl)⟩
  | ([],some body) =>
    let h ← returned names e s body "y" (sid 8) q (.tail (by decide) .head) found
    return by cases shape; exact ⟨body,h,by simp,
      by intro b hb; simp only [Option.toList,List.mem_singleton] at hb; exact hb ▸ h.gate,.fallback⟩
  | _ => throw (IO.userError "actual ordered wildcard/default tail")
private def matchWitness (src : Syntax.Block) (p q : V) (w : Core.Word) (tail : Resolved.LocalScope V) (store : List V) :
    IO (BC names (rows (.word w) p q tail) store src (if w=zero then p else q)) := do
  let e := rows (.word w) p q tail
  match shape : src with
  | ⟨_,[⟨_,.matchWith ⟨_,⟨guard,[]⟩⟩ ⟨_,⟨first::rest,fallback⟩⟩⟩]⟩ =>
    let hg ← reference names e store guard "tag" foreign (.word w)
      (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
    let meaning := (← literal first.value.pattern).down
    let ht ← returned names e store first.value.body "x" (sid 7) p .head (.tail (by decide) .head)
    let hf ← tailWitness e store q w rest fallback .head
    have chosen : RuntimeWordMatchChooses (.word w) (first::rest) fallback
        (if w=zero then first.value.body else hf.body) 1 := by
      by_cases same : w=zero
      · subst w; simp only [↓reduceIte]; exact .hit meaning
      · simp only [same,↓reduceIte]; exact .miss meaning same hf.choice
    proof chosen
    match picked : chooseRuntimeWordMatch? (.word w) (first::rest) fallback with
    | none => False.elim (by have h := chooseRuntimeWordMatch?_iff.mpr chosen; rw [picked] at h; cases h)
    | some (actual,count) =>
      proof ((chooseRuntimeWordMatch?_iff.mp picked).deterministic chosen)
      check (count==1) "one visited comparison remains distinct from whole source depth three"
    return by
      rw [shape]; refine ⟨.wordMatch hg.gate ?_ hf.defaults,?_⟩
      · intro arm ha; rcases List.mem_cons.mp ha with rfl|ha; exact ht.gate; exact hf.branches _ ha
      · by_cases same : w=zero
        · subst w; simp only [↓reduceIte]; exact .wordMatch hg.original (.hit meaning) ht.original
        · simp only [same,↓reduceIte]; exact .wordMatch hg.original (.miss meaning same hf.choice) hf.cert.original
  | _ => throw (IO.userError "actual ordered literal-headed match")
private def exercise {t e s src v} (h : BC t e s src v) (expectedBound : Nat) : IO Unit := do
  proof h.original
  let bound := closedSourceDataBodyDepthBound src
  check (bound==expectedBound) "actual syntax-only body depth"
  proof (h.gate.evaluates_at_depthBound h.original (Nat.le_refl bound))
  have endpoints : ∀ actual final, ClosedSourceBodyEvaluates owner t e s src actual final ↔ actual=v ∧ final=s :=
    fun _ _ => ⟨fun other => other.deterministic h.original,by rintro ⟨rfl,rfl⟩; exact h.original⟩
  proof endpoints
  for budget in [0,bound-1,bound,bound+3] do
    match ran : evaluateClosedSourceBody? budget owner t e s src with
    | none => check (budget<bound) "only below exact selected depth is absent in these fixtures"
    | some (actual,final) =>
      have original := evaluateClosedSourceBody?_sound ran
      have equal := (endpoints actual final).mp original
      proof equal; proof ((endpoints actual final).mpr equal)
      check (bound<=budget) "full actual endpoint and selected-depth boundary"
      if enough : bound≤budget then
        proof ((h.gate.evaluate_at_depthBound_iff enough).mp ran)
        proof ((h.gate.evaluate_at_depthBound_iff enough).mpr original)
        have stable := h.gate.evaluate_depth_stable owner t e s enough
        proof stable
        proof (show evaluateClosedSourceBody? bound owner t e s src = some (actual,final) from stable.symm.trans ran)
  for extra in [0,1,7] do
    proof (h.gate.evaluate_depth_stable owner t e s (Nat.le_add_right bound extra))
    proof (h.gate.evaluates_at_depthBound h.original (Nat.le_add_right bound extra))
end Tests.ParsedDataBodyDepthBridge
open Solcore Solcore.Frontend Tests.ParsedDataBodyDepthBridge in
def Tests.frontendParsedDataBodyDepthBridgeTests : IO Unit := do
  let bound ← parsed "{let x:Unit=x;let x=x;x;{return x;}}" bindingAST
    [(0,36),(1,14),(5,6),(7,11),(7,11),(7,11),(12,13),(12,13),(14,22),(18,19),(20,21),(20,21),
      (22,24),(22,23),(22,23),(24,35),(24,35),(25,34),(32,33),(32,33)]
  let wildcard ← parsed "{match(tag){case 0{return x;}case _{return y;}}}" (matchAST false)
    [(0,48),(1,47),(6,11),(7,10),(7,10),(11,47),(12,29),(17,18),(17,18),(18,29),(19,28),(26,27),(26,27),
      (29,46),(34,35),(34,35),(35,46),(36,45),(43,44),(43,44)]
  let fallback ← parsed "{match(tag){case 0{return x;}default{return y;}}}" (matchAST true)
    [(0,49),(1,48),(6,11),(7,10),(7,10),(11,48),(12,29),(17,18),(17,18),(18,29),(19,28),(26,27),(26,27),
      (36,47),(37,46),(44,45),(44,45)]
  let inert : Syntax.Expr := ⟨bound.span,.tuple ⟨bound.span,[]⟩⟩
  let saved := RuntimeValue.sourceClosure inert foreign.owner [("x",foreign),("x",sid 7)]
    [(foreign,.unit),(foreign,.word Core.Word.maximum)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let mut count := 0
  for p in [saved,RuntimeValue.pair (.word Core.Word.maximum) saved] do
    for tail in [[],[(sid 7,core),(foreign,saved),(sid 100,core),(sid 101,saved)]] do
      for store in [[],[saved,core,RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef (.function .word .word) 900]] do
        let h ← bindingWitness bound (.word Core.Word.maximum) p core tail store
        exercise h 6
        count := count+1
        for src in [wildcard,fallback] do
          for w in [zero,⟨1,by decide⟩] do
            let h ← matchWitness src p core w tail store
            exercise h 3
            count := count+1
  check (count==40) "three spellings / eight mixed contexts / five original success lanes"

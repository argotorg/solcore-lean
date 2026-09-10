import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.ClosedSourceEvaluatorCompletenessProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Syntax.Parser.Term

/- Independent original certificates precede depth search. Actual returned closures
are inspected and identified through soundness, then reapplied at a different owner.
None is not a fault; depth is neither cost nor resumable fuel. -/
set_option autoImplicit false
namespace Tests
namespace ParsedClosedSourceEvaluation
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev C := Resolved.LocalScope V
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (label : String) : IO Unit := unless b do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ClosedSourceRunner",by decide⟩],by decide⟩⟩,157⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def w (n : Nat) : Core.Word := ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def names : LocalNameTable := [("saved",sid 7),("other",sid 8),("c",sid 3),("tag",sid 31),("saved",sid 9),("x",foreign)]
private def rows (s o tag : V) (c : Bool) (extra : C) : C :=
  [(sid 32,.unit),(sid 7,s),(sid 8,o),(sid 31,tag),(sid 7,.bool false),(sid 3,.bool c),(foreign,.unit)]++extra
private def pn := ("x",sid 32)::names
private def pe (s o tag : V) (c : Bool) (extra : C) := (sid 32,s)::rows s o tag c extra
private def fn := ("f",sid 33)::pn
private def fval (fs : Syntax.Expr) (s o tag : V) (c : Bool) (extra : C) : V := .sourceClosure fs owner pn (pe s o tag c extra)
private def tn := ("x",sid 34)::fn
private def te (fs : Syntax.Expr) (s o tag : V) (c : Bool) (extra : C) := (sid 34,RuntimeValue.word (w 0))::(sid 33,fval fs s o tag c extra)::pe s o tag c extra
private theorem fresh0 : Resolved.freshLocalId owner (names.map Prod.snd)=sid 32 := by decide
private theorem fresh1 : Resolved.freshLocalId owner (pn.map Prod.snd)=sid 33 := by decide
private theorem fresh2 : Resolved.freshLocalId owner (fn.map Prod.snd)=sid 34 := by decide
private def result (fs : Syntax.Expr) (s o tag : V) (c hit : Bool) (extra : C) : V :=
  if c then if hit then .pair (.pair s (.word (w 0))) (.pair (fval fs s o tag c extra) .unit) else .unit else .pair s o
private def ref (own : Resolved.DeclarationId) (ns : LocalNameTable) (es : C) (st : List V) (e : Syntax.Expr)
    (name : String) (id : Resolved.LocalId) (value : V) (named : LocalNameTable.Lookup ns name id) (found : Resolved.LocalScope.Lookup es id value) : IO (PLift (E own ns es st e value st)) := do
  match shape : e with
  | ⟨_,.identifier n⟩ => if same : n.value=name then return ⟨by rw [shape]; exact .reference (same ▸ named) found⟩ else throw (IO.userError "original reference name")
  | _ => throw (IO.userError "original reference")
private def zeroPattern (p : Syntax.Pattern) : IO (PLift (WordMatchPatternClassifies p (some (w 0)))) := do
  match shape : p with
  | ⟨_,.literal ⟨_,.decimal "0"⟩⟩ => return ⟨by rw [shape]; exact .literal ⟨_,rfl,.decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)⟩⟩
  | ⟨_,.literal ⟨_,.hexadecimal "0x00"⟩⟩ => return ⟨by rw [shape]; exact .literal ⟨_,rfl,.hexadecimal rfl (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) (.cons (.decimal (digit:=0) (by decide) rfl) .nil))⟩⟩
  | _ => throw (IO.userError "original zero pattern")
private def wildcard (p : Syntax.Pattern) : IO (PLift (WordMatchPatternClassifies p none)) := do
  match shape : p with
  | ⟨_,.group ⟨_,.group ⟨_,.wildcard _⟩⟩⟩ => return ⟨by rw [shape]; exact .group (.group (.wildcard rfl))⟩
  | _ => throw (IO.userError "original grouped wildcard")
private def selection {v cases defaultBody selected tests} (proof : RuntimeWordMatchChooses v cases defaultBody selected tests) : IO Unit := do
  have _ := chooseRuntimeWordMatch?_iff.mpr proof
  match actual : chooseRuntimeWordMatch? v cases defaultBody with
  | some (body,count) => check (body == selected && count==tests) "actual selector body/count"; have _ := (chooseRuntimeWordMatch?_iff.mp actual).deterministic proof; pure ()
  | none => throw (IO.userError "independently witnessed selection missing")
private def absentChoice (v : V) (cases : List Syntax.MatchCase) (originalDefault : Option Syntax.Block) : IO Unit := do
  match absent : chooseRuntimeWordMatch? v cases originalDefault with
  | none =>
    have _ : ∀ body count, ¬RuntimeWordMatchChooses v cases originalDefault body count := by
      intro body count choice
      have accepted := chooseRuntimeWordMatch?_iff.mpr choice
      rw [absent] at accepted
      cases accepted
    pure ()
  | some _ => throw (IO.userError "unsupported or literal-first non-Word selection")
private structure Function (s o tag : V) (c : Bool) (extra : C) (st : List V) where
  source : Syntax.Expr
  parameter : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source parameter body
  named : parameter.value="y"
  pair : ∀ a, B owner (("y",sid 33)::pn) ((sid 33,a)::pe s o tag c extra) st body (.pair s a) st
private def function (fs : Syntax.Expr) (s o tag : V) (c : Bool) (extra : C) (st : List V) : IO {f : Function s o tag c extra st // f.source=fs} := do
  match shape : fs with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred y⟩]⟩ _ ⟨_,[⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[⟨_,.identifier x⟩,⟨_,.identifier arg⟩]⟩⟩)⟩]⟩⟩ =>
    if valid : y.value="y" ∧ x.value="x" ∧ arg.value="y" then
      return ⟨⟨fs,y,_,by rw [shape]; exact .inferred,valid.1,fun a => .expression (.pair
        (.reference (by simpa only [valid.2.1] using
          (show LocalNameTable.Lookup (("y",sid 33)::pn) "x" (sid 32) from .tail (by decide) .head)) (.tail (by decide) .head))
        (.reference (by simpa only [valid.2.2] using
          (show LocalNameTable.Lookup (("y",sid 33)::pn) "y" (sid 33) from .head)) .head))⟩,rfl⟩
    else throw (IO.userError "original captured x/y")
  | _ => throw (IO.userError "original inner pair lambda")
private def applyF {s o tag c extra st} (f : Function s o tag c extra st) (e : Syntax.Expr) (other : Bool) : IO (PLift (E owner tn (te f.source s o tag c extra) st e (.pair s (if other then o else .word (w 0))) st)) := do
  match shape : e with
  | ⟨_,.call callee ⟨_,[argument]⟩⟩ =>
    let head ← ref owner tn (te f.source s o tag c extra) st callee "f" (sid 33) (fval f.source s o tag c extra) (.tail (by decide) .head) (.tail (by decide) .head)
    if h : other=true then
      let a ← ref owner tn (te f.source s o tag c extra) st argument "other" (sid 8) o (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
      return ⟨by rw [shape]; simp only [h,↓reduceIte]; exact .call f.shape head.down a.down (by simpa only [f.named,fresh1] using f.pair o)⟩
    else
      have hfalse : other=false := by cases other <;> simp_all
      let a ← ref owner tn (te f.source s o tag c extra) st argument "x" (sid 34) (.word (w 0)) .head .head
      return ⟨by rw [shape]; simp only [hfalse,Bool.false_eq_true,↓reduceIte]; exact .call f.shape head.down a.down (by simpa only [f.named,fresh1] using f.pair (.word (w 0)))⟩
  | _ => throw (IO.userError "original f call")
private def selected {s o tag c extra st} (f : Function s o tag c extra st) (hit : Bool)
    (tagEq : tag=.word (w (if hit then 0 else 1))) (body : Syntax.Block) :
    IO (PLift (B owner tn (te f.source s o tag c extra) st body
      (if hit then .pair (.pair s (.word (w 0))) (.pair (fval f.source s o tag c extra) .unit) else .unit) st)) := do
  match shape : body with
  | ⟨_,[⟨_,.matchWith ⟨_,⟨scrutinee,[]⟩⟩ ⟨_,⟨[first,duplicate,last],none⟩⟩⟩]⟩ =>
    let r ← ref owner tn (te f.source s o tag c extra) st scrutinee "tag" (sid 31) tag
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
    let p ← zeroPattern first.value.pattern; let d ← zeroPattern duplicate.value.pattern; let q ← wildcard last.value.pattern
    if h : hit=true then
      match branch : first.value.body with
      | ⟨_,[⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[call,identifier,⟨_,.tuple ⟨_,[]⟩⟩]⟩⟩)⟩]⟩ =>
        let a ← applyF f call false
        let b ← ref owner tn (te f.source s o tag c extra) st identifier "f" (sid 33) (fval f.source s o tag c extra) (.tail (by decide) .head) (.tail (by decide) .head)
        have choice : RuntimeWordMatchChooses tag [first,duplicate,last] none first.value.body 1 := by rw [tagEq,h]; exact .hit p.down
        selection choice
        return ⟨by rw [shape]; simp only [h,↓reduceIte]; exact .wordMatch r.down choice (by rw [branch]; exact .expression (.many a.down (.pair b.down .unit)))⟩
      | _ => throw (IO.userError "original flat three-tuple")
    else
      have hfalse : hit=false := by cases hit <;> simp_all
      match branch : last.value.body with
      | ⟨_,[⟨_,.returnStmt none⟩]⟩ =>
        have choice : RuntimeWordMatchChooses tag [first,duplicate,last] none last.value.body 2 := by rw [tagEq,hfalse]; exact .miss p.down (by decide) (.miss d.down (by decide) (.wildcard q.down))
        selection choice
        return ⟨by rw [shape]; simp only [hfalse,Bool.false_eq_true,↓reduceIte]; exact .wordMatch r.down choice (by rw [branch]; exact .bare)⟩
      | _ => throw (IO.userError "original bare wildcard body")
  | _ => throw (IO.userError "original three-arm match")
private def ending {s o tag c extra st} (f : Function s o tag c extra st) (hit : Bool) (tagEq : c=true → tag=.word (w (if hit then 0 else 1))) (body : Syntax.Block) : IO (PLift (B owner tn (te f.source s o tag c extra) st body (result f.source s o tag c hit extra) st)) := do
  match shape : body with
  | ⟨_,[⟨_,.ifThen condition thenBody (some elseBody)⟩]⟩ =>
    let r ← ref owner tn (te f.source s o tag c extra) st condition "c" (sid 3) (.bool c)
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))))
    if h : c=true then
      match block : thenBody with
      | ⟨_,[⟨span,.block statements⟩]⟩ =>
        let a ← selected f hit (tagEq h) ⟨span,statements⟩
        have conditionTrue : E owner tn (te f.source s o tag c extra) st condition (.bool true) st := by simpa only [h] using r.down
        return ⟨by rw [shape]; simp only [result,h,↓reduceIte]; exact .ifTrue (by simpa only [h] using conditionTrue) (by rw [block]; exact .block (by simpa only [h] using a.down))⟩
      | _ => throw (IO.userError "original explicit block")
    else
      have hfalse : c=false := by cases c <;> simp_all
      match branch : elseBody with
      | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
        let a ← applyF f e true
        return ⟨by rw [shape]; simp only [result,hfalse,Bool.false_eq_true,↓reduceIte]; exact .ifFalse (by simpa only [hfalse] using r.down) (by rw [branch]; exact .expression (by simpa only [hfalse,↓reduceIte] using a.down))⟩
      | _ => throw (IO.userError "original else return")
  | _ => throw (IO.userError "original conditional")
private structure Witness (source : Syntax.Expr) (s o tag : V) (c hit : Bool) (extra : C) (st : List V) where
  f : Function s o tag c extra st
  originalBody : Syntax.Block
  body : B owner pn (pe s o tag c extra) st originalBody (result f.source s o tag c hit extra) st
  whole : E owner names (rows s o tag c extra) st source (result f.source s o tag c hit extra) st
private def witness (source : Syntax.Expr) (s o tag : V) (c hit : Bool) (extra : C) (st : List V) (tagEq : c=true → tag=.word (w (if hit then 0 else 1))) : IO (Witness source s o tag c hit extra st) := do
  match original : source with
  | ⟨_,.call ⟨_,.group ⟨_,.lambda _ ⟨_,[⟨_,.typed none parameter _⟩]⟩ _ body⟩⟩ ⟨_,[argument]⟩⟩ =>
    match prefixShape : body with
    | ⟨span,⟨_,.letDecl n none (some fs)⟩::⟨ls,.letDecl x (some annotation) (some ⟨ws,.literal literal⟩)⟩::⟨ds,.expression ⟨us,.tuple ⟨ts,[]⟩⟩ true⟩::rest⟩ =>
      if valid : parameter.value="x" ∧ n.value="f" ∧ x.value="x" then
        match numeric : literal with
        | ⟨_,.decimal "0"⟩ =>
          let ⟨f,fsEq⟩ ← function fs s o tag c extra st; let tail ← ending f hit tagEq ⟨span,rest⟩
          let a ← ref owner names (rows s o tag c extra) st argument "saved" (sid 7) s .head (.tail (by decide) .head)
          have zero : WordLiteralDenotes literal (w 0) := by rw [numeric]; exact .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
          have typed : B owner fn ((sid 33,fval fs s o tag c extra)::pe s o tag c extra) st
              ⟨span,⟨ls,.letDecl x (some annotation) (some ⟨ws,.literal literal⟩)⟩::
                ⟨ds,.expression ⟨us,.tuple ⟨ts,[]⟩⟩ true⟩::rest⟩ (result fs s o tag c hit extra) st :=
            .binding (.wordLiteral zero) (by simpa only [fsEq,valid.2.2,fresh2,tn,te] using
              (ClosedSourceBodyEvaluates.discard ClosedSourceExpressionEvaluates.unit tail.down))
          have b : B owner pn (pe s o tag c extra) st body (result fs s o tag c hit extra) st := by
            rw [prefixShape]; exact .inferred (.creation (by simpa only [fsEq] using f.shape))
              (by simpa only [valid.2.1,fresh1,fn,fval] using typed)
          return ⟨f,body,by simpa only [fsEq] using b,by
            rw [original]; exact .call SourceUnaryLambdaShape.typed (.group (.creation SourceUnaryLambdaShape.typed))
              a.down (by simpa only [fsEq,valid.1,fresh0,pn,pe] using b)⟩
        | _ => throw (IO.userError "original zero initializer")
      else throw (IO.userError "original binder names")
    | _ => throw (IO.userError "original typed/inferred/discard prefix")
  | _ => throw (IO.userError "original grouped unary call")
private def caller := {owner with declarationIndex:=158}
private def rid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def callNames : LocalNameTable := [("picked",rid 0),("other",rid 1)]
private def reapplied {s o tag c extra st} (f : Function s o tag c extra st) (source : Syntax.Expr) : IO (PLift (E caller callNames [(rid 0,fval f.source s o tag c extra),(rid 1,o)] st source (.pair s o) st)) := do
  match shape : source with
  | ⟨_,.call callee ⟨_,[argument]⟩⟩ =>
    let a ← ref caller callNames [(rid 0,fval f.source s o tag c extra),(rid 1,o)] st callee "picked" (rid 0) (fval f.source s o tag c extra) .head .head
    let b ← ref caller callNames [(rid 0,fval f.source s o tag c extra),(rid 1,o)] st argument "other" (rid 1) o (.tail (by decide) .head) (.tail (by decide) .head)
    return ⟨by rw [shape]; exact .call f.shape a.down b.down (by simpa only [f.named,fresh1] using f.pair o)⟩
  | _ => throw (IO.userError "original different-caller call")
private def run {source s o tag c hit extra st} (proof : Witness source s o tag c hit extra st) (picked : Syntax.Expr) (depth : Nat) : IO Unit := do
  have _ := evaluateClosedSourceExpression?_eventually_complete proof.whole
  have _ := evaluateClosedSourceBody?_eventually_complete proof.body
  let next ← reapplied proof.f picked
  have created : E owner pn (pe s o tag c extra) st proof.f.source (fval proof.f.source s o tag c extra) st := .creation proof.f.shape
  for budget in [0,1,2] do
    match actual : evaluateClosedSourceExpression? budget owner pn (pe s o tag c extra) st proof.f.source with
    | none => check (budget==0) "creation needs depth1 even without body evaluation"
    | some (value,store) =>
      match value with
      | .sourceClosure fs own ns es => check (0<budget && fs==proof.f.source && own==owner && ns==pn && es.map Prod.fst==(pe s o tag c extra).map Prod.fst && store.length==st.length) "actual creation fields"
      | _ => throw (IO.userError "actual creation is a source closure")
      have _ := (evaluateClosedSourceExpression?_sound actual).deterministic created
      pure ()
  for budget in List.range (depth+4) do
    match actual : evaluateClosedSourceExpression? budget owner names (rows s o tag c extra) st source with
    | none => check (budget<depth) "low depth None, not a fault"
    | some (value,final) =>
      check (depth≤budget && final.length==st.length) "actual full endpoint threshold"
      if chosen : c=true ∧ hit=true then
        match actualShape : value with
        | .pair (.pair _ (.word zero)) (.pair (.sourceClosure fs own ns es) .unit) =>
          check (zero==w 0 && fs==proof.f.source && own==owner && ns==pn && es.map Prod.fst==(pe s o tag c extra).map Prod.fst) "computed original closure/capture layout"
          have same := (evaluateClosedSourceExpression?_sound actual).deterministic proof.whole
          have saved : RuntimeValue.sourceClosure fs own ns es=fval proof.f.source s o tag c extra := by
            have valueEq := same.1
            rw [actualShape] at valueEq
            simp only [result,chosen.1,chosen.2,↓reduceIte] at valueEq
            simpa only [chosen.1] using (RuntimeValue.pair.inj (RuntimeValue.pair.inj valueEq).2).1
          have independent : E caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked (.pair s o) final := by simpa only [saved,same.2] using next.down
          have _ := evaluateClosedSourceExpression?_eventually_complete independent
          for more in List.range 8 do
            match computed : evaluateClosedSourceExpression? more caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked with
            | none => check (more<4) "returned closure low depth"
            | some (v,store) => check (4≤more && store.length==final.length && (match v with | .pair _ _ => true | _ => false)) "returned closure threshold/pair"; have _ := (evaluateClosedSourceExpression?_sound computed).deterministic independent; pure ()
        | _ => throw (IO.userError "actual returned closure shape")
      else
        check (match value with | .unit => c && !hit | .pair _ _ => !c | _ => false) "actual selected endpoint shape"
        have _ := (evaluateClosedSourceExpression?_sound actual).deterministic proof.whole
        pure ()
    match actual : evaluateClosedSourceBody? budget owner pn (pe s o tag c extra) st proof.originalBody with
    | none => check (budget+1<depth) "body low depth"
    | some (value,store) => check (depth≤budget+1) "body threshold"; have _ := (evaluateClosedSourceBody?_sound actual).deterministic proof.body; pure ()
private def boundaries (source : Syntax.Expr) (actual : V) : IO Unit := do
  match source with
  | ⟨_,.lambda _ _ _ ⟨_,[⟨_,.matchWith _ ⟨_,⟨[first,bad],some originalDefault⟩⟩⟩]⟩⟩ =>
    let p ← wildcard first.value.pattern
    selection (show RuntimeWordMatchChooses actual [first,bad] (some originalDefault) first.value.body 0 from .wildcard p.down)
    selection (show RuntimeWordMatchChooses actual [] (some originalDefault) originalDefault 0 from .fallback)
    absentChoice actual [bad] (some originalDefault)
    absentChoice actual [] none
  | _ => throw (IO.userError "original boundary arms/default")
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"closed-source-evaluator.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next => check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && source.span==Syntax.SourceSpan.fullFile file) "complete original AST/span"; return source
  | _ => throw (IO.userError "original parser")
end ParsedClosedSourceEvaluation

open ParsedClosedSourceEvaluation Solcore.Frontend in
/-- Actual depth-bounded results meet independently constructed original source certificates. -/
def frontendParsedClosedSourceEvaluationTests : IO Unit := do
  let source ← parsed "(lam(x:Unknown)->Unknown{let f=lam(y){return (x,y);};let x:Missing=0;();if(c){{match(tag){case 0{return (f(x),f,());}case 0x00{return absent;}case ((_)){return;}}}}else{return f(other);}})(saved)"
  let picked ← parsed "picked(other)"
  let boundary ← parsed "lam(z){match(z){case ((_)){return z;}case Missing{return absent;}default{return;}}}"
  let inert ← parsed "lam(){return absent;}"
  let s := Solcore.Frontend.RuntimeValue.sourceClosure inert caller [("unseen",foreign)] [(sid 32,.bool false)]
  for o in [.hostFunction .storageWrite,.coreClosure .unit .word (.var 99) [s,.cellRef .word 700]] do
    for extra in [[],[(sid 32,o),(foreign,s)]] do
      for store in [[.unit],[s,.cellRef (.function .word .word) 1]] do
        let hit ← witness source s o (.word (w 0)) true true extra store (by intro _; rfl)
        run hit picked 13
        let miss ← witness source s o (.word (w 1)) true false extra store (by intro _; rfl)
        run miss picked 8
        for tag in [s,o] do
          let skipped ← witness source s o tag false true extra store (by simp)
          run skipped picked 10
          match hit.originalBody.value with
          | [_,_,_,⟨_,.ifThen _ ⟨_,[⟨_,.block [⟨_,.matchWith _ ⟨_,⟨cases,originalDefault⟩⟩⟩]⟩]⟩ _⟩] => absentChoice tag cases originalDefault
          | _ => throw (IO.userError "original unvisited match fields")
          check ((evaluateClosedSourceExpression? 40 owner names (rows s o tag true extra) store source).isNone) "literal-first non-Word absence is not a fault"
    boundaries boundary o
  boundaries boundary s

end Tests

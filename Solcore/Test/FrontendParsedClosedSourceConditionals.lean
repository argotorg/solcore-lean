import Solcore.Frontend.ClosedSource
import Solcore.Syntax.Parser.Term

/- Independent original certificates precede search; actual returned closures and
stores are reused under a different caller. None is not a runtime fault. -/
set_option autoImplicit false
namespace Tests
namespace ParsedClosedSourceConditionals
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev C := Resolved.LocalScope V
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (label : String) : IO Unit := unless b do throw (IO.userError label)
private def mainText := "(lam(x:Unknown)->Unknown{let f=c?lam(y){return d?(x,y):(y,x);}:lam(y){return (y,x);};let x:Missing=0;return ((c?f:lam(y){return (x,y);})(c?x:other),f);})(saved)"
private def yesText := "(c?lam(y){return y;}:missing())(saved)"
private def noText := "(c?missing():lam(y){return y;})(saved)"
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ClosedSourceConditionals",by decide⟩],by decide⟩⟩,159⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def w (n : Nat) : Core.Word := ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def names : LocalNameTable := [("saved",sid 7),("other",sid 8),("c",sid 3),("d",sid 31),("saved",sid 9),("x",foreign)]
private def rows (s o d : V) (c : Bool) (extra : C) : C :=
  [(sid 32,.unit),(sid 7,s),(sid 8,o),(sid 31,d),(sid 7,.bool false),(sid 3,.bool c),(foreign,.unit)]++extra
private def pn := ("x",sid 32)::names
private def pe (s o d : V) (c : Bool) (extra : C) := (sid 32,s)::rows s o d c extra
private def fn := ("f",sid 33)::pn
private def fv (fs : Syntax.Expr) (s o d : V) (c : Bool) (extra : C) : V := .sourceClosure fs owner pn (pe s o d c extra)
private def tn := ("x",sid 34)::fn
private def te (fs : Syntax.Expr) (s o d : V) (c : Bool) (extra : C) := (sid 34,RuntimeValue.word (w 0))::(sid 33,fv fs s o d c extra)::pe s o d c extra
private theorem fresh0 : Resolved.freshLocalId owner (names.map Prod.snd)=sid 32 := by decide
private theorem fresh1 : Resolved.freshLocalId owner (pn.map Prod.snd)=sid 33 := by decide
private theorem fresh2 : Resolved.freshLocalId owner (fn.map Prod.snd)=sid 34 := by decide
private theorem fresh3 : Resolved.freshLocalId owner (tn.map Prod.snd)=sid 35 := by decide
private def pairResult (reverse : Bool) (x a : V) : V := if reverse then .pair a x else .pair x a
private def ref (own : Resolved.DeclarationId) (ns : LocalNameTable) (es : C) (st : List V) (e : Syntax.Expr)
    (name : String) (id : Resolved.LocalId) (value : V) (named : LocalNameTable.Lookup ns name id) (found : Resolved.LocalScope.Lookup es id value) : IO (PLift (E own ns es st e value st)) := do
  match shape : e with
  | ⟨_,.identifier n⟩ => if same : n.value=name then return ⟨by rw [shape]; exact .reference (same ▸ named) found⟩ else throw (IO.userError "original reference name")
  | _ => throw (IO.userError "original reference")
private structure OriginalConditional (source : Syntax.Expr) where
  span : Syntax.SourceSpan
  condition : Syntax.Expr
  question : Syntax.SourceSpan
  yes : Syntax.Expr
  colon : Syntax.SourceSpan
  no : Syntax.Expr
  exactSource : source=⟨span,.conditional condition question yes colon no⟩
private def originalConditional : (source : Syntax.Expr) → IO (OriginalConditional source)
  | ⟨s,.conditional c q y colon n⟩ => do
    let text := if s.endByte==30 then if colon.startByte==20 then yesText else noText else mainText
    check ([(31,84,32,62),(47,60,48,54),(110,135,111,113),(137,146,138,140),(1,30,2,20),(1,30,2,12)].contains (s.startByte,s.endByte,q.startByte,colon.startByte) && text.toUTF8[q.startByte]? == some 63 && text.toUTF8[colon.startByte]? == some 58) "literal original ranges and punctuation bytes"
    check (s.contains c.span && s.contains y.span && s.contains n.span && c.span.endByte≤q.startByte &&
      q.length==1 && q.endByte≤y.span.startByte && y.span.endByte≤colon.startByte && colon.length==1 && colon.endByte≤n.span.startByte) "original ?: spans and order"
    pure ⟨s,c,q,y,colon,n,rfl⟩
  | _ => throw (IO.userError "original conditional")
private theorem chosen {source own ns es st value} (p : OriginalConditional source) (c : Bool)
    (guard : E own ns es st p.condition (.bool c) st)
    (branch : E own ns es st (if c then p.yes else p.no) value st) : E own ns es st source value st := by
  rw [p.exactSource]
  have independent : E own ns es st ⟨p.span,.conditional p.condition p.question p.yes p.colon p.no⟩ value st := by
    cases c <;> first | exact .conditionalFalse guard branch | exact .conditionalTrue guard branch
  exact closedSourceExpressionEvaluates_conditional_iff.mpr (closedSourceExpressionEvaluates_conditional_iff.mp independent)
private def law {source} (p : OriginalConditional source) (ns : LocalNameTable) (es : C) (st : List V) : IO Unit := do
  for n in [0,1,3,10] do
    let selected := do
      let (.bool c,m) ← evaluateClosedSourceExpression? n owner ns es st p.condition | none
      evaluateClosedSourceExpression? n owner ns es m (if c then p.yes else p.no)
    have equation : evaluateClosedSourceExpression? (n+1) owner ns es st source=selected := by
      rw [p.exactSource]; exact evaluateClosedSourceExpression?_conditional n owner ns es st p.span p.question p.colon p.condition p.yes p.no
    match left : evaluateClosedSourceExpression? (n+1) owner ns es st source, right : selected with
    | some (v,s),some (v',s') => have _ : v=v' ∧ s=s' := Prod.mk.inj (Option.some.inj (left.symm.trans (equation.trans right))); pure ()
    | none,none => pure ()
    | _,_ => throw (IO.userError "original conditional exact executable equation")
private structure Function (source : Syntax.Expr) (ns : LocalNameTable) (es : C) (st : List V) (result : V → V) where
  parameter : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source parameter body
  named : parameter.value="y"
  evaluated : ∀ a, B owner (("y",Resolved.freshLocalId owner (ns.map Prod.snd))::ns)
    ((Resolved.freshLocalId owner (ns.map Prod.snd),a)::es) st body (result a) st
private def pairLambda (source : Syntax.Expr) (ns : LocalNameTable) (es : C) (st : List V)
    (x : V) (id : Resolved.LocalId) (named : LocalNameTable.Lookup ns "x" id) (found : Resolved.LocalScope.Lookup es id x)
    (different : Resolved.freshLocalId owner (ns.map Prod.snd) ≠ id) (reverse : Bool) : IO (Function source ns es st (pairResult reverse x)) := do
  match shape : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred y⟩]⟩ none ⟨_,[⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[⟨_,.identifier l⟩,⟨_,.identifier r⟩]⟩⟩)⟩]⟩⟩ =>
    if valid : y.value="y" ∧ l.value=(if reverse then "y" else "x") ∧ r.value=(if reverse then "x" else "y") then
      return ⟨y,_,by rw [shape]; exact .inferred,valid.1,fun a => by
        cases reverse <;> simp only [pairResult,Bool.false_eq_true,↓reduceIte] at valid ⊢
        · exact .expression (.pair (.reference (valid.2.1 ▸ .tail (by decide) named) (.tail different found)) (.reference (valid.2.2 ▸ .head) .head))
        · exact .expression (.pair (.reference (valid.2.1 ▸ .head) .head) (.reference (valid.2.2 ▸ .tail (by decide) named) (.tail different found)))⟩
    else throw (IO.userError "original ordered x/y pair")
  | _ => throw (IO.userError "original pair lambda")
private def conditionalLambda (source : Syntax.Expr) (s o : V) (b : Bool) (extra : C) (st : List V) :
    IO (Function source pn (pe s o (.bool b) true extra) st (pairResult (!b) s)) := do
  match shape : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred y⟩]⟩ none ⟨_,[⟨_,.returnStmt (some nested)⟩]⟩⟩ =>
    if named : y.value="y" then
      let p ← originalConditional nested
      match yes : p.yes, no : p.no with
      | ⟨_,.tuple ⟨_,[⟨_,.identifier x⟩,⟨_,.identifier a⟩]⟩⟩, ⟨_,.tuple ⟨_,[⟨_,.identifier a'⟩,⟨_,.identifier x'⟩]⟩⟩ =>
        if valid : x.value="x" ∧ a.value="y" ∧ a'.value="y" ∧ x'.value="x" then
          match guard : p.condition with
          | ⟨_,.identifier d⟩ =>
            if dname : d.value="d" then
              return ⟨y,_,by rw [shape]; exact .inferred,named,fun v => by
                refine .expression ?_
                apply chosen p b
                · rw [guard,fresh1]
                  exact .reference (dname ▸ .tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
                · cases b <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,pairResult,yes,no,fresh1]
                  · exact .pair (.reference (valid.2.2.1 ▸ .head) .head) (.reference (valid.2.2.2 ▸ .tail (by decide) .head) (.tail (by decide) .head))
                  · exact .pair (.reference (valid.1 ▸ .tail (by decide) .head) (.tail (by decide) .head)) (.reference (valid.2.1 ▸ .head) .head)⟩
            else throw (IO.userError "original d guard")
          | _ => throw (IO.userError "original guard reference")
        else throw (IO.userError "original conditional pair order")
      | _,_ => throw (IO.userError "original conditional pairs")
    else throw (IO.userError "original y parameter")
  | _ => throw (IO.userError "original conditional lambda")
private def fr (c b : Bool) (s : V) : V → V := if c then pairResult (!b) s else pairResult true s
private def selectedFunction {source} (p : OriginalConditional source) (s o d : V) (c b : Bool) (extra : C) (st : List V)
    (guardEq : c=true → d=.bool b) : IO (Function (if c then p.yes else p.no) pn (pe s o d c extra) st (fr c b s)) := do
  if h : c=true then
    let f ← conditionalLambda p.yes s o b extra st
    return by simpa only [h,guardEq h,fr,↓reduceIte] using f
  else
    have hfalse : c=false := by cases c <;> simp_all
    let f ← pairLambda p.no pn (pe s o d c extra) st s (sid 32) .head .head (by rw [fresh1]; decide) true
    return by simpa only [hfalse,fr,Bool.false_eq_true,↓reduceIte] using f
private def immediate (c b : Bool) (s o : V) : V := if c then fr c b s (.word (w 0)) else .pair (.word (w 0)) o
private def mainCall {fs s o d c b extra st} (f : Function fs pn (pe s o d c extra) st (fr c b s)) (source : Syntax.Expr) :
    IO (PLift (E owner tn (te fs s o d c extra) st source (immediate c b s o) st)) := do
  match shape : source with
  | ⟨_,.call ⟨_,.group callee⟩ ⟨_,[argument]⟩⟩ =>
    let p ← originalConditional callee; let q ← originalConditional argument
    let g ← ref owner tn (te fs s o d c extra) st p.condition "c" (sid 3) (.bool c)
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))))
    let h ← ref owner tn (te fs s o d c extra) st q.condition "c" (sid 3) (.bool c)
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))))
    if yes : c=true then
      let head ← ref owner tn (te fs s o d c extra) st p.yes "f" (sid 33) (fv fs s o d c extra) (.tail (by decide) .head) (.tail (by decide) .head)
      let arg ← ref owner tn (te fs s o d c extra) st q.yes "x" (sid 34) (.word (w 0)) .head .head
      return ⟨by
        subst c; rw [shape]; simp only [immediate,↓reduceIte]; exact .call f.shape
          (.group (chosen p true g.down (by simpa only [↓reduceIte,fv] using head.down)))
          (chosen q true h.down (by simpa only [↓reduceIte] using arg.down))
          (by simpa only [f.named] using f.evaluated (.word (w 0)))⟩
    else
      have no : c=false := by cases c <;> simp_all
      let post ← pairLambda p.no tn (te fs s o d c extra) st (.word (w 0)) (sid 34) .head .head (by rw [fresh3]; decide) false
      let arg ← ref owner tn (te fs s o d c extra) st q.no "other" (sid 8) o
        (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
      return ⟨by
        subst c; rw [shape]; simp only [immediate,Bool.false_eq_true,↓reduceIte]; exact .call post.shape
          (.group (chosen p false g.down (by simpa only [Bool.false_eq_true,↓reduceIte] using (show E owner tn (te fs s o d false extra) st p.no (.sourceClosure p.no owner tn (te fs s o d false extra)) st from .creation post.shape))))
          (chosen q false h.down (by simpa only [Bool.false_eq_true,↓reduceIte] using arg.down))
          (by simpa only [post.named,pairResult,Bool.false_eq_true,↓reduceIte] using post.evaluated o)⟩
  | _ => throw (IO.userError "original conditional callee/argument")
private structure Witness (source : Syntax.Expr) (s o d : V) (c b : Bool) (extra : C) (st : List V) where
  fs : Syntax.Expr
  f : Function fs pn (pe s o d c extra) st (fr c b s)
  originalBody : Syntax.Block
  body : B owner pn (pe s o d c extra) st originalBody (.pair (immediate c b s o) (fv fs s o d c extra)) st
  whole : E owner names (rows s o d c extra) st source (.pair (immediate c b s o) (fv fs s o d c extra)) st
private def witness (source : Syntax.Expr) (s o d : V) (c b : Bool) (extra : C) (st : List V)
    (guardEq : c=true → d=.bool b) : IO (Witness source s o d c b extra st) := do
  match original : source with
  | ⟨_,.call ⟨_,.group ⟨_,.lambda _ ⟨_,[⟨_,.typed none parameter _⟩]⟩ _ body⟩⟩ ⟨_,[argument]⟩⟩ =>
    match prefixShape : body with
    | ⟨span,[⟨_,.letDecl n none (some initial)⟩,⟨ls,.letDecl x (some annotation) (some ⟨ws,.literal ⟨litSpan,.decimal "0"⟩⟩)⟩,⟨rs,.returnStmt (some ⟨ts,.tuple ⟨ps,[called,returned]⟩⟩)⟩]⟩ =>
      if valid : parameter.value="x" ∧ n.value="f" ∧ x.value="x" then
        let p ← originalConditional initial; let fs := if c then p.yes else p.no
        let f ← selectedFunction p s o d c b extra st guardEq
        let g ← ref owner pn (pe s o d c extra) st p.condition "c" (sid 3) (.bool c)
          (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
        let call ← mainCall f called
        let ret ← ref owner tn (te fs s o d c extra) st returned "f" (sid 33) (fv fs s o d c extra) (.tail (by decide) .head) (.tail (by decide) .head)
        let a ← ref owner names (rows s o d c extra) st argument "saved" (sid 7) s .head (.tail (by decide) .head)
        have ending : B owner tn (te fs s o d c extra) st ⟨span,[⟨rs,.returnStmt (some ⟨ts,.tuple ⟨ps,[called,returned]⟩⟩)⟩]⟩ (.pair (immediate c b s o) (fv fs s o d c extra)) st := .expression (.pair call.down ret.down)
        have zero : WordLiteralDenotes ⟨litSpan,.decimal "0"⟩ (w 0) := .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
        have typed : B owner fn ((sid 33,fv fs s o d c extra)::pe s o d c extra) st
            ⟨span,[⟨ls,.letDecl x (some annotation) (some ⟨ws,.literal ⟨litSpan,.decimal "0"⟩⟩)⟩,⟨rs,.returnStmt (some ⟨ts,.tuple ⟨ps,[called,returned]⟩⟩)⟩]⟩ (.pair (immediate c b s o) (fv fs s o d c extra)) st :=
          .binding (.wordLiteral zero) (by simpa only [valid.2.2,fresh2,tn,te] using ending)
        have bodyProof : B owner pn (pe s o d c extra) st body (.pair (immediate c b s o) (fv fs s o d c extra)) st := by
          rw [prefixShape]; exact .inferred (chosen p c g.down (.creation f.shape)) (by simpa only [valid.2.1,fresh1,fn,fv] using typed)
        return ⟨fs,f,body,bodyProof,by rw [original]; exact .call SourceUnaryLambdaShape.typed (.group (.creation SourceUnaryLambdaShape.typed)) a.down (by simpa only [valid.1,fresh0,pn,pe] using bodyProof)⟩
      else throw (IO.userError "original x/f/shadow binders")
    | _ => throw (IO.userError "original initializer/shadow/return")
  | _ => throw (IO.userError "original grouped typed call")
private def caller := {owner with declarationIndex:=160}
private def rid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def callNames : LocalNameTable := [("picked",rid 0),("other",rid 1)]
private def reapplied {fs ns es st result} (f : Function fs ns es st result) (source : Syntax.Expr) (o : V) :
    IO (PLift (E caller callNames [(rid 0,.sourceClosure fs owner ns es),(rid 1,o)] st source (result o) st)) := do
  match shape : source with
  | ⟨_,.call callee ⟨_,[argument]⟩⟩ =>
    let a ← ref caller callNames [(rid 0,.sourceClosure fs owner ns es),(rid 1,o)] st callee "picked" (rid 0) (.sourceClosure fs owner ns es) .head .head
    let b ← ref caller callNames [(rid 0,.sourceClosure fs owner ns es),(rid 1,o)] st argument "other" (rid 1) o (.tail (by decide) .head) (.tail (by decide) .head)
    return ⟨by rw [shape]; exact .call f.shape a.down b.down (by simpa only [f.named] using f.evaluated o)⟩
  | _ => throw (IO.userError "original different-caller call")
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"closed-source-conditionals.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next => check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && source.span==Syntax.SourceSpan.fullFile file) "complete original AST/span"; return source
  | _ => throw (IO.userError "original parser")
private def run {source s o d c b extra st} (proof : Witness source s o d c b extra st) (picked : Syntax.Expr) : IO Unit := do
  let next ← reapplied proof.f picked o
  have _ := evaluateClosedSourceExpression?_eventually_complete proof.whole
  have _ := evaluateClosedSourceBody?_eventually_complete proof.body
  have _ := evaluateClosedSourceExpression?_eventually_complete next.down
  let depth := if c then 10 else 9
  match proof.originalBody.value with
  | [⟨_,.letDecl _ _ (some initial)⟩,_,⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[⟨_,.call ⟨_,.group callee⟩ ⟨_,[argument]⟩⟩,_]⟩⟩)⟩] =>
    let p ← originalConditional initial
    law p pn (pe s o d c extra) st
    law (← originalConditional callee) tn (te proof.fs s o d c extra) st
    law (← originalConditional argument) tn (te proof.fs s o d c extra) st
    match p.yes.value with
    | .lambda _ _ _ ⟨_,[⟨_,.returnStmt (some nested)⟩]⟩ => law (← originalConditional nested) (("y",sid 33)::pn) ((sid 33,.word (w 0))::pe s o d c extra) st
    | _ => throw (IO.userError "original nested conditional law")
  | _ => throw (IO.userError "original conditional law positions")
  for budget in List.range (depth+3) do
    match actual : evaluateClosedSourceExpression? budget owner names (rows s o d c extra) st source with
    | none => check (budget<depth) "expression below threshold; None is not a fault"
    | some (value,final) =>
      match actualShape : value with
      | .pair (.pair _ _) (.sourceClosure fs own ns es) =>
        check (depth≤budget && fs==proof.fs && own==owner && ns==pn && es.map Prod.fst==(pe s o d c extra).map Prod.fst && final.length==st.length) "actual returned original closure and raw store"
        have same := (evaluateClosedSourceExpression?_sound actual).deterministic proof.whole
        have saved : RuntimeValue.sourceClosure fs own ns es=fv proof.fs s o d c extra := by rw [actualShape] at same; exact (RuntimeValue.pair.inj same.1).2
        have independent : E caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked (fr c b s o) final := by simpa only [saved,same.2,fv] using next.down
        for more in List.range 8 do
          match computed : evaluateClosedSourceExpression? more caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked with
          | none => check (more<(if c then 5 else 4)) "returned closure below threshold"
          | some (v,store) => check ((if c then 5 else 4)≤more && store.length==final.length && (match v with | .pair _ _ => true | _ => false)) "actual reapplied mixed pair"; have _ := (evaluateClosedSourceExpression?_sound computed).deterministic independent; pure ()
      | _ => throw (IO.userError "actual result pair and returned source closure")
    match actual : evaluateClosedSourceBody? budget owner pn (pe s o d c extra) st proof.originalBody with
    | none => check (budget+1<depth) "body below threshold"
    | some (value,store) => check (depth≤budget+1) "body threshold"; have _ := (evaluateClosedSourceBody?_sound actual).deterministic proof.body; pure ()
private def standalone (source : Syntax.Expr) (s o : V) (c : Bool) (extra : C) (st : List V) : IO Unit := do
  match shape : source with
  | ⟨_,.call ⟨_,.group callee⟩ ⟨_,[argument]⟩⟩ =>
    let p ← originalConditional callee; let fs := if c then p.yes else p.no
    match original : fs with
    | ⟨_,.lambda _ ⟨_,[⟨_,.inferred y⟩]⟩ none ⟨_,[⟨_,.returnStmt (some ⟨_,.identifier r⟩)⟩]⟩⟩ =>
      if valid : y.value="y" ∧ r.value="y" then
        let g ← ref owner names (rows s o .unit c extra) st p.condition "c" (sid 3) (.bool c) (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
        let a ← ref owner names (rows s o .unit c extra) st argument "saved" (sid 7) s .head (.tail (by decide) .head)
        have lambda : SourceUnaryLambdaShape fs y _ := by rw [original]; exact .inferred
        have independent : E owner names (rows s o .unit c extra) st source s st := by
          rw [shape]; exact .call lambda (.group (chosen p c g.down (.creation lambda))) a.down (.expression (.reference (by rw [valid.1,valid.2]; exact .head) .head))
        have _ := evaluateClosedSourceExpression?_eventually_complete independent
        law p names (rows s o .unit c extra) st
        for n in List.range 7 do
          match actual : evaluateClosedSourceExpression? n owner names (rows s o .unit c extra) st source with
          | none => check (n<4) "identity selected closure depth"
          | some (v,store) => check (4≤n) "identity actual threshold"; have _ := (evaluateClosedSourceExpression?_sound actual).deterministic independent; pure ()
        check ((evaluateClosedSourceExpression? 40 owner names (rows s o .unit (!c) extra) st source).isNone) "selected missing zero-arity branch is unsupported"
      else throw (IO.userError "original identity references")
    | _ => throw (IO.userError "original selected identity lambda")
  | _ => throw (IO.userError "original standalone call")
end ParsedClosedSourceConditionals
open ParsedClosedSourceConditionals Solcore.Frontend in
/-- Parsed conditional selection preserves original captures and actual mixed endpoints. -/
def frontendParsedClosedSourceConditionalTests : IO Unit := do
  let source ← parsed mainText; let picked ← parsed "picked(other)"
  let yes ← parsed yesText; let no ← parsed noText; let inert ← parsed "lam(){return absent;}"
  let s := RuntimeValue.sourceClosure inert caller [("unseen",foreign)] [(sid 32,.bool false)]
  for o in [.hostFunction .storageWrite,.coreClosure .unit .word (.var 99) [s,.cellRef .word 700]] do
    for extra in [[],[(sid 32,o),(foreign,s)]] do
      for store in [[.unit],[s,.cellRef (.function .word .word) 1]] do
        for b in [true,false] do
          run (← witness source s o (.bool b) true b extra store (by intro _; rfl)) picked
          run (← witness source s o (.bool b) false b extra store (by simp)) picked
        run (← witness source s o o false true extra store (by simp)) picked
        check ((evaluateClosedSourceExpression? 40 owner names (rows s o o true extra) store source).isNone) "visited non-Bool d has no supported success"
        check ((evaluateClosedSourceExpression? 40 owner names ((sid 3,o)::rows s o .unit true extra) store source).isNone) "non-Bool c has no supported success"
        standalone yes s o true extra store; standalone no s o false extra store
end Tests

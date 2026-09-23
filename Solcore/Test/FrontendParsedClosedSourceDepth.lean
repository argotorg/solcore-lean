import Solcore.Frontend.ClosedSource
import Solcore.Syntax.Parser.Term

/- Independent original certificates precede search; actual returned closures and
stores are reused under a different caller. None is not a runtime fault. -/
set_option autoImplicit false
namespace Tests
namespace ParsedClosedSourceDepth
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev C := Resolved.LocalScope V
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (label : String) : IO Unit := unless b do throw (IO.userError label)
private def mainText := "(lam(x:Unknown)->Unknown{let f=c?lam(y){return d?(x,y):(y,x);}:lam(y){return (y,x);};let x:Missing=0;return f;})(saved)"
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ClosedSourceDepth",by decide⟩],by decide⟩⟩,161⟩
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
    check ([(31,84,32,62),(47,60,48,54)].contains (s.startByte,s.endByte,q.startByte,colon.startByte) && mainText.toUTF8[q.startByte]? == some 63 && mainText.toUTF8[colon.startByte]? == some 58) "literal original ranges and punctuation bytes"
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
private def function (fs : Syntax.Expr) (s o d : V) (c b : Bool) (extra : C) (st : List V)
    (guardEq : c=true → d=.bool b) : IO (Function fs pn (pe s o d c extra) st (fr c b s)) := do
  if h : c=true then
    let f ← conditionalLambda fs s o b extra st
    return by simpa only [h,guardEq h,fr,↓reduceIte] using f
  else
    have hfalse : c=false := by cases c <;> simp_all
    let f ← pairLambda fs pn (pe s o d c extra) st s (sid 32) .head .head (by rw [fresh1]; decide) true
    return by simpa only [hfalse,fr,Bool.false_eq_true,↓reduceIte] using f
private structure Witness (source : Syntax.Expr) (s o d : V) (c : Bool) (extra : C) (st : List V) where
  fs : Syntax.Expr
  originalBody : Syntax.Block
  body : B owner pn (pe s o d c extra) st originalBody (fv fs s o d c extra) st
  whole : E owner names (rows s o d c extra) st source (fv fs s o d c extra) st
private def witness (source : Syntax.Expr) (s o d : V) (c : Bool) (extra : C) (st : List V) : IO (Witness source s o d c extra st) := do
  match original : source with
  | ⟨_,.call ⟨_,.group ⟨_,.lambda _ ⟨_,[⟨_,.typed none parameter _⟩]⟩ _ body⟩⟩ ⟨_,[argument]⟩⟩ =>
    match prefixShape : body with
    | ⟨span,[⟨_,.letDecl n none (some initial)⟩,⟨ls,.letDecl x (some annotation) (some ⟨ws,.literal ⟨litSpan,.decimal "0"⟩⟩)⟩,⟨rs,.returnStmt (some returned)⟩]⟩ =>
      if valid : parameter.value="x" ∧ n.value="f" ∧ x.value="x" then
        let p ← originalConditional initial; let fs := if c then p.yes else p.no
        match fsShape : fs with
        | ⟨_,.lambda _ ⟨_,[⟨_,.inferred y⟩]⟩ none inner⟩ =>
          have lambda : SourceUnaryLambdaShape fs y inner := by rw [fsShape]; exact .inferred
          let g ← ref owner pn (pe s o d c extra) st p.condition "c" (sid 3) (.bool c)
            (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
          let ret ← ref owner tn (te fs s o d c extra) st returned "f" (sid 33) (fv fs s o d c extra) (.tail (by decide) .head) (.tail (by decide) .head)
          let a ← ref owner names (rows s o d c extra) st argument "saved" (sid 7) s .head (.tail (by decide) .head)
          have zero : WordLiteralDenotes ⟨litSpan,.decimal "0"⟩ (w 0) := .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
          have typed : B owner fn ((sid 33,fv fs s o d c extra)::pe s o d c extra) st
              ⟨span,[⟨ls,.letDecl x (some annotation) (some ⟨ws,.literal ⟨litSpan,.decimal "0"⟩⟩)⟩,⟨rs,.returnStmt (some returned)⟩]⟩ (fv fs s o d c extra) st :=
            .binding (.wordLiteral zero) (by simpa only [valid.2.2,fresh2,tn,te] using (show B owner tn (te fs s o d c extra) st ⟨span,[⟨rs,.returnStmt (some returned)⟩]⟩ (fv fs s o d c extra) st from .expression ret.down))
          have bodyProof : B owner pn (pe s o d c extra) st body (fv fs s o d c extra) st := by
            rw [prefixShape]; exact .inferred (chosen p c g.down (.creation lambda)) (by simpa only [valid.2.1,fresh1,fn,fv] using typed)
          return ⟨fs,body,bodyProof,by rw [original]; exact .call SourceUnaryLambdaShape.typed (.group (.creation SourceUnaryLambdaShape.typed)) a.down (by simpa only [valid.1,fresh0,pn,pe] using bodyProof)⟩
        | _ => throw (IO.userError "original selected unary source")
      else throw (IO.userError "original x/f/shadow binders")
    | _ => throw (IO.userError "original initializer/shadow/return")
  | _ => throw (IO.userError "original grouped typed call")
private def caller := {owner with declarationIndex:=162}
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
  let file : Syntax.SourceFile := ⟨⟨.main,"closed-source-depth.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next => check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && source.span==Syntax.SourceSpan.fullFile file) "complete original AST/span"; return source
  | _ => throw (IO.userError "original parser")
/- Adjacent budgets are handwritten constructor heights. The existential cutoff
stays in Prop and never selects an IO budget. -/
private theorem thresholdAt {α : Type} {search : Nat → Option α} {expected actual : α} {n : Nat}
    (low : search n=none) (high : search (n+1)=some actual)
    (threshold : ∃ required : Nat, 0<required ∧ ∀ budget, search budget=if required≤budget then some expected else none) :
    ∃ required : Nat, required=n+1 ∧ 0<required ∧ ∀ budget, search budget=if required≤budget then some expected else none := by
  obtain ⟨required,positive,formula⟩ := threshold
  have below : ¬required≤n := by intro order; have h := formula n; rw [if_pos order,low] at h; cases h
  have above : required≤n+1 := by
    by_cases order : required≤n+1
    · exact order
    · have h := formula (n+1); rw [if_neg order,high] at h; cases h
  exact ⟨required,by omega,positive,formula⟩
private def absent {α : Type} (search : Nat → Option α) (large : Nat)
    (down : ∀ {small large : Nat}, small≤large → search large=none → search small=none) : IO (PLift (search large=none)) := do
  match rejected : search large with
  | some _ => throw (IO.userError "independently chosen insufficient budget unexpectedly succeeds")
  | none =>
    for small in [0,1,large/2,large] do
      if order : small≤large then
        have predicted := down order rejected
        match actual : search small with
        | none => pure ()
        | some _ => have impossible := predicted.symm.trans actual; nomatch impossible
    return ⟨rejected⟩
private def depth {α : Type} {expected : α} (search : Nat → Option α) (n : Nat)
    (stable : ∀ {small large : Nat} {actual : α}, small≤large → search small=some actual → search large=some actual)
    (down : ∀ {small large : Nat}, small≤large → search large=none → search small=none)
    (threshold : ∃ required : Nat, 0<required ∧ ∀ budget, search budget=if required≤budget then some expected else none)
    (inspect : α → IO Unit) : IO {actual : α // search (n+1)=some actual ∧
      ∀ budget, search budget=if n+1≤budget then some expected else none} := do
  match accepted : search (n+1) with
  | none => throw (IO.userError "independently witnessed successful budget absent")
  | some endpoint =>
    inspect endpoint
    for larger in [n+1,n+2,n+5,n+13] do
      if order : n+1≤larger then
        have predicted := stable order accepted
        match actual : search larger with
        | none => have impossible := actual.symm.trans predicted; nomatch impossible
        | some observed => inspect observed; have _ : observed=endpoint := Option.some.inj (actual.symm.trans predicted); pure ()
    let rejected ← absent search n down
    have cutoff := thresholdAt rejected.down accepted threshold
    return ⟨endpoint,accepted,by obtain ⟨required,same,_,formula⟩ := cutoff; simpa only [same] using formula⟩
private def run {source s o d c extra st} (proof : Witness source s o d c extra st) (picked : Syntax.Expr)
    (b canCall : Bool) (guardEq : canCall=true → c=true → d=.bool b) : IO Unit := do
  let next : Option (PLift (E caller callNames [(rid 0,fv proof.fs s o d c extra),(rid 1,o)] st picked (fr c b s o) st)) ←
    if enabled : canCall=true then do
      let f ← function proof.fs s o d c b extra st (guardEq enabled)
      pure (some (← reapplied f picked o))
    else pure none
  let inspect : V × List V → IO Unit := fun (value,final) => match value with
    | .sourceClosure fs own ns es => check (fs==proof.fs && own==owner && ns==pn && es.map Prod.fst==(pe s o d c extra).map Prod.fst && final.length==st.length) "actual returned original closure and raw store"
    | _ => throw (IO.userError "actual returned source closure")
  let actual ← depth (fun n => evaluateClosedSourceExpression? n owner names (rows s o d c extra) st source) 4
    (fun order accepted => evaluateClosedSourceExpression?_monotone order accepted)
    (fun order rejected => evaluateClosedSourceExpression?_none_of_le order rejected)
    (ClosedSourceExpressionEvaluates.exact_depth_threshold proof.whole) inspect
  let final := actual.val.2
  match actualShape : actual.val.1 with
  | .sourceClosure fs own ns es =>
    have same := (evaluateClosedSourceExpression?_sound actual.property.1).deterministic proof.whole
    have saved : RuntimeValue.sourceClosure fs own ns es=fv proof.fs s o d c extra := by rw [actualShape] at same; exact same.1
    match next with
    | some certificate =>
      have independent : E caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked (fr c b s o) final := by simpa only [saved,final,same.2] using certificate.down
      let result ← depth (fun n => evaluateClosedSourceExpression? n caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked) (if c then 4 else 3)
        (fun order accepted => evaluateClosedSourceExpression?_monotone order accepted)
        (fun order rejected => evaluateClosedSourceExpression?_none_of_le order rejected)
        (ClosedSourceExpressionEvaluates.exact_depth_threshold independent)
        (fun (v,t) => check (t.length==final.length && (match v with | .pair _ _ => true | _ => false)) "actual reapplied mixed pair")
      have _ := (evaluateClosedSourceExpression?_sound result.property.1).deterministic independent
      pure ()
    | none =>
      let _ ← absent (fun n => evaluateClosedSourceExpression? n caller callNames [(rid 0,.sourceClosure fs own ns es),(rid 1,o)] final picked) 40
        (fun order rejected => evaluateClosedSourceExpression?_none_of_le order rejected)
      pure ()
  | _ => throw (IO.userError "actual main returned source closure")
  let body ← depth (fun n => evaluateClosedSourceBody? n owner pn (pe s o d c extra) st proof.originalBody) 3
    (fun order accepted => evaluateClosedSourceBody?_monotone order accepted)
    (fun order rejected => evaluateClosedSourceBody?_none_of_le order rejected)
    (ClosedSourceBodyEvaluates.exact_depth_threshold proof.body) inspect
  have _ := (evaluateClosedSourceBody?_sound body.property.1).deterministic proof.body
  pure ()
end ParsedClosedSourceDepth
open ParsedClosedSourceDepth Solcore.Frontend in
/-- Independent parsed closure endpoints and actual derivation-depth boundaries. -/
def frontendParsedClosedSourceDepthTests : IO Unit := do
  let source ← parsed mainText; let picked ← parsed "picked(other)"; let inert ← parsed "lam(){return absent;}"
  let s := RuntimeValue.sourceClosure inert caller [("unseen",foreign)] [(sid 32,.bool false)]
  for o in [.hostFunction .storageWrite,.coreClosure .unit .word (.var 99) [s,.cellRef .word 700]] do
    for extra in [[],[(sid 32,o),(foreign,s)]] do
      for store in [[.unit],[s,.cellRef (.function .word .word) 1]] do
        for c in [true,false] do
          for b in [true,false] do
            run (← witness source s o (.bool b) c extra store) picked b true (by intro _ _; rfl)
        run (← witness source s o o false extra store) picked true true (by simp)
        run (← witness source s o o true extra store) picked true false (by simp)
        let _ ← absent (fun n => evaluateClosedSourceExpression? n owner names ((sid 3,o)::rows s o .unit true extra) store source) 40
          (fun order rejected => evaluateClosedSourceExpression?_none_of_le order rejected)
        pure ()
end Tests

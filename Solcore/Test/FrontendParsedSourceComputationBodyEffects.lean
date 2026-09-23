import Solcore.Frontend.SourceComputationBody
import Solcore.Frontend.SourceLambdaEvaluation
import Solcore.Frontend.LocalReference
import Solcore.Resolved.LocalScope
import Solcore.Syntax.Parser.Term

set_option autoImplicit false
namespace Tests
namespace ParsedSourceComputationBodyEffects
open Solcore Solcore.Frontend
private abbrev Store := List RuntimeValue
private abbrev Captures := Resolved.LocalScope RuntimeValue
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def word (n : Nat) : Core.Word := ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def w (n : Nat) : RuntimeValue := .word (word n)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"MixedSourceBodies",by decide⟩],by decide⟩⟩,155⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def caller : Resolved.DeclarationId := {owner with declarationIndex:=156}
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def names : LocalNameTable := [("x",sid 7),("r",sid 31),("c",sid 3),("r",sid 8),("x",foreign)]
private def captured (c : Bool) : Captures :=
  [(sid 32,.bool false),(sid 31,.cellRef (.function .word .word) 0),(sid 7,w 5),(sid 31,w 99),(sid 3,.bool c),(foreign,.unit)]
private def ns0 := ("x",sid 32)::names
private def ns1 := ("x",sid 33)::ns0
private def ns2 := ("x",sid 34)::ns1
private def es0 (q : RuntimeValue) (c : Bool) := (sid 32,q)::captured c
private def es1 (q : RuntimeValue) (c : Bool) := (sid 33,q)::es0 q c
private def es2 (q r : RuntimeValue) (c : Bool) := (sid 34,r)::es1 q c
private theorem fresh0 : Resolved.freshLocalId owner (names.map Prod.snd)=sid 32 := by decide
private theorem fresh1 : Resolved.freshLocalId owner (ns0.map Prod.snd)=sid 33 := by decide
private theorem fresh2 : Resolved.freshLocalId owner (ns1.map Prod.snd)=sid 34 := by decide
private def finalStore (r : RuntimeValue) : Store := [r,.unit,.bool true,w 7]
private def refName (e : Syntax.Expr) : Option String := match e.value with | .identifier n => some n.value | _ => none
private def callShape (e : Syntax.Expr) (name : String) (args : List String) : Bool :=
  match e.value with | .call ⟨_,.identifier n⟩ ⟨_,es⟩ => n.value == name && es.map refName == args.map some | _ => false

/- These six independent callbacks describe only the named fixture operations.
They do not recursively close expression/body evaluation or enforce runtime typing. -/
private inductive Child (o : Resolved.DeclarationId) (ns : LocalNameTable) (es : Captures) :
    Store → Syntax.Expr → RuntimeValue → Store → Prop where
  | reference {s e n i v} (shape : refName e = some n) (name : LocalNameTable.Lookup ns n i)
      (value : Resolved.LocalScope.Lookup es i v) : Child o ns es s e v s
  | fetch {s e i v} (shape : callShape e "fetch" [] = true) (name : LocalNameTable.Lookup ns "fetch" i)
      (value : Resolved.LocalScope.Lookup es i v) : Child o ns es s e v (s ++ [.unit])
  | argument {s e i j q r} (shape : callShape e "argument" [] = true)
      (name : LocalNameTable.Lookup ns "argument" i) (value : Resolved.LocalScope.Lookup es i q)
      (writtenName : LocalNameTable.Lookup ns "written" j) (written : Resolved.LocalScope.Lookup es j r) :
      Child o ns es s e q (s.set 0 r)
  | load {s e i tag location v} (shape : callShape e "load" ["r"] = true)
      (name : LocalNameTable.Lookup ns "r" i) (reference : Resolved.LocalScope.Lookup es i (.cellRef tag location))
      (read : s[location]? = some v) : Child o ns es s e v s
  | touch {s e} (shape : callShape e "touch" [] = true) : Child o ns es s e .unit (s ++ [.bool true])
  | observe {s e i v} (shape : callShape e "observe" ["x"] = true)
      (name : LocalNameTable.Lookup ns "x" i) (value : Resolved.LocalScope.Lookup es i v) :
      Child o ns es s e v (s ++ [w 7])
private abbrev Body := SourceComputationBodyEvaluates Child
private def pattern (p : Syntax.Pattern) : IO (Σ tag : Option Core.Word, PLift (WordMatchPatternClassifies p tag)) := do
  match shape : p with
  | ⟨_,.wildcard _⟩ => return ⟨none,⟨by rw [shape]; exact .wildcard rfl⟩⟩
  | ⟨_,.group inner⟩ =>
    check (p.span.contains inner.span) "original grouped pattern ranges"
    let child ← pattern inner
    return ⟨child.1,⟨by rw [shape]; exact .group child.2.down⟩⟩
  | ⟨_,.literal ⟨s,.decimal "0"⟩⟩ =>
    return ⟨some (word 0),⟨by rw [shape]; exact .literal ⟨_,rfl,.decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)⟩⟩⟩
  | ⟨_,.literal ⟨s,.hexadecimal "0x00"⟩⟩ =>
    return ⟨some (word 0),⟨by rw [shape]; exact .literal ⟨_,rfl,.hexadecimal rfl (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) (.cons (.decimal (digit:=0) (by decide) rfl) .nil))⟩⟩⟩
  | _ => throw (IO.userError "outside independently supported fixture patterns")
termination_by sizeOf p
private def choice (r : RuntimeValue) (cs : List Syntax.MatchCase) (d : Option Syntax.Block) :
    IO (Σ selected : Syntax.Block, Σ tests : Nat, PLift (RuntimeWordMatchChooses r cs d selected tests)) := do
  match casesShape : cs with
  | [] => match defaultShape : d with
    | some b => return ⟨b,0,⟨by rw [casesShape,defaultShape]; exact .fallback⟩⟩
    | none => throw (IO.userError "no original fallback")
  | first::rest =>
    let p ← pattern first.value.pattern
    match tag : p.1 with
    | none => return ⟨first.value.body,0,⟨by rw [casesShape]; exact .wildcard (tag ▸ p.2.down)⟩⟩
    | some literal => match actual : r with
      | .word value =>
        if same : value = literal then
          return ⟨first.value.body,1,⟨by rw [casesShape,actual,same]; exact .hit (tag ▸ p.2.down)⟩⟩
        else
          let tail ← choice (.word value) rest d
          return ⟨tail.1,tail.2.1+1,⟨by rw [casesShape]; simpa only [actual] using RuntimeWordMatchChooses.miss (tag ▸ p.2.down) same tail.2.2.down⟩⟩
      | _ => throw (IO.userError "no successful literal choice, not a runtime fault")
termination_by cs.length
private def returned (q r : RuntimeValue) (c : Bool) (b : Syntax.Block) :
    IO (Σ bare : Bool, PLift (Body owner ns2 (es2 q r c) (finalStore r) b (if bare then .unit else r) (finalStore r))) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨true,⟨by rw [shape]; exact .bare⟩⟩
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
    if ref : refName e = some "x" then return ⟨false,⟨by rw [shape]; exact .expression (.reference ref .head .head)⟩⟩
    else throw (IO.userError "unselected or unsupported returned expression")
  | _ => throw (IO.userError "fixture return shape")
private def matched (q r : RuntimeValue) (c : Bool) (b : Syntax.Block) :
    IO (Σ bare : Bool, PLift (Body owner ns2 (es2 q r c) [r,.unit,.bool true] b (if bare then .unit else r) (finalStore r))) := do
  match shape : b with
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨cs,d⟩⟩⟩]⟩ =>
    check (b.span.contains e.span && cs.all (fun arm => b.span.contains arm.span &&
      arm.span.contains arm.value.pattern.span && arm.span.contains arm.value.body.span) &&
      d.toList.all (fun branch => b.span.contains branch.span)) "original scrutinee, arms and optional default spans"
    if observed : callShape e "observe" ["x"] = true then
      let selected ← choice r cs d
      let result ← returned q r c selected.1
      have _ : ∀ b n, RuntimeWordMatchChooses r cs d b n → b=selected.1 ∧ n=selected.2.1 :=
        fun _ _ other => RuntimeWordMatchChooses.deterministic other selected.2.2.down
      return ⟨result.1,⟨by rw [shape]; exact .wordMatch (.observe observed .head .head) selected.2.2.down result.2.down⟩⟩
    else throw (IO.userError "original single effectful scrutinee")
  | _ => throw (IO.userError "original singleton match")
private def terminal (q r : RuntimeValue) (c : Bool) (b : Syntax.Block) :
    IO (Σ bare : Bool, PLift (Body owner ns2 (es2 q r c) [r,.unit,.bool true] b (if bare then .unit else r) (finalStore r))) := do
  match shape : b with
  | ⟨_,[⟨_,.ifThen condition thenBody (some elseBody)⟩]⟩ =>
    if ref : refName condition = some "c" then
      have evaluated : Child owner ns2 (es2 q r c) [r,.unit,.bool true] condition (.bool c) [r,.unit,.bool true] :=
        .reference ref (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
          (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))))
      match branch : c with
      | true =>
        match explicit : thenBody with
        | ⟨_,[⟨innerSpan,.block statements⟩]⟩ =>
          let result ← matched q r c ⟨innerSpan,statements⟩
          return ⟨result.1,⟨by rw [shape]; exact .ifTrue (by simpa only [branch] using evaluated) (by rw [explicit]; exact .block result.2.down)⟩⟩
        | _ => throw (IO.userError "original explicit then block")
      | false =>
        let result ← matched q r c elseBody
        return ⟨result.1,⟨by rw [shape]; exact .ifFalse (by simpa only [branch] using evaluated) result.2.down⟩⟩
    else throw (IO.userError "captured condition")
  | _ => matched q r c b
private def body (q r : RuntimeValue) (c : Bool) (b : Syntax.Block) :
    IO (Σ bare : Bool, PLift (Body owner ns0 (es0 q c) [r,.unit] b (if bare then .unit else r) (finalStore r))) := do
  match shape : b with
  | ⟨span,⟨_,.letDecl n (some _) (some init)⟩::⟨ms,.letDecl m none (some load)⟩::⟨ds,.expression touch true⟩::rest⟩ =>
    check (span.contains n.span && span.contains m.span && span.contains init.span && span.contains load.span &&
      span.contains touch.span && rest.all (fun statement => span.contains statement.span)) "original initializer and tail ranges"
    if valid : n.value="x" ∧ m.value="x" ∧ refName init=some "x" ∧
        callShape load "load" ["r"]=true ∧ callShape touch "touch" []=true then
      have hn := valid.1; have hm := valid.2.1
      let result ← terminal q r c ⟨span,rest⟩
      have first : Child owner ns0 (es0 q c) [r,.unit] init q [r,.unit] := .reference valid.2.2.1 .head .head
      have second : Child owner ns1 (es1 q c) [r,.unit] load r [r,.unit] :=
        .load valid.2.2.2.1 (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
          (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))) rfl
      have last : Body owner ns2 (es2 q r c) [r,.unit] ⟨span,⟨ds,.expression touch true⟩::rest⟩ (if result.1 then .unit else r) (finalStore r) :=
        .discard (.touch valid.2.2.2.2) result.2.down
      have next : Body owner ns1 (es1 q c) [r,.unit] ⟨span,⟨ms,.letDecl m none (some load)⟩::⟨ds,.expression touch true⟩::rest⟩ (if result.1 then .unit else r) (finalStore r) :=
        .inferred second (by simpa only [hm,fresh2,ns2,es2] using last)
      return ⟨result.1,⟨by rw [shape]; exact .binding first (by simpa only [hn,fresh1,ns1,es1] using next)⟩⟩
    else throw (IO.userError "original same-name binders, old initializer, load and discard")
  | _ => throw (IO.userError "independent typed/inferred/discard original prefix")
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"mixed-source-body-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && source.span == Syntax.SourceSpan.fullFile file) "full original source and diagnostics"
    return source
  | .reject _ _ => throw (IO.userError "parser rejection")
  | .invariant _ => throw (IO.userError "parser invariant")
private def inspect (source callSource : Syntax.Expr) (q r : RuntimeValue) (c : Bool) (bare : Bool := false) : IO Unit := do
  match original : source, callShapeEq : callSource with
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none name _⟩]⟩ _ savedBody⟩,⟨callSpan,.call callee ⟨argumentsSpan,[argument]⟩⟩ =>
    if valid : name.value="x" ∧ callShape callee "fetch" []=true ∧ callShape argument "argument" []=true then
      have parameter := valid.1; have fetch := valid.2.1; have arg := valid.2.2
      have saved : SourceUnaryLambdaShape source name savedBody := by rw [original]; exact .typed
      check (source.span.contains name.span && source.span.contains savedBody.span &&
        savedBody.span.startByte==23 && savedBody.span.endByte==source.span.endByte) "whole saved original lambda and body"
      have created : SourceLambdaEvaluates Child Body owner names (captured c) [w 5] source
          (.sourceClosure source owner names (captured c)) [w 5] := .creation saved
      have _ := (SourceLambdaEvaluates.creation_iff saved).mp created
      let result ← body q r c savedBody
      let callerNames : LocalNameTable := [("fetch",cid 7),("argument",cid 900),("written",cid 42)]
      let callerValues : Captures := [(cid 900,q),(cid 42,r),(cid 7,.sourceClosure source owner names (captured c))]
      have first : Child caller callerNames callerValues [w 23] callee
          (.sourceClosure source owner names (captured c)) [w 23,.unit] :=
        .fetch fetch .head (.tail (by decide) (.tail (by decide) .head))
      have second : Child caller callerNames callerValues [w 23,.unit] argument q [r,.unit] :=
        .argument arg (.tail (by decide) .head) .head (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) .head)
      have actual : SourceLambdaEvaluates Child Body caller callerNames callerValues [w 23] callSource (if result.1 then .unit else r) (finalStore r) := by
        rw [callShapeEq]; exact .call saved first second (by simpa only [parameter,fresh0,ns0,es0] using result.2.down)
      have literal : SourceLambdaEvaluates Child Body caller callerNames callerValues [w 23]
          ⟨callSpan,.call callee ⟨argumentsSpan,[argument]⟩⟩ (if result.1 then .unit else r) (finalStore r) := by
        simpa only [callShapeEq] using actual
      have exposed := SourceLambdaEvaluates.call_iff.mp literal
      have _ := (SourceLambdaEvaluates.call_iff (span:=callSpan) (argumentsSpan:=argumentsSpan)).mpr exposed
      check (decide (owner≠caller ∧ Resolved.freshLocalId owner (names.map Prod.snd)=sid 32 ∧
        Resolved.freshLocalId owner (ns0.map Prod.snd)=sid 33 ∧ Resolved.freshLocalId owner (ns1.map Prod.snd)=sid 34)) "saved-owner names-only freshness"
      check (decide ((es2 q r c).map Prod.fst=[sid 34,sid 33,sid 32,sid 32,sid 31,sid 7,sid 31,sid 3,foreign])) "all old and colliding captures retained"
      have _ : Resolved.LocalScope.Lookup (es2 q r c) (sid 34) r := .head
      have _ : Resolved.LocalScope.Lookup (es2 q r c) (sid 33) q := .tail (by decide) .head
      have _ : Resolved.LocalScope.Lookup (es2 q r c) (sid 32) q := .tail (by decide) (.tail (by decide) .head)
      check ((finalStore r).map RuntimeValue.toCore? == [r.toCore?,some .unit,some (.bool true),some (.word (word 7))]) "distinct argument/discard/scrutinee effects"
      if exactReturn : result.1=bare then
        have _ : SourceLambdaEvaluates Child Body caller callerNames callerValues [w 23] callSource
            (if bare then .unit else r) (finalStore r) := by simpa only [exactReturn] using actual
        pure ()
      else throw (IO.userError "wrong original selected return")
    else throw (IO.userError "original parameter/callee/argument callback shapes")
  | _,_ => throw (IO.userError "independent original lambda/call shape")
private theorem no_literal_choice {r : RuntimeValue} (nonword : ∀ v, r ≠ .word v)
    {first : Syntax.MatchCase} {rest : List Syntax.MatchCase} {d : Option Syntax.Block}
    (meaning : WordMatchPatternClassifies first.value.pattern (some (word 0))) :
    ∀ b n, ¬ RuntimeWordMatchChooses r (first::rest) d b n := by
  intro b n chosen
  cases chosen with
  | wildcard other => cases meaning.tag_unique other
  | hit => exact nonword _ rfl
  | miss => exact nonword _ rfl
private def literalBoundary (source : Syntax.Expr) (q r : RuntimeValue) (nonword : ∀ v, r ≠ .word v) : IO Unit := do
  match source.value with
  | .lambda _ _ _ ⟨_,[_,_,_,⟨_,.matchWith ⟨_,⟨scrutinee,[]⟩⟩ ⟨_,⟨[first,duplicate,wildcard],none⟩⟩⟩]⟩ =>
    let p ← pattern first.value.pattern; let d ← pattern duplicate.value.pattern; let wild ← pattern wildcard.value.pattern
    if tags : p.1=some (word 0) ∧ d.1=some (word 0) ∧ wild.1=none then
      have pm := tags.1 ▸ p.2.down; have dm := tags.2.1 ▸ d.2.down; have wm := tags.2.2 ▸ wild.2.down
      have firstHit : RuntimeWordMatchChooses (w 0) [first,duplicate,wildcard] none first.value.body 1 := .hit pm
      have misses : RuntimeWordMatchChooses (w 1) [first,duplicate,wildcard] none wildcard.value.body 2 :=
        .miss pm (by decide) (.miss dm (by decide) (.wildcard wm))
      let a ← choice (w 0) [first,duplicate,wildcard] none
      let b ← choice (w 1) [first,duplicate,wildcard] none
      have _ := a.2.2.down.deterministic firstHit
      have _ := b.2.2.down.deterministic misses
      have oldHit : WordMatchChooses (.word (word 0)) [first,duplicate,wildcard] none first.value.body 1 := .hit pm
      have _ := runtimeWordMatchChooses_ofCore_iff.mpr oldHit
      have _ : WordMatchChooses (.word (word 1)) [first,duplicate,wildcard] none wildcard.value.body 2 :=
        runtimeWordMatchChooses_ofCore_iff.mp (by simpa only [RuntimeValue.ofCore,w] using misses)
      have _ : ∀ selected tests, ¬ RuntimeWordMatchChooses r [first,duplicate,wildcard] none selected tests :=
        no_literal_choice nonword pm
      if observed : callShape scrutinee "observe" ["x"]=true then
        have _ : Child owner ns2 (es2 q r true) [r,.unit,.bool true] scrutinee r (finalStore r) :=
          .observe observed .head .head
        check (a.1 == first.value.body && a.2.1==1 && b.1 == wildcard.value.body && b.2.1==2)
          "independent original first hit/miss counts; non-Word choice absent, not a fault-store claim"
      else throw (IO.userError "original literal-first scrutinee")
    else throw (IO.userError "independent 0/0x00/grouped-wildcard meanings")
  | _ => throw (IO.userError "original literal-first lambda body")
end ParsedSourceComputationBodyEffects

open ParsedSourceComputationBodyEffects in
/-- Bounded original callback/body witnesses, not a recursively closed evaluator or safety claim. -/
def frontendParsedSourceComputationBodyEffectTests : IO Unit := do
  let conditional ← parsed "lam(x:Unknown)->Unknown{let x:Missing=x;let x=load(r);touch();if(c){{match(observe(x)){case ((_)){return x;}case Missing{return absent;}}}}else{match(observe(x)){default{return x;}}}}"
  let literals ← parsed "lam(x:Unknown)->Unknown{let x:Missing=x;let x=load(r);touch();match(observe(x)){case 0{return x;}case 0x00{return absent;}case ((_)){return x;}}}"
  let bare ← parsed "lam(x:Unknown)->Unknown{let x:Missing=x;let x=load(r);touch();match(observe(x)){default{return;}}}"
  let callSource ← parsed "fetch()(argument())"
  let payload ← parsed "lam(){return absent;}"
  let q := Solcore.Frontend.RuntimeValue.sourceClosure payload caller [] [(sid 99,.bool false)]
  let r := Solcore.Frontend.RuntimeValue.sourceClosure payload owner [("saved",sid 7)] [(sid 7,w 41)]
  for actual in [r,.coreClosure .bool .unit (.var 99) [r,.cellRef .word 700]] do
    for c in [true,false] do inspect conditional callSource q actual c
    inspect bare callSource q actual true true
  inspect literals callSource q (w 0) true
  inspect literals callSource q (w 1) false
  literalBoundary literals q r (by intro value; dsimp only [r]; intro impossible; cases impossible)
  literalBoundary literals q (.coreClosure .bool .unit (.var 99) [r,.cellRef .word 700])
    (by intro value impossible; cases impossible)

end Tests

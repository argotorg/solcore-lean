import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Syntax.Parser.Term

set_option autoImplicit false
namespace Tests
namespace ParsedClosedSourceClosures
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private abbrev Store := List RuntimeValue
private abbrev Captures := Resolved.LocalScope RuntimeValue
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def word (n : Nat) : Core.Word := ⟨n % Core.wordModulus,Nat.mod_lt _ (by decide)⟩
private def zero : RuntimeValue := .word (word 0)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ClosedSourceCalls",by decide⟩],by decide⟩⟩,157⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def names : LocalNameTable := [("saved",sid 7),("other",sid 8),("c",sid 3),("tag",sid 31),("saved",sid 9),("x",foreign)]
private def captures (s o : RuntimeValue) (c hit : Bool) : Captures :=
  [(sid 32,.unit),(sid 7,s),(sid 8,o),(sid 31,.word (word (if hit then 0 else 1))),(sid 7,.bool false),(sid 3,.bool c),(foreign,.unit)]
private def pn := ("x",sid 32)::names
private def pe (s o : RuntimeValue) (c hit : Bool) := (sid 32,s)::captures s o c hit
private def fn := ("f",sid 33)::pn
private def closure (source : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) : RuntimeValue := .sourceClosure source owner pn (pe s o c hit)
private def fe (source : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) := (sid 33,closure source s o c hit)::pe s o c hit
private def tn := ("x",sid 34)::fn
private def te (source : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) := (sid 34,zero)::fe source s o c hit
private theorem fresh0 : Resolved.freshLocalId owner (names.map Prod.snd)=sid 32 := by decide
private theorem fresh1 : Resolved.freshLocalId owner (pn.map Prod.snd)=sid 33 := by decide
private theorem fresh2 : Resolved.freshLocalId owner (fn.map Prod.snd)=sid 34 := by decide
private structure Unary (source : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source name body
private def unary : (source : Syntax.Expr) → IO (Unary source)
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred n⟩]⟩ _ b⟩ => pure ⟨n,b,.inferred⟩
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none n _⟩]⟩ _ b⟩ => pure ⟨n,b,.typed⟩
  | _ => throw (IO.userError "original unary source shape")
private def reference (ns : LocalNameTable) (es : Captures) (store : Store) (source : Syntax.Expr)
    (spelling : String) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup ns spelling id) (found : Resolved.LocalScope.Lookup es id value) :
    IO (PLift (E owner ns es store source value store)) := do
  match shape : source with
  | ⟨_,.identifier n⟩ => if same : n.value=spelling then return ⟨by rw [shape]; exact .reference (same ▸ named) found⟩ else throw (IO.userError "original reference spelling")
  | _ => throw (IO.userError "original identifier")
private def pairBody (s o a : RuntimeValue) (c hit : Bool) (store : Store) (body : Syntax.Block) :
    IO (PLift (B owner (("y",sid 33)::pn) ((sid 33,a)::pe s o c hit) store body (.pair s a) store)) := do
  match shape : body with
  | ⟨_,[⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[x,y]⟩⟩)⟩]⟩ =>
    let left ← reference (("y",sid 33)::pn) ((sid 33,a)::pe s o c hit) store x "x" (sid 32) s (.tail (by decide) .head) (.tail (by decide) .head)
    let right ← reference (("y",sid 33)::pn) ((sid 33,a)::pe s o c hit) store y "y" (sid 33) a .head .head
    return ⟨by rw [shape]; exact .expression (.pair left.down right.down)⟩
  | _ => throw (IO.userError "saved original pair return")
private def av (k : Nat) (s o : RuntimeValue) : RuntimeValue := match k with | 0 => zero | 1 => o | 2 => s | _ => .unit
private def argument (k : Nat) (fs : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) (store : Store) (e : Syntax.Expr) :
    IO (PLift (E owner tn (te fs s o c hit) store e (av k s o) store)) := do
  match index : k with
  | 0 =>
    let value ← reference tn (te fs s o c hit) store e "x" (sid 34) zero .head .head
    return ⟨by simpa only [index,av] using value.down⟩
  | 1 =>
    let value ← reference tn (te fs s o c hit) store e "other" (sid 8) o
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
    return ⟨by simpa only [index,av] using value.down⟩
  | 2 =>
    let value ← reference tn (te fs s o c hit) store e "saved" (sid 7) s
      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
    return ⟨by simpa only [index,av] using value.down⟩
  | _+3 => match shape : e with
    | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨by rw [shape,index]; exact .unit⟩
    | _ => throw (IO.userError "original empty tuple argument")
private def applyF (k : Nat) (fs : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) (store : Store) (e : Syntax.Expr) :
    IO (PLift (E owner tn (te fs s o c hit) store e (.pair s (av k s o)) store)) := do
  match shape : e with
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
    let header ← unary fs
    if parameter : header.name.value="y" then
      let callee ← reference tn (te fs s o c hit) store f "f" (sid 33) (closure fs s o c hit) (.tail (by decide) .head) (.tail (by decide) .head)
      let arg ← argument k fs s o c hit store a
      let body ← pairBody s o (av k s o) c hit store header.body
      return ⟨by rw [shape]; exact .call header.shape callee.down arg.down (by simpa only [parameter,fresh1] using body.down)⟩
    else throw (IO.userError "inner original parameter y")
  | _ => throw (IO.userError "original f unary call")
private def answer (s o : RuntimeValue) (c hit : Bool) : RuntimeValue :=
  if c then if hit then .pair (.pair s zero) (.pair (.pair s o) (.pair .unit s)) else .pair s s else .pair s o
private def returnedCall (k : Nat) (fs : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) (store : Store) (body : Syntax.Block) :
    IO (PLift (B owner tn (te fs s o c hit) store body (.pair s (av k s o)) store)) := do
  match shape : body with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let result ← applyF k fs s o c hit store e; return ⟨by rw [shape]; exact .expression result.down⟩
  | _ => throw (IO.userError "original selected call return")
private def four (fs : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) (store : Store) (body : Syntax.Block) :
    IO (PLift (B owner tn (te fs s o c hit) store body (.pair (.pair s zero) (.pair (.pair s o) (.pair .unit s))) store)) := do
  match shape : body with
  | ⟨_,[⟨_,.returnStmt (some ⟨_,.tuple ⟨_,[a,b,⟨_,.tuple ⟨_,[]⟩⟩,saved]⟩⟩)⟩]⟩ =>
    let left ← applyF 0 fs s o c hit store a; let middle ← applyF 1 fs s o c hit store b
    let last ← argument 2 fs s o c hit store saved
    return ⟨by rw [shape]; exact .expression (.many left.down (.many middle.down (.pair .unit last.down)))⟩
  | _ => throw (IO.userError "original flat four tuple with explicit unit third element")
private def selected (fs : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) (store : Store) (body : Syntax.Block) :
    IO (PLift (B owner tn (te fs s o c hit) store body (if hit then .pair (.pair s zero) (.pair (.pair s o) (.pair .unit s)) else .pair s s) store)) := do
  match shape : body with
  | ⟨_,[⟨_,.matchWith ⟨_,⟨tag,[]⟩⟩ ⟨_,⟨[first,wild],none⟩⟩⟩]⟩ =>
    let scrutinee ← reference tn (te fs s o c hit) store tag "tag" (sid 31) (.word (word (if hit then 0 else 1)))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))
    match literal : first.value.pattern, wildcard : wild.value.pattern with
    | ⟨_,.literal ⟨_,.decimal "0"⟩⟩,⟨_,.group ⟨_,.group ⟨_,.wildcard _⟩⟩⟩ =>
      have pm : WordMatchPatternClassifies first.value.pattern (some (word 0)) := by rw [literal]; exact .literal ⟨_,rfl,.decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)⟩
      have wm : WordMatchPatternClassifies wild.value.pattern none := by rw [wildcard]; exact .group (.group (.wildcard rfl))
      if h : hit=true then
        let branch ← four fs s o c hit store first.value.body
        return ⟨by rw [shape]; simpa only [h,↓reduceIte] using ClosedSourceBodyEvaluates.wordMatch scrutinee.down (by simpa only [h,↓reduceIte] using RuntimeWordMatchChooses.hit pm) branch.down⟩
      else
        have hfalse : hit=false := by cases hit <;> simp_all
        let branch ← returnedCall 2 fs s o c hit store wild.value.body
        return ⟨by rw [shape]; simpa only [hfalse,Bool.false_eq_true,↓reduceIte,av] using ClosedSourceBodyEvaluates.wordMatch scrutinee.down (by simpa only [hfalse,Bool.false_eq_true,↓reduceIte] using RuntimeWordMatchChooses.miss pm (show word 1≠word 0 by decide) (.wildcard wm)) branch.down⟩
    | _,_ => throw (IO.userError "original literal/grouped-wildcard patterns")
  | _ => throw (IO.userError "original single-scrutinee two-arm match")
private def tailBody (fs : Syntax.Expr) (s o : RuntimeValue) (c hit : Bool) (store : Store) (body : Syntax.Block) :
    IO (PLift (B owner tn (te fs s o c hit) store body (answer s o c hit) store)) := do
  match shape : body with
  | ⟨_,[⟨_,.ifThen condition thenBody (some elseBody)⟩]⟩ =>
    let guard ← reference tn (te fs s o c hit) store condition "c" (sid 3) (.bool c)
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))))))
    if h : c=true then
      match explicit : thenBody with
      | ⟨_,[⟨innerSpan,.block statements⟩]⟩ =>
        let branch ← selected fs s o c hit store ⟨innerSpan,statements⟩
        have guardTrue : E owner tn (te fs s o c hit) store condition (.bool true) store := by simpa only [h] using guard.down
        have selectedBody : B owner tn (te fs s o c hit) store thenBody (if hit then .pair (.pair s zero) (.pair (.pair s o) (.pair .unit s)) else .pair s s) store := by rw [explicit]; exact .block branch.down
        return ⟨by rw [shape]; simpa only [answer,h,↓reduceIte] using ClosedSourceBodyEvaluates.ifTrue guardTrue selectedBody⟩
      | _ => throw (IO.userError "original explicit then block")
    else
      have hfalse : c=false := by cases c <;> simp_all
      let branch ← returnedCall 1 fs s o c hit store elseBody
      have guardFalse : E owner tn (te fs s o c hit) store condition (.bool false) store := by simpa only [hfalse] using guard.down
      return ⟨by rw [shape]; simpa only [answer,hfalse,Bool.false_eq_true,↓reduceIte,av] using ClosedSourceBodyEvaluates.ifFalse guardFalse branch.down⟩
  | _ => throw (IO.userError "original terminal conditional")
private def mainBody (s o : RuntimeValue) (c hit : Bool) (store : Store) (body : Syntax.Block) :
    IO (PLift (B owner pn (pe s o c hit) store body (answer s o c hit) store)) := do
  match shape : body with
  | ⟨span,⟨_,.letDecl f none (some fs)⟩::⟨xs,.letDecl x (some annotation) (some ⟨literalSpan,.literal literal⟩)⟩::⟨ds,.expression discard true⟩::rest⟩ =>
    let header ← unary fs
    if valid : f.value="f" ∧ x.value="x" then
      match zeroShape : literal with
      | ⟨_,.decimal "0"⟩ =>
        let ending ← tailBody fs s o c hit store ⟨span,rest⟩
        let discarded ← applyF 3 fs s o c hit store discard
        have tail : B owner tn (te fs s o c hit) store ⟨span,⟨ds,.expression discard true⟩::rest⟩ (answer s o c hit) store := .discard discarded.down ending.down
        have zeroProof : WordLiteralDenotes literal (word 0) := by rw [zeroShape]; exact .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
        have typed : B owner fn (fe fs s o c hit) store ⟨span,⟨xs,.letDecl x (some annotation) (some ⟨literalSpan,.literal literal⟩)⟩::⟨ds,.expression discard true⟩::rest⟩ (answer s o c hit) store :=
          .binding (.wordLiteral zeroProof) (by simpa only [valid.2,fresh2,tn,te,zero] using tail)
        return ⟨by rw [shape]; exact .inferred (.creation header.shape) (by simpa only [valid.1,fresh1,fn,fe,closure] using typed)⟩
      | _ => throw (IO.userError "original zero initializer")
    else throw (IO.userError "original function/shadow names")
  | _ => throw (IO.userError "original inferred f/typed x/discard prefix")
private def completed {ns es store source value} (proof : E owner ns es store source value store) : IO Unit := do
  have _ : ∀ v final, E owner ns es store source v final → v=value ∧ final=store := fun _ _ other => other.deterministic proof
  match shape : source with
  | ⟨span,.call callee ⟨argsSpan,[argument]⟩⟩ =>
    have literal : E owner ns es store ⟨span,.call callee ⟨argsSpan,[argument]⟩⟩ value store := by simpa only [shape] using proof
    have opened := closedSourceExpressionEvaluates_call_iff.mp literal
    have _ := (closedSourceExpressionEvaluates_call_iff (span:=span) (argumentsSpan:=argsSpan)).mpr opened
    pure ()
  | _ => throw (IO.userError "completed original unary call")
private def mainCall (s o : RuntimeValue) (c hit : Bool) (store : Store) (source : Syntax.Expr) : IO Unit := do
  match shape : source with
  | ⟨_,.call ⟨_,.group fs⟩ ⟨_,[arg]⟩⟩ =>
    let header ← unary fs
    if parameter : header.name.value="x" then
      let argument ← reference names (captures s o c hit) store arg "saved" (sid 7) s .head (.tail (by decide) .head)
      let body ← mainBody s o c hit store header.body
      have openBody := closedSourceBodyEvaluates_iff.mp body.down
      have closedBody := closedSourceBodyEvaluates_iff.mpr openBody
      have _ : ∀ v final, B owner pn (pe s o c hit) store header.body v final → v=answer s o c hit ∧ final=store := fun _ _ other => other.deterministic closedBody
      have evaluated : E owner names (captures s o c hit) store source (answer s o c hit) store := by
        rw [shape]; exact .call header.shape (.group (.creation header.shape)) argument.down (by simpa only [parameter,fresh0,pn,pe] using closedBody)
      completed evaluated
    else throw (IO.userError "outer original x")
  | _ => throw (IO.userError "original grouped outer lambda call")
private def nestedCall (s o : RuntimeValue) (c hit : Bool) (store : Store) (source : Syntax.Expr) : IO Unit := do
  match shape : source with
  | ⟨_,.call ⟨_,.group ⟨_,.call ⟨_,.group fs⟩ ⟨_,[arg]⟩⟩⟩ ⟨_,[other]⟩⟩ =>
    let outer ← unary fs
    match returned : outer.body with
    | ⟨_,[⟨_,.returnStmt (some innerSource)⟩]⟩ =>
      let inner ← unary innerSource
      if parameters : outer.name.value="x" ∧ inner.name.value="y" then
        let a ← reference names (captures s o c hit) store arg "saved" (sid 7) s .head (.tail (by decide) .head)
        let b ← reference names (captures s o c hit) store other "other" (sid 8) o (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
        have innerCreated : B owner pn (pe s o c hit) store outer.body (closure innerSource s o c hit) store := by rw [returned]; exact .expression (.creation inner.shape)
        let pair ← pairBody s o o c hit store inner.body
        have evaluated : E owner names (captures s o c hit) store source (.pair s o) store := by
          rw [shape]; exact .call (savedNames:=pn) (savedCaptured:=pe s o c hit) inner.shape (.group (.call outer.shape (.group (.creation outer.shape)) a.down (by simpa only [parameters.1,fresh0,pn,pe,closure] using innerCreated))) b.down (by simpa only [parameters.2,fresh1] using pair.down)
        completed evaluated
      else throw (IO.userError "original nested x/y names")
    | _ => throw (IO.userError "original returned lambda expression")
  | _ => throw (IO.userError "two original nested unary calls")
private def bareCall (s o : RuntimeValue) (c hit : Bool) (store : Store) (source : Syntax.Expr) : IO Unit := do
  match shape : source with
  | ⟨_,.call ⟨_,.group fs⟩ ⟨_,[arg]⟩⟩ =>
    let header ← unary fs
    match originalBody : header.body with
    | ⟨_,[⟨_,.matchWith ⟨_,⟨x,[]⟩⟩ ⟨_,⟨[],some ⟨_,[⟨_,.returnStmt none⟩]⟩⟩⟩⟩]⟩ =>
      if parameter : header.name.value="x" then
        let a ← reference names (captures s o c hit) store arg "saved" (sid 7) s .head (.tail (by decide) .head)
        let scrutinee ← reference pn (pe s o c hit) store x "x" (sid 32) s .head .head
        have body : B owner pn (pe s o c hit) store header.body .unit store := by rw [originalBody]; exact .wordMatch scrutinee.down .fallback .bare
        have _ := closedSourceBodyEvaluates_iff.mp body
        have evaluated : E owner names (captures s o c hit) store source .unit store := by
          rw [shape]; exact .call header.shape (.group (.creation header.shape)) a.down (by simpa only [parameter,fresh0,pn,pe] using body)
        completed evaluated
      else throw (IO.userError "original bare lambda parameter")
    | _ => throw (IO.userError "original default-only bare body")
  | _ => throw (IO.userError "original bare lambda call")
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"closed-source-captures.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next => check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && source.span == Syntax.SourceSpan.fullFile file) "full original source/span"; return source
  | .reject _ _ => throw (IO.userError "parser rejection")
  | .invariant _ => throw (IO.userError "parser invariant")
end ParsedClosedSourceClosures

open ParsedClosedSourceClosures in
/-- Constructor-built callback-free proofs for original source closure calls; no execution bound or typing claim. -/
def frontendParsedClosedSourceClosureTests : IO Unit := do
  let mainSource ← parsed "(lam(x:Unknown)->Unknown{let f=lam(y){return (x,y);};let x:Missing=0;f(());if(c){{match(tag){case 0{return (f(x),f(other),(),saved);}case ((_)){return f(saved);}}}}else{return f(other);}})(saved)"
  let nested ← parsed "((lam(x){return lam(y){return (x,y);};})(saved))(other)"
  let bare ← parsed "(lam(x){match(x){default{return;}}})(saved)"
  let inert ← parsed "lam(){return absent;}"
  let saved := Solcore.Frontend.RuntimeValue.sourceClosure inert owner names [(sid 32,.bool false)]
  for other in [.hostFunction .storageWrite,.coreClosure .unit .word (.var 99) [saved,.cellRef .word 700]] do
    for store in [[.unit],[saved,.cellRef (.function .word .word) 1]] do
      mainCall saved other true true store mainSource
      mainCall saved other true false store mainSource
      mainCall saved other false true store mainSource
      nestedCall saved other false false store nested
      bareCall saved other true false store bare

end Tests

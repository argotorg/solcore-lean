import Solcore.Frontend.DirectDataLambdaDepth
import Solcore.Syntax.Parser.Term

/- Actual direct calls retain independently handwritten ASTs and every span.
Original creation/argument/fresh-body/call witnesses precede depth laws. The
grouped bare-call control is a different whole AST: depth three, while its
explicitly extracted direct call has depth two. No saved-call bound or Core cost. -/
set_option autoImplicit false
namespace Tests.ParsedDirectDataLambdaDepth
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedDirectDepth",by decide⟩],by decide⟩⟩,304⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=904},700⟩
private def names : LocalNameTable := [("x",foreign),("p",sid 8),("x",sid 99),("p",sid 99)]
private def rows (v : V) (tail : Resolved.LocalScope V) :=
  [(foreign,v),(foreign,.unit),(sid 8,.bool false),(sid 99,.word Core.Word.maximum)]++tail
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (n : String) : Syntax.Expr :=
  ⟨span f a b,.identifier ⟨span f a b,n⟩⟩
private def expected (typed bare grouped : Bool) (key : String) (f : Syntax.SourceFile) : Syntax.Expr :=
  let k := if grouped then 1 else 0
  let t := if typed then 5 else 0
  let b := k+6+t
  let stop := b+(if bare then 9 else 11)
  let c := stop+(if grouped then 1 else 0)
  let parameter : Syntax.LambdaParameter := if typed then
    ⟨span f (k+4) (k+10),.typed none ⟨span f (k+4) (k+5),"p"⟩
      ⟨span f (k+6) (k+10),.named ⟨span f (k+6) (k+10),⟨⟨⟨span f (k+6) (k+10),"Unit"⟩,[]⟩⟩⟩ none⟩⟩
    else ⟨span f (k+4) (k+5),.inferred ⟨span f (k+4) (k+5),"p"⟩⟩
  let body : Syntax.Block := ⟨span f b stop,[⟨span f (b+1) (stop-1),
    .returnStmt (if bare then none else some (ref f (b+8) (b+9) "p"))⟩]⟩
  let source : Syntax.Expr := ⟨span f k stop,.lambda (span f k (k+3))
    ⟨span f (k+3) (k+6+t),[parameter]⟩ none body⟩
  ⟨span f 0 (c+3),.call (if grouped then ⟨span f 0 c,.group source⟩ else source)
    ⟨span f c (c+3),[ref f (c+1) (c+2) key]⟩⟩
private def refSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span] | _ => []
private def typeSpans : Syntax.TypeExpr → List Syntax.SourceSpan
  | ⟨s,.named ⟨q,⟨⟨i,[]⟩⟩⟩ none⟩ => [s,q,i.span] | _ => []
private def parameterSpans : Syntax.LambdaParameter → List Syntax.SourceSpan
  | ⟨s,.inferred n⟩ => [s,n.span]
  | ⟨s,.typed none n t⟩ => [s,n.span]++typeSpans t | _ => []
private def lambdaSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.lambda k ⟨ps,[p]⟩ none ⟨b,[⟨r,.returnStmt child⟩]⟩⟩ =>
    [s,k,ps]++parameterSpans p++[b,r]++child.toList.flatMap refSpans
  | _ => []
private def calleeSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.group child⟩ => [s]++lambdaSpans child | source => lambdaSpans source
private def actualSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.call callee ⟨a,[argument]⟩⟩ => [s]++calleeSpans callee++[a]++refSpans argument | _ => []
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr)
    (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-direct-data-depth.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "direct depth lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole independent AST / EOF / diagnostics zero"
    check ((actualSpans actual).all (fun s => s.isValidFor file) &&
      (actualSpans actual).map (fun s => (s.startByte,s.endByte))==ranges) "every actual expression/name/type/delimiter span"
    return actual
  | _ => throw (IO.userError "direct depth parser")
private structure LC (source : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source name body
private def lambda (source : Syntax.Expr) : IO (LC source) := do
  match h : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred name⟩]⟩ _ body⟩ => return ⟨name,body,by rw [h]; exact .inferred⟩
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none name _⟩]⟩ _ body⟩ => return ⟨name,body,by rw [h]; exact .typed⟩
  | _ => throw (IO.userError "actual direct unary lambda")
private structure CC (e : Resolved.LocalScope V) (st : List V) (callee : Syntax.Expr) where
  source : Syntax.Expr
  cert : LC source
  original : E owner names e st callee (.sourceClosure source owner names e) st
private def calleeWitness (e : Resolved.LocalScope V) (st : List V) (callee : Syntax.Expr) : IO (CC e st callee) := do
  match h : callee with
  | ⟨s,.group inner⟩ =>
    have notDirect : ∀ name body, ¬ SourceUnaryLambdaShape ⟨s,.group inner⟩ name body := by
      intro name body impossible; cases impossible
    proof notDirect
    let c ← lambda inner
    return ⟨inner,c,by rw [h]; exact .group (.creation c.shape)⟩
  | _ =>
    let c ← lambda callee
    return ⟨callee,c,.creation c.shape⟩
private structure BC (e : Resolved.LocalScope V) (st : List V) (name : Syntax.Identifier)
    (argument : V) (body : Syntax.Block) where
  value : V
  gate : ClosedSourceDataBody body
  original : ClosedSourceBodyEvaluates owner
    ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
    ((Resolved.freshLocalId owner (names.map Prod.snd),argument)::e) st body value st
private def bodyWitness (e : Resolved.LocalScope V) (st : List V) (name : Syntax.Identifier)
    (v : V) (body : Syntax.Block) : IO (BC e st name v body) := do
  match h : body with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,by rw [h]; exact .bare,by rw [h]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some ⟨_,.identifier key⟩)⟩]⟩ =>
    if same : key.value=name.value then
      return ⟨v,by rw [h]; exact .expression .reference,
        by rw [h]; exact .expression (.reference (same ▸ LocalNameTable.Lookup.head) .head)⟩
    else throw (IO.userError "actual fresh parameter reference")
  | _ => throw (IO.userError "actual return body")
private theorem noArgument {e st callee source argument callSpan argumentsSpan}
    (created : E owner names e st callee (.sourceClosure source owner names e) st)
    (absent : ∀ value final, ¬ E owner names e st argument value final) :
    ∀ value final, ¬ E owner names e st ⟨callSpan,.call callee ⟨argumentsSpan,[argument]⟩⟩ value final := by
  intro value final original
  cases original with
  | creation impossible => cases impossible
  | call _ actualCallee actualArgument _ =>
    obtain ⟨sameCallee,sameStore⟩ := actualCallee.deterministic created
    cases sameCallee; cases sameStore
    exact absent _ _ actualArgument
private def fullEndpoint {e st src value} (original : E owner names e st src value st) (depth : Nat) : IO Unit := do
  have endpoints : ∀ actual final, E owner names e st src actual final ↔ actual=value ∧ final=st :=
    fun _ _ => ⟨fun other => other.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩
  proof endpoints
  for budget in [0,depth-1,depth,depth+3] do
    match ran : evaluateClosedSourceExpression? budget owner names e st src with
    | none => check (budget<depth) "fixture selected exact depth"
    | some (actual,final) =>
      have equal := (endpoints actual final).mp (evaluateClosedSourceExpression?_sound ran)
      proof equal; proof ((endpoints actual final).mpr equal)
      check (depth<=budget) "complete actual RuntimeValue and store retained"
private def exercise (whole : Syntax.Expr) (v : V) (tail : Resolved.LocalScope V) (st : List V)
    (directDepth wholeDepth : Nat) (failure : Bool) : IO Unit := do
  let e := rows v tail
  match hwhole : whole with
  | ⟨callSpan,.call actualCallee ⟨argumentsSpan,[argument]⟩⟩ =>
    let c ← calleeWitness e st actualCallee
    let b ← bodyWitness e st c.cert.name v c.cert.body
    let direct : Syntax.Expr := ⟨callSpan,.call c.source ⟨argumentsSpan,[argument]⟩⟩
    have created : E owner names e st c.source (.sourceClosure c.source owner names e) st := .creation c.cert.shape
    proof created; proof c.original; proof b.original
    match ha : argument with
    | ⟨_,.identifier key⟩ =>
      have argGate : ClosedSourceDataExpression argument := by rw [ha]; exact .reference
      let bound := directDataLambdaDepthBound argument c.cert.body
      check (bound==directDepth) "actual extracted direct-call bound"
      if missing : key.value="z" then
        check failure "only the planned missing-argument fixture"
        have absent : ∀ value final, ¬ E owner names e st argument value final := by
          intro value final original
          rw [ha] at original
          cases original with
          | reference named _ =>
            have lookup := LocalNameTable.lookup?_iff.mpr named
            rw [missing] at lookup
            cases lookup
          | creation impossible => cases impossible
        have noDirect := noArgument (callSpan:=callSpan) (argumentsSpan:=argumentsSpan) created absent
        have noWhole := noArgument (callSpan:=callSpan) (argumentsSpan:=argumentsSpan) c.original absent
        proof noDirect; proof (show ∀ value final, ¬ E owner names e st whole value final from hwhole ▸ noWhole)
        have atBound := (directDataLambda_evaluate_depth_none_iff c.cert.shape argGate b.gate
          (Nat.le_refl bound) (callSpan:=callSpan) (argumentsSpan:=argumentsSpan)).mpr noDirect
        proof atBound
        have allBudgets := (directDataLambda_evaluate_depth_none_iff_all_budgets c.cert.shape argGate b.gate).mp atBound
        proof allBudgets
        proof ((directDataLambda_evaluate_depth_none_iff c.cert.shape argGate b.gate (Nat.le_refl bound)).mp atBound)
        for extra in [0,1,7] do
          proof (directDataLambda_evaluate_depth_stable c.cert.shape argGate b.gate (Nat.le_add_right bound extra)
            (owner:=owner) (names:=names) (captured:=e) (initialStore:=st)
            (callSpan:=callSpan) (argumentsSpan:=argumentsSpan))
        for budget in [0,bound-1,bound,bound+3] do
          check ((evaluateClosedSourceExpression? budget owner names e st whole).isNone) "actual whole missing argument"
          proof (allBudgets budget)
      else if named : key.value="x" then
        check (!failure) "planned original successful call"
        have arg : E owner names e st argument v st := by rw [ha]; exact .reference (named ▸ LocalNameTable.Lookup.head) .head
        have original : E owner names e st direct b.value st := .call c.cert.shape created arg b.original
        have originalWhole : E owner names e st whole b.value st := by
          rw [hwhole]; exact .call c.cert.shape c.original arg b.original
        proof arg; proof original; proof originalWhole
        fullEndpoint original directDepth
        fullEndpoint originalWhole wholeDepth
        for extra in [0,1,7] do
          have enough := Nat.le_add_right bound extra
          have everyEndpoint : ∀ actual final,
              evaluateClosedSourceExpression? (bound+extra) owner names e st direct = some (actual,final) ↔
                E owner names e st direct actual final := fun _ _ =>
            directDataLambda_evaluate_at_depthBound_iff c.cert.shape argGate b.gate enough
          proof everyEndpoint
          have found := directDataLambda_evaluates_at_depthBound c.cert.shape argGate b.gate original enough
          proof found
          proof ((directDataLambda_evaluate_at_depthBound_iff c.cert.shape argGate b.gate enough).mp found)
          proof ((directDataLambda_evaluate_at_depthBound_iff c.cert.shape argGate b.gate enough).mpr original)
          proof (directDataLambda_evaluate_depth_stable c.cert.shape argGate b.gate enough
            (owner:=owner) (names:=names) (captured:=e) (initialStore:=st)
            (callSpan:=callSpan) (argumentsSpan:=argumentsSpan))
      else throw (IO.userError "actual argument spelling")
    | _ => throw (IO.userError "actual argument reference")
  | _ => throw (IO.userError "actual whole unary call")
end Tests.ParsedDirectDataLambdaDepth
open Solcore Solcore.Frontend Tests.ParsedDirectDataLambdaDepth in
def Tests.frontendParsedDirectDataLambdaDepthTests : IO Unit := do
  let inferred ← parsed "lam(p){return p;}(x)" (expected false false false "x")
    [(0,20),(0,17),(0,3),(3,6),(4,5),(4,5),(6,17),(7,16),(14,15),(14,15),(17,20),(18,19),(18,19)]
  let typed ← parsed "lam(p:Unit){return p;}(x)" (expected true false false "x")
    [(0,25),(0,22),(0,3),(3,11),(4,10),(4,5),(6,10),(6,10),(6,10),(11,22),(12,21),(19,20),(19,20),(22,25),(23,24),(23,24)]
  let bare ← parsed "lam(p){return;}(x)" (expected false true false "x")
    [(0,18),(0,15),(0,3),(3,6),(4,5),(4,5),(6,15),(7,14),(15,18),(16,17),(16,17)]
  let missing ← parsed "lam(p:Unit){return;}(z)" (expected true true false "z")
    [(0,23),(0,20),(0,3),(3,11),(4,10),(4,5),(6,10),(6,10),(6,10),(11,20),(12,19),(20,23),(21,22),(21,22)]
  let grouped ← parsed "(lam(p){return;})(x)" (expected false true true "x")
    [(0,20),(0,17),(1,16),(1,4),(4,7),(5,6),(5,6),(7,16),(8,15),(17,20),(18,19),(18,19)]
  let saved := RuntimeValue.sourceClosure inferred foreign.owner [("p",foreign),("p",sid 8)]
    [(foreign,.unit),(foreign,.word Core.Word.maximum)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let mut count := 0
  for value in [saved,RuntimeValue.pair (.word Core.Word.maximum) core] do
    for tail in [[],[(foreign,core),(sid 8,saved),(sid 100,core),(sid 101,saved)]] do
      for store in [[],[saved,core,RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef (.function .word .word) 900]] do
        for (source,d,w,bad) in [(inferred,3,3,false),(typed,3,3,false),(bare,2,2,false),
            (missing,2,2,true),(grouped,2,3,false)] do
          exercise source value tail store d w bad
          count := count+1
  check (count==40) "five actual spellings / eight mixed duplicate-row full-store contexts"

import Solcore.Frontend.SelfApplication
import Solcore.Frontend.ClosedSource
import Solcore.Syntax.Parser.Term

/- Separate actual source occurrences create finite closures with literal saved fields.
Successful child runs precede exact self-reentry non-return laws. Identity and
false short-circuit controls succeed; None alone is not a fault/divergence classifier. -/
set_option autoImplicit false
namespace Tests.ParsedSelfApplication
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedSelf",by decide⟩],by decide⟩⟩,n⟩
private def so := owner 310
private def co := owner 910
private def sid (n : Nat) : Resolved.LocalId := ⟨so,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def sn : LocalNameTable := [("q",sid 8),("r",sid 9),("q",sid 99),("r",sid 99),("x",cid 70)]
private def se (core other : V) : Resolved.LocalScope V :=
  [(sid 8,core),(sid 8,other),(sid 9,other),(sid 99,.unit),(sid 100,core),(cid 70,.cellRef .word 700)]
private def cn : LocalNameTable := [("f",cid 1),("x",cid 2),("a",cid 3),("f",cid 99),("x",cid 99)]
private def ce (saved other : V) : Resolved.LocalScope V :=
  [(cid 1,saved),(cid 1,other),(cid 2,saved),(cid 2,other),(cid 3,.bool false),(cid 99,other)]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (n : String) : Syntax.Expr := ⟨span f a b,.identifier ⟨span f a b,n⟩⟩
private def expectedLambda (typed loop : Bool) (k : Nat) (name : String) (f : Syntax.SourceFile) : Syntax.Expr :=
  let t := if typed then 5 else 0
  let b := k+6+t
  let stop := b+(if loop then 14 else 11)
  let parameter : Syntax.LambdaParameter := if typed then
    ⟨span f (k+4) (k+10),.typed none ⟨span f (k+4) (k+5),name⟩
      ⟨span f (k+6) (k+10),.named ⟨span f (k+6) (k+10),⟨⟨⟨span f (k+6) (k+10),"Word"⟩,[]⟩⟩⟩ none⟩⟩
    else ⟨span f (k+4) (k+5),.inferred ⟨span f (k+4) (k+5),name⟩⟩
  let child := if loop then ⟨span f (b+8) (b+12),.call (ref f (b+8) (b+9) name)
    ⟨span f (b+9) (b+12),[ref f (b+10) (b+11) name]⟩⟩ else ref f (b+8) (b+9) name
  ⟨span f k stop,.lambda (span f k (k+3)) ⟨span f (k+3) (k+6+t),[parameter]⟩ none
    ⟨span f b stop,[⟨span f (b+1) (stop-1),.returnStmt (some child)⟩]⟩⟩
private def expectedWhole (lt rt loop : Bool) (f : Syntax.SourceFile) : Syntax.Expr :=
  let k := (if loop then 21 else 18)+(if lt then 5 else 0)
  let stop := k+21+(if rt then 5 else 0)
  ⟨span f 0 stop,.call (expectedLambda lt loop 0 "q" f)
    ⟨span f (k-1) stop,[expectedLambda rt true k "r" f]⟩⟩
private def expectedCall (k : Nat) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f k (k+4),.call (ref f k (k+1) "f") ⟨span f (k+1) (k+4),[ref f (k+2) (k+3) "x"]⟩⟩
private def expectedShort (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 9,.binary (ref f 0 1 "a") ⟨span f 2 4,.logicalAnd⟩ (expectedCall 5 f)⟩
private def parameterSpans : Syntax.LambdaParameter → List Syntax.SourceSpan
  | ⟨s,.inferred n⟩ => [s,n.span]
  | ⟨s,.typed none n ⟨t,.named ⟨q,⟨⟨i,[]⟩⟩⟩ none⟩⟩ => [s,n.span,t,q,i.span]
  | _ => []
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.call f ⟨a,[x]⟩⟩ => [s]++spans f++[a]++spans x
  | ⟨s,.binary l op r⟩ => [s]++spans l++[op.span]++spans r
  | ⟨s,.lambda k ⟨ps,[p]⟩ none ⟨b,[⟨r,.returnStmt (some e)⟩]⟩⟩ => [s,k,ps]++parameterSpans p++[b,r]++spans e
  | _ => []
private def lambdaRanges (typed loop : Bool) (k : Nat) : List (Nat × Nat) :=
  let t := if typed then 5 else 0
  let b := k+6+t
  let stop := b+(if loop then 14 else 11)
  [(k,stop),(k,k+3),(k+3,k+6+t),(k+4,k+5+t),(k+4,k+5)]++
    (if typed then [(k+6,k+10),(k+6,k+10),(k+6,k+10)] else [])++[(b,stop),(b+1,stop-1)]++
    (if loop then [(b+8,b+12),(b+8,b+9),(b+8,b+9),(b+9,b+12),(b+10,b+11),(b+10,b+11)]
      else [(b+8,b+9),(b+8,b+9)])
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr) (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-self.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "self lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole handwritten AST / EOF / zero diagnostics"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==ranges) "every actual source occurrence/name/type span"
    return actual
  | _ => throw (IO.userError "self parser")
private structure LC (source : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape source name body
private def lambda (source : Syntax.Expr) : IO (LC source) := do
  match h : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred name⟩]⟩ _ body⟩ => return ⟨name,body,by rw [h]; exact .inferred⟩
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none name _⟩]⟩ _ body⟩ => return ⟨name,body,by rw [h]; exact .typed⟩
  | _ => throw (IO.userError "actual unary shape")
private def selfBody (name : Syntax.Identifier) (body : Syntax.Block) : IO (PLift (SourceSelfApplicationBody body name)) := do
  match h : body with
  | ⟨_,[⟨_,.returnStmt (some ⟨_,.call ⟨_,.identifier f⟩ ⟨_,[⟨_,.identifier x⟩]⟩⟩)⟩]⟩ =>
    if same : f.value=name.value ∧ x.value=name.value then return ⟨by rw [h]; exact .returning same.1 same.2⟩
    else throw (IO.userError "actual self reference spellings")
  | _ => throw (IO.userError "actual self body")
private structure Created (o : Resolved.DeclarationId) (n : LocalNameTable) (e : Resolved.LocalScope V)
    (st : List V) (source : Syntax.Expr) where
  saved : Syntax.Expr
  savedOwner : Resolved.DeclarationId
  savedNames : LocalNameTable
  savedCaptured : Resolved.LocalScope V
  out : List V
  fields : RuntimeValue.sourceClosure saved savedOwner savedNames savedCaptured = .sourceClosure source o n e
  unchanged : out=st
  original : E o n e st source (.sourceClosure saved savedOwner savedNames savedCaptured) out
  run : evaluateClosedSourceExpression? 1 o n e st source = some (.sourceClosure saved savedOwner savedNames savedCaptured,out)
private def creation {o n e st source} (cert : LC source) : IO (Created o n e st source) := do
  have independent : E o n e st source (.sourceClosure source o n e) st := .creation cert.shape
  proof independent
  match ran : evaluateClosedSourceExpression? 1 o n e st source with
  | some (.sourceClosure actual ao an ae,out) =>
    have original := evaluateClosedSourceExpression?_sound ran
    have same := original.deterministic independent
    proof same
    return ⟨actual,ao,an,ae,out,same.1,same.2,original,ran⟩
  | _ => throw (IO.userError "actual independent creation")
private def nonreturn {o n e st source}
    (absent : ∀ value final, ¬ E o n e st source value final)
    (exhausted : ∀ budget, evaluateClosedSourceExpression? budget o n e st source = none) : IO Unit := do
  proof absent; proof exhausted
  for budget in [0,1,2,3,8,17] do
    match ran : evaluateClosedSourceExpression? budget o n e st source with
    | none => proof (exhausted budget)
    | some (_,_) => False.elim (absent _ _ (evaluateClosedSourceExpression?_sound ran))
private def direct (source : Syntax.Expr) (loop : Bool) (core other : V) (st : List V) : IO Unit := do
  match hw : source with
  | ⟨cs,.call left ⟨als,[right]⟩⟩ =>
    let lc ← lambda left; let rc ← lambda right
    let lm ← creation (o:=co) (n:=sn) (e:=se core other) (st:=st) lc
    let rm ← creation (o:=co) (n:=sn) (e:=se core other) (st:=lm.out) rc
    proof lm.original; proof rm.original; proof lm.fields; proof rm.fields; proof rm.unchanged; proof lm.run; proof rm.run
    check (left.span != right.span && lc.name.value != rc.name.value && lm.saved != rm.saved) "separate actual lambda occurrences"
    if loop then
      let ls ← selfBody lc.name lc.body; let rs ← selfBody rc.name rc.body
      nonreturn (o:=co) (n:=sn) (e:=se core other) (st:=st) (source:=source)
        (by rw [hw]; exact directSelfApplication_no_original lc.shape ls.down rc.shape rs.down co sn (se core other) st cs als)
        (by rw [hw]; exact directSelfApplication_none lc.shape ls.down rc.shape rs.down co sn (se core other) st cs als)
    else
      let actual ← lambda lm.saved
      match hb : actual.body with
      | ⟨_,[⟨_,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
        if same : key.value=actual.name.value then
          let value := RuntimeValue.sourceClosure rm.saved rm.savedOwner rm.savedNames rm.savedCaptured
          let fresh := Resolved.freshLocalId lm.savedOwner (lm.savedNames.map Prod.snd)
          have independent : B lm.savedOwner ((actual.name.value,fresh)::lm.savedNames)
              ((fresh,value)::lm.savedCaptured) rm.out actual.body value rm.out := by
            rw [hb]; exact .expression (.reference (same ▸ LocalNameTable.Lookup.head) .head)
          have notSelf : ¬ SourceSelfApplicationBody actual.body actual.name := by rw [hb]; intro impossible; cases impossible
          have original : E co sn (se core other) st source value rm.out := by
            rw [hw]; exact .call actual.shape lm.original rm.original independent
          proof notSelf; proof independent; proof original
          match br : evaluateClosedSourceBody? 2 lm.savedOwner ((actual.name.value,fresh)::lm.savedNames)
              ((fresh,value)::lm.savedCaptured) rm.out actual.body with
          | some (bv,bs) =>
            have actualBody := evaluateClosedSourceBody?_sound br
            proof (show bv=value ∧ bs=rm.out from actualBody.deterministic independent)
            have actualCall : E co sn (se core other) st source bv bs := by
              rw [hw]; exact .call actual.shape lm.original rm.original actualBody
            proof actualCall
            for budget in [0,2,3,6] do
              match ran : evaluateClosedSourceExpression? budget co sn (se core other) st source with
              | none => check (budget<3) "identity low depth"
              | some (_,_) => proof ((evaluateClosedSourceExpression?_sound ran).deterministic actualCall)
          | none => throw (IO.userError "actual identity body returns complete loop closure")
        else throw (IO.userError "actual identity parameter")
      | _ => throw (IO.userError "actual identity return")
  | _ => throw (IO.userError "actual whole direct call")
private def savedLaws {saved : Syntax.Expr} (cert : LC saved) (self : SourceSelfApplicationBody cert.body cert.name)
    (ao : Resolved.DeclarationId) (an : LocalNameTable) (ae : Resolved.LocalScope V)
    (other : V) (st : List V) (source : Syntax.Expr) : IO Unit := do
  match hw : source with
  | ⟨cs,.call ⟨fs,.identifier f⟩ ⟨als,[⟨xs,.identifier x⟩]⟩⟩ =>
    if same : f.value="f" ∧ x.value="x" then
      let value := RuntimeValue.sourceClosure saved ao an ae
      let e := ce value other
      have fn : LocalNameTable.Lookup cn f.value (cid 1) := same.1 ▸ .head
      have xn : LocalNameTable.Lookup cn x.value (cid 2) := same.2 ▸ .tail (by decide) .head
      have fv : Resolved.LocalScope.Lookup e (cid 1) value := .head
      have xv : Resolved.LocalScope.Lookup e (cid 2) value := .tail (by decide) (.tail (by decide) .head)
      have picked : E co cn e st ⟨fs,.identifier f⟩ value st := .reference fn fv
      proof picked
      match fr : evaluateClosedSourceExpression? 1 co cn e st ⟨fs,.identifier f⟩ with
      | some (actual,cst) =>
        proof fr; proof (show actual=value ∧ cst=st from (evaluateClosedSourceExpression?_sound fr).deterministic picked)
        have argument : E co cn e cst ⟨xs,.identifier x⟩ value cst := .reference xn xv
        proof argument
        match xr : evaluateClosedSourceExpression? 1 co cn e cst ⟨xs,.identifier x⟩ with
        | some (av,ast) =>
          proof xr; proof (show av=value ∧ ast=cst from (evaluateClosedSourceExpression?_sound xr).deterministic argument)
        | none => throw (IO.userError "actual self argument success")
        proof (show actual=value from ((evaluateClosedSourceExpression?_sound fr).deterministic picked).1)
      | none => throw (IO.userError "actual self callee success")
      nonreturn (o:=co) (n:=cn) (e:=e) (st:=st) (source:=source)
        (by rw [hw]; exact savedSelfApplication_no_original cert.shape self ao an ae co cn e st cs als fs xs f x (cid 1) (cid 2) fn fv xn xv)
        (by rw [hw]; exact savedSelfApplication_none cert.shape self ao an ae co cn e st cs als fs xs f x (cid 1) (cid 2) fn fv xn xv)
    else throw (IO.userError "actual saved f/x")
  | _ => throw (IO.userError "actual saved invocation")
private def saved (source call short : Syntax.Expr) (core other : V) (st : List V) : IO Unit := do
  let cert ← lambda source
  let made ← creation (o:=so) (n:=sn) (e:=se core other) (st:=[other,core,.unit]) cert
  let actual ← lambda made.saved
  let self ← selfBody actual.name actual.body
  proof made.fields; proof made.original; proof made.unchanged; proof made.run
  check (made.savedOwner != co && made.out.length != st.length) "actual creation vs invocation owner/store"
  savedLaws actual self.down made.savedOwner made.savedNames made.savedCaptured other st call
  match hs : short with
  | ⟨_,.binary ⟨ls,.identifier a⟩ ⟨_,.logicalAnd⟩ right⟩ =>
    savedLaws actual self.down made.savedOwner made.savedNames made.savedCaptured other st right
    if key : a.value="a" then
      let value := RuntimeValue.sourceClosure made.saved made.savedOwner made.savedNames made.savedCaptured
      let e := ce value other
      have left : E co cn e st ⟨ls,.identifier a⟩ (.bool false) st :=
        .reference (key ▸ LocalNameTable.Lookup.tail (by decide) (.tail (by decide) .head))
          (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      have original : E co cn e st short (.bool false) st := by rw [hs]; exact .andFalse left
      have direct : evaluateClosedSourceExpression? 2 co cn e st short = some (.bool false,st) := by
        simp [hs,evaluateClosedSourceExpression?,cn,e,ce,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,key,cid]
      proof left; proof original; proof direct
      for budget in [0,1,2,5] do
        match ran : evaluateClosedSourceExpression? budget co cn e st short with
        | none => check (budget<2) "short circuit low depth"
        | some (_,_) => proof ((evaluateClosedSourceExpression?_sound ran).deterministic original)
    else throw (IO.userError "actual false guard")
  | _ => throw (IO.userError "actual short circuit")
end Tests.ParsedSelfApplication
open Solcore Solcore.Frontend Tests.ParsedSelfApplication in
def Tests.frontendParsedSelfApplicationTests : IO Unit := do
  let call ← parsed "f(x)" (expectedCall 0) [(0,4),(0,1),(0,1),(1,4),(2,3),(2,3)]
  let short ← parsed "a && f(x)" expectedShort [(0,9),(0,1),(0,1),(2,4),(5,9),(5,6),(5,6),(6,9),(7,8),(7,8)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let other := RuntimeValue.sourceClosure call (owner 610) [("q",cid 77),("q",cid 88)] [(cid 77,core),(cid 77,.unit)]
  let mut count := 0
  for lt in [false,true] do
    for rt in [false,true] do
      for loop in [true,false] do
        let l := "lam(q"++(if lt then ":Word" else "")++"){return "++(if loop then "q(q)" else "q")++";}"
        let r := "lam(r"++(if rt then ":Word" else "")++"){return r(r);}"
        let k := (if loop then 21 else 18)+(if lt then 5 else 0)
        let stop := k+21+(if rt then 5 else 0)
        let whole ← parsed (l++"("++r++")") (expectedWhole lt rt loop)
          ([(0,stop)]++lambdaRanges lt loop 0++[(k-1,stop)]++lambdaRanges rt true k)
        for st in [[],[other,core,.hostFunction .storageWrite,.cellRef .word 900]] do
          direct whole loop core other st
          let ⟨_,.call _ ⟨_,[right]⟩⟩ := whole | throw (IO.userError "whole argument extraction")
          saved right call short core other st
          count := count+1
  check (count==16) "four typed/inferred pairs / self and identity / two mixed stores"

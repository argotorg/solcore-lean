import Solcore.Frontend.ClosedSource
import Solcore.Syntax.Parser.Term

set_option autoImplicit false
namespace Tests.ParsedClosedStrictWordSavedCalls
open Solcore Solcore.Frontend
private def check (ok : Bool) (message : String) : IO Unit := unless ok do throw (IO.userError message)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def savedOwner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"SavedStrictWord",by decide⟩],by decide⟩⟩,300⟩
private def caller := {savedOwner with declarationIndex := 9300}
private def sid (i : Nat) : Resolved.LocalId := ⟨savedOwner,i⟩
private def cid (i : Nat) : Resolved.LocalId := ⟨caller,i⟩
private def old : RuntimeValue := .coreClosure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700]
private def savedNames : LocalNameTable := [("p",sid 2),("p",sid 2),("foreign",cid 900)]
private def savedRows (fs : Syntax.Expr) : Resolved.LocalScope RuntimeValue :=
  [(sid 2,old),(sid 2,.unit),(cid 900,.sourceClosure fs savedOwner [] [])]
private def names : LocalNameTable := [("picked",cid 0),("p",cid 1),("other",cid 2),("p",cid 1)]
private def rows (made : RuntimeValue) (argument other : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(cid 0,made),(cid 1,.word argument),(cid 2,.word other),(cid 1,old),(sid 2,made),(cid 0,.unit)]
private def file (name text : String) : Syntax.SourceFile := ⟨⟨.main,name⟩,text⟩
private def sp (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (name : String) : Syntax.Expr :=
  ⟨sp f a b,.identifier ⟨sp f a b,name⟩⟩
private def expectedLambda (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨sp f 0 17,.lambda (sp f 0 3) ⟨sp f 3 6,[⟨sp f 4 5,.inferred ⟨sp f 4 5,"p"⟩⟩]⟩ none
    ⟨sp f 6 17,[⟨sp f 7 16,.returnStmt (some (ref f 14 15 "p"))⟩]⟩⟩
private def expectedCall (f : Syntax.SourceFile) (offset : Nat) : Syntax.Expr :=
  ⟨sp f offset (offset+9),.call (ref f offset (offset+6) "picked")
    ⟨sp f (offset+6) (offset+9),[ref f (offset+7) (offset+8) "p"]⟩⟩
private def expectedBinary (f : Syntax.SourceFile) (onLeft : Bool) (symbol : String)
    (op : Syntax.BinaryOp) : Syntax.Expr :=
  let n := symbol.utf8ByteSize
  if onLeft then ⟨sp f 0 (16+n),.binary (expectedCall f 0) ⟨sp f 10 (10+n),op⟩ (ref f (11+n) (16+n) "other")⟩
  else ⟨sp f 0 (16+n),.binary (ref f 0 5 "other") ⟨sp f 6 (6+n),op⟩ (expectedCall f (7+n))⟩
private def parsed (f : Syntax.SourceFile) (expected : Syntax.Expr) : IO Syntax.Expr := do
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok src next =>
    check (next.file==f && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span==Syntax.SourceSpan.fullFile f && src==expected) "exact original AST/all handwritten spans/EOF"
    return src
  | _ => throw (IO.userError "parser")

private structure Trace (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.LocalScope RuntimeValue) (s : List RuntimeValue) (src : Syntax.Expr) where
  value : RuntimeValue
  final : List RuntimeValue
  original : ClosedSourceExpressionEvaluates o n e s src value final
  store_eq : final=s
private def observe {o n e s src v} (d : Nat)
    (original : ClosedSourceExpressionEvaluates o n e s src v s) : IO (Trace o n e s src) := do
  proof original
  match run : evaluateClosedSourceExpression? d o n e s src with
  | none => throw (IO.userError "actual expression absent")
  | some (value,final) =>
    have eq := (evaluateClosedSourceExpression?_sound run).deterministic original
    check (reprStr value==reprStr v && reprStr final==reprStr s) "actual complete expression endpoint"
    return ⟨value,final,by rw [eq.1,eq.2]; exact original,eq.2⟩
private structure BodyTrace (o : Resolved.DeclarationId) (n : LocalNameTable)
    (e : Resolved.LocalScope RuntimeValue) (s : List RuntimeValue) (src : Syntax.Block) where
  value : RuntimeValue
  final : List RuntimeValue
  original : ClosedSourceBodyEvaluates o n e s src value final
  store_eq : final=s
private def observeBody {o n e s src v}
    (original : ClosedSourceBodyEvaluates o n e s src v s) : IO (BodyTrace o n e s src) := do
  proof original
  match run : evaluateClosedSourceBody? 2 o n e s src with
  | none => throw (IO.userError "actual saved body absent")
  | some (value,final) =>
    have eq := (evaluateClosedSourceBody?_sound run).deterministic original
    check (reprStr value==reprStr v && reprStr final==reprStr s) "actual complete body endpoint"
    return ⟨value,final,by rw [eq.1,eq.2]; exact original,eq.2⟩
private def adjacent {o n e s src v} (d : Nat)
    (original : ClosedSourceExpressionEvaluates o n e s src v s) : IO Unit := do
  proof original
  for budget in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? budget o n e s src with
    | none => check (budget<d) "closed adjacent exhaustion"
    | some (value,final) =>
      proof ((evaluateClosedSourceExpression?_sound run).deterministic original)
      check (budget≥d && reprStr value==reprStr v && reprStr final==reprStr s) "closed adjacent actual endpoint"

private def meaning (op : Syntax.BinaryOp) (l r : Core.Word) : IO {v : Core.Value // StrictWordBinaryDenotes op l r v} :=
  match op with
  | .add => pure ⟨.word (l.add r),.add⟩
  | .subtract => pure ⟨.word (l.sub r),.subtract⟩
  | .multiply => pure ⟨.word (l.mul r),.multiply⟩
  | .divide => pure ⟨.word (l.udiv r),.divide⟩
  | .modulo => pure ⟨.word (l.umod r),.modulo⟩
  | .bitAnd => pure ⟨.word (l.bitAnd r),.bitAnd⟩
  | .bitOr => pure ⟨.word (l.bitOr r),.bitOr⟩
  | .bitXor => pure ⟨.word (l.bitXor r),.bitXor⟩
  | .greater => pure ⟨.bool (decide (l>r)),.greater⟩
  | .less => pure ⟨.bool (decide (l<r)),.less⟩
  | .equal => pure ⟨.bool (l==r),.equal⟩
  | .notEqual => pure ⟨.bool (!(l==r)),.notEqual⟩
  | .lessEqual => pure ⟨.bool (!(decide (l>r))),.lessEqual⟩
  | .greaterEqual => pure ⟨.bool (!(decide (l<r))),.greaterEqual⟩
  | .logicalAnd | .logicalOr => throw (IO.userError "not a strict Word operator")

private def invoke (fs : Syntax.Expr) (made : RuntimeValue) (argument other : Core.Word)
    (s : List RuntimeValue) (src : Syntax.Expr)
    (createdEq : made=.sourceClosure fs savedOwner savedNames (savedRows fs)) :
    IO (Trace caller names (rows made argument other) s src) := do
  match lambda : fs, callShape : src with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred ⟨ps,"p"⟩⟩]⟩ none ⟨bs,[⟨rs,.returnStmt (some ⟨es,.identifier ⟨ns,"p"⟩⟩)⟩]⟩⟩,
      ⟨cs,.call ⟨fs0,.identifier ⟨fn,"picked"⟩⟩ ⟨args,[⟨as0,.identifier ⟨an,"p"⟩⟩]⟩⟩ =>
    let body : Syntax.Block := ⟨bs,[⟨rs,.returnStmt (some ⟨es,.identifier ⟨ns,"p"⟩⟩)⟩]⟩
    have shape : SourceUnaryLambdaShape fs ⟨ps,"p"⟩ body := by rw [lambda]; exact .inferred
    have fetchedOriginal : ClosedSourceExpressionEvaluates caller names (rows made argument other) s
        ⟨fs0,.identifier ⟨fn,"picked"⟩⟩ made s := .reference .head .head
    let fetched ← observe 1 fetchedOriginal
    match fetchedShape : fetched.value with
    | .sourceClosure actualSource actualOwner actualNames actualRows =>
      have fetchedEq := (fetched.original.deterministic fetchedOriginal).1
      have fields := RuntimeValue.sourceClosure.inj (show RuntimeValue.sourceClosure actualSource actualOwner actualNames actualRows =
          .sourceClosure fs savedOwner savedNames (savedRows fs) from by rw [← fetchedShape]; exact fetchedEq.trans createdEq)
      proof fields
      check (actualSource==fs && actualOwner==savedOwner && actualOwner != caller && actualNames==savedNames &&
        reprStr actualRows==reprStr (savedRows fs)) "all returned closure fields and foreign saved owner"
      have returnedShape : SourceUnaryLambdaShape actualSource ⟨ps,"p"⟩ body := by rw [fields.1]; exact shape
      have argumentOriginal : ClosedSourceExpressionEvaluates caller names (rows made argument other) fetched.final
          ⟨as0,.identifier ⟨an,"p"⟩⟩ (.word argument) fetched.final :=
        .reference (.tail (by change ("picked" : String) ≠ "p"; decide) .head) (.tail (by decide) .head)
      let actualArgument ← observe 1 argumentOriginal
      let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
      have bodyOriginal : ClosedSourceBodyEvaluates actualOwner (("p",fresh)::actualNames)
          ((fresh,actualArgument.value)::actualRows) actualArgument.final body actualArgument.value actualArgument.final :=
        .expression (.reference .head .head)
      let actualBody ← observeBody bodyOriginal
      check (fresh.owner==actualOwner && fresh==sid 3) "fresh saved parameter shadows old opaque p"
      have callOriginal : ClosedSourceExpressionEvaluates caller names (rows made argument other) s src actualBody.value actualBody.final := by
        rw [callShape]
        exact .call returnedShape (by rw [← fetchedShape]; exact fetched.original) actualArgument.original actualBody.original
      have finalEq := actualBody.store_eq.trans (actualArgument.store_eq.trans fetched.store_eq)
      have complete : ClosedSourceExpressionEvaluates caller names (rows made argument other) s src actualBody.value s := by
        simpa only [finalEq] using callOriginal
      adjacent 3 complete
      observe 3 complete
    | _ => throw (IO.userError "actual saved closure expected")
  | _,_ => throw (IO.userError "exact original identity lambda and unary saved call")

private def otherReference (made : RuntimeValue) (argument other : Core.Word)
    (s : List RuntimeValue) (src : Syntax.Expr) : IO (Trace caller names (rows made argument other) s src) := do
  match shape : src with
  | ⟨es,.identifier ⟨ns,"other"⟩⟩ =>
    have original : ClosedSourceExpressionEvaluates caller names (rows made argument other) s src (.word other) s := by
      rw [shape]
      exact .reference (.tail (by change ("picked" : String) ≠ "other"; decide)
        (.tail (by change ("p" : String) ≠ "other"; decide) .head)) (.tail (by decide) (.tail (by decide) .head))
    observe 1 original
  | _ => throw (IO.userError "original other reference")

private def exercise (symbol : String) (op : Syntax.BinaryOp) (onLeft : Bool)
    (argument other : Core.Word) (s : List RuntimeValue) : IO Unit := do
  let lf := file "strict-word-saved-lambda.sol" "lam(p){return p;}"
  let fs ← parsed lf (expectedLambda lf)
  let f := file "strict-word-saved-call.sol" (if onLeft then "picked(p) "++symbol++" other" else "other "++symbol++" picked(p)")
  let src ← parsed f (expectedBinary f onLeft symbol op)
  match lambda : fs with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred name⟩]⟩ none body⟩ =>
    have shape : SourceUnaryLambdaShape fs name body := by rw [lambda]; exact .inferred
    have creation : ClosedSourceExpressionEvaluates savedOwner savedNames (savedRows fs) s fs
        (.sourceClosure fs savedOwner savedNames (savedRows fs)) s := .creation shape
    adjacent 1 creation
    let made ← observe 1 creation
    have createdEq := (made.original.deterministic creation).1
    match outer : src with
    | ⟨span,.binary left ⟨operatorSpan,actualOp⟩ right⟩ =>
      if opEq : actualOp=op then
        let l ← if onLeft then invoke fs made.value argument other made.final left createdEq
          else otherReference made.value argument other made.final left
        let r ← if onLeft then otherReference made.value argument other l.final right
          else invoke fs made.value argument other l.final right createdEq
        match lv : l.value, rv : r.value with
        | .word lw,.word rw =>
          let m ← meaning actualOp lw rw
          have leftOriginal : ClosedSourceExpressionEvaluates caller names (rows made.value argument other) made.final left (.word lw) l.final := by
            rw [← lv]; exact l.original
          have rightOriginal : ClosedSourceExpressionEvaluates caller names (rows made.value argument other) l.final right (.word rw) r.final := by
            rw [← rv]; exact r.original
          have original : ClosedSourceExpressionEvaluates caller names (rows made.value argument other) made.final src (RuntimeValue.ofCore m.val) r.final := by
            rw [outer]; exact .strictWordBinary leftOriginal rightOriginal m.property
          proof original
          have decomposition := closedSourceExpressionEvaluates_strictWordBinary_iff
            (value:=RuntimeValue.ofCore m.val) (span:=span) (operatorSpan:=operatorSpan)
            m.property.operator_is_strict.1 m.property.operator_is_strict.2
          proof (decomposition.mp (by simpa only [outer] using original))
          proof (decomposition.mpr ⟨lw,rw,m.val,l.final,rfl,leftOriginal,rightOriginal,m.property⟩)
          have finalEq := r.store_eq.trans l.store_eq
          adjacent 4 (show ClosedSourceExpressionEvaluates caller names (rows made.value argument other) made.final src (RuntimeValue.ofCore m.val) made.final from by
            simpa only [finalEq] using original)
          check (lw==(if onLeft then argument else other) && rw==(if onLeft then other else argument)) "actual operand order"
        | _,_ => throw (IO.userError "strict operands must be actual Words")
      else throw (IO.userError "original operator differs from explicit spelling")
    | _ => throw (IO.userError "original binary AST")
  | _ => throw (IO.userError "original unary lambda AST")
end Tests.ParsedClosedStrictWordSavedCalls
open Tests.ParsedClosedStrictWordSavedCalls in
def Tests.frontendParsedClosedStrictWordSavedCallsTests : IO Unit := do
  let operations : List (String × Solcore.Syntax.BinaryOp) :=
    [("+",.add),("-",.subtract),("*",.multiply),("/",.divide),("%",.modulo),("&",.bitAnd),("|",.bitOr),
     ("^",.bitXor),(">",.greater),("<",.less),("==",.equal),("!=",.notEqual),("<=",.lessEqual),(">=",.greaterEqual)]
  for (symbol,op) in operations do
    for onLeft in [false,true] do
      exercise symbol op onLeft Solcore.Core.Word.maximum (Solcore.Core.Word.ofNatModulo 1) []
      exercise symbol op onLeft Solcore.Core.Word.zero (Solcore.Core.Word.ofNatModulo 7)
        [old,.hostFunction .storageWrite,.cellRef .word 900,.unit]

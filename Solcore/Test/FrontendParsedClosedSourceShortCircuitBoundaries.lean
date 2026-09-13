import Solcore.Frontend.ClosedSourceShortCircuitProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Syntax.Parser.Term

/- Original AST witnesses precede every run. Actual full
values/stores are retained through creation, selection and a foreign saved call.
No typing, data-image, Core-cost, NoDup or parser-correctness theorem is claimed. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedClosedSourceShortCircuitBoundaries
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ShortCircuit",by decide⟩],by decide⟩⟩,298⟩
private def caller := {owner with declarationIndex := 901}
private def lid (own : Resolved.DeclarationId) (i : Nat) : Resolved.LocalId := ⟨own,i⟩
private def names (own : Resolved.DeclarationId) : LocalNameTable :=
  [("flag",lid own 0),("right",lid own 1),("saved",lid own 1),("p",lid own 2)]
private def rows (own : Resolved.DeclarationId) (b : Bool) (p : V)
    (tail : Resolved.LocalScope V) := (lid own 0,RuntimeValue.bool b)::(lid own 1,p)::(lid own 2,RuntimeValue.unit)::tail
private theorem index_ne (own : Resolved.DeclarationId) {i j : Nat} (h : i≠j) : lid own i≠lid own j :=
  fun equal => h (congrArg Resolved.LocalId.binderIndex equal)
private def span (f : Syntax.SourceFile) (a z : Nat) : Syntax.SourceSpan := ⟨f.id,a,z⟩
private def ref (f : Syntax.SourceFile) (a z : Nat) (n : String) : Syntax.Expr :=
  ⟨span f a z,.identifier ⟨span f a z,n⟩⟩
private def binaryAST (b : Bool) (right : String) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 (8+right.utf8ByteSize),.binary (ref f 0 4 "flag")
    ⟨span f 5 7,if b then .logicalAnd else .logicalOr⟩ (ref f 8 (8+right.utf8ByteSize) right)⟩
private def factoryAST (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 19,.group ⟨span f 1 18,.lambda (span f 1 4)
    ⟨span f 4 7,[⟨span f 5 6,.inferred ⟨span f 5 6,"p"⟩⟩]⟩ none
    ⟨span f 7 18,[⟨span f 8 17,.returnStmt (some (ref f 15 16 "p"))⟩]⟩⟩⟩
private def callAST (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 9,.call (ref f 0 6 "picked") ⟨span f 6 9,[ref f 7 8 "p"]⟩⟩
private def parsed (text : String) (expected : Syntax.SourceFile → Syntax.Expr) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"short-circuit-"++text++".sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      src.span==Syntax.SourceSpan.fullFile file && src==expected file) "complete original AST/ranges/source/EOF"
    return src
  | _ => throw (IO.userError "parser")
private theorem endpoint {own ns es st src v} (h : E own ns es st src v st) :
    ∀ a s, E own ns es st src a s ↔ a=v ∧ s=st := by
  intro a s; exact ⟨fun other => other.deterministic h,by rintro ⟨rfl,rfl⟩; exact h⟩
private structure Cert (own : Resolved.DeclarationId) (ns : LocalNameTable)
    (es : Resolved.LocalScope V) (st : List V) (src : Syntax.Expr) (v : V) where
  depth : Nat
  original : E own ns es st src v st
  image : ∀ a s, E own ns es st src a s ↔ a=v ∧ s=st
private def certified {own ns es st src v} (d : Nat) (h : E own ns es st src v st) : Cert own ns es st src v :=
  ⟨d,h,endpoint h⟩
private structure Actual (own : Resolved.DeclarationId) (ns : LocalNameTable)
    (es : Resolved.LocalScope V) (st : List V) (src : Syntax.Expr) (v : V) where
  value : V
  store : List V
  evidence : E own ns es st src value store
  endpoint : value=v ∧ store=st
private def run {own ns es st src v} (h : Cert own ns es st src v) : IO (Actual own ns es st src v) := do
  proof h.original
  for budget in [0,h.depth-1,h.depth,h.depth+3] do
    match result : evaluateClosedSourceExpression? budget own ns es st src with
    | none => check (budget<h.depth) "expected positive depth"
    | some (a,s) =>
      have same := (h.image a s).mp (evaluateClosedSourceExpression?_sound result)
      proof same; proof ((h.image a s).mpr same); proof ((h.image v st).mpr ⟨rfl,rfl⟩)
      check (budget≥h.depth) "adjacent lower depth"
  match result : evaluateClosedSourceExpression? h.depth own ns es st src with
  | none => throw (IO.userError "actual certified endpoint")
  | some (a,s) => return ⟨a,s,evaluateClosedSourceExpression?_sound result,
      (h.image a s).mp (evaluateClosedSourceExpression?_sound result)⟩
private def reject {own ns es st src} (absent : ∀ a s, ¬ E own ns es st src a s) : IO Unit := do
  proof absent
  for budget in [0,1,2,3,8] do
    match result : evaluateClosedSourceExpression? budget own ns es st src with
    | none => pure ()
    | some (a,s) => False.elim (absent a s (evaluateClosedSourceExpression?_sound result))
private def selected (b : Bool) (p : V) (tail : Resolved.LocalScope V) (st : List V)
    (src : Syntax.Expr) : IO (Cert owner (names owner) (rows owner b p tail) st src p) := do
  match shape : src with
  | ⟨_,.binary ⟨ls,.identifier ⟨ln,"flag"⟩⟩ ⟨_,op⟩ ⟨rs,.identifier n⟩⟩ =>
    if admitted : n.value="right" ∨ n.value="saved" then
      have l : E owner (names owner) (rows owner b p tail) st
          ⟨ls,.identifier ⟨ln,"flag"⟩⟩ (.bool b) st := .reference .head .head
      have r : E owner (names owner) (rows owner b p tail) st ⟨rs,.identifier n⟩ p st :=
        .reference (LocalNameTable.lookup?_iff.mp (by rcases admitted with h|h <;> rw [h] <;> rfl))
          (.tail (index_ne owner (by decide)) .head)
      match operator : op, choice : b with
      | .logicalAnd,true =>
        have h : E owner (names owner) (rows owner b p tail) st src p st := by
          rw [shape,operator]; exact .andTrue (by simpa only [choice] using l) r
        return ⟨2,h,by
          intro a s; rw [shape,operator]; constructor
          · intro e; exact (closedSourceExpressionEvaluates_logicalAnd_iff.mpr
              (closedSourceExpressionEvaluates_logicalAnd_iff.mp e)).deterministic (by simpa only [shape,operator] using h)
          · rintro ⟨rfl,rfl⟩; exact closedSourceExpressionEvaluates_logicalAnd_iff.mpr
              (.inr ⟨_,by simpa only [choice] using l,r⟩)⟩
      | .logicalOr,false =>
        have h : E owner (names owner) (rows owner b p tail) st src p st := by
          rw [shape,operator]; exact .orFalse (by simpa only [choice] using l) r
        return ⟨2,h,by
          intro a s; rw [shape,operator]; constructor
          · intro e; exact (closedSourceExpressionEvaluates_logicalOr_iff.mpr
              (closedSourceExpressionEvaluates_logicalOr_iff.mp e)).deterministic (by simpa only [shape,operator] using h)
          · rintro ⟨rfl,rfl⟩; exact closedSourceExpressionEvaluates_logicalOr_iff.mpr
              (.inr ⟨_,by simpa only [choice] using l,r⟩)⟩
      | _,_ => throw (IO.userError "selected guard/operator")
    else throw (IO.userError "selected original name")
  | _ => throw (IO.userError "selected original binary")
private def missing (b : Bool) (p : V) (tail : Resolved.LocalScope V) (st : List V)
    (src : Syntax.Expr) : IO Unit := do
  match shape : src with
  | ⟨_,.binary ⟨ls,.identifier ⟨ln,"flag"⟩⟩ ⟨_,op⟩ ⟨rs,.identifier ⟨rn,"missing"⟩⟩⟩ =>
    have l : E owner (names owner) (rows owner b p tail) st
        ⟨ls,.identifier ⟨ln,"flag"⟩⟩ (.bool b) st := .reference .head .head
    have absent (s a final) : ¬ E owner (names owner) (rows owner b p tail) s
        ⟨rs,.identifier ⟨rn,"missing"⟩⟩ a final := by
      intro e; cases e with
      | creation impossible => cases impossible
      | reference named _ => have h := LocalNameTable.lookup?_iff.mpr named; simp [names,LocalNameTable.lookup?] at h
    proof absent
    match operator : op, choice : b with
    | .logicalAnd,false =>
      let _ ← run (certified 2 (show E owner (names owner) (rows owner b p tail) st src (.bool b) st by
        rw [shape,operator,choice]; exact .andFalse (by simpa only [choice] using l)))
      pure ()
    | .logicalOr,true =>
      let _ ← run (certified 2 (show E owner (names owner) (rows owner b p tail) st src (.bool b) st by
        rw [shape,operator,choice]; exact .orTrue (by simpa only [choice] using l)))
      pure ()
    | .logicalAnd,true => reject (own:=owner) (ns:=names owner) (es:=rows owner b p tail) (st:=st) (src:=src) (by
        intro a final e; rw [shape,operator] at e
        rcases closedSourceExpressionEvaluates_logicalAnd_iff.mp e with ⟨_,bad⟩|⟨s,_,right⟩
        · have clash := (l.deterministic bad).1; simp only [choice] at clash; cases clash
        · exact absent s a final right)
    | .logicalOr,false => reject (own:=owner) (ns:=names owner) (es:=rows owner b p tail) (st:=st) (src:=src) (by
        intro a final e; rw [shape,operator] at e
        rcases closedSourceExpressionEvaluates_logicalOr_iff.mp e with ⟨_,bad⟩|⟨s,_,right⟩
        · have clash := (l.deterministic bad).1; simp only [choice] at clash; cases clash
        · exact absent s a final right)
    | _,_ => throw (IO.userError "missing short-circuit operator")
  | _ => throw (IO.userError "missing original binary")
private structure Factory (src : Syntax.Expr) where
  inner : Syntax.Expr
  parameter : Syntax.Identifier
  body : Syntax.Block
  shape : SourceUnaryLambdaShape inner parameter body
  witness : ∀ own ns es id a st, B own ((parameter.value,id)::ns) ((id,a)::es) st body a st
  creation : ∀ ns es st, E owner ns es st src (.sourceClosure inner owner ns es) st
private def factory (src : Syntax.Expr) : IO (Factory src) := do
  match whole : src with
  | ⟨_,.group inner⟩ => match form : inner with
    | ⟨_,.lambda _ ⟨_,[⟨_,.inferred parameter⟩]⟩ none body⟩ => match returned : body with
      | ⟨_,[⟨_,.returnStmt (some ⟨_,.identifier n⟩)⟩]⟩ =>
        if same : n.value=parameter.value then
          have sh : SourceUnaryLambdaShape inner parameter body := by rw [form]; exact .inferred
          return ⟨inner,parameter,body,sh,by
            intro own ns es id a st; rw [returned]; exact .expression (.reference (by rw [same]; exact .head) .head),by
            intro ns es st; rw [whole]; exact .group (.creation sh)⟩
        else throw (IO.userError "parameter return shadow")
      | _ => throw (IO.userError "original return")
    | _ => throw (IO.userError "original lambda")
  | _ => throw (IO.userError "original grouped creation")
private def savedCall {src} (f : Factory src) (sn : LocalNameTable) (sc : Resolved.LocalScope V)
    (made : V) (same : made=.sourceClosure f.inner owner sn sc) (arg : V)
    (tail : Resolved.LocalScope V) (st : List V) (call : Syntax.Expr) : IO Unit := do
  let ns : LocalNameTable := [("picked",lid caller 0),("p",lid caller 1),("p",lid owner 2)]
  let es := (lid caller 0,made)::(lid caller 1,arg)::tail
  proof (show caller≠owner by decide)
  match form : call with
  | ⟨_,.call ⟨fs,.identifier ⟨fn,"picked"⟩⟩ ⟨_,[⟨argSpan,.identifier ⟨an,"p"⟩⟩]⟩⟩ =>
    let callee : Syntax.Expr := ⟨fs,.identifier ⟨fn,"picked"⟩⟩
    let argument : Syntax.Expr := ⟨argSpan,.identifier ⟨an,"p"⟩⟩
    have fetched (s) : E caller ns es s callee made s := .reference .head .head
    have argumentOld (s) : E caller ns es s argument arg s :=
      .reference (.tail (by change "picked"≠"p"; decide) .head) (.tail (index_ne caller (by decide)) .head)
    have old : E caller ns es st call arg st := by
      rw [form]; exact .call f.shape (by rw [← same]; exact fetched st) (argumentOld st)
        (f.witness owner sn sc (Resolved.freshLocalId owner (sn.map Prod.snd)) arg st)
    proof old
    let fetchedActual ← run (certified 1 (fetched st))
    let argumentActual ← run (certified 1 (argumentOld fetchedActual.store))
    have fullClosure := fetchedActual.endpoint.1.trans same
    match actualShape : fetchedActual.value with
    | .sourceClosure savedSource savedOwner actualNames actualRows =>
      match selectedShape : sourceUnaryLambdaShape? savedSource with
      | none => throw (IO.userError "actual saved source shape")
      | some (parameter,body) =>
        let id := Resolved.freshLocalId savedOwner (actualNames.map Prod.snd)
        let bodyNames := (parameter.value,id)::actualNames
        let bodyRows := (id,argumentActual.value)::actualRows
        have bodyOld : B savedOwner bodyNames bodyRows argumentActual.store body argumentActual.value argumentActual.store := by
          have fields : RuntimeValue.sourceClosure savedSource savedOwner actualNames actualRows=.sourceClosure f.inner owner sn sc :=
            by simpa only [actualShape] using fullClosure
          obtain ⟨rfl,rfl,rfl,rfl⟩ := RuntimeValue.sourceClosure.inj fields
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj
            (selectedShape.symm.trans (sourceUnaryLambdaShape?_iff.mpr f.shape)))
          exact f.witness _ _ _ _ _ _
        have image (v s) : B savedOwner bodyNames bodyRows argumentActual.store body v s ↔
            v=argumentActual.value ∧ s=argumentActual.store :=
          ⟨fun other => other.deterministic bodyOld,by rintro ⟨rfl,rfl⟩; exact bodyOld⟩
        proof bodyOld
        for budget in [0,1,2,5] do
          match result : evaluateClosedSourceBody? budget savedOwner bodyNames bodyRows argumentActual.store body with
          | none => check (budget<2) "actual saved body depth2"
          | some (v,s) =>
            have endpoint := (image v s).mp (evaluateClosedSourceBody?_sound result)
            proof endpoint; proof ((image v s).mpr endpoint); proof ((image argumentActual.value argumentActual.store).mpr ⟨rfl,rfl⟩)
            proof (endpoint.1.trans argumentActual.endpoint.1)
            proof (endpoint.2.trans (argumentActual.endpoint.2.trans fetchedActual.endpoint.2))
            have actualCall : E caller ns es st call v s := by
              rw [form]
              exact .call (sourceUnaryLambdaShape?_iff.mp selectedShape)
                (by simpa only [actualShape] using fetchedActual.evidence)
                argumentActual.evidence (evaluateClosedSourceBody?_sound result)
            proof (actualCall.deterministic old)
            proof ((Tests.ParsedClosedSourceShortCircuitBoundaries.endpoint old v s).mpr (actualCall.deterministic old))
            check (budget≥2) "saved body adjacent depth"
    | _ => throw (IO.userError "actual saved closure")
    let _ ← run (certified 3 old)
    pure ()
  | _ => throw (IO.userError "original saved call")
private def exercise (creation : Syntax.Expr) (f : Factory creation) (b : Bool) (p : V)
    (tail : Resolved.LocalScope V) (st : List V) : IO Unit := do
  let text := if b then "flag && " else "flag || "
  let raw ← parsed (text++"right") (binaryAST b "right")
  let _ ← run (← selected b p tail st raw)
  for op in [false,true] do
    let missingSource ← parsed ((if op then "flag && " else "flag || ")++"missing") (binaryAST op "missing")
    missing b p tail st missingSource
  let sn := names owner
  let sc := rows owner b p tail
  let created ← run (certified 2 (f.creation sn sc st))
  let selectSource ← parsed (text++"saved") (binaryAST b "saved")
  let selectedActual ← run (← selected b created.value tail created.store selectSource)
  proof (selectedActual.endpoint.2.trans created.endpoint.2)
  let call ← parsed "picked(p)" callAST
  savedCall f sn sc selectedActual.value (selectedActual.endpoint.1.trans created.endpoint.1)
    p tail selectedActual.store call
end Tests.ParsedClosedSourceShortCircuitBoundaries
open Tests.ParsedClosedSourceShortCircuitBoundaries in
def Tests.frontendParsedClosedSourceShortCircuitBoundaryTests : IO Unit := do
  let creation ← parsed "(lam(p){return p;})" factoryAST
  let f ← factory creation
  let opaquePayload := Solcore.Frontend.RuntimeValue.ofCore
    (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let saved := Solcore.Frontend.RuntimeValue.sourceClosure f.inner caller [("p",lid caller 0)] [(lid caller 0,opaquePayload)]
  for p in [Solcore.Frontend.RuntimeValue.unit,.bool false,.bool true,
      .word Solcore.Core.Word.zero,.word Solcore.Core.Word.maximum,.pair saved opaquePayload,opaquePayload,
      .hostFunction .storageWrite,.cellRef .word 700,saved,.inLeft .word saved,
      .inRight .unit opaquePayload,.constructed ⟨⟨4⟩,7⟩ saved] do
    for b in [false,true] do
      for tail in [[],[(lid owner 0,.bool (!b)),(lid owner 2,saved),(lid caller 1,opaquePayload),(lid caller 1,p)]] do
        for st in [[],[p,saved,opaquePayload,.hostFunction .storageWrite,.cellRef .word 900]] do
          exercise creation f b p tail st

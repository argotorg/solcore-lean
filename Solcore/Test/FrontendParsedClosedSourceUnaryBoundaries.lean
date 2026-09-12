import Solcore.Frontend.ClosedSourceUnaryProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Syntax.Parser.Term

/- Original operand certificates distinguish shape and lookup fixtures before closed runs. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceUnaryBoundaries
open Solcore Solcore.Frontend

private def check (b : Bool) (message : String) : IO Unit := unless b do throw (IO.userError message)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"UnaryParsed", by decide⟩], by decide⟩⟩, 296⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex := 901}
private def fid (n : Nat) : Resolved.LocalId := ⟨foreign, n⟩
private def opaqueCore : RuntimeValue := RuntimeValue.ofCore
  (.closure .unit .word (.var 99) [.hostFunction .storageWrite, .cellRef .word 700])
private def names : LocalNameTable :=
  [("flag",sid 7),("word",sid 31),("unit",sid 8),("pair",sid 9),
    ("core",sid 10),("src",sid 11),("lost",sid 17),("flag",fid 700)]
private def rows (p : RuntimeValue) (b : Bool) (w : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(sid 99,p),(sid 31,.word w),(sid 7,.bool b),(sid 8,.unit),
    (sid 9,.pair .unit (.word w)),(sid 10,opaqueCore),(sid 11,p),
    (sid 7,.bool (!b)),(fid 700,.word Core.Word.maximum)]
private def stores (p : RuntimeValue) (w : Core.Word) : List (List RuntimeValue) :=
  [[p,opaqueCore,.hostFunction .storageWrite,.cellRef (.function .word .word) 900,
    .pair (.word w) .unit],[opaqueCore,p]]

private def parsed (text : String) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main,"unary-" ++ text ++ ".sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "unary lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span == Syntax.SourceSpan.fullFile file) "complete original source and EOF"
    return (file,src)
  | _ => throw (IO.userError "unary original parser")

private def Rejected (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (src : Syntax.Expr) : Prop :=
  ∀ actual final, ¬ ClosedSourceExpressionEvaluates owner names captured store src actual final

private inductive Outcome (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (src : Syntax.Expr) where
  | success (value : RuntimeValue) (depth : Nat)
      (original : ClosedSourceExpressionEvaluates owner names captured store src value store)
      (image : ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store src actual final ↔
        actual = value ∧ final = store)
  | failure (kind operandDepth : Nat) (rejected : Rejected captured store src)

private def primitive? : Syntax.UnaryOp → RuntimeValue → Option RuntimeValue
  | .logicalNot,.bool b => some (.bool (!b))
  | .bitNot,.word w => some (.word w.bitNot)
  | _,_ => none

private theorem endpoint_image {captured store src value}
    (original : ClosedSourceExpressionEvaluates owner names captured store src value store) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store src actual final ↔
      actual = value ∧ final = store := by
  intro actual final
  constructor
  · exact fun evaluated => evaluated.deterministic original
  · rintro ⟨rfl,rfl⟩; exact original

private theorem primitive_original {captured store operand value result}
    (span operatorSpan : Syntax.SourceSpan) (op : Syntax.UnaryOp)
    (child : ClosedSourceExpressionEvaluates owner names captured store operand value store)
    (applied : primitive? op value = some result) :
    ClosedSourceExpressionEvaluates owner names captured store
      ⟨span,.unary ⟨operatorSpan,op⟩ operand⟩ result store := by
  cases op with
  | logicalNot =>
      cases value <;> simp only [primitive?, reduceCtorEq] at applied
      cases Option.some.inj applied
      exact .logicalNot child
  | bitNot =>
      cases value <;> simp only [primitive?, reduceCtorEq] at applied
      cases Option.some.inj applied
      exact .bitNot child

private theorem primitive_image {captured store operand value result}
    (span operatorSpan : Syntax.SourceSpan) (op : Syntax.UnaryOp)
    (child : ClosedSourceExpressionEvaluates owner names captured store operand value store)
    (applied : primitive? op value = some result) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store
      ⟨span,.unary ⟨operatorSpan,op⟩ operand⟩ actual final ↔ actual = result ∧ final = store := by
  cases op with
  | logicalNot =>
      cases value <;> simp only [primitive?, reduceCtorEq] at applied
      cases Option.some.inj applied
      intro actual final
      constructor
      · intro evaluated
        obtain ⟨b,ev,same⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp evaluated
        obtain ⟨sameChild,sameStore⟩ := ev.deterministic child
        cases RuntimeValue.bool.inj sameChild
        exact ⟨same,sameStore⟩
      · rintro ⟨rfl,rfl⟩
        exact closedSourceExpressionEvaluates_logicalNot_iff.mpr ⟨_,child,rfl⟩
  | bitNot =>
      cases value <;> simp only [primitive?, reduceCtorEq] at applied
      cases Option.some.inj applied
      intro actual final
      constructor
      · intro evaluated
        obtain ⟨w,ev,same⟩ := closedSourceExpressionEvaluates_bitNot_iff.mp evaluated
        obtain ⟨sameChild,sameStore⟩ := ev.deterministic child
        cases RuntimeValue.word.inj sameChild
        exact ⟨same,sameStore⟩
      · rintro ⟨rfl,rfl⟩
        exact closedSourceExpressionEvaluates_bitNot_iff.mpr ⟨_,child,rfl⟩

private theorem primitive_rejected {captured store operand value}
    (span operatorSpan : Syntax.SourceSpan) (op : Syntax.UnaryOp)
    (child : ClosedSourceExpressionEvaluates owner names captured store operand value store)
    (applied : primitive? op value = none) :
    Rejected captured store ⟨span,.unary ⟨operatorSpan,op⟩ operand⟩ := by
  intro actual final evaluated
  cases op with
  | logicalNot =>
      obtain ⟨b,ev,_⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp evaluated
      rw [← (ev.deterministic child).1] at applied
      cases applied
  | bitNot =>
      obtain ⟨w,ev,_⟩ := closedSourceExpressionEvaluates_bitNot_iff.mp evaluated
      rw [← (ev.deterministic child).1] at applied
      cases applied

private theorem child_rejected {captured store operand}
    (span operatorSpan : Syntax.SourceSpan) (op : Syntax.UnaryOp)
    (rejected : Rejected captured store operand) :
    Rejected captured store ⟨span,.unary ⟨operatorSpan,op⟩ operand⟩ := by
  intro actual final evaluated
  cases op with
  | logicalNot =>
      obtain ⟨b,ev,_⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp evaluated
      exact rejected _ _ ev
  | bitNot =>
      obtain ⟨w,ev,_⟩ := closedSourceExpressionEvaluates_bitNot_iff.mp evaluated
      exact rejected _ _ ev

private def certificate (file : Syntax.SourceFile) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (src : Syntax.Expr) : IO (Outcome captured store src) := do
  check (src.span.isValidFor file) "original expression range"
  match shape : src with
  | ⟨span,.identifier name⟩ =>
      check (span == name.span && name.span.isValidFor file) "original identifier range"
      match named : names.lookup? name.value with
      | none =>
          return .failure 0 0 (by
            intro actual final evaluated
            rw [shape] at evaluated
            cases evaluated with
            | creation impossible => cases impossible
            | reference otherNamed _ =>
                have present := LocalNameTable.lookup?_iff.mpr otherNamed
                rw [named] at present
                cases present)
      | some id => match found : captured.lookup? id with
        | none =>
            return .failure 1 0 (by
              intro actual final evaluated
              rw [shape] at evaluated
              cases evaluated with
              | creation impossible => cases impossible
              | reference otherNamed otherFound =>
                  cases (LocalNameTable.lookup?_iff.mp named).id_unique otherNamed
                  have present := Resolved.LocalScope.lookup?_iff.mpr otherFound
                  rw [found] at present
                  cases present)
        | some value =>
            have original : ClosedSourceExpressionEvaluates owner names captured store src value store := by
              rw [shape]
              exact .reference (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)
            proof original
            return .success value 1 original (endpoint_image original)
  | ⟨span,.unary op operand⟩ =>
      check (op.span.isValidFor file && span.contains operand.span && span.contains op.span &&
        op.span.length == 1 && op.span.endByte == operand.span.startByte &&
        span == Syntax.SourceSpan.cover op.span operand.span) "original unary ranges"
      check (file.content.toByteArray.data[op.span.startByte]? ==
        some (match op.value with | .logicalNot => 33 | .bitNot => 126)) "original operator byte"
      let h ← certificate file captured store operand
      match h with
      | .failure kind depth rejected =>
          return .failure kind depth (by
            rw [shape]
            exact child_rejected span op.span op.value rejected)
      | .success value depth child _ =>
          proof child
          match applied : primitive? op.value value with
          | none =>
              return .failure 2 depth (by
                rw [shape]
                exact primitive_rejected span op.span op.value child applied)
          | some result =>
              have original : ClosedSourceExpressionEvaluates owner names captured store src result store := by
                rw [shape]; exact primitive_original span op.span op.value child applied
              proof original
              match op.value with
              | .logicalNot => proof (evaluateClosedSourceExpression?_logicalNot depth owner names captured store span op.span operand)
              | .bitNot => proof (evaluateClosedSourceExpression?_bitNot depth owner names captured store span op.span operand)
              return .success result (depth+1) original (by
                rw [shape]; exact primitive_image span op.span op.value child applied)
  | _ => throw (IO.userError "unexpected boundary source shape")
termination_by sizeOf src

private def runRejected (text : String) (kind depth : Nat) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) : IO Unit := do
  let (file,src) ← parsed text
  let .failure actualKind actualDepth absent ← certificate file captured store src |
    throw (IO.userError "expected independently rejected original source")
  check (actualKind == kind && actualDepth == depth) "independent rejection fixture and operand depth"
  proof absent
  for budget in [0,1,2,3,8] do
    match result : evaluateClosedSourceExpression? budget owner names captured store src with
    | none => pure ()
    | some (actual,final) =>
        proof (absent actual final (evaluateClosedSourceExpression?_sound result))
        throw (IO.userError "relationally rejected original source completed")

private def runPositive (text : String) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (expected : Core.Value) : IO Unit := do
  let (file,src) ← parsed text
  let .success value depth original image ← certificate file captured store src |
    throw (IO.userError "expected original positive unary control")
  proof original
  check (depth == 2) "positive unary depth"
  match value,expected with
  | .bool a,.bool b => check (a == b) "positive original Bool"
  | .word a,.word b => check (a == b) "positive original Word"
  | _,_ => throw (IO.userError "positive primitive shape")
  for budget in [0,2] do
    match result : evaluateClosedSourceExpression? budget owner names captured store src with
    | none => check (budget == 0) "positive unary success2"
    | some (actual,final) =>
        check (budget == 2) "positive unary zero boundary"
        have exactImage := (image actual final).mp (evaluateClosedSourceExpression?_sound result)
        proof exactImage
        proof ((image actual final).mpr exactImage)
        proof ((image value store).mpr ⟨rfl,rfl⟩)

end Tests.ParsedClosedSourceUnaryBoundaries
open Tests.ParsedClosedSourceUnaryBoundaries in
def Tests.frontendParsedClosedSourceUnaryBoundaryTests : IO Unit := do
  let (_,inert) ← parsed "lam(){return absent;}"
  let p := Solcore.Frontend.RuntimeValue.sourceClosure inert foreign
    [("unused",fid 700)] [(fid 700,.bool true)]
  for b in [false,true] do
    for w in [Solcore.Core.Word.zero,Solcore.Core.Word.maximum,Solcore.Core.Word.ofNatModulo 17] do
      for store in stores p w do
        let captured := rows p b w
        for text in ["!word","~flag","!unit","~unit","!pair","~pair","!core","~core","!src","~src"] do
          runRejected text 2 1 captured store
        for text in ["!~word","~!flag"] do runRejected text 2 2 captured store
        for text in ["!missing","~missing"] do runRejected text 0 0 captured store
        for text in ["!lost","~lost"] do runRejected text 1 0 captured store
        runPositive "!flag" captured store (.bool (!b))
        runPositive "~word" captured store (.word w.bitNot)

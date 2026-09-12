import Solcore.Frontend.ClosedSourceUnaryProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.WordLiteralProperties
import Solcore.Core.UnaryPrimitives
import Solcore.Syntax.Parser.Term

/- Independent original certificates precede depth runs and full actual image checks. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceUnary
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

private structure Certificate (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (src : Syntax.Expr) where
  value : RuntimeValue
  depth : Nat
  original : ClosedSourceExpressionEvaluates owner names captured store src value store
  image : ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store src actual final ↔
    actual = value ∧ final = store

private theorem endpoint_image {captured store src value}
    (original : ClosedSourceExpressionEvaluates owner names captured store src value store) :
    ∀ actual final, ClosedSourceExpressionEvaluates owner names captured store src actual final ↔
      actual = value ∧ final = store := by
  intro actual final
  constructor
  · exact fun evaluated => evaluated.deterministic original
  · rintro ⟨rfl,rfl⟩; exact original

private def certificate (file : Syntax.SourceFile) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (src : Syntax.Expr) : IO (Certificate captured store src) := do
  check (src.span.isValidFor file) "original source-owned expression span"
  match shape : src with
  | ⟨span,.identifier name⟩ =>
    check (span == name.span && name.span.isValidFor file) "original reference span"
    match named : names.lookup? name.value with
    | none => throw (IO.userError "independent name")
    | some id => match found : captured.lookup? id with
      | none => throw (IO.userError "independent capture")
      | some value =>
        have original : ClosedSourceExpressionEvaluates owner names captured store src value store := by
          rw [shape]
          exact .reference (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)
        return ⟨value,1,original,endpoint_image original⟩
  | ⟨span,.literal literal⟩ =>
    check (span == literal.span && literal.span.isValidFor file) "original numeric literal span"
    match meaning : interpretWordLiteral? literal with
    | none => throw (IO.userError "independent literal meaning")
    | some value =>
      have original : ClosedSourceExpressionEvaluates owner names captured store src (.word value) store := by
        rw [shape]; exact .wordLiteral (interpretWordLiteral?_sound meaning)
      return ⟨.word value,1,original,endpoint_image original⟩
  | ⟨span,.group child⟩ =>
    check (span.contains child.span && span.startByte+1 == child.span.startByte &&
      child.span.endByte+1 == span.endByte &&
      file.content.toByteArray.data[span.startByte]? == some 40 &&
      file.content.toByteArray.data[span.endByte-1]? == some 41) "original group parentheses"
    let h ← certificate file captured store child
    have original : ClosedSourceExpressionEvaluates owner names captured store src h.value store := by
      rw [shape]; exact .group h.original
    return ⟨h.value,h.depth+1,original,by
      intro actual final
      constructor
      · intro evaluated; rw [shape] at evaluated
        cases evaluated with
        | creation impossible => cases impossible
        | group child => exact (h.image _ _).mp child
      · rintro ⟨rfl,rfl⟩; exact original⟩
  | ⟨span,.unary op operand⟩ =>
    check (op.span.isValidFor file && span.contains operand.span && span.contains op.span &&
      op.span.length == 1 && op.span.endByte == operand.span.startByte &&
      span == Syntax.SourceSpan.cover op.span operand.span) "original unary operator/operand ranges"
    let h ← certificate file captured store operand
    match operator : op.value, value : h.value with
    | .logicalNot,.bool b =>
      check (file.content.toByteArray.data[op.span.startByte]? == some 33) "original logical-not byte"
      have child : ClosedSourceExpressionEvaluates owner names captured store operand (.bool b) store :=
        value ▸ h.original
      have original : ClosedSourceExpressionEvaluates owner names captured store src (.bool (!b)) store := by
        rw [shape]; cases op; simp only at operator; cases operator; exact .logicalNot child
      proof original
      proof (evaluateClosedSourceExpression?_logicalNot h.depth owner names captured store span op.span operand)
      return ⟨.bool (!b),h.depth+1,original,by
        intro actual final
        rw [shape]; cases op; simp only at operator; cases operator
        constructor
        · intro evaluated
          obtain ⟨v,ev,same⟩ := closedSourceExpressionEvaluates_logicalNot_iff.mp evaluated
          obtain ⟨sameChild,rfl⟩ := (h.image _ _).mp ev
          rw [value] at sameChild
          cases RuntimeValue.bool.inj sameChild
          exact ⟨same,rfl⟩
        · rintro ⟨rfl,rfl⟩
          exact closedSourceExpressionEvaluates_logicalNot_iff.mpr ⟨b,child,rfl⟩⟩
    | .bitNot,.word w =>
      check (file.content.toByteArray.data[op.span.startByte]? == some 126) "original bit-not byte"
      have child : ClosedSourceExpressionEvaluates owner names captured store operand (.word w) store :=
        value ▸ h.original
      have original : ClosedSourceExpressionEvaluates owner names captured store src (.word w.bitNot) store := by
        rw [shape]; cases op; simp only at operator; cases operator; exact .bitNot child
      proof original
      proof (evaluateClosedSourceExpression?_bitNot h.depth owner names captured store span op.span operand)
      return ⟨.word w.bitNot,h.depth+1,original,by
        intro actual final
        rw [shape]; cases op; simp only at operator; cases operator
        constructor
        · intro evaluated
          obtain ⟨v,ev,same⟩ := closedSourceExpressionEvaluates_bitNot_iff.mp evaluated
          obtain ⟨sameChild,rfl⟩ := (h.image _ _).mp ev
          rw [value] at sameChild
          cases RuntimeValue.word.inj sameChild
          exact ⟨same,rfl⟩
        · rintro ⟨rfl,rfl⟩
          exact closedSourceExpressionEvaluates_bitNot_iff.mpr ⟨w,child,rfl⟩⟩
    | _,_ => throw (IO.userError "independent actual unary operand shape")
  | _ => throw (IO.userError "independent direct unary profile")
termination_by sizeOf src

private def runCase (text : String) (depth : Nat) (p : RuntimeValue) (b : Bool) (w : Core.Word)
    (store : List RuntimeValue) (expected : Core.Value) : IO Unit := do
  let (file,src) ← parsed text
  let captured := rows p b w
  let h ← certificate file captured store src
  proof h.original
  check (h.depth == depth) "handwritten exact path depth"
  match h.value,expected with
  | .bool a,.bool b => check (a == b) "independent Boolean expectation"
  | .word a,.word b => check (a == b) "independent complete Word expectation"
  | _,_ => throw (IO.userError "independent primitive result")
  for budget in [0,depth-1,depth,depth+3] do
    match result : evaluateClosedSourceExpression? budget owner names captured store src with
    | none => check (budget < depth) "unary depth should succeed"
    | some (actual,final) =>
      have evaluated := evaluateClosedSourceExpression?_sound result
      have exactImage := (h.image actual final).mp evaluated
      proof exactImage
      proof ((h.image actual final).mpr exactImage)
      proof ((h.image h.value store).mpr ⟨rfl,rfl⟩)
      check (budget ≥ depth) "unary depth below exact path"

end Tests.ParsedClosedSourceUnary
open Tests.ParsedClosedSourceUnary in
def Tests.frontendParsedClosedSourceUnaryTests : IO Unit := do
  let (_,inert) ← parsed "lam(){return absent;}"
  let p := Solcore.Frontend.RuntimeValue.sourceClosure inert foreign
    [("unused",fid 700)] [(fid 700,.bool true)]
  for b in [false,true] do
    for w in [Solcore.Core.Word.zero,Solcore.Core.Word.maximum,Solcore.Core.Word.ofNatModulo 17] do
      for store in stores p w do
        for (text,depth,expected) in
          [("flag",1,Solcore.Core.Value.bool b),("word",1,.word w),
            ("!flag",2,.bool (!b)),("~word",2,.word w.bitNot),
            ("!!flag",3,.bool b),("~~word",3,.word w),
            ("!(flag)",3,.bool (!b)),("~(word)",3,.word w.bitNot),
            ("!((flag))",4,.bool (!b)),("~((word))",4,.word w.bitNot),
            ("~0",2,.word Solcore.Core.Word.maximum),
            ("~0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",2,
              .word Solcore.Core.Word.zero)] do
          runCase text depth p b w store expected

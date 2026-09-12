import Solcore.Frontend.ClosedSourceUnaryProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Core.UnaryPrimitives
import Solcore.Syntax.Parser.Term
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedClosedSourceBitNotClosures
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"UnaryParsed",by decide⟩],by decide⟩⟩,296⟩
private def caller := {owner with declarationIndex := 297}
private def foreign := {owner with declarationIndex := 901}
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def fid (n : Nat) : Resolved.LocalId := ⟨foreign,n⟩
private def opaqueCore : V := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
private def savedNames : LocalNameTable := [("saved",sid 7),("tag",sid 31),("saved",sid 9),("arg",sid 8),("other",fid 900)]
private def savedRows (p : V) (x : Core.Word) := [(sid 32,p),(sid 7,RuntimeValue.word x),(sid 31,.hostFunction .storageWrite),
  (sid 7,.word (x.bitNot)),(sid 8,.pair p .unit),(fid 900,opaqueCore),(sid 9,.unit)]
private def innerNames := ("seed",sid 32)::savedNames
private def innerRows (p : V) (x : Core.Word) := (sid 32,RuntimeValue.pair p .unit)::savedRows p x
private def bodyNames := ("ignored",sid 33)::innerNames
private def bodyRows (p : V) (x : Core.Word) (a : V) := (sid 33,a)::innerRows p x
private def callerNames : LocalNameTable := [("picked",cid 0),("arg",cid 900),("saved",cid 7),("picked",cid 0),("ignored",fid 901)]
private def callerRows (p : V) (x : Core.Word) (made : V) := [(cid 900,RuntimeValue.pair .unit p),(cid 7,.word (x.bitNot)),
  (cid 0,made),(cid 0,p),(sid 7,.word (x.bitNot)),(fid 900,opaqueCore)]
private def stores (p : V) (x : Core.Word) := [[p,opaqueCore,.hostFunction .storageWrite,
  .cellRef (.function .word .word) 900,.pair (.word x) .unit],[opaqueCore,p]]
private theorem fresh0 : Resolved.freshLocalId owner (savedNames.map Prod.snd)=sid 32 := by decide
private theorem fresh1 : Resolved.freshLocalId owner (innerNames.map Prod.snd)=sid 33 := by decide
private theorem freshCaller : Resolved.freshLocalId caller (callerNames.map Prod.snd)=cid 901 := by decide
private def visit (file : Syntax.SourceFile) (src : Syntax.Expr) : IO (List (Nat × Nat)) := do
  let range (s : Syntax.SourceSpan) := (s.startByte,s.endByte)
  let valid (parent : Syntax.SourceSpan) (children : List Syntax.SourceSpan) :=
    parent.isValidFor file && children.all (fun s => s.isValidFor file && parent.contains s)
  match src with
  | ⟨s,.identifier n⟩ => check (valid s [n.span] && s==n.span) "reference spans"; return [range s,range n.span]
  | ⟨s,.group e⟩ =>
    check (valid s [e.span] && s.startByte+1==e.span.startByte && e.span.endByte+1==s.endByte &&
      file.content.toUTF8[s.startByte]?==some 40 && file.content.toUTF8[s.endByte-1]?==some 41) "group spans"
    return range s :: (← visit file e)
  | ⟨s,.unary op e⟩ =>
    check (valid s [op.span,e.span] && op.span.length==1 && op.span.endByte==e.span.startByte &&
      s==Syntax.SourceSpan.cover op.span e.span &&
      file.content.toUTF8[op.span.startByte]?==some (if op.value==.logicalNot then 33 else 126)) "unary spans"
    return range s :: range op.span :: (← visit file e)
  | ⟨s,.call f ⟨args,[a]⟩⟩ =>
    check (valid s [f.span,args] && valid args [a.span] && s==Syntax.SourceSpan.cover f.span args &&
      f.span.endByte==args.startByte && args.startByte+1==a.span.startByte && a.span.endByte+1==args.endByte) "call spans"
    return [range s,range args] ++ (← visit file f) ++ (← visit file a)
  | ⟨s,.lambda kw ⟨ps,parameters⟩ none ⟨bs,[⟨rs,.returnStmt (some e)⟩]⟩⟩ =>
    check (valid s [kw,ps,bs] && valid bs [rs] && valid rs [e.span] && kw.length==3 &&
      kw.endByte==ps.startByte && ps.endByte==bs.startByte &&
      file.content.toUTF8[rs.endByte-1]?==some 59) "lambda body/return spans"
    let mut ranges := [range s,range kw,range ps]
    for p in parameters do
      match p with
      | ⟨ns,.inferred n⟩ => check (valid ps [ns] && valid ns [n.span] && ns==n.span) "parameter spans"
                            ranges := ranges ++ [range ns,range n.span]
      | _ => throw (IO.userError "inferred parameters only")
    return ranges ++ [range bs,range rs] ++ (← visit file e)
  | _ => throw (IO.userError "original closure fixture syntax")
termination_by sizeOf src
private def parsed (text : String) (ranges : List (Nat × Nat) := []) : IO (Syntax.SourceFile × Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main,"word-closure-"++text++".sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span==Syntax.SourceSpan.fullFile file) "complete original EOF/diagnostics/span"
    let actual ← visit file src
    check (ranges.isEmpty || actual==ranges) "handwritten complete original ranges"
    return (file,src)
  | _ => throw (IO.userError "parser")
private structure Cert (own : Resolved.DeclarationId) (ns : LocalNameTable)
    (es : Resolved.LocalScope V) (st : List V) (src : Syntax.Expr) where
  value : V
  depth : Nat
  original : E own ns es st src value st
  image : ∀ v s, E own ns es st src v s ↔ v=value ∧ s=st
private def certified {own ns es st src value} (d : Nat) (h : E own ns es st src value st) : Cert own ns es st src :=
  ⟨value,d,h,fun _ _ => ⟨fun other => other.deterministic h,by rintro ⟨rfl,rfl⟩; exact h⟩⟩
private def reference (own : Resolved.DeclarationId) (ns : LocalNameTable) (es : Resolved.LocalScope V)
    (st : List V) (src : Syntax.Expr) : IO (Cert own ns es st src) := do
  match shape : src with
  | ⟨_,.identifier n⟩ => match named : ns.lookup? n.value with
    | some id => match found : es.lookup? id with
      | some v => return certified 1 (by rw [shape]; exact .reference (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))
      | none => throw (IO.userError "capture")
    | none => throw (IO.userError "name")
  | _ => throw (IO.userError "reference")
private def wrap {own ns es st} (base : (e : Syntax.Expr) → IO (Cert own ns es st e))
    (src : Syntax.Expr) : IO (Cert own ns es st src) := do
  match shape : src with
  | ⟨_,.group e⟩ =>
    let h ← wrap base e
    return ⟨h.value,h.depth+1,by rw [shape]; exact .group h.original,by
      intro v s; rw [shape]; constructor
      · intro ev; cases ev with
        | group child => exact (h.image _ _).mp child
        | creation impossible => cases impossible
      · rintro ⟨rfl,rfl⟩; exact .group h.original⟩
  | ⟨s,.unary ⟨ops,.bitNot⟩ e⟩ =>
    let h ← wrap base e
    match value : h.value with
    | .word b =>
      have child : E own ns es st e (.word b) st := value ▸ h.original
      have original : E own ns es st src (.word (b.bitNot)) st := by rw [shape]; exact .bitNot child
      proof original; proof (evaluateClosedSourceExpression?_bitNot h.depth own ns es st s ops e)
      return ⟨.word (b.bitNot),h.depth+1,original,by
        intro v fs; rw [shape]; constructor
        · intro ev
          obtain ⟨a,operand,same⟩ := closedSourceExpressionEvaluates_bitNot_iff.mp ev
          obtain ⟨hv,rfl⟩ := (h.image _ _).mp operand
          rw [value] at hv; cases RuntimeValue.word.inj hv; exact ⟨same,rfl⟩
        · rintro ⟨rfl,rfl⟩; exact closedSourceExpressionEvaluates_bitNot_iff.mpr ⟨b,child,rfl⟩⟩
    | _ => throw (IO.userError "saved primitive operand")
  | _ => base src
termination_by sizeOf src
private def run {own ns es st src} (h : Cert own ns es st src) (d : Nat) (expected : V) (sameValue : h.value=expected) : IO Unit := do
  proof h.original; check (h.depth==d) "independent depth"
  for budget in [0,d-1,d,d+3] do
    match result : evaluateClosedSourceExpression? budget own ns es st src with
    | none => check (budget<d) "expected success"
    | some (v,s) =>
      have same := (h.image v s).mp (evaluateClosedSourceExpression?_sound result)
      proof (And.intro (same.1.trans sameValue) same.2); proof ((h.image v s).mpr same); proof ((h.image expected st).mpr ⟨sameValue.symm,rfl⟩)
      check (budget≥d) "adjacent lower depth"
private def primitive (v : V) (expected : Core.Word) : IO (PLift (v=.word expected)) := do
  match value : v with
  | .word b => if same : b=expected then return ⟨by rw [value,same]⟩ else throw (IO.userError "saved Word")
  | _ => throw (IO.userError "complete scalar shape")
private structure Factory (src : Syntax.Expr) (p : V) (x : Core.Word) where
  inner : Syntax.Expr
  parameter : Syntax.Identifier
  body : Syntax.Block
  child : Syntax.Expr
  bs : Syntax.SourceSpan
  rs : Syntax.SourceSpan
  shape : SourceUnaryLambdaShape inner parameter body
  named : parameter.value="ignored"
  returned : body=⟨bs,[⟨rs,.returnStmt (some child)⟩]⟩
  witness : ∀ a st, E owner bodyNames (bodyRows p x a) st child (.word (x.bitNot)) st
  original : E owner savedNames (savedRows p x) [.unit] src
    (.sourceClosure inner owner innerNames (innerRows p x)) [.unit]
private def factory (src : Syntax.Expr) (p : V) (x : Core.Word) : IO (Factory src p x) := do
  match whole : src with
  | ⟨_,.call ⟨_,.group outer⟩ ⟨_,[arg]⟩⟩ => match outerShape : outer with
    | ⟨_,.lambda _ ⟨_,[⟨_,.inferred seed⟩]⟩ none ob⟩ => match returned : ob with
      | ⟨_,[⟨_,.returnStmt (some inner)⟩]⟩ => match innerShape : inner with
        | ⟨_,.lambda _ ⟨_,[⟨_,.inferred ignored⟩]⟩ none ib⟩ => match bodyShape : ib with
          | ⟨bs,[⟨rs,.returnStmt (some child)⟩]⟩ => match childShape : child with
            | ⟨_,.unary ⟨_,.bitNot⟩ ⟨_,.identifier n⟩⟩ =>
              if valid : seed.value="seed" ∧ ignored.value="ignored" ∧ n.value="saved" then
                let a ← reference owner savedNames (savedRows p x) [.unit] arg
                match argShape : arg with
                | ⟨_,.identifier ⟨_,"arg"⟩⟩ =>
                  have av : E owner savedNames (savedRows p x) [.unit] arg (.pair p .unit) [.unit] := by
                    rw [argShape]; exact .reference (.tail (by change "saved"≠"arg"; decide) (.tail (by change "tag"≠"arg"; decide) (.tail (by change "saved"≠"arg"; decide) .head)))
                      (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
                  proof (a.original.deterministic av)
                  have ish : SourceUnaryLambdaShape inner ignored ib := by rw [innerShape]; exact .inferred
                  have osh : SourceUnaryLambdaShape outer seed ob := by rw [outerShape]; exact .inferred
                  have witness (a st) : E owner bodyNames (bodyRows p x a) st child (.word (x.bitNot)) st := by
                    rw [childShape]; exact .bitNot (.reference (id:=sid 7) (by rw [valid.2.2]; exact .tail (by decide) (.tail (by decide) .head))
                      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
                  have body : B owner innerNames (innerRows p x) [.unit] ob
                      (.sourceClosure inner owner innerNames (innerRows p x)) [.unit] := by
                    rw [returned]; exact .expression (.creation ish)
                  return ⟨inner,ignored,ib,child,bs,rs,ish,valid.2.1,bodyShape,witness,by
                    rw [whole]; exact .call osh (.group (.creation osh)) av
                      (by simpa only [valid.1,fresh0,innerNames,innerRows] using body)⟩
                | _ => throw (IO.userError "factory arg")
              else throw (IO.userError "saved names")
            | _ => throw (IO.userError "saved unary")
          | _ => throw (IO.userError "saved return")
        | _ => throw (IO.userError "saved lambda")
      | _ => throw (IO.userError "factory return")
    | _ => throw (IO.userError "factory lambda")
  | _ => throw (IO.userError "factory call")
private def callCert {src p x} (f : Factory src p x) (made : V)
    (hm : made=.sourceClosure f.inner owner innerNames (innerRows p x)) (st : List V)
    (call : Syntax.Expr) : IO (Cert caller callerNames (callerRows p x made) st call) := do
  match shape : call with
  | ⟨_,.call ⟨_,.identifier ⟨_,"picked"⟩⟩ ⟨_,[⟨_,.identifier ⟨_,"arg"⟩⟩]⟩⟩ =>
    return certified 4 (by
      rw [shape]
      exact ClosedSourceExpressionEvaluates.call f.shape
        (by rw [← hm]; exact .reference .head (.tail (by decide) (.tail (by decide) .head)))
        (.reference (.tail (by change "picked"≠"arg"; decide) .head) .head)
        (by rw [f.named,fresh1]; change B owner bodyNames (bodyRows p x (.pair .unit p)) st f.body (.word (x.bitNot)) st
            rw [f.returned]; exact .expression (f.witness _ _)))
  | _ => throw (IO.userError "caller call")
private def callLeaf (src : Syntax.Expr) : IO Syntax.Expr := do
  match src with
  | ⟨_,.group e⟩ | ⟨_,.unary _ e⟩ => callLeaf e
  | ⟨_,.call _ _⟩ => return src
  | _ => throw (IO.userError "original call leaf")
termination_by sizeOf src
private def exercise (p : V) (x : Core.Word) : IO Unit := do
  let (_,src) ← parsed "(lam(seed){return lam(ignored){return ~saved;};})(arg)"
    [(0,54),(49,54),(0,49),(1,48),(1,4),(4,10),(5,9),(5,9),(10,48),(11,47),
      (18,46),(18,21),(21,30),(22,29),(22,29),(30,46),(31,45),(38,44),(38,39),(39,44),(39,44),(50,53),(50,53)]
  let f ← factory src p x
  proof fresh0; proof fresh1; proof freshCaller; proof (show owner≠caller by decide); proof (Core.Word.bitNot_involutive x)
  run (certified 3 f.original) 3 _ rfl
  match created : evaluateClosedSourceExpression? 3 owner savedNames (savedRows p x) [.unit] src with
  | none => throw (IO.userError "factory returned closure")
  | some (made,creationFinal) =>
    have creationEq := (evaluateClosedSourceExpression?_sound created).deterministic f.original
    proof creationEq
    for entry in (stores p x).attach do
      let st := entry.val
      have noSnapshot : st≠[RuntimeValue.unit] := by
        have member := entry.property
        simp only [stores,List.mem_cons,List.not_mem_nil,or_false] at member
        change entry.val≠[RuntimeValue.unit]
        rcases member with same | same <;> rw [same] <;> intro h <;> have := congrArg List.length h <;> simp at this
      proof noSnapshot; proof (show st≠creationFinal from fun h => noSnapshot (h.trans creationEq.2))
      for (text,d,ranges) in [
          ("picked(arg)",4,[(0,11),(6,11),(0,6),(0,6),(7,10),(7,10)]),
          ("~picked(arg)",5,[(0,12),(0,1),(1,12),(7,12),(1,7),(1,7),(8,11),(8,11)]),
          ("~((picked(arg)))",7,[(0,16),(0,1),(1,16),(2,15),(3,14),(9,14),(3,9),(3,9),(10,13),(10,13)])] do
        let (_,whole) ← parsed text ranges
        let h ← wrap (callCert f made creationEq.1 st) whole
        let expected ← primitive h.value (if d==4 then x.bitNot else x)
        proof expected.down
        let leaf ← callLeaf whole
        match callShape : leaf with
        | ⟨_,.call ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩ ⟨_,[⟨argSpan,.identifier ⟨argName,"arg"⟩⟩]⟩⟩ =>
          let fn : Syntax.Expr := ⟨fnSpan,.identifier ⟨fnName,"picked"⟩⟩
          let arg : Syntax.Expr := ⟨argSpan,.identifier ⟨argName,"arg"⟩⟩
          let independent ← callCert f made creationEq.1 st leaf
          have callee (s) : E caller callerNames (callerRows p x made) s fn made s :=
            .reference .head (.tail (by decide) (.tail (by decide) .head))
          have argument (s) : E caller callerNames (callerRows p x made) s arg (.pair .unit p) s :=
            .reference (.tail (by change "picked"≠"arg"; decide) .head) .head
          proof independent.original; proof (callee st); proof (argument st)
          match fnRun : evaluateClosedSourceExpression? 1 caller callerNames (callerRows p x made) st fn with
          | none => throw (IO.userError "actual callee")
          | some (actualFn,calleeStore) =>
            have fnEq := (evaluateClosedSourceExpression?_sound fnRun).deterministic (callee st)
            match argRun : evaluateClosedSourceExpression? 1 caller callerNames (callerRows p x made) calleeStore arg with
            | none => throw (IO.userError "actual argument")
            | some (actualArg,bodyStore) =>
              have argEq := (evaluateClosedSourceExpression?_sound argRun).deterministic (argument calleeStore)
              proof fnEq; proof argEq; proof (argEq.2.trans fnEq.2)
              have fnValue := fnEq.1.trans creationEq.1
              match actualShape : actualFn with
              | .sourceClosure savedSource savedOwner sn sc =>
                match selected : sourceUnaryLambdaShape? savedSource with
                | none => throw (IO.userError "actual saved source shape")
                | some (parameter,body) =>
                  let ns := (parameter.value,Resolved.freshLocalId savedOwner (sn.map Prod.snd))::sn
                  let es := (Resolved.freshLocalId savedOwner (sn.map Prod.snd),actualArg)::sc
                  have originalBody : B savedOwner ns es bodyStore body (.word (x.bitNot)) bodyStore := by
                    have same : RuntimeValue.sourceClosure savedSource savedOwner sn sc =
                        .sourceClosure f.inner owner innerNames (innerRows p x) := by simpa only [actualShape] using fnValue
                    obtain ⟨rfl,rfl,rfl,rfl⟩ := RuntimeValue.sourceClosure.inj same
                    have shapeEq := Prod.mk.inj (Option.some.inj
                      (selected.symm.trans (sourceUnaryLambdaShape?_iff.mpr f.shape)))
                    obtain ⟨rfl,rfl⟩ := shapeEq
                    dsimp [ns,es]; rw [f.named,fresh1]
                    change B owner bodyNames (bodyRows p x actualArg) bodyStore f.body (.word (x.bitNot)) bodyStore
                    rw [f.returned]; exact .expression (f.witness _ _)
                  proof originalBody
                  match returned : body with
                  | ⟨bs,[⟨rs,.returnStmt (some child)⟩]⟩ =>
                    have independentChild : E savedOwner ns es bodyStore child (.word (x.bitNot)) bodyStore := by
                      rw [returned] at originalBody; cases originalBody with | expression h => exact h
                    let ch ← wrap (reference savedOwner ns es bodyStore) child
                    proof (ch.original.deterministic independentChild); check (ch.depth==2) "saved unary depth2"
                    have image (v s) : B savedOwner ns es bodyStore body v s ↔ v=ch.value ∧ s=bodyStore := by
                      rw [returned]; constructor
                      · intro ev; cases ev with | expression h => exact (ch.image _ _).mp h
                      · rintro ⟨rfl,rfl⟩; exact .expression ((ch.image _ _).mpr ⟨rfl,rfl⟩)
                    for budget in [0,2,3,6] do
                      match bodyRun : evaluateClosedSourceBody? budget savedOwner ns es bodyStore body with
                      | none => check (budget<3) "saved body success3"
                      | some (v,s) =>
                        have same := (image v s).mp (evaluateClosedSourceBody?_sound bodyRun)
                        proof same; proof ((image v s).mpr same); proof ((image ch.value bodyStore).mpr ⟨rfl,rfl⟩)
                        proof ((evaluateClosedSourceBody?_sound bodyRun).deterministic originalBody)
                        check (budget≥3) "saved body lower boundary"
                  | _ => throw (IO.userError "actual saved return")
              | _ => throw (IO.userError "actual source closure")
              run h d _ expected.down
        | _ => throw (IO.userError "call shape")
end Tests.ParsedClosedSourceBitNotClosures
open Tests.ParsedClosedSourceBitNotClosures in
def Tests.frontendParsedClosedSourceBitNotClosureTests : IO Unit := do
  let (_,inert) ← parsed "lam(){return absent;}"
  let p := Solcore.Frontend.RuntimeValue.sourceClosure inert foreign [("unused",fid 700)] [(fid 700,.bool true)]
  for x in [Solcore.Core.Word.zero,Solcore.Core.Word.maximum,Solcore.Core.Word.ofNatModulo 17] do exercise p x

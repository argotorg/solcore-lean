import Solcore.Frontend.ClosedSourceStoreProperties
import Solcore.Frontend.ClosedSourceEvaluatorStoreProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Syntax.Parser.Term

/- Literal runtime values and saved lexical fields survive store replacement.
Opaque cells are data, not a guarantee that replacement heaps validate them.
Independent original fixtures and actual endpoints precede the replay laws. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceStoreReplay
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedStoreReplay",by decide⟩],by decide⟩⟩,n⟩
private def so := owner 309
private def co := owner 909
private def sid (n : Nat) : Resolved.LocalId := ⟨so,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def sn : LocalNameTable := [("z",sid 2),("q",sid 8),("x",cid 40),("z",sid 99),("q",sid 99)]
private def se (sv core : V) : Resolved.LocalScope V := [(sid 2,sv),(sid 2,.unit),(sid 8,core),(sid 99,.bool false),(sid 100,core)]
private def cn : LocalNameTable := [("f",cid 1),("x",cid 2),("z",cid 3),("f",cid 99),("x",cid 99)]
private def ce (saved av other : V) : Resolved.LocalScope V :=
  [(cid 1,saved),(cid 1,other),(cid 2,av),(cid 2,.unit),(cid 3,other),(cid 99,other)]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (name : String) : Syntax.Expr := ⟨span f a b,.identifier ⟨span f a b,name⟩⟩
private def expectedLambda (binding : Bool) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 (if binding then 25 else 17),.lambda (span f 0 3)
    ⟨span f 3 6,[⟨span f 4 5,.inferred ⟨span f 4 5,"q"⟩⟩]⟩ none
    (if binding then ⟨span f 6 25,[⟨span f 7 15,.letDecl ⟨span f 11 12,"q"⟩ none (some (ref f 13 14 "q"))⟩,
      ⟨span f 15 24,.returnStmt (some (ref f 22 23 "q"))⟩]⟩
    else ⟨span f 6 17,[⟨span f 7 16,.returnStmt (some (ref f 14 15 "z"))⟩]⟩)⟩
private def expectedCall (f : Syntax.SourceFile) : Syntax.Expr := ⟨span f 0 4,.call (ref f 0 1 "f") ⟨span f 1 4,[ref f 2 3 "x"]⟩⟩
private def expectedShort (op : Syntax.BinaryOp) (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 6,.binary (ref f 0 1 "a") ⟨span f 2 4,op⟩ (ref f 5 6 "w")⟩
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.call f ⟨a,[x]⟩⟩ => [s]++spans f++[a]++spans x
  | ⟨s,.binary l op r⟩ => [s]++spans l++[op.span]++spans r
  | ⟨s,.lambda k ⟨ps,[⟨p,.inferred n⟩]⟩ none ⟨b,[⟨r,.returnStmt (some e)⟩]⟩⟩ => [s,k,ps,p,n.span,b,r]++spans e
  | ⟨s,.lambda k ⟨ps,[⟨p,.inferred n⟩]⟩ none ⟨b,[⟨l,.letDecl v none (some i)⟩,⟨r,.returnStmt (some e)⟩]⟩⟩ =>
    [s,k,ps,p,n.span,b,l,v.span]++spans i++[r]++spans e
  | _ => []
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr) (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-store-replay.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "store replay lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole handwritten AST / EOF / zero diagnostics"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==ranges) "every actual range"
    return actual
  | _ => throw (IO.userError "store replay parser")
private def expression {o n e st source v final} (original : E o n e st source v final)
    (depth : Nat) (replacements : List (List V)) : IO Unit := do
  proof original
  for budget in [0,depth-1,depth,depth+3] do
    match ran : evaluateClosedSourceExpression? budget o n e st source with
    | none =>
      check (budget<depth) "independent low expression None"
      for replacement in replacements do
        check ((evaluateClosedSourceExpression? budget o n e replacement source).isNone) "same low expression None"
        have law := evaluateClosedSourceExpression?_replay_store budget o n e st replacement source
        proof law
        proof (show evaluateClosedSourceExpression? budget o n e replacement source = none by simpa only [ran,Option.map_none] using law)
    | some (actual,out) =>
      have evaluated := evaluateClosedSourceExpression?_sound ran
      proof (show actual=v ∧ out=final from evaluated.deterministic original); proof evaluated.store_eq
      check (depth≤budget) "independent sharp expression depth"
      for replacement in replacements do
        have replay := evaluated.replay_store replacement
        match other : evaluateClosedSourceExpression? budget o n e replacement source with
        | some (_,_) => proof ((evaluateClosedSourceExpression?_sound other).deterministic replay)
        | none => throw (IO.userError "successful expression store replacement")
        have law := evaluateClosedSourceExpression?_replay_store budget o n e st replacement source
        proof law
        proof (show evaluateClosedSourceExpression? budget o n e replacement source = some (actual,replacement) by
          simpa only [ran,Option.map_some] using law)
private def body {o n e st source v final} (original : B o n e st source v final)
    (depth : Nat) (replacements : List (List V)) : IO Unit := do
  proof original
  for budget in [0,depth-1,depth,depth+3] do
    match ran : evaluateClosedSourceBody? budget o n e st source with
    | none =>
      check (budget<depth) "independent low body None"
      for replacement in replacements do
        check ((evaluateClosedSourceBody? budget o n e replacement source).isNone) "same low body None"
        have law := evaluateClosedSourceBody?_replay_store budget o n e st replacement source
        proof law
        proof (show evaluateClosedSourceBody? budget o n e replacement source = none by simpa only [ran,Option.map_none] using law)
    | some (actual,out) =>
      have evaluated := evaluateClosedSourceBody?_sound ran
      proof (show actual=v ∧ out=final from evaluated.deterministic original); proof evaluated.store_eq
      check (depth≤budget) "independent sharp body depth"
      for replacement in replacements do
        have replay := evaluated.replay_store replacement
        match other : evaluateClosedSourceBody? budget o n e replacement source with
        | some (_,_) => proof ((evaluateClosedSourceBody?_sound other).deterministic replay)
        | none => throw (IO.userError "successful body store replacement")
        have law := evaluateClosedSourceBody?_replay_store budget o n e st replacement source
        proof law
        proof (show evaluateClosedSourceBody? budget o n e replacement source = some (actual,replacement) by
          simpa only [ran,Option.map_some] using law)
private def application {source callee argument : Syntax.Expr} {parameter : Syntax.Identifier} {block : Syntax.Block}
    {o n e st av value savedOwner savedNames savedCaptured} {cs als : Syntax.SourceSpan}
    (shape : SourceUnaryLambdaShape source parameter block)
    (picked : E o n e st callee (.sourceClosure source savedOwner savedNames savedCaptured) st)
    (argumentOriginal : E o n e st argument av st)
    (independent : B savedOwner ((parameter.value,Resolved.freshLocalId savedOwner (savedNames.map Prod.snd))::savedNames)
      ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd),av)::savedCaptured) st block value st)
    (depth : Nat) (replacements : List (List V)) : IO Unit := do
  have originalCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) shape picked argumentOriginal independent
  proof independent; proof originalCall
  match ran : evaluateClosedSourceBody? depth savedOwner
      ((parameter.value,Resolved.freshLocalId savedOwner (savedNames.map Prod.snd))::savedNames)
      ((Resolved.freshLocalId savedOwner (savedNames.map Prod.snd),av)::savedCaptured) st block with
  | some (bv,bs) =>
    have actualBody := evaluateClosedSourceBody?_sound ran
    proof (show bv=value ∧ bs=st from actualBody.deterministic independent)
    have actualCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) shape picked argumentOriginal actualBody
    body independent depth replacements
    expression actualCall (depth+1) replacements
  | none => throw (IO.userError "independent actual saved body")
private def savedCall (source whole : Syntax.Expr) (sv av core other : V) (st : List V)
    (replacements : List (List V)) : IO Unit := do
  match hs : source, hw : whole with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred parameter⟩]⟩ _ block⟩,⟨cs,.call ⟨fs,.identifier f⟩ ⟨als,[⟨xs,.identifier x⟩]⟩⟩ =>
    have shape : SourceUnaryLambdaShape source parameter block := by rw [hs]; exact .inferred
    let creationStore := [other,core,.unit]
    have creation : E so sn (se sv core) creationStore source (.sourceClosure source so sn (se sv core)) creationStore := .creation shape
    proof creation
    match created : evaluateClosedSourceExpression? 1 so sn (se sv core) creationStore source with
    | some (.sourceClosure actualSource actualOwner actualNames actualCaptured,creationFinal) =>
      have same := (evaluateClosedSourceExpression?_sound created).deterministic creation
      have fields := RuntimeValue.sourceClosure.inj same.1
      have actualShape : SourceUnaryLambdaShape actualSource parameter block := fields.1.symm ▸ shape
      proof fields; proof same.2
      check (actualOwner != co && creationFinal.length != st.length) "actual saved owner/creation store distinct from invocation"
      let n := cn; let e := ce (.sourceClosure actualSource actualOwner actualNames actualCaptured) av other
      if names : f.value="f" ∧ x.value="x" ∧ parameter.value="q" then
        have picked : E co n e st ⟨fs,.identifier f⟩ (.sourceClosure actualSource actualOwner actualNames actualCaptured) st :=
          .reference (names.1 ▸ LocalNameTable.Lookup.head) .head
        have argumentOriginal : E co n e st ⟨xs,.identifier x⟩ av st :=
          .reference (names.2.1 ▸ LocalNameTable.Lookup.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
        proof picked; proof argumentOriginal
        match xr : evaluateClosedSourceExpression? 1 co n e st ⟨xs,.identifier x⟩ with
        | some (_,_) => proof ((evaluateClosedSourceExpression?_sound xr).deterministic argumentOriginal)
        | none => throw (IO.userError "actual caller x planned payload")
        let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
        let bn := (parameter.value,fresh)::actualNames; let be := (fresh,av)::actualCaptured
        match hb : block with
        | ⟨_,[⟨_,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
          if hk : key.value="z" then
            have child : E actualOwner bn be st ⟨ys,.identifier key⟩ sv st := by
              rcases fields with ⟨_,rfl,rfl,rfl⟩
              apply ClosedSourceExpressionEvaluates.reference (id:=sid 2) _ (Resolved.LocalScope.Lookup.tail (by decide) .head)
              rw [hk]; exact .tail (by simpa only [names.2.2] using (by decide : "q" ≠ "z")) .head
            have originalBody : B actualOwner bn be st block sv st := by rw [hb]; exact .expression child
            application (cs:=cs) (als:=als) actualShape picked argumentOriginal originalBody 2 replacements
          else throw (IO.userError "actual saved free z")
        | ⟨bs,[⟨_,.letDecl bound none (some ⟨is,.identifier initializer⟩)⟩,⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
          if equal : initializer.value=parameter.value ∧ key.value=bound.value then
            have init : E actualOwner bn be st ⟨is,.identifier initializer⟩ av st :=
              .reference (equal.1 ▸ LocalNameTable.Lookup.head) .head
            have returned : B actualOwner ((bound.value,Resolved.freshLocalId actualOwner (bn.map Prod.snd))::bn)
                ((Resolved.freshLocalId actualOwner (bn.map Prod.snd),av)::be) st
                ⟨bs,[⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ av st :=
              .expression (.reference (equal.2 ▸ LocalNameTable.Lookup.head) .head)
            have originalBody : B actualOwner bn be st block av st := by rw [hb]; exact .inferred init returned
            application (cs:=cs) (als:=als) actualShape picked argumentOriginal originalBody 3 replacements
          else throw (IO.userError "actual initializer before fresh shadow and fresh return")
        | _ => throw (IO.userError "actual saved binding or free body")
        expression creation 1 replacements
      else throw (IO.userError "actual f/x/q spellings")
    | _ => throw (IO.userError "actual closure creation endpoint")
  | _,_ => throw (IO.userError "actual saved lambda and f(x)")
private def failure (o : Resolved.DeclarationId) (n : LocalNameTable) (e : Resolved.LocalScope V)
    (st : List V) (source : Syntax.Expr) (replacements : List (List V)) : IO Unit := do
  for budget in [0,1,2,5] do
    match ran : evaluateClosedSourceExpression? budget o n e st source with
    | none =>
      for replacement in replacements do
        check ((evaluateClosedSourceExpression? budget o n e replacement source).isNone) "store cannot repair this failure"
        have law := evaluateClosedSourceExpression?_replay_store budget o n e st replacement source
        proof law
        proof (show evaluateClosedSourceExpression? budget o n e replacement source = none by simpa only [ran,Option.map_none] using law)
    | some _ => throw (IO.userError "independent actual unsupported expression")
private def shortCircuit (source : Syntax.Expr) (core : V) (st : List V) (replacements : List (List V)) : IO Unit := do
  match hs : source with
  | ⟨ss,.binary ⟨ls,.identifier left⟩ ⟨os,.logicalAnd⟩ ⟨rs,.identifier right⟩⟩ =>
    if names : left.value="a" ∧ right.value="w" then
      let n : LocalNameTable := [("a",cid 4),("a",cid 99)]
      let e (v : V) : Resolved.LocalScope V := [(cid 4,v),(cid 4,core),(cid 99,core)]
      have absent : ∀ v final, ¬ E co n (e (.bool false)) st ⟨rs,.identifier right⟩ v final := by
        intro v final original; cases original with
        | creation impossible => cases impossible
        | reference named _ =>
          have looked := LocalNameTable.lookup?_iff.mpr named
          simp [n,LocalNameTable.lookup?,names.2] at looked
      have leftOriginal : E co n (e (.bool false)) st ⟨ls,.identifier left⟩ (.bool false) st :=
        .reference (names.1 ▸ LocalNameTable.Lookup.head) .head
      have original : E co n (e (.bool false)) st source (.bool false) st := by rw [hs]; exact .andFalse leftOriginal
      have direct : evaluateClosedSourceExpression? 2 co n (e (.bool false)) st source = some (.bool false,st) := by
        simp [hs,evaluateClosedSourceExpression?,n,e,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,names.1]
      proof absent; proof original; proof direct
      expression original 2 replacements
      failure co n (e (.bool false)) st ⟨rs,.identifier right⟩ replacements
      let bad := RuntimeValue.cellRef .word 700
      have badLeft : E co n (e bad) st ⟨ls,.identifier left⟩ bad st := .reference (names.1 ▸ LocalNameTable.Lookup.head) .head
      have impossible : ∀ v final, ¬ E co n (e bad) st source v final := by
        intro v final original; rw [hs] at original; cases original with
        | creation noShape => cases noShape
        | andFalse child => have equal := (child.deterministic badLeft).1; dsimp only [bad] at equal; cases equal
        | andTrue child _ => have equal := (child.deterministic badLeft).1; dsimp only [bad] at equal; cases equal
        | strictWordBinary _ _ meaning => cases meaning
      proof badLeft; proof impossible
      failure co n (e bad) st source replacements
    else throw (IO.userError "actual a/w short circuit names")
  | _ => throw (IO.userError "actual logical and short circuit")
end Tests.ParsedClosedSourceStoreReplay
open Solcore Solcore.Frontend Tests.ParsedClosedSourceStoreReplay in
def Tests.frontendParsedClosedSourceStoreReplayTests : IO Unit := do
  let free ← parsed "lam(q){return z;}" (expectedLambda false) [(0,17),(0,3),(3,6),(4,5),(4,5),(6,17),(7,16),(14,15),(14,15)]
  let bound ← parsed "lam(q){let q=q;return q;}" (expectedLambda true)
    [(0,25),(0,3),(3,6),(4,5),(4,5),(6,25),(7,15),(11,12),(13,14),(13,14),(15,24),(22,23),(22,23)]
  let call ← parsed "f(x)" expectedCall [(0,4),(0,1),(0,1),(1,4),(2,3),(2,3)]
  let short ← parsed "a && w" (expectedShort .logicalAnd) [(0,6),(0,1),(0,1),(2,4),(5,6),(5,6)]
  let core := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let other := RuntimeValue.sourceClosure free (owner 609) [("q",cid 77),("q",cid 88)] [(cid 77,core),(cid 77,.bool false)]
  let replacements : List (List RuntimeValue) := [[],[.unit],[other,core,.cellRef .word 999,.hostFunction .storageWrite]]
  let mut count := 0
  for st in [[],[other,core,.hostFunction .storageWrite,.cellRef .word 900]] do
    for (sv,av) in [(other,RuntimeValue.cellRef .word 700),(core,other),
        (RuntimeValue.pair core other,RuntimeValue.word Core.Word.maximum)] do
      for source in [free,bound] do
        savedCall source call sv av core other st replacements
        count := count+1
    shortCircuit short core st replacements
  check (count==12) "two saved bodies / three mixed payload pairs / two initial stores / three replacements"

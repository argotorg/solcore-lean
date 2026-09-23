import Solcore.Frontend.ClosedSource
import Solcore.Syntax.Parser.Term
/- Actual mapped endpoints precede reflection; independent originals and adjacent runs identify full preimages and a shared cutoff. -/
set_option autoImplicit false
namespace Tests.ParsedOwnerReflection
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner (n : Nat) : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedOwner",by decide⟩],by decide⟩⟩,n⟩
private def so := owner 311
private def co := owner 711
private def fo := owner 911
private def lid (o : Resolved.DeclarationId) (i : Nat) : Resolved.LocalId := ⟨o,i⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := {o with declarationIndex:=o.declarationIndex+5}
private theorem shift_injective : Function.Injective shift := by
  intro a b same
  have hm := congrArg Resolved.DeclarationId.moduleId same
  have hi := congrArg Resolved.DeclarationId.declarationIndex same
  cases a; cases b
  simp only [shift,Resolved.DeclarationId.mk.injEq] at hm hi ⊢
  exact ⟨hm,by omega⟩
private theorem shift_not_surjective : ¬ Function.Surjective shift := by
  intro onto
  obtain ⟨a,same⟩ := onto (owner 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex same
  simp [shift,owner] at impossible
private def sn : LocalNameTable := [("q",lid so 8),("foreign",lid fo 99),("q",lid so 99),("q",lid fo 8)]
private def se (v : V) : Resolved.LocalScope V :=
  [(lid fo 8,.unit),(lid so 8,v),(lid so 8,.bool false),(lid so 100,.cellRef .word 800),
   (lid so 101,.hostFunction .storageWrite),(lid so 102,.bool false),(lid fo 100,v)]
private def cn : LocalNameTable := [("f",lid co 1),("x",lid co 2),("x",lid fo 2),("f",lid co 99),("x",lid co 99)]
private def ce (saved av : V) : Resolved.LocalScope V :=
  [(lid fo 1,.unit),(lid co 1,saved),(lid co 1,.bool false),(lid fo 2,.unit),(lid co 2,av),(lid co 2,.unit)]
private def core : V := .ofCore (.closure .unit .word (.var 99) [.cellRef .word 701,.hostFunction .storageWrite])
private def mixed (source : Syntax.Expr) (caller saved foreign : Resolved.DeclarationId) : V :=
  .pair (.sourceClosure source saved [("q",lid saved 8),("q",lid foreign 8)]
    [(lid saved 8,.coreClosure .unit .word (.var 17)
      [.sourceClosure source foreign [("q",lid caller 8)] [(lid caller 8,.cellRef .word 702),(lid caller 8,.unit)],core]),
     (lid saved 8,.bool false)]) (.pair core (.cellRef .word 703))
private theorem mixed_fields (source : Syntax.Expr) :
    (mixed source co so fo).mapOwners shift = mixed source (shift co) (shift so) (shift fo) := by
  simp only [mixed,core,RuntimeValue.ofCore,List.attach_map_val,RuntimeValue.mapOwners_sourceClosure,
    RuntimeValue.mapOwners_coreClosure,RuntimeValue.mapOwners,mapRuntimeCapturedOwners,
    LocalNameTable.mapIds,ownerLocalIdMap,lid,List.map_cons,List.map_nil]
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (n : String) : Syntax.Expr := ⟨span f a b,.identifier ⟨span f a b,n⟩⟩
private def ty (f : Syntax.SourceFile) (a b : Nat) : Syntax.TypeExpr :=
  ⟨span f a b,.named ⟨span f a b,⟨⟨⟨span f a b,"Unit"⟩,[]⟩⟩⟩ none⟩
private def expectedLambda (typed : Bool) (f : Syntax.SourceFile) : Syntax.Expr :=
  let d := if typed then 5 else 0
  ⟨span f 0 (38+d),.lambda (span f 0 3)
    ⟨span f 3 (6+d),[if typed then ⟨span f 4 10,.typed none ⟨span f 4 5,"q"⟩ (ty f 6 10)⟩
      else ⟨span f 4 5,.inferred ⟨span f 4 5,"q"⟩⟩]⟩ none
    ⟨span f (6+d) (38+d),[⟨span f (7+d) (20+d),.letDecl ⟨span f (11+d) (12+d),"q"⟩
      (some (ty f (13+d) (17+d))) (some (ref f (18+d) (19+d) "q"))⟩,
      ⟨span f (20+d) (28+d),.letDecl ⟨span f (24+d) (25+d),"q"⟩ none (some (ref f (26+d) (27+d) "q"))⟩,
      ⟨span f (28+d) (37+d),.returnStmt (some (ref f (35+d) (36+d) "q"))⟩]⟩⟩
private def expectedCall (f : Syntax.SourceFile) : Syntax.Expr := ⟨span f 0 4,.call (ref f 0 1 "f") ⟨span f 1 4,[ref f 2 3 "x"]⟩⟩
private def typeSpans : Syntax.TypeExpr → List Syntax.SourceSpan
  | ⟨s,.named ⟨q,⟨⟨n,[]⟩⟩⟩ none⟩ => [s,q,n.span]
  | _ => []
private def parameterSpans : Syntax.LambdaParameter → List Syntax.SourceSpan
  | ⟨s,.inferred n⟩ => [s,n.span]
  | ⟨s,.typed none n t⟩ => [s,n.span]++typeSpans t
  | _ => []
private def spans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.identifier n⟩ => [s,n.span]
  | ⟨s,.call f ⟨a,[x]⟩⟩ => [s]++spans f++[a]++spans x
  | ⟨s,.lambda k ⟨ps,[p]⟩ none ⟨b,[⟨l,.letDecl n (some t) (some i)⟩,
      ⟨l2,.letDecl n2 none (some i2)⟩,⟨r,.returnStmt (some e)⟩]⟩⟩ =>
    [s,k,ps]++parameterSpans p++[b,l,n.span]++typeSpans t++spans i++[l2,n2.span]++spans i2++[r]++spans e
  | _ => []
private def ranges (typed : Bool) : List (Nat × Nat) :=
  let d := if typed then 5 else 0
  [(0,38+d),(0,3),(3,6+d)]++(if typed then [(4,10),(4,5),(6,10),(6,10),(6,10)] else [(4,5),(4,5)])++
    ([(6,38),(7,20),(11,12),(13,17),(13,17),(13,17),(18,19),(18,19),(20,28),(24,25),
      (26,27),(26,27),(28,37),(35,36),(35,36)].map (fun (a,b) => (a+d,b+d)))
private def parsed (text : String) (ast : Syntax.SourceFile → Syntax.Expr) (expectedRanges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-owner-replay.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "owner lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok actual next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      actual.span==Syntax.SourceSpan.fullFile file && actual==ast file) "whole handwritten AST / EOF / diagnostics"
    check ((spans actual).all (fun s => s.isValidFor file) &&
      (spans actual).map (fun s => (s.startByte,s.endByte))==expectedRanges) "all actual handwritten spans"
    return actual
  | _ => throw (IO.userError "owner parser")
private theorem pinCutoff {before after : Nat → Option (V × List V)} {value final mapped mappedStore depth}
    (low : before (depth-1)=none) (high : before depth=some (value,final))
    (cutoff : ∃ required : Nat, 0<required ∧ ∀ budget,
      (before budget=if required≤budget then some (value,final) else none) ∧
      (after budget=if required≤budget then some (mapped,mappedStore) else none)) :
    0<depth ∧ ∀ budget, (before budget=if depth≤budget then some (value,final) else none) ∧
      (after budget=if depth≤budget then some (mapped,mappedStore) else none) := by
  obtain ⟨required,positive,cutoff⟩ := cutoff
  have upper : required≤depth := by
    have impossible := (cutoff depth).1
    split at impossible
    · assumption
    · simp only [high,Option.some_ne_none] at impossible
  have lower : depth≤required := by
    have impossible := (cutoff (depth-1)).1
    split at impossible
    · simp only [low,reduceCtorEq] at impossible
    · omega
  have same : required=depth := Nat.le_antisymm upper lower
  simpa only [same] using And.intro positive cutoff
private def expression {o n e st source v final} (original : E o n e st source v final) (depth : Nat) : IO Unit := do
  let before := fun budget => evaluateClosedSourceExpression? budget o n e st source
  let after := fun budget => evaluateClosedSourceExpression? budget (shift o)
    (LocalNameTable.mapIds (ownerLocalIdMap shift) n) (mapRuntimeCapturedOwners shift e)
    (st.map (RuntimeValue.mapOwners shift)) source
  for budget in [0,depth-1,depth,depth+3] do
    match observed : after budget with
    | none =>
      match ran : before budget with
      | none =>
        check (budget<depth) "independent mapped/original expression insufficient budget"
        proof ((evaluateClosedSourceExpression?_mapOwners_none_iff shift shift_injective budget o n e st source).mp observed)
      | some _ => throw (IO.userError "independent expression Option mismatch")
    | some (actual,out) =>
      have mappedOriginal := evaluateClosedSourceExpression?_sound observed
      have recovered := (ClosedSourceExpressionEvaluates.mapOwners_iff_exists shift shift_injective).mp mappedOriginal
      have complete : actual=v.mapOwners shift ∧ out=final.map (RuntimeValue.mapOwners shift) := by
        obtain ⟨prior,priorStore,priorOriginal,values,stores⟩ := recovered
        have same := priorOriginal.deterministic original
        simpa only [same.1,same.2] using And.intro values stores
      have finite := (evaluateClosedSourceExpression?_mapOwners_some_iff_exists shift shift_injective).mp observed
      have finiteComplete : before budget=some (v,final) := by
        obtain ⟨prior,priorStore,priorRun,_,_⟩ := finite
        have same := (evaluateClosedSourceExpression?_sound priorRun).deterministic original
        simpa only [same.1,same.2] using priorRun
      proof mappedOriginal; proof complete; proof finiteComplete
      match ran : before budget with
      | some (prior,priorStore) =>
        proof (show prior=v ∧ priorStore=final from (evaluateClosedSourceExpression?_sound ran).deterministic original)
        check (depth≤budget) "independent expression full recovered endpoint"
      | none => throw (IO.userError "actual old expression must match recovered run")
  match low : before (depth-1), high : before depth with
  | none,some (actual,out) =>
    have same := (evaluateClosedSourceExpression?_sound high).deterministic original
    have exactHigh : before depth=some (v,final) := by simpa only [same.1,same.2] using high
    proof (pinCutoff low exactHigh (original.mapOwners_exact_depth_threshold shift shift_injective))
  | _,_ => throw (IO.userError "independent expression adjacent cutoff observations")
private def body {o n e st source v final} (original : B o n e st source v final) (depth : Nat) : IO Unit := do
  let before := fun budget => evaluateClosedSourceBody? budget o n e st source
  let after := fun budget => evaluateClosedSourceBody? budget (shift o)
    (LocalNameTable.mapIds (ownerLocalIdMap shift) n) (mapRuntimeCapturedOwners shift e)
    (st.map (RuntimeValue.mapOwners shift)) source
  for budget in [0,depth-1,depth,depth+3] do
    match observed : after budget with
    | none =>
      match ran : before budget with
      | none =>
        check (budget<depth) "independent mapped/original body insufficient budget"
        proof ((evaluateClosedSourceBody?_mapOwners_none_iff shift shift_injective budget o n e st source).mp observed)
      | some _ => throw (IO.userError "independent body Option mismatch")
    | some (actual,out) =>
      have mappedOriginal := evaluateClosedSourceBody?_sound observed
      have recovered := (ClosedSourceBodyEvaluates.mapOwners_iff_exists shift shift_injective).mp mappedOriginal
      have complete : actual=v.mapOwners shift ∧ out=final.map (RuntimeValue.mapOwners shift) := by
        obtain ⟨prior,priorStore,priorOriginal,values,stores⟩ := recovered
        have same := priorOriginal.deterministic original
        simpa only [same.1,same.2] using And.intro values stores
      have finite := (evaluateClosedSourceBody?_mapOwners_some_iff_exists shift shift_injective).mp observed
      have finiteComplete : before budget=some (v,final) := by
        obtain ⟨prior,priorStore,priorRun,_,_⟩ := finite
        have same := (evaluateClosedSourceBody?_sound priorRun).deterministic original
        simpa only [same.1,same.2] using priorRun
      proof mappedOriginal; proof complete; proof finiteComplete
      match ran : before budget with
      | some (prior,priorStore) =>
        proof (show prior=v ∧ priorStore=final from (evaluateClosedSourceBody?_sound ran).deterministic original)
        check (depth≤budget) "independent body full recovered endpoint"
      | none => throw (IO.userError "actual old body must match recovered run")
  match low : before (depth-1), high : before depth with
  | none,some (actual,out) =>
    have same := (evaluateClosedSourceBody?_sound high).deterministic original
    have exactHigh : before depth=some (v,final) := by simpa only [same.1,same.2] using high
    proof (pinCutoff low exactHigh (original.mapOwners_exact_depth_threshold shift shift_injective))
  | _,_ => throw (IO.userError "independent body adjacent cutoff observations")
private def application {source whole : Syntax.Expr} {parameter : Syntax.Identifier} {block : Syntax.Block}
    (shape : SourceUnaryLambdaShape source parameter block) (av : V) (st : List V) : IO Unit := do
  let creationStore := [core,.unit]
  have creation : E so sn (se av) creationStore source (.sourceClosure source so sn (se av)) creationStore := .creation shape
  proof creation
  match created : evaluateClosedSourceExpression? 1 so sn (se av) creationStore source with
  | some (.sourceClosure actualSource actualOwner actualNames actualCaptured,creationFinal) =>
    have same := (evaluateClosedSourceExpression?_sound created).deterministic creation
    have fields := RuntimeValue.sourceClosure.inj same.1
    have actualShape : SourceUnaryLambdaShape actualSource parameter block := fields.1.symm ▸ shape
    proof fields; proof same.2
    check (actualOwner != co && actualOwner != fo && creationFinal.length != st.length) "separate saved owner / creation and invocation stores"
    match hw : whole with
    | ⟨cs,.call ⟨fs,.identifier f⟩ ⟨als,[⟨xs,.identifier x⟩]⟩⟩ =>
      if names : f.value="f" ∧ x.value="x" ∧ parameter.value="q" then
        let n := cn; let e := ce (.sourceClosure actualSource actualOwner actualNames actualCaptured) av
        have picked : E co n e st ⟨fs,.identifier f⟩ (.sourceClosure actualSource actualOwner actualNames actualCaptured) st :=
          .reference (names.1 ▸ LocalNameTable.Lookup.head) (.tail (by decide) .head)
        have argumentOriginal : E co n e st ⟨xs,.identifier x⟩ av st :=
          .reference (names.2.1 ▸ LocalNameTable.Lookup.tail (by decide) .head)
            (.tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
        let fresh := Resolved.freshLocalId actualOwner (actualNames.map Prod.snd)
        let bn := (parameter.value,fresh)::actualNames; let be := (fresh,av)::actualCaptured
        have freshExact : fresh=lid so 100 ∧
            Resolved.freshLocalId actualOwner (bn.map Prod.snd)=lid so 101 := by
          rcases fields with ⟨_,rfl,rfl,rfl⟩
          exact ⟨by decide,by change Resolved.freshLocalId so (lid so 100 :: sn.map Prod.snd)=lid so 101; decide⟩
        proof freshExact
        match hb : block with
        | ⟨bs,[⟨_,.letDecl bound (some _) (some ⟨is,.identifier initializer⟩)⟩,
            ⟨_,.letDecl bound2 none (some ⟨is2,.identifier initializer2⟩)⟩,⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ =>
          if equal : initializer.value=parameter.value ∧ initializer2.value=bound.value ∧ key.value=bound2.value then
            have init : E actualOwner bn be st ⟨is,.identifier initializer⟩ av st := .reference (equal.1 ▸ LocalNameTable.Lookup.head) .head
            let fresh2 := Resolved.freshLocalId actualOwner (bn.map Prod.snd)
            let bn2 := (bound.value,fresh2)::bn; let be2 := (fresh2,av)::be
            have init2 : E actualOwner bn2 be2 st ⟨is2,.identifier initializer2⟩ av st :=
              .reference (equal.2.1 ▸ LocalNameTable.Lookup.head) .head
            have fresh3 : Resolved.freshLocalId actualOwner (bn2.map Prod.snd)=lid so 102 := by
              rcases fields with ⟨_,rfl,rfl,rfl⟩
              change Resolved.freshLocalId so (lid so 101 :: lid so 100 :: sn.map Prod.snd)=lid so 102
              decide
            proof fresh3
            have returned : B actualOwner ((bound2.value,Resolved.freshLocalId actualOwner (bn2.map Prod.snd))::bn2)
                ((Resolved.freshLocalId actualOwner (bn2.map Prod.snd),av)::be2) st
                ⟨bs,[⟨rs,.returnStmt (some ⟨ys,.identifier key⟩)⟩]⟩ av st :=
              .expression (.reference (equal.2.2 ▸ LocalNameTable.Lookup.head) .head)
            have originalBody : B actualOwner bn be st block av st := by rw [hb]; exact .binding init (.inferred init2 returned)
            have originalCall : E co n e st whole av st := by rw [hw]; exact .call actualShape picked argumentOriginal originalBody
            proof picked; proof argumentOriginal; proof init; proof init2; proof returned; proof originalBody; proof originalCall
            expression originalCall 5; body originalBody 4
            match cr : evaluateClosedSourceExpression? 1 co n e st ⟨fs,.identifier f⟩ with
            | some (calleeValue,calleeStore) =>
              have actualCallee := evaluateClosedSourceExpression?_sound cr
              have calleeEndpoint := actualCallee.deterministic picked
              proof calleeEndpoint
              match ar : evaluateClosedSourceExpression? 1 co n e calleeStore ⟨xs,.identifier x⟩ with
              | some (argumentValue,argumentStore) =>
                have actualArgument := evaluateClosedSourceExpression?_sound ar
                have alignedArgument : E co n e st ⟨xs,.identifier x⟩ argumentValue argumentStore := calleeEndpoint.2 ▸ actualArgument
                have argumentEndpoint := alignedArgument.deterministic argumentOriginal
                proof argumentEndpoint
                match ran : evaluateClosedSourceBody? 4 actualOwner bn ((fresh,argumentValue)::actualCaptured) argumentStore block with
                | some (actual,out) =>
                  have actualBody := evaluateClosedSourceBody?_sound ran
                  have alignedBody : B actualOwner bn be st block actual out := by
                    simpa only [argumentEndpoint.1,argumentEndpoint.2] using actualBody
                  have endpoint := alignedBody.deterministic originalBody
                  proof endpoint
                  have actualCall := ClosedSourceExpressionEvaluates.call (span:=cs) (argumentsSpan:=als) actualShape
                    (calleeEndpoint.1 ▸ actualCallee) actualArgument actualBody
                  proof actualCall
                | none => throw (IO.userError "actual typed/inferred saved body")
              | none => throw (IO.userError "actual argument at actual callee store")
            | none => throw (IO.userError "actual caller saved callee")
            expression creation 1; expression picked 1; expression argumentOriginal 1
          else throw (IO.userError "actual fresh shadowing spellings")
        | _ => throw (IO.userError "actual typed/inferred saved body shape")
      else throw (IO.userError "actual caller and parameter spellings")
    | _ => throw (IO.userError "actual f(x) shape")
  | _ => throw (IO.userError "actual returned creation closure")
private def savedCall (source whole : Syntax.Expr) (av : V) (st : List V) : IO Unit := do
  match hs : source with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred p⟩]⟩ _ b⟩ =>
    have shape : SourceUnaryLambdaShape source p b := by rw [hs]; exact .inferred
    application (whole:=whole) shape av st
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none p _⟩]⟩ _ b⟩ =>
    have shape : SourceUnaryLambdaShape source p b := by rw [hs]; exact .typed
    application (whole:=whole) shape av st
  | _ => throw (IO.userError "actual unmarked unary lambda")
end Tests.ParsedOwnerReflection
open Solcore Solcore.Frontend Tests.ParsedOwnerReflection in
def Tests.frontendParsedOwnerReflectionTests : IO Unit := do
  let inferred ← parsed "lam(q){let q:Unit=q;let q=q;return q;}" (expectedLambda false) (ranges false)
  let typed ← parsed "lam(q:Unit){let q:Unit=q;let q=q;return q;}" (expectedLambda true) (ranges true)
  let call ← parsed "f(x)" expectedCall [(0,4),(0,1),(0,1),(1,4),(2,3),(2,3)]
  let mut count := 0
  for source in [inferred,typed] do
    let nested := mixed source co so fo
    have exactValue := mixed_fields source
    have exactStore : [nested,RuntimeValue.cellRef .word 900,core].map (RuntimeValue.mapOwners shift) =
        [mixed source (shift co) (shift so) (shift fo),.cellRef .word 900,core] := by
      simp only [List.map_cons,List.map_nil,nested,exactValue,core,RuntimeValue.ofCore,List.attach_map_val,
        RuntimeValue.mapOwners_coreClosure,RuntimeValue.mapOwners,List.map_cons,List.map_nil]
    proof exactValue; proof exactStore
    for av in [nested,RuntimeValue.pair (.cellRef .word 901) nested] do
      for st in [[nested,.cellRef .word 900,core],[core,nested,.cellRef .word 999,.hostFunction .storageRead]] do
        savedCall source call av st
        count := count+1
  check (count==8) "two actual lambda annotations / two nested arguments / two nonempty stores"

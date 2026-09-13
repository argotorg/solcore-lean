import Solcore.Test.FrontendExpectedBoolStrictDataImageProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Core.ExactFuelProperties
import Solcore.Syntax.Parser.Term

set_option autoImplicit false
namespace Tests.ParsedExpectedBoolStrictDataBridge
open Solcore Solcore.Frontend Tests.ExpectedBoolStrictDataImages
private def check (ok : Bool) (message : String) : IO Unit := unless ok do throw (IO.userError message)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"StrictBoolData",by decide⟩],by decide⟩⟩,301⟩
private def caller := {owner with declarationIndex:=9301}
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def fid : Resolved.LocalId := ⟨{owner with declarationIndex:=900},900⟩
private def inputs : LocalTypeInputs := ⟨[⟨"p",sid 7,.unit⟩,⟨"c",sid 31,.word⟩,⟨"p",fid,.unit⟩],by decide⟩
private def old : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700]
private def env (w : Core.Word) : Resolved.Environment := [(sid 7,old),(sid 31,.word w),(fid,old)]
private def callerNames : LocalNameTable := [("picked",cid 7),("c",cid 31),("c",cid 31),("p",fid)]
private def callerRows (fn : RuntimeValue) (w : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(cid 7,fn),(cid 31,.word w),(cid 31,RuntimeValue.ofCore old),(fid,fn),(cid 7,.unit)]
private def directText := "lam(p){let p:Word=p + 1;return !(p < 2) && (p >= 2);}(c + 1)"
private def range (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ranges : List (Nat × Nat) :=
  [(0,53),(0,3),(3,6),(4,5),(4,5),(6,53),(7,24),(11,12),(13,17),(18,23),(18,19),(20,21),(22,23),
   (24,52),(31,51),(31,39),(31,32),(32,39),(33,38),(33,34),(35,36),(37,38),(40,42),(43,51),
   (44,50),(44,45),(46,48),(49,50),(54,59),(54,55),(56,57),(58,59),(0,60),(53,60)]
private def spans (f : Syntax.SourceFile) (i : Nat) : Syntax.SourceSpan :=
  let p := ranges[i]?.getD (0,0); range f p.1 p.2
private def savedSpans (f : Syntax.SourceFile) (i : Nat) : Syntax.SourceSpan :=
  let p := if i=28 then (7,12) else if i=29 then (7,8) else if i=30 then (9,10)
    else if i=31 then (11,12) else if i=32 then (0,13) else if i=33 then (6,13) else (0,0)
  range f p.1 p.2
private def exactTree (a b : Syntax.Expr) : Option (PLift (a=b)) :=
  match a,b with
  | ⟨s,.identifier n⟩,⟨t,.identifier m⟩ =>
    if h : (s,n)=(t,m) then some ⟨by rcases Prod.mk.inj h with ⟨rfl,rfl⟩; rfl⟩ else none
  | ⟨s,.literal n⟩,⟨t,.literal m⟩ =>
    if h : (s,n)=(t,m) then some ⟨by rcases Prod.mk.inj h with ⟨rfl,rfl⟩; rfl⟩ else none
  | ⟨s,.group x⟩,⟨t,.group y⟩ =>
    if h : s=t then match exactTree x y with
      | some ⟨e⟩ => some ⟨by cases h; cases e; rfl⟩ | none => none
    else none
  | ⟨s,.unary op x⟩,⟨t,.unary oq y⟩ =>
    if h : (s,op)=(t,oq) then match exactTree x y with
      | some ⟨e⟩ => some ⟨by rcases Prod.mk.inj h with ⟨rfl,rfl⟩; cases e; rfl⟩ | none => none
    else none
  | ⟨s,.binary x op y⟩,⟨t,.binary z oq w⟩ =>
    if h : (s,op)=(t,oq) then match exactTree x z,exactTree y w with
      | some ⟨e⟩,some ⟨f⟩ => some ⟨by rcases Prod.mk.inj h with ⟨rfl,rfl⟩; cases e; cases f; rfl⟩ | _,_ => none
    else none
  | ⟨s,.call x ⟨ps,[y]⟩⟩,⟨t,.call z ⟨pt,[w]⟩⟩ =>
    if h : (s,ps)=(t,pt) then match exactTree x z,exactTree y w with
      | some ⟨e⟩,some ⟨f⟩ => some ⟨by rcases Prod.mk.inj h with ⟨rfl,rfl⟩; cases e; cases f; rfl⟩ | _,_ => none
    else none
  | ⟨s,.lambda k ⟨ps,[⟨p,.inferred n⟩]⟩ none ⟨bs,[⟨ls,.letDecl name (some ⟨ann,.named qn none⟩) (some x)⟩,⟨rs,.returnStmt (some y)⟩]⟩⟩,
    ⟨t,.lambda j ⟨pt,[⟨q,.inferred m⟩]⟩ none ⟨bt,[⟨lt,.letDecl other (some ⟨annt,.named qm none⟩) (some z)⟩,⟨rt,.returnStmt (some w)⟩]⟩⟩ =>
    if h : [s,k,ps,p,bs,ls,ann,rs]=[t,j,pt,q,bt,lt,annt,rt] ∧ (n,name,qn)=(m,other,qm) then
      match exactTree x z,exactTree y w with
      | some ⟨e⟩,some ⟨f⟩ => some ⟨by
          simp only [List.cons.injEq,Prod.mk.injEq] at h
          rcases h with ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩,rfl,rfl,rfl⟩
          cases e; cases f; rfl⟩
      | _,_ => none
    else none
  | _,_ => none
termination_by sizeOf a
private def parsed (f : Syntax.SourceFile) (expected : Syntax.Expr) : IO {actual : Syntax.Expr // actual=expected} := do
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok actual next =>
    check (next.file==f && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      actual.span==Syntax.SourceSpan.fullFile f) "whole actual SourceFile/EOF/diagnostics"
    match exactTree actual expected with
    | some ⟨h⟩ => return ⟨actual,h⟩
    | none => throw (IO.userError "whole handwritten AST and every nested range")
  | _ => throw (IO.userError "parser")
private structure Trace (o : Resolved.DeclarationId) (n : LocalNameTable) (e : Resolved.LocalScope RuntimeValue)
    (st : List RuntimeValue) (src : Syntax.Expr) where
  value : RuntimeValue
  final : List RuntimeValue
  original : ClosedSourceExpressionEvaluates o n e st src value final
  storeEq : final=st
private def observe {o n e st src v} (d : Nat)
    (original : ClosedSourceExpressionEvaluates o n e st src v st) : IO (Trace o n e st src) := do
  proof original
  match run : evaluateClosedSourceExpression? d o n e st src with
  | none => throw (IO.userError "actual expression endpoint")
  | some (a,z) =>
    have same := (evaluateClosedSourceExpression?_sound run).deterministic original
    return ⟨a,z,by rw [same.1,same.2]; exact original,same.2⟩
private structure BodyTrace (o : Resolved.DeclarationId) (n : LocalNameTable) (e : Resolved.LocalScope RuntimeValue)
    (st : List RuntimeValue) (src : Syntax.Block) where
  value : RuntimeValue
  final : List RuntimeValue
  original : ClosedSourceBodyEvaluates o n e st src value final
private def observeBody {o n e st src v} (d : Nat)
    (original : ClosedSourceBodyEvaluates o n e st src v st) : IO (BodyTrace o n e st src) := do
  proof original
  match run : evaluateClosedSourceBody? d o n e st src with
  | none => throw (IO.userError "actual saved body endpoint")
  | some (a,z) =>
    have same := (evaluateClosedSourceBody?_sound run).deterministic original
    return ⟨a,z,by rw [same.1,same.2]; exact original⟩
private def runCore {e st c v k} (steps : Core.Steps k (.initial c e st) (.final v st)) : IO Unit := do
  proof steps
  for fuel in [0,k-1,k,k+3] do
    match run : Core.runStateful fuel (.initial c e st) with
    | .done a z =>
      have same := Core.evaluation_deterministic (Core.runStateful_evaluation_sound run) (Core.steps_from_initial_sound steps)
      proof same; proof (steps.runStateful_done_iff.mp (by simpa only [same.1,same.2] using run))
      check (a==v && z==st && fuel≥k) "all actual Core values/stores and exact cost"
    | .outOfFuel suspended => proof (steps.runStateful_outOfFuel_iff.mp ⟨suspended,run⟩); check (fuel<k) "Core exhaustion"
    | _ => throw (IO.userError "Core stuck")
private def runClosed {o n e st src v} (d : Nat)
    (original : ClosedSourceExpressionEvaluates o n e st src v st)
    (image : ∀ a z, ClosedSourceExpressionEvaluates o n e st src a z ↔ a=v ∧ z=st) : IO Unit := do
  proof original
  for depth in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? depth o n e st src with
    | none => check (depth<d) "closed depth exhaustion"
    | some (a,z) =>
      have endpoints := (image a z).mp (evaluateClosedSourceExpression?_sound run)
      proof endpoints; proof ((image a z).mpr endpoints)
      check (depth≥d && reprStr a==reprStr v && reprStr z==reprStr st) "all actual closed endpoints"
private theorem exactOriginal {o n e st src v}
    (original : ClosedSourceExpressionEvaluates o n e st src v st) :
    ∀ a z, ClosedSourceExpressionEvaluates o n e st src a z ↔ a=v ∧ z=st := by
  intro a z; constructor
  · exact fun h => h.deterministic original
  · rintro ⟨rfl,rfl⟩; exact original
private theorem oneMeaning (s : Syntax.SourceSpan) : WordLiteralDenotes ⟨s,.decimal "1"⟩ one :=
  .decimal (by decide) (.cons (.decimal (digit:=1) (by decide) rfl) .nil)
private def exercise (w : Core.Word) (st : Core.Store) : IO Unit := do
  let f : Syntax.SourceFile := ⟨⟨.main,"strict-bool-direct.sol"⟩,directText⟩
  let s := spans f
  let ⟨actual,treeEq⟩ ← parsed f (call s (source s) (argument s))
  let g : Syntax.SourceFile := ⟨⟨.main,"strict-bool-saved.sol"⟩,"picked(c + 1)"⟩
  let q := savedSpans g
  let ⟨invoked,invokeEq⟩ ← parsed g (call q (ref (range g 0 6) "picked") (argument q))
  let fs := match actual.value with | .call fn _ => fn | _ => actual
  let actualArg := match actual.value with | .call _ ⟨_,[a]⟩ => a | _ => actual
  let actualBody := match fs.value with | .lambda _ _ _ b => b | _ => body s
  have fsEq : fs=source s := by simp only [fs,treeEq,call]
  have argEq : actualArg=argument s := by simp only [actualArg,treeEq,call]
  have bodyEq : actualBody=body s := by simp only [actualBody,fsEq,source]
  have shape : SourceUnaryLambdaShape fs ⟨s 4,"p"⟩ actualBody := by rw [fsEq,bodyEq]; exact .inferred
  let e := env w
  have aligned : e.ids=inputs.context.ids := rfl
  have b := body_evidence s owner inputs e st (w.add one) aligned
  have a := argument_paths s owner inputs.names e st w (sid 31) 1 (.tail (by decide) .head) (.tail (by decide) .head) (.tail (by decide) .head)
  have beta : ClosedSourceBodyEvaluates owner (("p",Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
      ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),.word (w.add one))::up e) (heap st) actualBody (RuntimeValue.ofCore (result (w.add one))) (heap st) := by
    simpa only [bodyEq,entered,entry,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using b.original
  have creation : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) fs (.sourceClosure fs owner inputs.names (up e)) (heap st) := .creation shape
  have argOriginal : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) actualArg (.word (w.add one)) (heap st) := argEq ▸ a.2.2.2.2
  have directOriginal : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) actual (RuntimeValue.ofCore (result (w.add one))) (heap st) := by
    have h := ClosedSourceExpressionEvaluates.call (span:=s 32) (argumentsSpan:=s 33) shape creation argOriginal beta
    simpa only [treeEq,fsEq,argEq,call] using h
  have argSteps := a.2.2.2.1.toStepsWithContinuation a.2.1 a.2.2.1
  have betaSteps := b.steps []
  have fullSteps : Core.Steps (1+5+bodyCost (w.add one)+3)
      (.initial (.apply (.lambda .word .bool code) (.binary .wordAdd (.var 1) (.word one))) e.values st)
      (.final (result (w.add one)) st) := CostStepComposition.apply (.cons .lambda .refl) (argSteps _) betaSteps
  proof creation; proof a.2.2.2.1.erase; proof b.old; proof beta; proof directOriginal; proof fullSteps
  check (bodyCost (w.add one)==if predicate ((w.add one).add one) then 35 else 23) "independent body cost"
  runCore fullSteps; runCore betaSteps; runCore (argSteps [])
  let directImage : ∀ v z, ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) actual v z ↔
      v=RuntimeValue.ofCore (result (w.add one)) ∧ z=heap st := by
    intro v z; rw [treeEq]
    exact core_exact (Core.steps_from_initial_sound fullSteps)
      (fun _ _ => closedSourceExpectedDataLambda_application_core_iff .inferred b.admitted b.expected aligned a.1 a.2.1 a.2.2.1) v z
  runClosed 8 directOriginal directImage
  runClosed 1 creation (exactOriginal creation)
  let made ← observe 1 creation
  have madeEq := made.original.deterministic creation
  match madeShape : made.value with
  | .sourceClosure saved savedOwner savedNames savedRows =>
    have fields := RuntimeValue.sourceClosure.inj (show RuntimeValue.sourceClosure saved savedOwner savedNames savedRows =
        .sourceClosure fs owner inputs.names (up e) from by rw [← madeShape]; exact madeEq.1)
    check (saved==fs && savedOwner==owner && savedOwner != caller && savedNames==inputs.names &&
      reprStr savedRows==reprStr (up e)) "all actually returned saved closure fields"
    let rows := callerRows made.value w
    let callee := ref (range g 0 6) "picked"
    let passed := argument q
    have fetchedOriginal : ClosedSourceExpressionEvaluates caller callerNames rows made.final callee made.value made.final := .reference .head .head
    let fetched ← observe 1 fetchedOriginal
    have fetchedEq := fetched.original.deterministic fetchedOriginal
    have passedOriginal : ClosedSourceExpressionEvaluates caller callerNames rows fetched.final passed (.word (w.add one)) fetched.final := by
      rw [← RuntimeValue.ofCore.eq_3 (w.add one)]
      exact .strictWordBinary (.reference (.tail (by change "picked"≠"c"; decide) .head) (.tail (by decide) .head)) (.wordLiteral (oneMeaning _)) .add
    let argumentRun ← observe 2 passedOriginal
    have passedEq := argumentRun.original.deterministic passedOriginal
    have initialEq := passedEq.2.trans (fetchedEq.2.trans madeEq.2)
    have savedShape : SourceUnaryLambdaShape saved ⟨s 4,"p"⟩ actualBody := by rw [fields.1]; exact shape
    let fresh := Resolved.freshLocalId savedOwner (savedNames.map Prod.snd)
    have bodyOriginal : ClosedSourceBodyEvaluates savedOwner (("p",fresh)::savedNames)
        ((fresh,argumentRun.value)::savedRows) argumentRun.final actualBody (RuntimeValue.ofCore (result (w.add one))) argumentRun.final := by
      simpa only [fields.2.1,fields.2.2.1,fields.2.2.2,passedEq.1,initialEq,fresh] using beta
    proof bodyOriginal
    check (fresh==sid 32 && Resolved.freshLocalId savedOwner (fresh::savedNames.map Prod.snd)==sid 33) "both actual saved-owner fresh shadows"
    for depth in [0,6,7,10] do
      match br : evaluateClosedSourceBody? depth savedOwner (("p",fresh)::savedNames) ((fresh,argumentRun.value)::savedRows) argumentRun.final actualBody with
      | none => check (depth<7) "body depth exhaustion"
      | some (v,z) =>
        have actualBodyRun : ClosedSourceBodyEvaluates owner (entered owner inputs).names (up (entry owner inputs e (w.add one))) (heap st) (body s) v z := by
          simpa only [fields.2.1,fields.2.2.1,fields.2.2.2,passedEq.1,initialEq,fresh,bodyEq,entered,entry,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using evaluateClosedSourceBody?_sound br
        proof ((b.localImage v z).mp actualBodyRun); proof ((b.localImage v z).mpr ((b.localImage v z).mp actualBodyRun))
        proof ((b.coreImage v z).mp actualBodyRun); proof ((b.coreImage v z).mpr ((b.coreImage v z).mp actualBodyRun))
        check (depth≥7 && reprStr z==reprStr (heap st)) "actual body image endpoints"
    have fetchedActual : ClosedSourceExpressionEvaluates caller callerNames rows made.final callee (.sourceClosure fs owner inputs.names (up e)) fetched.final := by
      simpa only [fetchedEq.1,madeEq.1] using fetched.original
    have argumentActual : ClosedSourceExpressionEvaluates caller callerNames rows fetched.final passed (RuntimeValue.ofCore (.word (w.add one))) (heap st) := by
      simpa only [passedEq.1,initialEq,RuntimeValue.ofCore] using argumentRun.original
    let bodyRun ← observeBody 7 bodyOriginal
    have returnedEq := bodyRun.original.deterministic bodyOriginal
    have fetchedSaved : ClosedSourceExpressionEvaluates caller callerNames rows made.final callee
        (.sourceClosure saved savedOwner savedNames savedRows) fetched.final := by
      simpa only [fetchedEq.1,madeShape] using fetched.original
    have callActual : ClosedSourceExpressionEvaluates caller callerNames rows made.final invoked bodyRun.value bodyRun.final := by
      rw [invokeEq]; exact .call savedShape fetchedSaved argumentRun.original bodyRun.original
    proof callActual
    have original : ClosedSourceExpressionEvaluates caller callerNames rows made.final invoked (RuntimeValue.ofCore (result (w.add one))) (heap st) := by
      simpa only [returnedEq.1,returnedEq.2,initialEq] using callActual
    have originalSame : ClosedSourceExpressionEvaluates caller callerNames rows made.final invoked (RuntimeValue.ofCore (result (w.add one))) made.final := by simpa only [madeEq.2] using original
    runClosed 8 originalSame (fun v z => by
      rw [madeEq.2,invokeEq]
      exact core_exact (Core.steps_from_initial_sound betaSteps)
        (fun _ _ => closedSourceExpectedDataLambda_invocation_core_iff shape (bodyEq ▸ b.admitted) (by simpa only [fsEq] using b.expected) aligned
          (by simpa only [madeEq.2,callee,up] using fetchedActual) argumentActual) v z)
  | _ => throw (IO.userError "actual created source closure")
end Tests.ParsedExpectedBoolStrictDataBridge
open Tests.ParsedExpectedBoolStrictDataBridge in
def Tests.frontendParsedExpectedBoolStrictDataBridgeTests : IO Unit := do
  for w in [Solcore.Core.Word.zero,Solcore.Core.Word.ofNatModulo 1,Solcore.Core.Word.maximum,
      Solcore.Core.Word.ofNatModulo (2^256-2),Solcore.Core.Word.ofNatModulo (2^255)] do
    for st in [[],[old,.hostFunction .storageWrite,.cellRef .word 900,.unit]] do exercise w st

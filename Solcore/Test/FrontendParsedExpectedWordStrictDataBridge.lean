import Solcore.Test.FrontendExpectedWordStrictDataImageProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Syntax.Parser.Term
/- Saved typed identities are unique, but their opaque Core payloads need not
inhabit the declared types. Raw caller rows deliberately retain duplicate IDs.
Depth checks below are finite fixture checks, separate from independent costs. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Tests.ParsedExpectedWordStrictDataBridge
open Solcore Solcore.Frontend
private def check (b : Bool) (m : String) : IO Unit := unless b do throw (IO.userError m)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def heap (s : Core.Store) := s.map RuntimeValue.ofCore
private def one : Core.Word := Core.Word.ofNatModulo 1
private def two : Core.Word := Core.Word.ofNatModulo 2
private def ref (s : Nat → Syntax.SourceSpan) (i : Nat) (n : String) : Syntax.Expr :=
  ⟨s i,.identifier ⟨s (i+1),n⟩⟩
private def lit (s : Nat → Syntax.SourceSpan) (i : Nat) (n : String) : Syntax.Expr :=
  ⟨s i,.literal ⟨s (i+1),.decimal n⟩⟩
private def init (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 4,.binary (ref s 0 "p") ⟨s 5,.add⟩ (lit s 2 "1")⟩
private def returned (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 23,.conditional ⟨s 12,.group ⟨s 10,.binary (ref s 6 "p") ⟨s 11,.less⟩ (lit s 8 "2")⟩⟩
    (s 24) ⟨s 17,.binary (ref s 13 "p") ⟨s 18,.multiply⟩ (lit s 15 "2")⟩
    (s 25) ⟨s 21,.unary ⟨s 22,.bitNot⟩ (ref s 19 "p")⟩⟩
private def annotation (s : Nat → Syntax.SourceSpan) : Syntax.TypeExpr :=
  ⟨s 26,.named ⟨s 27,⟨⟨⟨s 28,"Word"⟩,[]⟩⟩⟩ none⟩
private def body (s : Nat → Syntax.SourceSpan) : Syntax.Block :=
  ⟨s 29,[⟨s 30,.letDecl ⟨s 31,"p"⟩ (some (annotation s)) (some (init s))⟩,
    ⟨s 32,.returnStmt (some (returned s))⟩]⟩
private def source (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 33,.lambda (s 34) ⟨s 35,[⟨s 36,.inferred ⟨s 37,"p"⟩⟩]⟩ none (body s)⟩
private def call (s : Nat → Syntax.SourceSpan) (fn arg : Syntax.Expr) : Syntax.Expr := ⟨s 38,.call fn ⟨s 39,[arg]⟩⟩
private def argument (s : Nat → Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s 44,.binary (ref s 40 "c") ⟨s 45,.add⟩ (lit s 42 "1")⟩
private def decision (w : Core.Word) := decide (w.add one < two)
private def value (w : Core.Word) : Core.Value := .word (if decision w then (w.add one).mul two else (w.add one).bitNot)
private def retCore : Core.Expr := .ifE ((Core.Expr.var 0).wordLt (.word two))
  (.binary .wordMul (.var 0) (.word two)) (.unary .wordNot (.var 0))
private def core : Core.Expr := .letE (.binary .wordAdd (.var 0) (.word one)) retCore
private def cost (w : Core.Word) : Nat := 5 + (11 + (if decision w then 5 else 3) + 2) + 2
private def entry (o : Resolved.DeclarationId) (t : LocalTypeInputs) := t.bindFresh o "p" .word
private def env (o : Resolved.DeclarationId) (t : LocalTypeInputs) (e : Resolved.Environment) (w : Core.Word) : Resolved.Environment :=
  (Resolved.freshLocalId o t.ids,.word w)::e
private def text := "(lam(p){let p:Word=p + 1;return (p < 2) ? p * 2 : ~p;})(c + 1)"
private def file (s : String) : Syntax.SourceFile := ⟨⟨.main,"word-strict-data.sol"⟩,s⟩
private def sp (a b : Nat) : Syntax.SourceSpan := ⟨(file "").id,a,b⟩
private def ranges : List Syntax.SourceSpan :=
  [(19,20),(19,20),(23,24),(23,24),(19,24),(21,22),(33,34),(33,34),(37,38),(37,38),
   (33,38),(35,36),(32,39),(42,43),(42,43),(46,47),(46,47),(42,47),(44,45),(51,52),
   (51,52),(50,52),(50,51),(32,52),(40,41),(48,49),(14,18),(14,18),(14,18),(7,54),
   (8,25),(12,13),(25,53),(1,54),(1,4),(4,7),(5,6),(5,6),(0,62),(55,62),(56,57),
   (56,57),(60,61),(60,61),(56,61),(58,59),(0,55)].map (fun p => sp p.1 p.2)
private def spans (i : Nat) := ranges.getD i (sp 0 0)
private def whole (s : Nat → Syntax.SourceSpan) : Syntax.Expr := call s ⟨s 46,.group (source s)⟩ (argument s)
private def parse : IO {actual : Syntax.Expr // actual=whole spans} := do
  let f := file text
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "Word lexer")
  let .ok actual next := Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) | throw (IO.userError "Word parser")
  check (next.file==f && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && actual==whole spans) "whole handwritten AST/EOF/diagnostics"
  match shape : actual with
  | ⟨s38,.call ⟨s46,.group ⟨s33,.lambda s34 ⟨s35,[⟨s36,.inferred ⟨s37,"p"⟩⟩]⟩ none
      ⟨s29,[⟨s30,.letDecl ⟨s31,"p"⟩ (some ⟨s26,.named ⟨s27,⟨⟨⟨s28,"Word"⟩,[]⟩⟩⟩ none⟩)
        (some ⟨s4,.binary ⟨s0,.identifier ⟨s1,"p"⟩⟩ ⟨s5,.add⟩ ⟨s2,.literal ⟨s3,.decimal "1"⟩⟩⟩)⟩,
        ⟨s32,.returnStmt (some ⟨s23,.conditional ⟨s12,.group ⟨s10,.binary ⟨s6,.identifier ⟨s7,"p"⟩⟩ ⟨s11,.less⟩ ⟨s8,.literal ⟨s9,.decimal "2"⟩⟩⟩⟩ s24
          ⟨s17,.binary ⟨s13,.identifier ⟨s14,"p"⟩⟩ ⟨s18,.multiply⟩ ⟨s15,.literal ⟨s16,.decimal "2"⟩⟩⟩ s25
          ⟨s21,.unary ⟨s22,.bitNot⟩ ⟨s19,.identifier ⟨s20,"p"⟩⟩⟩⟩)⟩]⟩⟩⟩
      ⟨s39,[⟨s44,.binary ⟨s40,.identifier ⟨s41,"c"⟩⟩ ⟨s45,.add⟩ ⟨s42,.literal ⟨s43,.decimal "1"⟩⟩⟩]⟩⟩ =>
    let ss := [s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33,s34,s35,s36,s37,s38,s39,s40,s41,s42,s43,s44,s45,s46]
    if exactRanges : ss=ranges then
      have reconstruct : actual=whole (fun i => ss.getD i (sp 0 0)) := by rw [shape]; rfl
      return ⟨actual,reconstruct.trans (congrArg (fun xs => whole (fun i => xs.getD i (sp 0 0))) exactRanges)⟩
    else throw (IO.userError "all 47 handwritten ranges")
  | _ => throw (IO.userError "exact Word lambda/binding/conditional/call shape")
private def picked : Syntax.Expr := ⟨sp 0 9,.call ⟨sp 0 6,.identifier ⟨sp 0 6,"picked"⟩⟩ ⟨sp 6 9,[⟨sp 7 8,.identifier ⟨sp 7 8,"w"⟩⟩]⟩⟩
private def parseSaved : IO {actual : Syntax.Expr // actual=picked} := do
  let f := file "picked(w)"
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "saved lexer")
  let .ok actual next := Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) | throw (IO.userError "saved parser")
  check (next.file==f && lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && actual==picked) "saved full AST/EOF/diagnostics"
  match shape : actual with
  | ⟨a,.call ⟨b,.identifier ⟨c,"picked"⟩⟩ ⟨d,[⟨e,.identifier ⟨f,"w"⟩⟩]⟩⟩ =>
    if exactRanges : a=sp 0 9 ∧ b=sp 0 6 ∧ c=sp 0 6 ∧ d=sp 6 9 ∧ e=sp 7 8 ∧ f=sp 7 8 then
      return ⟨actual,by rcases exactRanges with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩; exact shape⟩
    else throw (IO.userError "saved six exact ranges")
  | _ => throw (IO.userError "saved actual AST shape")
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WordStrictData",by decide⟩],by decide⟩⟩,301⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def caller : Resolved.DeclarationId := {owner with declarationIndex:=991}
private def cid (n : Nat) : Resolved.LocalId := ⟨caller,n⟩
private def inputs : LocalTypeInputs := ⟨[⟨"c",sid 7,.word⟩,⟨"p",sid 31,.word⟩,⟨"tail",cid 700,.unit⟩,⟨"p",cid 701,.word⟩],by decide⟩
private def environment (c : Core.Word) (q : Core.Value) : Resolved.Environment :=
  [(sid 7,.word c),(sid 31,q),(cid 700,.cellRef .word 900),(cid 701,q)]
private def names : LocalNameTable := [("picked",cid 7),("w",cid 900),("p",sid 31),("picked",cid 7)]
private def rows (fn : RuntimeValue) (w : Core.Word) : Resolved.LocalScope RuntimeValue :=
  [(cid 900,.word w),(cid 7,fn),(sid 31,fn),(cid 7,.unit),(cid 701,.hostFunction .storageWrite)]
private def coreRuns {e s c v k} (p : Core.Steps k (.initial c e s) (.final v s)) : IO Unit := do
  proof p
  for fuel in [0,k-1,k,k+3] do
    match run : Core.runStateful fuel (.initial c e s) with
    | .done a z => proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound run) (Core.steps_from_initial_sound p)); check (fuel≥k && a==v && z==s) "Core independent cost/full endpoints"
    | .outOfFuel _ => check (fuel<k) "Core independent exhaustion"
    | .fault _ _ => throw (IO.userError "Core fault")
private def closedRuns {o n e s src v} (d : Nat) (old : ClosedSourceExpressionEvaluates o n e s src v s)
    (after : ∀ {a z}, ClosedSourceExpressionEvaluates o n e s src a z → IO Unit) : IO Unit := do
  proof old
  for fuel in [0,d-1,d,d+3] do
    match run : evaluateClosedSourceExpression? fuel o n e s src with
    | none => check (fuel<d) "closed fixture depth exhaustion"
    | some _ => have actual := evaluateClosedSourceExpression?_sound run; proof (actual.deterministic old); after actual; check (fuel≥d) "closed fixture depth success"
private def endpoint {P : RuntimeValue → List RuntimeValue → Prop} {v : Core.Value} {s : Core.Store}
    (both : ∀ a z, P a z ↔ a=RuntimeValue.ofCore v ∧ z=heap s) {a z} (actual : P a z) : IO Unit := do
  let equal := (both a z).mp actual
  proof ((both a z).mpr equal)
  check (a.toCore?==some v && z.mapM RuntimeValue.toCore?==some s) "both directions/full actual endpoints"
private def consumeCore {P : Prop} {e s c v a z} (old : Core.Evaluates e s c v s)
    (image : P ↔ ∃ x t, a=RuntimeValue.ofCore x ∧ z=heap t ∧ Core.Evaluates e s c x t) (actual : P) : IO Unit := do
  have equal : a=RuntimeValue.ofCore v ∧ z=heap s := by
    obtain ⟨x,t,hx,ht,run⟩ := image.mp actual
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic run old; exact ⟨hx,ht⟩
  proof (image.mpr ⟨v,s,equal.1,equal.2,old⟩)
  check (a.toCore?==some v && z.mapM RuntimeValue.toCore?==some s) "independent Core reverse/full actual endpoint"
private def calleeOf (src : Syntax.Expr) : Syntax.Expr := match src with | ⟨_,.call fn _⟩ => fn | _ => src
private def argumentOf (src : Syntax.Expr) : Syntax.Expr := match src with | ⟨_,.call _ ⟨_,[a]⟩⟩ => a | _ => src
private def ungroup (src : Syntax.Expr) : Syntax.Expr := match src with | ⟨_,.group fn⟩ => fn | _ => src
private def bodyOf (src : Syntax.Expr) : Syntax.Block := match src with | ⟨_,.lambda _ _ _ b⟩ => b | _ => ⟨sp 0 0,[]⟩
private def exercise (c : Core.Word) (q : Core.Value) (st : Core.Store) : IO Unit := do
  let ⟨actual,actualEq⟩ ← parse
  let ⟨savedActual,savedEq⟩ ← parseSaved
  let actualFn := ungroup (calleeOf actual)
  let actualArg := argumentOf actual
  let actualBody := bodyOf actualFn
  have actualFnEq : actualFn=source spans := by simp only [actualFn,actualEq,whole,call,calleeOf,ungroup]
  have actualArgEq : actualArg=argument spans := by simp only [actualArg,actualEq,whole,call,argumentOf]
  have actualBodyEq : actualBody=body spans := by simp only [actualBody,actualFnEq,source,bodyOf]
  let e := environment c q
  let w := c.add one
  have same : e.ids=inputs.context.ids := rfl
  have h := ExpectedWordStrictDataImages.body_original_and_all_actual_images spans owner inputs e st w same
  have gate : ClosedSourceDataBody (body spans) := h.1
  have checked : elaborateExpectedComputationLambda? elaborateLocalExpression? [(["Word"],.word)] owner inputs (source spans) (.function .word .word)=some (.lambda .word .word core) := h.2.1
  have beta : ClosedSourceBodyEvaluates owner (entry owner inputs).names (up (env owner inputs e w)) (heap st) (body spans) (RuntimeValue.ofCore (value w)) (heap st) := h.2.2.1
  have bodyPath (k) : Core.Steps (cost w) ⟨.eval core (.word w::e.values),k,st⟩ ⟨.ret (value w),k,st⟩ := h.2.2.2.2.1 k
  have bodyExact : ∀ a z, ClosedSourceBodyEvaluates owner (entry owner inputs).names (up (env owner inputs e w)) (heap st) (body spans) a z ↔ a=RuntimeValue.ofCore (value w) ∧ z=heap st := h.2.2.2.2.2
  have argOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) (argument spans) (.word w) (heap st) := by
    simpa only [argument,ref,lit,RuntimeValue.ofCore,w] using ClosedSourceExpressionEvaluates.strictWordBinary
      (owner:=owner) (names:=inputs.names) (captured:=up e) (initialStore:=heap st) (span:=spans 44) (operatorSpan:=spans 45)
      (leftWord:=c) (rightWord:=one)
      (.reference (span:=spans 40) (name:=⟨spans 41,"c"⟩) .head (by simp only [up,e,environment,List.map_cons,RuntimeValue.ofCore]; exact .head))
      (.wordLiteral (span:=spans 42) (interpretWordLiteral?_iff.mp (show interpretWordLiteral? ⟨spans 43,.decimal "1"⟩=some one from rfl))) StrictWordBinaryDenotes.add
  have madeOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) (source spans)
      (.sourceClosure (source spans) owner inputs.names (up e)) (heap st) := .creation .inferred
  have actualMadeOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) actualFn
      (.sourceClosure actualFn owner inputs.names (up e)) (heap st) := by rw [actualFnEq]; exact madeOld
  have actualArgOld : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) actualArg (.word w) (heap st) := by rw [actualArgEq]; exact argOld
  have betaCall : ClosedSourceBodyEvaluates owner (("p",Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
      ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),.word w)::up e) (heap st) (body spans) (RuntimeValue.ofCore (value w)) (heap st) := by
    simpa only [entry,env,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids,up,List.map_cons,RuntimeValue.ofCore] using beta
  have grouped : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) actual (RuntimeValue.ofCore (value w)) (heap st) := by
    rw [actualEq]; exact .call .inferred (.group madeOld) argOld betaCall
  proof beta; proof h.2.2.2.1; proof bodyPath; proof grouped
  check (decide (Resolved.freshLocalId owner inputs.ids=sid 32 ∧ Resolved.freshLocalId owner (entry owner inputs).ids=sid 33)) "two fresh shadows preserve old opaque p"
  coreRuns (bodyPath [])
  for fuel in [0,5,6,9] do
    match run : evaluateClosedSourceBody? fuel owner (entry owner inputs).names (up (env owner inputs e w)) (heap st) actualBody with
    | none => check (fuel<6) "body fixture depth exhaustion"
    | some (a,z) => endpoint (a:=a) (z:=z) bodyExact (by simpa only [actualBodyEq] using evaluateClosedSourceBody?_sound run); check (fuel≥6) "body fixture depth success"
  closedRuns 2 actualArgOld (fun a => proof (a.deterministic actualArgOld))
  closedRuns 1 actualMadeOld (fun a => proof (a.deterministic actualMadeOld))
  match made : evaluateClosedSourceExpression? 1 owner inputs.names (up e) (heap st) actualFn with
  | none => throw (IO.userError "actual creation")
  | some (actualClosure,creationStore) =>
    have creation : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) (source spans) actualClosure creationStore := by simpa only [actualFnEq] using evaluateClosedSourceExpression?_sound made
    have ceq := creation.deterministic madeOld
    check ((match actualClosure with | .sourceClosure sf so sn se => sf==actualFn && so==owner && sn==inputs.names && se.mapM (fun r => (r.2.toCore?).map (r.1,·))==some e | _ => false) && creationStore.mapM RuntimeValue.toCore?==some st) "all saved creation fields"
    let cr := rows actualClosure w
    let fn := calleeOf savedActual
    let arg := argumentOf savedActual
    have fnEq : fn=(⟨sp 0 6,.identifier ⟨sp 0 6,"picked"⟩⟩ : Syntax.Expr) := by simp only [fn,savedEq,picked,calleeOf]
    have argEq : arg=(⟨sp 7 8,.identifier ⟨sp 7 8,"w"⟩⟩ : Syntax.Expr) := by simp only [arg,savedEq,picked,argumentOf]
    have fetchOld : ClosedSourceExpressionEvaluates caller names cr creationStore fn actualClosure creationStore := by rw [fnEq]; exact .reference .head (.tail (by decide) .head)
    have savedArg : ClosedSourceExpressionEvaluates caller names cr creationStore arg (.word w) (heap st) := by rw [ceq.2,argEq]; exact .reference (.tail (by change "picked" ≠ "w"; decide) .head) .head
    let savedCoreRows := [Core.Value.closure .word .word core e.values,.word w,q,.cellRef .word 900]
    have savedCorePath : Core.Steps (1+1+cost w+3) (.initial (.apply (.var 0) (.var 1)) savedCoreRows st) (.final (value w) st) :=
      CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) (bodyPath [])
    coreRuns savedCorePath
    match fetched : evaluateClosedSourceExpression? 1 caller names cr creationStore fn with
    | none => throw (IO.userError "actual saved callee")
    | some (actualFn,calleeStore) =>
      have fe := evaluateClosedSourceExpression?_sound fetched
      have feq := fe.deterministic fetchOld
      match arun : evaluateClosedSourceExpression? 1 caller names cr calleeStore arg with
      | none => throw (IO.userError "actual saved argument")
      | some (actualArg,argumentStore) =>
        have ae := evaluateClosedSourceExpression?_sound arun
        have aeq := (show ClosedSourceExpressionEvaluates caller names cr creationStore arg actualArg argumentStore from by simpa only [feq.2] using ae).deterministic savedArg
        match brun : evaluateClosedSourceBody? 6 owner (entry owner inputs).names ((Resolved.freshLocalId owner inputs.ids,actualArg)::up e) argumentStore actualBody with
        | none => throw (IO.userError "actual body from actual saved argument")
        | some (bv,bs) =>
          have bodyActual := evaluateClosedSourceBody?_sound brun
          have alignedBody : ClosedSourceBodyEvaluates owner (entry owner inputs).names (up (env owner inputs e w)) (heap st) (body spans) bv bs := by
            simpa only [aeq.1,aeq.2,actualBodyEq,env,up,List.map_cons,RuntimeValue.ofCore] using bodyActual
          proof (alignedBody.deterministic beta)
          endpoint (a:=bv) (z:=bs) bodyExact alignedBody
          have actualCallee : ClosedSourceExpressionEvaluates caller names cr creationStore fn
              (.sourceClosure (source spans) owner inputs.names (up e)) calleeStore := by simpa only [feq.1,ceq.1] using fe
          have actualArgument : ClosedSourceExpressionEvaluates caller names cr calleeStore arg (.word w) argumentStore := by simpa only [aeq.1] using ae
          have actualBeta : ClosedSourceBodyEvaluates owner (("p",Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
              ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),.word w)::up e) argumentStore (body spans) bv bs := by
            simpa only [aeq.1,actualBodyEq,entry,LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using bodyActual
          have actualCall : ClosedSourceExpressionEvaluates caller names cr creationStore
              ⟨sp 0 9,.call fn ⟨sp 6 9,[arg]⟩⟩ bv bs := .call .inferred actualCallee actualArgument actualBeta
          have actualSavedCall : ClosedSourceExpressionEvaluates caller names cr creationStore savedActual bv bs := by
            rw [savedEq]; simpa only [fnEq,argEq,picked] using actualCall
          proof actualSavedCall
          consumeCore (a:=bv) (z:=bs) (Core.steps_from_initial_sound (bodyPath []))
            (closedSourceExpectedDataLambda_invocation_core_iff (callSpan:=sp 0 9) (argumentsSpan:=sp 6 9) .inferred gate checked same
              actualCallee (by simpa only [aeq.2,RuntimeValue.ofCore,heap] using actualArgument)) actualCall
        let ss := fun i => if i=38 then sp 0 9 else if i=39 then sp 6 9 else spans i
        have creation1 : ClosedSourceExpressionEvaluates owner inputs.names (up e) (heap st) (source ss) actualClosure creationStore := creation
        have fetched1 : ClosedSourceExpressionEvaluates caller names cr creationStore fn actualClosure creationStore := by simpa only [feq.1,feq.2] using fe
        have arg1 : ClosedSourceExpressionEvaluates caller names cr creationStore arg (.word w) (heap st) := by simpa only [feq.2,aeq.1,aeq.2] using ae
        have all := ExpectedWordStrictDataImages.calls_original_and_all_actual_images ss owner inputs e st c same (sid 7) .head .head 0 .head caller names cr fn arg actualClosure creationStore creation1 fetched1 arg1
        have path := all.2.2.1
        have savedOld : ClosedSourceExpressionEvaluates caller names cr creationStore (call ss fn arg) (RuntimeValue.ofCore (value w)) (heap st) := all.2.2.2.2.1
        have savedExact : ∀ a z, ClosedSourceExpressionEvaluates caller names cr creationStore (call ss fn arg) a z ↔ a=RuntimeValue.ofCore (value w) ∧ z=heap st := all.2.2.2.2.2.2
        coreRuns (path [])
        have actualSaved : ClosedSourceExpressionEvaluates caller names cr creationStore savedActual (RuntimeValue.ofCore (value w)) creationStore := by rw [savedEq,ceq.2]; simpa [ceq.2,call,ss,fnEq,argEq,picked] using savedOld
        closedRuns 7 actualSaved (fun {a z} run => endpoint (a:=a) (z:=z) savedExact (by simpa [savedEq,call,ss,fnEq,argEq,picked] using run))
        have original := ExpectedWordStrictDataImages.calls_original_and_all_actual_images spans owner inputs e st c same (sid 7) .head .head 0 .head caller names cr fn arg actualClosure creationStore creation fetched1 arg1
        have full := original.2.2.1; have direct := original.2.2.2.1; have exactDirect := original.2.2.2.2.2.1
        coreRuns (full [])
        closedRuns 7 direct (fun run => endpoint exactDirect run)
        closedRuns 7 grouped (fun {a z} run => consumeCore (a:=a) (z:=z) (Core.steps_from_initial_sound (bodyPath []))
          (closedSourceExpectedDataLambda_invocation_core_iff (callSpan:=spans 38) (argumentsSpan:=spans 39) .inferred gate checked same
            (.group (span:=spans 46) madeOld) (by simpa only [RuntimeValue.ofCore,heap] using argOld))
          (by simpa only [actualEq,whole,call] using run))
end Tests.ParsedExpectedWordStrictDataBridge
open Tests.ParsedExpectedWordStrictDataBridge in
def Tests.frontendParsedExpectedWordStrictDataBridgeTests : IO Unit := do
  let q := Solcore.Core.Value.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let mut count := 0
  for c in [0,1,2^256-1,2^256-2,2^255] do
    for st in [[],[q,.cellRef .word 900,.hostFunction .storageWrite,.unit]] do
      exercise (Solcore.Core.Word.ofNatModulo c) q st; count := count+1
  check (count==10) "five boundary Words/two stores/both branches"

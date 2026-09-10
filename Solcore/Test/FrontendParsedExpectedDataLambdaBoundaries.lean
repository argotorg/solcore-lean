import Solcore.Frontend.ExpectedDataLambdaInvocationProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties
import Solcore.Frontend.LocalExpressionCostCorrespondence
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalFunctionApplicationStepComposition
import Solcore.Syntax.Parser.Term
/- Independent raw original witnesses precede every search. Failed admission
does not erase annotations, saved rows, source closures or an unrelated store row. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedExpectedDataLambdaBoundaries
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private theorem noImage {v : RuntimeValue} (h : v.toCore?=none) : ¬ ∃ c, v=RuntimeValue.ofCore c := by
  rintro ⟨c,rfl⟩; have r := RuntimeValue.toCore?_ofCore c; rw [h] at r; cases r
private theorem noStoreImage {s : List RuntimeValue} (h : s.mapM RuntimeValue.toCore?=none) : ¬ ∃ c : Core.Store, s=c.map RuntimeValue.ofCore := by
  rintro ⟨c,rfl⟩
  have r : (c.map RuntimeValue.ofCore).mapM RuntimeValue.toCore?=some c := by
    clear h
    induction c with | nil => rfl | cons a as ih => simp only [List.map_cons,List.mapM_cons,RuntimeValue.toCore?_ofCore,ih,pure,bind,Option.bind_some]
  rw [h] at r; cases r
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedBoundaries",by decide⟩],by decide⟩⟩,178⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign (n : Nat) : Resolved.LocalId := ⟨{owner with declarationIndex:=901},n⟩
private def inputs : LocalTypeInputs := ⟨[⟨"x",sid 7,.bool⟩,⟨"saved",sid 31,.unit⟩,⟨"c",sid 11,.bool⟩,
  ⟨"d",sid 20,.bool⟩,⟨"arg",sid 9,.unit⟩,⟨"other",foreign 700,.unit⟩,⟨"x",foreign 701,.word⟩],by decide⟩
private def types : TypeNameTable := [(["Unit"],.unit),(["Word"],.word)]
private def up (e : Resolved.Environment) := e.map (fun r => (r.1,RuntimeValue.ofCore r.2))
private def env (a q : Core.Value) (c : Bool) : Resolved.Environment :=
  [(sid 7,.bool false),(sid 31,q),(sid 11,.bool c),(sid 20,.bool true),(sid 9,a),(foreign 700,a),(foreign 701,.word (Core.Word.ofNatModulo 99))]
private def parsed (text : String) : IO Syntax.Expr := do
  let f : Syntax.SourceFile := ⟨⟨.main,"expected-data-boundaries.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex f | throw (IO.userError "lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial f lexed) with
  | .ok src next => check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && src.span==Syntax.SourceSpan.fullFile f) "original complete source/EOF/diagnostics"; return src
  | _ => throw (IO.userError "original boundary parser")
private structure Shape (src : Syntax.Expr) where
  name : Syntax.Identifier
  body : Syntax.Block
  evidence : SourceUnaryLambdaShape src name body
private def shape (src : Syntax.Expr) : IO (Shape src) := do
  match original : src with
  | ⟨_,.lambda _ ⟨_,[⟨_,.inferred n⟩]⟩ _ b⟩ => return ⟨n,b,by rw [original]; exact .inferred⟩
  | ⟨_,.lambda _ ⟨_,[⟨_,.typed none n _⟩]⟩ _ b⟩ => return ⟨n,b,by rw [original]; exact .typed⟩
  | _ => throw (IO.userError "independent original raw unary shape")
private structure AC (e : Resolved.Environment) (s : Core.Store) (src : Syntax.Expr) where
  core : Core.Expr
  value : Core.Value
  gate : ClosedSourceDataExpression src
  old : LocalExpressionEvaluatesWithCost inputs.names e s src value s 1
  closed : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore value) (s.map RuntimeValue.ofCore)
  path : ∀ k, Core.Steps 1 ⟨.eval core e.values,k,s⟩ ⟨.ret value,k,s⟩
private def arg (a q : Core.Value) (s : Core.Store) (src : Syntax.Expr) : IO (AC (env a q true) s src) := do
  match original : src with
  | ⟨_,.identifier ⟨_ ,"arg"⟩⟩ =>
    have n : LocalNameTable.Lookup inputs.names "arg" (sid 9) := LocalNameTable.lookup?_iff.mp rfl
    have f : Resolved.LocalScope.Lookup (env a q true) (sid 9) a := .tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
    have m : Resolved.LocalScope.Lookup (up (env a q true)) (sid 9) (RuntimeValue.ofCore a) := .tail (by change sid 7≠sid 9; decide) (.tail (by change sid 31≠sid 9; decide) (.tail (by change sid 11≠sid 9; decide) (.tail (by change sid 20≠sid 9; decide) .head)))
    return ⟨.var 4,a,by rw [original]; exact .reference,by rw [original]; exact .identifier n f,
      by rw [original]; exact .reference n m,fun _ => .cons (.var rfl) .refl⟩
  | ⟨_,.literal ⟨ls,.decimal "7"⟩⟩ =>
    let w := Core.Word.ofNatModulo 7
    have meaning : WordLiteralDenotes ⟨ls,.decimal "7"⟩ w := interpretWordLiteral?_sound (by rfl)
    return ⟨.word w,.word w,by rw [original]; exact .literal,by rw [original]; exact .wordLiteral meaning,
      by rw [original]; simpa only [RuntimeValue.ofCore] using ClosedSourceExpressionEvaluates.wordLiteral meaning,fun _ => .cons .word .refl⟩
  | _ => throw (IO.userError "original boundary argument")
private def identity (text : String) (ret : Core.Ty) (headerYes checkedYes : Bool) (a q : Core.Value) (s : Core.Store) : IO Unit := do
  let src ← parsed text; let e := env a q true
  match original : src with
  | ⟨cs,.call ⟨gs,.group fs⟩ ⟨args,[argument]⟩⟩ =>
    let h ← shape fs; let ac ← arg a q s argument
    match bodyShape : h.body with
    | ⟨bs,[⟨rs,.returnStmt (some ⟨es,.identifier name⟩)⟩]⟩ =>
      if equalName : name.value=h.name.value then
        have fragment : ClosedSourceDataBody h.body := by rw [bodyShape]; exact .expression .reference
        have body : ClosedSourceBodyEvaluates owner ((h.name.value,Resolved.freshLocalId owner (inputs.names.map Prod.snd))::inputs.names)
            ((Resolved.freshLocalId owner (inputs.names.map Prod.snd),RuntimeValue.ofCore ac.value)::up e) (s.map RuntimeValue.ofCore) h.body (RuntimeValue.ofCore ac.value) (s.map RuntimeValue.ofCore) := by
          rw [bodyShape]; exact .expression (.reference (equalName ▸ LocalNameTable.Lookup.head) .head)
        have oldBody : ComputationReturnTreeEvaluatesWithCost LocalExpressionEvaluatesWithCost owner ((h.name.value,sid 32)::inputs.names) ((sid 32,ac.value)::e) s h.body ac.value s 1 := by
          rw [bodyShape]; exact .expression (.identifier (equalName ▸ LocalNameTable.Lookup.head) .head)
        have made : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) ⟨gs,.group fs⟩ (.sourceClosure fs owner inputs.names (up e)) (s.map RuntimeValue.ofCore) := .group (.creation h.evidence)
        have closed : ClosedSourceExpressionEvaluates owner inputs.names (up e) (s.map RuntimeValue.ofCore) src (RuntimeValue.ofCore ac.value) (s.map RuntimeValue.ofCore) := by rw [original]; exact .call h.evidence made ac.closed body
        let core := Core.Expr.apply (.lambda .unit ret (.var 0)) ac.core
        have beta : Core.Evaluates (ac.value::e.values) s (.var 0) ac.value s := .var rfl
        have full (k) : Core.Steps 6 ⟨.eval core e.values,k,s⟩ ⟨.ret ac.value,k,s⟩ := CostStepComposition.apply (.cons .lambda .refl) (ac.path _) (.cons (.var rfl) .refl)
        proof oldBody; proof closed; proof (Core.steps_from_initial_sound (full []))
        check ((declareExpectedUnaryLambdaHeader? types owner inputs fs (.function .unit ret)).isSome==headerYes) "actual header disagreement versus body mismatch"
        match run : evaluateClosedSourceExpression? 3 owner inputs.names (up e) (s.map RuntimeValue.ofCore) src with
        | none => throw (IO.userError "raw original ignores annotations and expected type")
        | some (mv,ms) =>
          have actual := evaluateClosedSourceExpression?_sound run
          proof (actual.deterministic closed)
          if checked : elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs fs (.function .unit ret)=some (.lambda .unit ret (.var 0)) then
            check checkedYes "only the declared checked boundary is admitted"
            have image {v st} := closedSourceExpectedDataLambda_invocation_core_iff h.evidence fragment checked (show e.ids=inputs.context.ids from rfl) made ac.closed (callSpan:=cs) (argumentsSpan:=args) (actualValue:=v) (actualFinal:=st)
            have transported := (image (v:=mv) (st:=ms)).mp (by simpa only [original] using actual)
            proof ((image (v:=mv) (st:=ms)).mpr transported)
            proof ((image (v:=RuntimeValue.ofCore ac.value) (st:=s.map RuntimeValue.ofCore)).mpr ⟨ac.value,s,rfl,rfl,beta⟩)
            match coreRun : Core.runStateful 6 (.initial core e.values s) with
            | .done v final => proof (Core.evaluation_deterministic (Core.runStateful_evaluation_sound coreRun) (Core.steps_from_initial_sound (full []))); check (mv.toCore?==some v && (ms.mapM RuntimeValue.toCore?)==some final) "actual complete checked-boundary endpoint"
            | _ => throw (IO.userError "actual independent Core cost 6")
            check (Core.infer? inputs.context.values core).isNone "expected checked lambda does not imply whole-call typing"
            check (elaborateLocalExpression? inputs.names inputs.context argument==some (ac.core,.word)) "actual original argument is Word, not checked lambda domain Unit"
          else check (!checkedYes && (elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs fs (.function .unit ret)).isNone) "actual checker profile absence, never a raw language fault"
      else throw (IO.userError "original identity parameter reference")
    | _ => throw (IO.userError "original identity body")
  | _ => throw (IO.userError "original grouped identity call")
private structure RC (names : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (src : Syntax.Expr) where
  value : RuntimeValue
  gate : ClosedSourceDataExpression src
  evidence : ClosedSourceExpressionEvaluates owner names rows store src value store
private def rawExpr (names : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (src : Syntax.Expr) : IO (RC names rows store src) := do
  match original : src with
  | ⟨_,.identifier name⟩ =>
    match named : names.lookup? name.value with
    | some i => match found : rows.lookup? i with
      | some v => return ⟨v,by rw [original]; exact .reference,by rw [original]; exact .reference (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent raw row")
    | none => throw (IO.userError "independent raw name")
  | ⟨_,.group child⟩ => let h ← rawExpr names rows store child; return ⟨h.value,by rw [original]; exact .group h.gate,by rw [original]; exact .group h.evidence⟩
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
    let l ← rawExpr names rows store left; let r ← rawExpr names rows store right
    return ⟨.pair l.value r.value,by rw [original]; exact .pair l.gate r.gate,by rw [original]; exact .pair l.evidence r.evidence⟩
  | ⟨_,.conditional guard _ yes _ no⟩ =>
    let g ← rawExpr names rows store guard; let a ← rawExpr names rows store yes; let b ← rawExpr names rows store no
    match value : g.value with
    | .bool c => return ⟨if c then a.value else b.value,by rw [original]; exact .conditional g.gate a.gate b.gate,
        by rw [original]; cases c <;> first | exact .conditionalTrue (value ▸ g.evidence) a.evidence | exact .conditionalFalse (value ▸ g.evidence) b.evidence⟩
    | _ => throw (IO.userError "independent raw Bool condition")
  | _ => throw (IO.userError "original raw data-child certificate")
termination_by sizeOf src
private structure RB (names : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (src : Syntax.Block) where
  value : RuntimeValue
  gate : ClosedSourceDataBody src
  evidence : ClosedSourceBodyEvaluates owner names rows store src value store
private def rawBody (names : LocalNameTable) (rows : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (src : Syntax.Block) : IO (RB names rows store src) := do
  match original : src with
  | ⟨bs,[⟨ls,.letDecl name (some ann) (some init)⟩,⟨rs,.returnStmt (some result)⟩]⟩ =>
    let a ← rawExpr names rows store init
    let fresh := Resolved.freshLocalId owner (names.map Prod.snd)
    let b ← rawExpr ((name.value,fresh)::names) ((fresh,a.value)::rows) store result
    return ⟨b.value,by rw [original]; exact .binding a.gate (.expression b.gate),by rw [original]; exact .binding a.evidence (.expression b.evidence)⟩
  | _ => throw (IO.userError "original raw pre-shadow initializer")
private def rawText := "(lam(x){let x:Unit=(x);return c?(x,saved):(saved,x);})(d?arg:other)"
private def rawBoundary (src : Syntax.Expr) (rows : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
    (aligned valueImage storeImage : Bool) : IO Unit := do
  match original : src with
  | ⟨cs,.call ⟨gs,.group fs⟩ ⟨args,[argument]⟩⟩ =>
    let h ← shape fs; let ac ← rawExpr inputs.names rows store argument
    let fresh := Resolved.freshLocalId owner (inputs.names.map Prod.snd)
    let bc ← rawBody ((h.name.value,fresh)::inputs.names) ((fresh,ac.value)::rows) store h.body
    have made : ClosedSourceExpressionEvaluates owner inputs.names rows store ⟨gs,.group fs⟩ (.sourceClosure fs owner inputs.names rows) store := .group (.creation h.evidence)
    have closed : ClosedSourceExpressionEvaluates owner inputs.names rows store src bc.value store := by rw [original]; exact .call h.evidence made ac.evidence bc.evidence
    proof closed; proof bc.gate
    check (decide (rows.ids=inputs.context.ids)==aligned) "whole ordered saved IDs, not lookup equivalence"
    check (decide (fresh=sid 32 ∧ Resolved.freshLocalId owner (((h.name.value,fresh)::inputs.names).map Prod.snd)=sid 33)) "runtime-only collisions do not alter names-only freshness"
    check ((elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs fs (.function .unit (.product .unit .unit))).isSome) "actual lambda checker cannot establish runtime alignment or image"
    match run : evaluateClosedSourceExpression? 6 owner inputs.names rows store src with
    | none => throw (IO.userError "raw preserved body succeeds before static/image boundaries")
    | some (mv,ms) =>
      proof ((evaluateClosedSourceExpression?_sound run).deterministic closed)
      check (mv.toCore?.isSome==valueImage && (ms.mapM RuntimeValue.toCore?).isSome==storeImage && ac.value.toCore?.isSome==valueImage) "entire actual payload and store, no dropped nonimage row"
      match noValue : mv.toCore? with | none => proof (noImage noValue) | some _ => pure ()
      match noStore : ms.mapM RuntimeValue.toCore? with | none => proof (noStoreImage noStore) | some _ => pure ()
  | _ => throw (IO.userError "original raw grouped application")
private def nonimageArgument (source callSrc : Syntax.Expr) (poison : RuntimeValue) (absent : poison.toCore?=none)
    (a q : Core.Value) (c : Bool) (s : Core.Store) : IO Unit := do
  match outer : source, original : callSrc with
  | ⟨_,.call ⟨_,.group fs⟩ _⟩,⟨cs,.call ⟨sp,.identifier ⟨np,"picked"⟩⟩ ⟨aps,[⟨sa,.identifier ⟨na,"arg"⟩⟩]⟩⟩ =>
    let h ← shape fs; let e := env a q c
    let names : LocalNameTable := [("picked",sid 80),("arg",sid 81)]
    let fn := RuntimeValue.sourceClosure fs owner inputs.names (up e)
    let rows : Resolved.LocalScope RuntimeValue := [(sid 80,fn),(sid 81,poison)]
    let fresh := Resolved.freshLocalId owner (inputs.names.map Prod.snd)
    let bc ← rawBody ((h.name.value,fresh)::inputs.names) ((fresh,poison)::up e) (s.map RuntimeValue.ofCore) h.body
    have callee : ClosedSourceExpressionEvaluates owner names rows (s.map RuntimeValue.ofCore) ⟨sp,.identifier ⟨np,"picked"⟩⟩ fn (s.map RuntimeValue.ofCore) := .reference .head .head
    have arg : ClosedSourceExpressionEvaluates owner names rows (s.map RuntimeValue.ofCore) ⟨sa,.identifier ⟨na,"arg"⟩⟩ poison (s.map RuntimeValue.ofCore) := .reference (.tail (by change "picked"≠"arg"; decide) .head) (.tail (by decide) .head)
    have closed : ClosedSourceExpressionEvaluates owner names rows (s.map RuntimeValue.ofCore) callSrc bc.value (s.map RuntimeValue.ofCore) := by rw [original]; exact .call h.evidence callee arg bc.evidence
    proof closed; proof (noImage absent)
    check (decide (e.ids=inputs.context.ids) && (elaborateExpectedComputationLambda? elaborateLocalExpression? types owner inputs fs (.function .unit (.product .unit .unit))).isSome) "saved Core capture is aligned and checked; only caller argument lacks an image"
    match run : evaluateClosedSourceExpression? 6 owner names rows (s.map RuntimeValue.ofCore) callSrc with
    | some (mv,ms) =>
      proof ((evaluateClosedSourceExpression?_sound run).deterministic closed)
      match failed : mv.toCore? with | none => proof (noImage failed) | some _ => throw (IO.userError "actual source closure argument unexpectedly projected")
      check ((ms.mapM RuntimeValue.toCore?)==some s) "entire raw argument call store remains a Core image"
    | none => throw (IO.userError "independent raw nonimage argument invocation")
  | _,_ => throw (IO.userError "original nonimage-argument call")
end Tests.ParsedExpectedDataLambdaBoundaries
open Tests.ParsedExpectedDataLambdaBoundaries in
def Tests.frontendParsedExpectedDataLambdaBoundaryTests : IO Unit := do
  let a := Solcore.Core.Value.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let q := Solcore.Core.Value.cellRef (.function .unit .word) 900
  let store := [q,a,Solcore.Core.Value.hostFunction .storageWrite]
  identity "(lam(x:Unknown){return x;})(arg)" .unit false false a q store
  identity "(lam(x:Unit)->Unknown{return x;})(arg)" .unit false false a q store
  identity "(lam(x:Word){return x;})(arg)" .unit false false a q store
  identity "(lam(x:Unit)->Word{return x;})(arg)" .unit false false a q store
  identity "(lam(x){return x;})(arg)" .word true false a q store
  identity "(lam(x:Unit){return x;})(7)" .unit true true a q store
  let src ← parsed rawText; let inert ← parsed "lam(){return absent;}"; let called ← parsed "picked(arg)"
  let poison := Solcore.Frontend.RuntimeValue.sourceClosure inert owner [] [(sid 700,.bool true)]
  for c in [false,true] do
    let rows := up (env a q c); let heap := store.map Solcore.Frontend.RuntimeValue.ofCore
    rawBoundary src rows heap true true true
    rawBoundary src rows.tail heap false true true
    rawBoundary src rows.reverse heap false true true
    rawBoundary src ((sid 7,.unit)::rows) heap false true true
    rawBoundary src ((sid 32,poison)::rows) heap false true true
    rawBoundary src rows (heap++[poison]) true true false
    rawBoundary src (rows.map (fun r => (r.1,if r.1==sid 9 then poison else r.2))) heap true false true
    nonimageArgument src called poison (by simp only [poison,Solcore.Frontend.RuntimeValue.toCore?]) a q c store

import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.LocalExpressionEvaluator
import Solcore.Frontend.LocalExpression
import Solcore.Syntax.Parser.Term

/- Original gate and two independent derivations precede semantic search.
Actual mixed endpoints enter each iff unchanged; all existential elimination stays in Prop. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceCoreImage
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ClosedSourceCoreImage",by decide⟩],by decide⟩⟩,171⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=900},700⟩
private def names : LocalNameTable := [("x",sid 7),("c",sid 3),("y",sid 8),("z",foreign),("x",sid 9)]
private def env (c : Core.Value) (x y z shadow : Core.Value) (extra : Resolved.Environment) :=
  [(sid 8,y),(sid 7,x),(sid 3,c),(foreign,z),(sid 7,shadow)] ++ extra
private def up (environment : Resolved.Environment) := environment.map (fun e => (e.1,RuntimeValue.ofCore e.2))
private def seven : Core.Word := ⟨7,by decide⟩
private def result (x y z : Core.Value) := Core.Value.pair x (.pair .unit (.pair (.word seven) (.pair y z)))
private structure Cert (table : LocalNameTable) (environment : Resolved.Environment)
    (store : Core.Store) (source : Syntax.Expr) (value : Core.Value) (cost : Nat) : Type where
  fragment : ClosedSourceDataExpression source
  closed : ClosedSourceExpressionEvaluates owner table (up environment) (store.map RuntimeValue.ofCore)
    source (RuntimeValue.ofCore value) (store.map RuntimeValue.ofCore)
  old : LocalExpressionEvaluatesWithCost table environment store source value store cost
private theorem mapped {environment : Resolved.Environment} {id : Resolved.LocalId} {value : Core.Value}
    (h : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup (up environment) id (RuntimeValue.ofCore value) := by
  induction h with
  | head => exact .head
  | tail different _ ih => exact .tail different ih
private def reference (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) (spelling : String) (id : Resolved.LocalId) (value : Core.Value)
    (named : LocalNameTable.Lookup table spelling id) (found : Resolved.LocalScope.Lookup environment id value) :
    IO (Cert table environment store source value 1) := do
  match shape : source with
  | ⟨_,.identifier name⟩ =>
    if h : name.value=spelling then
      have n : LocalNameTable.Lookup table name.value id := h ▸ named
      return by rw [shape]; exact ⟨.reference,.reference n (mapped found),.identifier n found⟩
    else throw (IO.userError "original reference spelling")
  | _ => throw (IO.userError "original reference")
private def lastZ (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) (z : Core.Value) (grouped : Bool)
    (named : LocalNameTable.Lookup table "z" foreign) (found : Resolved.LocalScope.Lookup environment foreign z) :
    IO (Cert table environment store source z 1) := do
  if grouped then
    match shape : source with
    | ⟨span,.group child⟩ =>
      check (span.startByte==13 && span.endByte==16) "original grouped z range"
      let h ← reference table environment store child "z" foreign z named found
      return by rw [shape]; exact ⟨.group h.fragment,.group h.closed,.group h.old⟩
    | _ => throw (IO.userError "original group")
  else reference table environment store source "z" foreign z named found
private def branch (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) (a b : String) (i j : Resolved.LocalId) (x y z : Core.Value) (grouped : Bool)
    (nx : LocalNameTable.Lookup table a i) (ny : LocalNameTable.Lookup table b j)
    (nz : LocalNameTable.Lookup table "z" foreign) (fx : Resolved.LocalScope.Lookup environment i x)
    (fy : Resolved.LocalScope.Lookup environment j y) (fz : Resolved.LocalScope.Lookup environment foreign z) :
    IO (Cert table environment store source (result x y z) 17) := do
  match shape : source with
  | ⟨span,.tuple ⟨ts,[first,⟨_,.tuple ⟨_,[]⟩⟩,⟨_,.literal ⟨litSpan,.decimal spelling⟩⟩,⟨_,.tuple ⟨_,[second,last]⟩⟩]⟩⟩ =>
    check (span==ts) "original tuple span"
    if h : spelling="7" then
      let hx ← reference table environment store first a i x nx fx
      let hy ← reference table environment store second b j y ny fy
      let hz ← lastZ table environment store last z grouped nz fz
      have meaning : WordLiteralDenotes ⟨litSpan,.decimal spelling⟩ seven := by
        subst spelling
        exact .decimal (by decide) (.cons (.decimal (digit := 7) (by decide) (by decide)) .nil)
      return by
        rw [shape]; refine ⟨.many hx.fragment (.many .unit (.pair .literal (.pair hy.fragment hz.fragment))), ?_,
          .many hx.old (.many .unit (.pair (.wordLiteral meaning) (.pair hy.old hz.old)))⟩
        simp only [result,RuntimeValue.ofCore]
        exact .many hx.closed (.many .unit (.pair (.wordLiteral meaning) (.pair hy.closed hz.closed)))
    else throw (IO.userError "original decimal seven")
  | _ => throw (IO.userError "original four-tuple")
private def witness (source : Syntax.Expr) (c : Bool) (x y z shadow : Core.Value)
    (extra : Resolved.Environment) (store : Core.Store) :
    IO (Cert names (env (.bool c) x y z shadow extra) store source
      (if c then result x y z else result y x z) 20) := do
  let e := env (.bool c) x y z shadow extra
  have nx : LocalNameTable.Lookup names "x" (sid 7) := .head
  have nc : LocalNameTable.Lookup names "c" (sid 3) := .tail (by decide) .head
  have ny : LocalNameTable.Lookup names "y" (sid 8) := .tail (by decide) (.tail (by decide) .head)
  have nz : LocalNameTable.Lookup names "z" foreign := .tail (by decide) (.tail (by decide) (.tail (by decide) .head))
  have fx : Resolved.LocalScope.Lookup e (sid 7) x := .tail (by decide) .head
  have fc : Resolved.LocalScope.Lookup e (sid 3) (.bool c) := .tail (by decide) (.tail (by decide) .head)
  have fy : Resolved.LocalScope.Lookup e (sid 8) y := .head
  have fz : Resolved.LocalScope.Lookup e foreign z := .tail (by decide) (.tail (by decide) (.tail (by decide) .head))
  match shape : source with
  | ⟨span,.conditional guard q yes colon no⟩ =>
    check (span.startByte==0 && span.endByte==33 && q.startByte==1 && q.endByte==2 && colon.startByte==18 && colon.endByte==19 && yes.span.startByte==2 && yes.span.endByte==18 && no.span.startByte==19 && no.span.endByte==33) "original conditional ranges"
    let hc ← reference names e store guard "c" (sid 3) (.bool c) nc fc
    let ht ← branch names e store yes "x" "y" (sid 7) (sid 8) x y z true nx ny nz fx fy fz
    let hf ← branch names e store no "y" "x" (sid 8) (sid 7) y x z false ny nx nz fy fx fz
    return by
      rw [shape]; refine ⟨.conditional hc.fragment ht.fragment hf.fragment, ?_, ?_⟩
      · cases c <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact .conditionalFalse (by simpa only [RuntimeValue.ofCore] using hc.closed) hf.closed
        · exact .conditionalTrue (by simpa only [RuntimeValue.ofCore] using hc.closed) ht.closed
      · cases c <;> first | exact .ifTrue hc.old ht.old | exact .ifFalse hc.old hf.old
  | _ => throw (IO.userError "original conditional")
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"closed-source-core-image.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && source.span==Syntax.SourceSpan.fullFile file) "complete original AST/span"
    return source
  | _ => throw (IO.userError "original parser")
-- Context identity order is exact; the opaque runtime payloads are deliberately not assumed typed.
private def context (e : Resolved.Environment) (bad : Bool := false) : Resolved.Context :=
  e.map (fun row => (row.1,if row.1=sid 3 then .bool else if bad && row.1==sid 8 then .word else .unit))
private def coreChecks (table : LocalNameTable) (e : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) (actual : Core.Value) (cost : Nat) (mv : RuntimeValue) (ms : List RuntimeValue)
    (g : ClosedSourceDataExpression source)
    (closed : ClosedSourceExpressionEvaluates owner table (up e) (store.map RuntimeValue.ofCore) source mv ms)
    (old : LocalExpressionEvaluatesWithCost table e store source actual store cost) : IO Unit := do
  match resolvedResult : resolveLocalExpression? table source with
  | none => throw (IO.userError "whole resolution")
  | some resolved =>
    let resolution := resolveLocalExpression?_sound resolvedResult
    match lowerResult : resolved.lower? (Resolved.LocalScope.ids e) with
    | none => throw (IO.userError "whole lowering at runtime IDs")
    | some loweredCore =>
      let lowered := Resolved.Expr.lower?_sound lowerResult
      have image := (g.core_evaluates_iff resolution lowered).mp closed
      proof image
      match accepted : elaborateLocalExpression? table (context e) source with
      | none => throw (IO.userError "whole checker")
      | some (core,ty) =>
        have sameIds : Resolved.LocalScope.ids e = Resolved.LocalScope.ids (context e) := by
          simp only [Resolved.LocalScope.ids,context,List.map_map,Function.comp_def]
        have sameCore : loweredCore=core := by
          obtain ⟨r,rr,ll,_⟩ := elaborateLocalExpression?_sound accepted
          cases resolution.deterministic rr
          exact lowered.deterministic (sameIds ▸ ll)
        check (core==loweredCore && ty==.product .unit (.product .unit (.product .word (.product .unit .unit)))) "actual checked and lowered Core/type"
        let actualLowered : Resolved.Lowers (Resolved.LocalScope.ids e) resolved core := sameCore ▸ lowered
        for fuel in [0,cost-1,cost,cost+1] do
          match ran : Core.runStateful fuel (Core.State.initial core (Resolved.LocalScope.values e) store) with
          | .done value finalStore =>
            let actualCore := Core.runStateful_evaluation_sound ran
            let actualOld := (elaborateLocalExpression?_run_done_sound accepted sameIds ran).1
            proof (actualOld.deterministic old.erase)
            proof (show ClosedSourceExpressionEvaluates owner table (up e) (store.map RuntimeValue.ofCore) source mv ms from by
              obtain ⟨v,s,hv,hs,ev⟩ := image
              have same := ((resolution.core_evaluates_iff lowered).mpr ev).deterministic actualOld
              exact (g.core_evaluates_iff resolution actualLowered).mpr
                ⟨value,finalStore,hv.trans (congrArg _ same.1),hs.trans (congrArg _ same.2),actualCore⟩)
            proof ((old.runStateful_done_iff (fuel := fuel) resolution actualLowered).mp (by
              have ⟨vv,ss⟩ := actualOld.deterministic old.erase
              simpa only [vv,ss] using ran))
            check (value==actual && finalStore==store && cost<=fuel) "actual Core full payload/store/cost"
          | .outOfFuel suspended =>
            proof ((old.runStateful_outOfFuel_iff resolution actualLowered).mp ⟨suspended,ran⟩)
            check (fuel<cost) "Core exact exhaustion"
          | .fault _ _ => throw (IO.userError "unexpected Core fault")
private def runSuccessful (table : LocalNameTable) (e : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) (expected : Core.Value) (expectedCost threshold : Nat)
    (h : Cert table e store source expected expectedCost) (withCore : Bool) : IO Unit := do
  match oldResult : evaluateLocalExpressionWithCost? table e source with
  | none => throw (IO.userError "independent old success")
  | some (actual,cost) =>
    let old := evaluateLocalExpressionWithCost?_sound oldResult store
    proof (old.deterministic h.old)
    check (actual==expected && cost==expectedCost) "actual complete old payload and cost"
    for depth in [0,threshold-1,threshold,threshold+1] do
      match actualResult : evaluateClosedSourceExpression? depth owner table (up e) (store.map RuntimeValue.ofCore) source with
      | none => check (depth < threshold) "actual missing below depth threshold"
      | some (actualValue,actualFinal) =>
        check (depth >= threshold) "actual success at depth threshold"
        if withCore then
          match actualValue with
          | .pair _ (.pair .unit (.pair (.word w) (.pair _ _))) => check (w==seven) "actual nested full-result shape"
          | _ => throw (IO.userError "actual mixed result shape")
        let closed := evaluateClosedSourceExpression?_sound actualResult
        have reflected := h.fragment.local_evaluates_iff.mp closed
        have allOutputs : actualValue=RuntimeValue.ofCore actual ∧ actualFinal=store.map RuntimeValue.ofCore := by
          obtain ⟨v,s,hv,hs,ev⟩ := reflected
          obtain ⟨rfl,rfl⟩ := ev.deterministic old.erase
          exact ⟨hv,hs⟩
        proof ((h.fragment.local_evaluates_iff (owner := owner)).mpr ⟨actual,store,allOutputs.1,allOutputs.2,old.erase⟩)
        proof (closed.deterministic h.closed)
        if withCore then coreChecks table e store source actual cost actualValue actualFinal h.fragment closed old
        check (actualValue.toCore?==some actual && actualFinal.mapM RuntimeValue.toCore?==some store)
          "actual full mixed payload and whole store after image reflection"
private def boundaryWitness (source : Syntax.Expr) (x y z : Core.Value) (store : Core.Store) (mappedName : Bool) :
    IO (Cert (names ++ if mappedName then [("missing",sid 99)] else [])
      (env (.bool true) x y z .unit []) store source x 4) := do
  let table := names ++ if mappedName then [("missing",sid 99)] else []
  let e := env (.bool true) x y z .unit []
  match shape : source with
  | ⟨span,.conditional guard q yes colon ⟨_,.identifier missing⟩⟩ =>
    check (span.endByte==11 && q.startByte==1 && q.endByte==2 && colon.startByte==3 && colon.endByte==4 && missing.value=="missing") "original missing boundary"
    let hc ← reference table e store guard "c" (sid 3) (.bool true)
      (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
    let hx ← reference table e store yes "x" (sid 7) x .head (.tail (by decide) .head)
    return by
      rw [shape]; exact ⟨.conditional hc.fragment hx.fragment .reference,
        .conditionalTrue (by simpa only [RuntimeValue.ofCore] using hc.closed) hx.closed,.ifTrue hc.old hx.old⟩
  | _ => throw (IO.userError "original missing conditional")
private def boundaryChecks (source : Syntax.Expr) (x y z : Core.Value) (store : Core.Store) : IO Unit := do
  for mappedName in [false,true] do
    let table := names ++ if mappedName then [("missing",sid 99)] else []
    let e := env (.bool true) x y z .unit []
    let h ← boundaryWitness source x y z store mappedName
    runSuccessful table e store source x 4 2 h false
    check ((elaborateLocalExpression? table (context e) source).isNone) "whole checker cannot skip missing"
    match resolveLocalExpression? table source with
    | none => check (!mappedName) "whole resolution failure despite selected success"
    | some r => check (mappedName && r==.ifE (.var (sid 3)) (.var (sid 7)) (.var (sid 99)) &&
        (r.lower? (Resolved.LocalScope.ids e)).isNone) "resolved unselected ID prevents whole lowering"
    let visited := env (.bool false) x y z .unit []
    check ((evaluateLocalExpressionWithCost? table visited source).isNone &&
      (evaluateClosedSourceExpression? 40 owner table (up visited) (store.map RuntimeValue.ofCore) source).isNone) "visited missing is actual None, not a fault claim"
end ParsedClosedSourceCoreImage
open Solcore Solcore.Frontend ParsedClosedSourceCoreImage
def frontendParsedClosedSourceCoreImageTests : IO Unit := do
  let source ← parsed "c?(x,(),7,(y,(z))):(y,(),7,(x,z))"
  let x : Core.Value := .closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .unit 700]
  let y : Core.Value := .hostFunction .storageWrite
  let z : Core.Value := .cellRef (.function .word .word) 700
  for c in [true,false] do
    for extra in [[],[(sid 7,z),(foreign,x)]] do
      for store in [[],[x,.cellRef (.function .unit .word) 1]] do
        let h ← witness source c x y z (.word seven) extra store
        let e := env (.bool c) x y z (.word seven) extra
        runSuccessful names e store source (if c then result x y z else result y x z) 20 (if c then 7 else 6) h true
        check ((elaborateLocalExpression? names (context e true) source).isNone) "raw success does not make both branches equally typed"
  let badGuard := env (.word seven) x y z .unit []
  check ((evaluateLocalExpressionWithCost? names badGuard source).isNone &&
    (evaluateClosedSourceExpression? 40 owner names (up badGuard) [] source).isNone) "non-Bool guard actual None"
  let boundary ← parsed "c?x:missing"
  boundaryChecks boundary x y z [x,z]
  IO.println "ADR0293 parsed actual-output raw/Core image, independent depth/cost, and whole-pipeline boundaries GREEN"
end Tests

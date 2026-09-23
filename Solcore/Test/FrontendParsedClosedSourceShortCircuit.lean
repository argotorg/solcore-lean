import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Syntax.Parser.Term

/-! Parsed IO consumers. Closed raw-store depth and independently costed
Core-valued source evaluation are separate lanes, not a data-image bridge.
Every original group, identifier and operator range is checked by hand.
Left group depth/cost = 2/1; right grouped double-not = 4/5;
whole skip = 3/4 and whole selected = 5/8. -/
set_option autoImplicit false
namespace Tests.ParsedClosedSourceShortCircuit
open Solcore Solcore.Frontend
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"ParsedShortCircuit",by decide⟩],by decide⟩⟩,298⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex := 901}
private def fid : Resolved.LocalId := ⟨foreign,900⟩
private def names : LocalNameTable := [("flag",sid 7),("right",sid 31),("flag",fid)]
private def rawRows (p : RuntimeValue) (left right : Bool) : Resolved.LocalScope RuntimeValue :=
  [(sid 0,p),(sid 7,.bool left),(sid 31,.bool right),(sid 7,.word Core.Word.maximum),(fid,p)]
private def opaqueCore : Core.Value :=
  .closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700]
private def coreRows (left right : Bool) : Resolved.Environment :=
  [(sid 7,.bool left),(sid 31,.bool right),(sid 7,opaqueCore),(fid,.unit)]
private structure Ranges where
  whole : Syntax.SourceSpan
  op : Syntax.SourceSpan
  lg : Syntax.SourceSpan
  lr : Syntax.SourceSpan
  ln : Syntax.SourceSpan
  rg : Syntax.SourceSpan
  uo : Syntax.SourceSpan
  oo : Syntax.SourceSpan
  ui : Syntax.SourceSpan
  oi : Syntax.SourceSpan
  rr : Syntax.SourceSpan
  rn : Syntax.SourceSpan
private def allRanges (s : Ranges) := [s.whole,s.op,s.lg,s.lr,s.ln,s.rg,s.uo,s.oo,s.ui,s.oi,s.rr,s.rn]
private def leftSource (s : Ranges) : Syntax.Expr := ⟨s.lg,.group ⟨s.lr,.identifier ⟨s.ln,"flag"⟩⟩⟩
private def rightSource (s : Ranges) : Syntax.Expr :=
  ⟨s.rg,.group ⟨s.uo,.unary ⟨s.oo,.logicalNot⟩ ⟨s.ui,.unary ⟨s.oi,.logicalNot⟩
    ⟨s.rr,.identifier ⟨s.rn,"right"⟩⟩⟩⟩⟩
private def source (s : Ranges) (isOr : Bool) : Syntax.Expr :=
  ⟨s.whole,.binary (leftSource s) ⟨s.op,if isOr then .logicalOr else .logicalAnd⟩ (rightSource s)⟩
private def answer (isOr left right : Bool) := if left == isOr then isOr else right
private def depth (isOr left : Bool) : Nat := if left == isOr then 3 else 5
private def cost (isOr left : Bool) : Nat := if left == isOr then 4 else 8
private def resolved (isOr : Bool) : Resolved.Expr :=
  let r := Resolved.Expr.unary .boolNot (.unary .boolNot (.var (sid 31)))
  if isOr then .ifE (.var (sid 7)) (.bool true) r else .ifE (.var (sid 7)) r (.bool false)
private def core (isOr : Bool) : Core.Expr :=
  let r := Core.Expr.unary .boolNot (.unary .boolNot (.var 1))
  if isOr then .ifE (.var 0) (.bool true) r else .ifE (.var 0) r (.bool false)

private theorem original (s : Ranges) (isOr left right : Bool) (p : RuntimeValue)
    (store : List RuntimeValue) : ClosedSourceExpressionEvaluates owner names (rawRows p left right)
      store (source s isOr) (.bool (answer isOr left right)) store := by
  have l : ClosedSourceExpressionEvaluates owner names (rawRows p left right) store
      (leftSource s) (.bool left) store := .group (.reference .head (.tail (by decide) .head))
  have leaf : ClosedSourceExpressionEvaluates owner names (rawRows p left right) store
      ⟨s.rr,.identifier ⟨s.rn,"right"⟩⟩ (.bool right) store :=
    .reference (.tail (by change "flag" ≠ "right"; decide) .head) (.tail (by decide) (.tail (by decide) .head))
  have r : ClosedSourceExpressionEvaluates owner names (rawRows p left right) store
      (rightSource s) (.bool right) store := by
    simpa only [rightSource,Bool.not_not] using ClosedSourceExpressionEvaluates.group (span:=s.rg)
      (ClosedSourceExpressionEvaluates.logicalNot (span:=s.uo) (operatorSpan:=s.oo)
        (ClosedSourceExpressionEvaluates.logicalNot (span:=s.ui) (operatorSpan:=s.oi) leaf))
  cases isOr <;> cases left
  · exact .andFalse l
  · exact .andTrue l r
  · exact .orFalse l r
  · exact .orTrue l

private theorem cutoff (s : Ranges) (isOr left right : Bool) (p : RuntimeValue)
    (store : List RuntimeValue) : ∀ n, evaluateClosedSourceExpression? n owner names (rawRows p left right)
      store (source s isOr) = if depth isOr left ≤ n then some (.bool (answer isOr left right),store) else none := by
  cases isOr <;> cases left <;> cases right
  all_goals
    intro n
    by_cases high : 5 ≤ n
    · have split : n = (n-5)+5 := by omega
      rw [split]
      simp [source,leftSource,rightSource,depth,answer,evaluateClosedSourceExpression?,
        names,rawRows,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,sid,owner,fid,foreign]
    · have small : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 := by omega
      rcases small with rfl | rfl | rfl | rfl | rfl
      all_goals simp [source,leftSource,rightSource,depth,answer,evaluateClosedSourceExpression?,
        names,rawRows,LocalNameTable.lookup?,Resolved.LocalScope.lookup?,sid,owner,fid,foreign]

private theorem localOriginal (s : Ranges) (isOr left right : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (coreRows left right) store (source s isOr)
      (.bool (answer isOr left right)) store (cost isOr left) := by
  have l : LocalExpressionEvaluatesWithCost names (coreRows left right) store
      (leftSource s) (.bool left) store 1 := .group (.identifier .head .head)
  have leaf : LocalExpressionEvaluatesWithCost names (coreRows left right) store
      ⟨s.rr,.identifier ⟨s.rn,"right"⟩⟩ (.bool right) store 1 :=
    .identifier (.tail (by change "flag" ≠ "right"; decide) .head) (.tail (by decide) .head)
  have r : LocalExpressionEvaluatesWithCost names (coreRows left right) store
      (rightSource s) (.bool right) store 5 := by
    simpa only [rightSource,Bool.not_not] using LocalExpressionEvaluatesWithCost.group (span:=s.rg)
      (LocalExpressionEvaluatesWithCost.logicalNot (span:=s.uo) (operatorSpan:=s.oo)
        (LocalExpressionEvaluatesWithCost.logicalNot (span:=s.ui) (operatorSpan:=s.oi) leaf))
  cases isOr <;> cases left
  · exact .andFalse l
  · exact .andTrue l r
  · exact .orFalse l r
  · exact .orTrue l
private theorem resolution (s : Ranges) (isOr : Bool) :
    ResolvesLocalExpression names (source s isOr) (resolved isOr) := by
  cases isOr
  · exact .logicalAnd (.group (.identifier .head))
      (.group (.logicalNot (.logicalNot (.identifier (.tail (by change "flag" ≠ "right"; decide) .head)))))
  · exact .logicalOr (.group (.identifier .head))
      (.group (.logicalNot (.logicalNot (.identifier (.tail (by change "flag" ≠ "right"; decide) .head)))))
private theorem lowering (isOr left right : Bool) :
    Resolved.Lowers (Resolved.LocalScope.ids (coreRows left right)) (resolved isOr) (core isOr) := by
  cases isOr
  · exact .ifE (.var .head) (.unary (.unary (.var (.tail (by change sid 7 ≠ sid 31; decide) .head)))) .bool
  · exact .ifE (.var .head) .bool (.unary (.unary (.var (.tail (by change sid 7 ≠ sid 31; decide) .head))))
private theorem image {captured store src value}
    (h : ClosedSourceExpressionEvaluates owner names captured store src value store) :
    ∀ a st, ClosedSourceExpressionEvaluates owner names captured store src a st ↔ a=value ∧ st=store := by
  intro a st; constructor
  · exact fun e => e.deterministic h
  · rintro ⟨rfl,rfl⟩; exact h
private theorem coreImage {e s c v k} (h : Core.Steps k (.initial c e s) (.final v s)) (fuel a st) :
    Core.runStateful fuel (.initial c e s) = .done a st ↔ a=v ∧ st=s ∧ k≤fuel := by
  constructor
  · intro run
    obtain ⟨rfl,rfl⟩ := Core.evaluation_deterministic (Core.runStateful_evaluation_sound run)
      (Core.steps_from_initial_sound h)
    exact ⟨rfl,rfl,h.runStateful_done_iff.mp run⟩
  · rintro ⟨rfl,rfl,enough⟩; exact h.runStateful_done_iff.mpr enough
private theorem ruleRoundtrip {s : Ranges} {isOr : Bool} {captured store a st}
    (h : ClosedSourceExpressionEvaluates owner names captured store (source s isOr) a st) :
    ClosedSourceExpressionEvaluates owner names captured store (source s isOr) a st := by
  cases isOr
  · exact closedSourceExpressionEvaluates_logicalAnd_iff.mpr
      (closedSourceExpressionEvaluates_logicalAnd_iff.mp h)
  · exact closedSourceExpressionEvaluates_logicalOr_iff.mpr
      (closedSourceExpressionEvaluates_logicalOr_iff.mp h)

private def exercise (src : Syntax.Expr) (s : Ranges) (isOr : Bool) (shape : src=source s isOr)
    (left right : Bool) (p : RuntimeValue) (rawStore : List RuntimeValue) (coreStore : Core.Store) : IO Unit := do
  have orig : ClosedSourceExpressionEvaluates owner names (rawRows p left right)
      rawStore src (.bool (answer isOr left right)) rawStore := by rw [shape]; exact original s isOr left right p rawStore
  have cut : ∀ n, evaluateClosedSourceExpression? n owner names (rawRows p left right) rawStore src =
      if depth isOr left ≤ n then some (.bool (answer isOr left right),rawStore) else none := by
    intro n; rw [shape]; exact cutoff s isOr left right p rawStore n
  proof orig; proof cut
  have lc : LocalExpressionEvaluatesWithCost names (coreRows left right) coreStore src
      (.bool (answer isOr left right)) coreStore (cost isOr left) := by rw [shape]; exact localOriginal s isOr left right coreStore
  have res : ResolvesLocalExpression names src (resolved isOr) := by rw [shape]; exact resolution s isOr
  have low := lowering isOr left right
  have paths := lc.toStepsWithContinuation res low
  have steps := lc.toSteps res low
  proof lc; proof res; proof low; proof paths
  for n in [0,depth isOr left-1,depth isOr left,depth isOr left+3] do
    proof (cut n)
    match run : evaluateClosedSourceExpression? n owner names (rawRows p left right) rawStore src with
    | none =>
      have below : n < depth isOr left := by
        by_cases enough : depth isOr left ≤ n
        · have expected := cut n
          rw [run,if_pos enough] at expected
          cases expected
        · omega
      proof below; check (n < depth isOr left) "raw exact depth rejection"
    | some (a,st) =>
      have actual := evaluateClosedSourceExpression?_sound run
      have endpoints := (image orig a st).mp actual
      proof endpoints; proof ((image orig a st).mpr endpoints)
      proof (ruleRoundtrip (s:=s) (isOr:=isOr) (by rw [← shape]; exact actual))
      have enough : depth isOr left ≤ n := by
        by_cases enough : depth isOr left ≤ n
        · exact enough
        · have expected := cut n
          rw [run,if_neg enough] at expected
          cases expected
      have back : evaluateClosedSourceExpression? n owner names (rawRows p left right) rawStore src = some (a,st) := by
        rw [cut n,if_pos enough,endpoints.1,endpoints.2]
      proof back; check (n ≥ depth isOr left) "raw complete value/store image"
  for k in [0,cost isOr left-1,cost isOr left,cost isOr left+3] do
    match run : Core.runStateful k (.initial (core isOr) (coreRows left right).values coreStore) with
    | .done a st =>
      have endpoints := (coreImage steps k a st).mp run
      proof endpoints; proof ((coreImage steps k a st).mpr endpoints)
      check (a == .bool (answer isOr left right) && st == coreStore && k ≥ cost isOr left) "Core full actual endpoint/cost"
    | .outOfFuel suspended =>
      have below := steps.runStateful_outOfFuel_iff.mp ⟨suspended,run⟩
      proof below; proof (steps.runStateful_outOfFuel_iff.mpr below)
      check (k < cost isOr left) "Core exact exhaustion"
    | _ => throw (IO.userError "independent Core lane stuck")

private def parsedCase (isOr : Bool) : IO Unit := do
  let text := if isOr then "(flag) || (!!right)" else "(flag) && (!!right)"
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-short-circuit.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "short-circuit lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
      src.span == Syntax.SourceSpan.fullFile file) "whole AST / source ownership / EOF / zero diagnostics"
    match shape : src with
    | ⟨whole,.binary ⟨lg,.group ⟨lr,.identifier ⟨ln,"flag"⟩⟩⟩ ⟨opSpan,op⟩
        ⟨rg,.group ⟨uo,.unary ⟨oo,.logicalNot⟩ ⟨ui,.unary ⟨oi,.logicalNot⟩
          ⟨rr,.identifier ⟨rn,"right"⟩⟩⟩⟩⟩⟩ =>
      let s : Ranges := ⟨whole,opSpan,lg,lr,ln,rg,uo,oo,ui,oi,rr,rn⟩
      check ((allRanges s).all (fun r => r.isValidFor file) &&
        (allRanges s).map (fun r => (r.startByte,r.endByte)) ==
          [(0,19),(7,9),(0,6),(1,5),(1,5),(10,19),(11,18),(11,12),(12,18),(12,13),(13,18),(13,18)])
        "all handwritten expression, group, identifier and operator ranges"
      if operator : op = (if isOr then .logicalOr else .logicalAnd) then
        have originalShape : src = source s isOr := by rw [shape,operator]; rfl
        let inert : Syntax.Expr := ⟨whole,.identifier ⟨whole,"opaque-unused"⟩⟩
        let p := RuntimeValue.sourceClosure inert foreign [("flag",fid)] [(fid,.unit)]
        for left in [false,true] do
          for right in [false,true] do
            for rawStore in [[],[p,RuntimeValue.ofCore opaqueCore,.hostFunction .storageWrite,
                .cellRef (.function .word .word) 900,.pair .unit (.word Core.Word.maximum)]] do
              for coreStore in [[],[opaqueCore,.hostFunction .storageWrite,.cellRef .word 700,.unit]] do
                exercise src s isOr originalShape left right p rawStore coreStore
      else throw (IO.userError "actual parsed short-circuit operator")
    | _ => throw (IO.userError "actual original groups/double-not/identifiers")
  | _ => throw (IO.userError "short-circuit parser")
end Tests.ParsedClosedSourceShortCircuit
open Tests.ParsedClosedSourceShortCircuit in
def Tests.frontendParsedClosedSourceShortCircuitTests : IO Unit := do
  parsedCase false
  parsedCase true

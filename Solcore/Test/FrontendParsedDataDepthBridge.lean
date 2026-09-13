import Solcore.Frontend.ClosedSourceDataDepthDecisionProperties
import Solcore.Frontend.ClosedSourceEvaluationProperties
import Solcore.Syntax.Parser.Term

/- Two actual parsed trees exercise original right-associated many tails and a
deep unselected missing branch. Independent raw constructor witnesses come first.
Depth is a sufficient source-search bound, not a minimum or a Core transition cost.
Duplicate lexical/captured rows, arbitrary mixed payloads and entire stores remain. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Tests.ParsedDataDepthBridge
open Solcore Solcore.Frontend
private abbrev V := RuntimeValue
private abbrev E := ClosedSourceExpressionEvaluates
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def proof {p : Prop} (_ : p) : IO Unit := pure ()
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ParsedDataDepth",by decide⟩],by decide⟩⟩,302⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex:=903},700⟩
private def names : LocalNameTable :=
  [("x",sid 7),("c",sid 3),("y",sid 8),("z",foreign),("x",sid 99),("c",sid 99)]
private def rows (guard p q r : V) (tail : Resolved.LocalScope V) :=
  [(sid 8,q),(sid 7,p),(sid 3,guard),(foreign,r),(sid 7,.unit),
    (sid 3,.word Core.Word.maximum)] ++ tail
private def span (f : Syntax.SourceFile) (a b : Nat) : Syntax.SourceSpan := ⟨f.id,a,b⟩
private def ref (f : Syntax.SourceFile) (a b : Nat) (n : String) : Syntax.Expr :=
  ⟨span f a b,.identifier ⟨span f a b,n⟩⟩
private def tupleAST (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 10,.tuple ⟨span f 0 10,[ref f 1 2 "x",⟨span f 3 5,.tuple ⟨span f 3 5,[]⟩⟩,
    ref f 6 7 "y",ref f 8 9 "z"]⟩⟩
private def conditionalAST (f : Syntax.SourceFile) : Syntax.Expr :=
  ⟨span f 0 21,.conditional (ref f 0 1 "c") (span f 2 3) (ref f 4 5 "x") (span f 6 7)
    ⟨span f 8 21,.group ⟨span f 9 20,.group ⟨span f 10 19,.group (ref f 11 18 "missing")⟩⟩⟩⟩
private def actualSpans : Syntax.Expr → List Syntax.SourceSpan
  | ⟨s,.tuple ⟨t,[⟨x,.identifier ⟨xn,_⟩⟩,⟨u,.tuple ⟨ut,[]⟩⟩,
      ⟨y,.identifier ⟨yn,_⟩⟩,⟨z,.identifier ⟨zn,_⟩⟩]⟩⟩ => [s,t,x,xn,u,ut,y,yn,z,zn]
  | ⟨s,.conditional ⟨c,.identifier ⟨cn,_⟩⟩ qu ⟨x,.identifier ⟨xn,_⟩⟩ co
      ⟨a,.group ⟨b,.group ⟨d,.group ⟨m,.identifier ⟨mn,_⟩⟩⟩⟩⟩⟩ => [s,c,cn,qu,x,xn,co,a,b,d,m,mn]
  | _ => []
private def parsed (text : String) (expected : Syntax.SourceFile → Syntax.Expr)
    (ranges : List (Nat × Nat)) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"parsed-data-depth.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "data depth lexer")
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok src next =>
    check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && next.file==file &&
      src.span==Syntax.SourceSpan.fullFile file && src==expected file) "whole handwritten AST / EOF / zero diagnostics"
    check ((actualSpans src).all (fun s => s.isValidFor file) &&
      (actualSpans src).map (fun s => (s.startByte,s.endByte))==ranges) "all actual node/name/delimiter/operator spans"
    return src
  | _ => throw (IO.userError "data depth parser")
private structure Cert (captured : Resolved.LocalScope V) (store : List V) (src : Syntax.Expr) (value : V) : Type where
  gate : ClosedSourceDataExpression src
  original : E owner names captured store src value store
private def reference (captured : Resolved.LocalScope V) (store : List V) (src : Syntax.Expr)
    (spelling : String) (id : Resolved.LocalId) (value : V)
    (named : LocalNameTable.Lookup names spelling id) (found : Resolved.LocalScope.Lookup captured id value) :
    IO (Cert captured store src value) := do
  match shape : src with
  | ⟨_,.identifier name⟩ =>
    if h : name.value=spelling then
      return by rw [shape]; exact ⟨.reference,.reference (h ▸ named) found⟩
    else throw (IO.userError "actual identifier spelling")
  | _ => throw (IO.userError "actual reference")
private def tupleWitness (src : Syntax.Expr) (guard p q r : V)
    (tail : Resolved.LocalScope V) (store : List V) :
    IO (Cert (rows guard p q r tail) store src (.pair p (.pair .unit (.pair q r)))) := do
  let captured := rows guard p q r tail
  match shape : src with
  | ⟨_,.tuple ⟨_,[x,⟨_,.tuple ⟨_,[]⟩⟩,y,z]⟩⟩ =>
    let hx ← reference captured store x "x" (sid 7) p .head (.tail (by decide) .head)
    let hy ← reference captured store y "y" (sid 8) q
      (.tail (by decide) (.tail (by decide) .head)) .head
    let hz ← reference captured store z "z" foreign r
      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
    return by rw [shape]; exact ⟨.many hx.gate (.many .unit (.pair hy.gate hz.gate)),
      .many hx.original (.many .unit (.pair hy.original hz.original))⟩
  | _ => throw (IO.userError "original flat four-tuple and right-associated tail")
private theorem endpoints {captured store src value}
    (original : E owner names captured store src value store) (a : V) (st : List V) :
    E owner names captured store src a st ↔ a=value ∧ st=store :=
  ⟨fun other => other.deterministic original,by rintro ⟨rfl,rfl⟩; exact original⟩
private def successful {captured store src value} (h : Cert captured store src value)
    (selectedDepth expectedBound : Nat) : IO Unit := do
  proof h.original
  let bound := closedSourceDataDepthBound src
  check (bound==expectedBound) "actual source-only depth counts right tuple tails and both branches"
  have atBound := h.gate.evaluates_at_depthBound h.original (Nat.le_refl bound)
  have allHigh : ∀ n, bound≤n → evaluateClosedSourceExpression? n owner names captured store src =
      some (value,store) := fun _ enough => h.gate.evaluates_at_depthBound h.original enough
  proof atBound; proof allHigh
  for budget in [0,selectedDepth-1,selectedDepth,bound-1,bound,bound+3] do
    match run : evaluateClosedSourceExpression? budget owner names captured store src with
    | none => check (budget<selectedDepth) "only lower selected-path depth fails for witnessed success"
    | some (actual,finalStore) =>
      have original := evaluateClosedSourceExpression?_sound run
      have equal := (endpoints h.original actual finalStore).mp original
      proof equal; proof ((endpoints h.original actual finalStore).mpr equal)
      check (selectedDepth≤budget) "complete actual value and final store proved without a mixed-value comparison"
      if enough : bound≤budget then
        proof ((h.gate.evaluate_at_depthBound_iff enough).mp run)
        proof ((h.gate.evaluate_at_depthBound_iff enough).mpr original)
        proof (h.gate.evaluate_depth_stable owner names captured store enough)
      if below : budget<bound then
        proof (show ∃ n, n<bound ∧ evaluateClosedSourceExpression? n owner names captured store src =
          some (actual,finalStore) from ⟨budget,below,run⟩)
  for extra in [0,1,7] do
    have stable := h.gate.evaluate_depth_stable owner names captured store (Nat.le_add_right bound extra)
    proof stable
    match high : evaluateClosedSourceExpression? (bound+extra) owner names captured store src with
    | none => False.elim (by
        have accepted := allHigh (bound+extra) (Nat.le_add_right bound extra)
        rw [high] at accepted; cases accepted)
    | some (actual,finalStore) =>
      proof (show evaluateClosedSourceExpression? bound owner names captured store src =
        some (actual,finalStore) from stable.symm.trans high)
private def rejected {captured store src} (gate : ClosedSourceDataExpression src)
    (directNone : evaluateClosedSourceExpression? (closedSourceDataDepthBound src)
      owner names captured store src = none) : IO Unit := do
  proof directNone
  have absent := (gate.evaluate_depth_none_iff owner names captured store (Nat.le_refl _)).mp directNone
  have allBudgets := (gate.evaluate_depth_none_iff_all_budgets owner names captured store).mp directNone
  proof absent; proof allBudgets
  proof ((gate.evaluate_depth_none_iff owner names captured store (Nat.le_refl _)).mpr absent)
  proof ((gate.evaluate_depth_none_iff_all_budgets owner names captured store).mpr allBudgets)
  let bound := closedSourceDataDepthBound src
  for budget in [0,1,bound-1,bound,bound+7] do
    proof (allBudgets budget)
    check ((evaluateClosedSourceExpression? budget owner names captured store src).isNone) "selected failure at every tested budget"
  have stable := gate.evaluate_depth_stable owner names captured store (Nat.le_add_right bound 7)
  proof stable
  check ((evaluateClosedSourceExpression? (bound+7) owner names captured store src).isNone &&
    (evaluateClosedSourceExpression? bound owner names captured store src).isNone) "proved whole Option stability also preserves none"
private def conditionalCase (src : Syntax.Expr) (p q r : V)
    (tail : Resolved.LocalScope V) (store : List V) : IO Unit := do
  match shape : src with
  | ⟨_,.conditional c _ x _ ⟨_,.group ⟨_,.group ⟨_,.group ⟨_,.identifier ⟨_,"missing"⟩⟩⟩⟩⟩⟩ =>
    let captured := rows (.bool true) p q r tail
    let hc ← reference captured store c "c" (sid 3) (.bool true)
      (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
    let hx ← reference captured store x "x" (sid 7) p .head (.tail (by decide) .head)
    have cert : Cert captured store src p := by
      rw [shape]; exact ⟨.conditional hc.gate hx.gate (.group (.group (.group .reference))),
        .conditionalTrue hc.original hx.original⟩
    successful cert 2 5
    match cShape : c, xShape : x with
    | ⟨_,.identifier ⟨_,"c"⟩⟩, ⟨_,.identifier ⟨_,"x"⟩⟩ =>
      have missing : evaluateClosedSourceExpression? (closedSourceDataDepthBound src)
          owner names (rows (.bool false) p q r tail) store src = none := by
        rw [shape,cShape,xShape]
        simp [closedSourceDataDepthBound,evaluateClosedSourceExpression?,names,rows,
          LocalNameTable.lookup?,Resolved.LocalScope.lookup?,sid,owner,foreign]
      have wrong : evaluateClosedSourceExpression? (closedSourceDataDepthBound src)
          owner names (rows (.word Core.Word.maximum) p q r tail) store src = none := by
        rw [shape,cShape,xShape]
        simp [closedSourceDataDepthBound,evaluateClosedSourceExpression?,names,rows,
          LocalNameTable.lookup?,Resolved.LocalScope.lookup?,sid,owner,foreign]
      rejected cert.gate missing
      rejected cert.gate wrong
    | _,_ => throw (IO.userError "actual Bool guard and selected payload identifiers")
  | _ => throw (IO.userError "original conditional and deep missing branch")
end Tests.ParsedDataDepthBridge
open Solcore Solcore.Frontend Tests.ParsedDataDepthBridge in
def Tests.frontendParsedDataDepthBridgeTests : IO Unit := do
  let tuple ← parsed "(x,(),y,z)" tupleAST
    [(0,10),(0,10),(1,2),(1,2),(3,5),(3,5),(6,7),(6,7),(8,9),(8,9)]
  let conditional ← parsed "c ? x : (((missing)))" conditionalAST
    [(0,21),(0,1),(0,1),(2,3),(4,5),(4,5),(6,7),(8,21),(9,20),(10,19),(11,18),(11,18)]
  let inert := tuple
  let saved := RuntimeValue.sourceClosure inert foreign.owner [("x",foreign),("x",sid 7)]
    [(foreign,.unit),(foreign,.word Core.Word.maximum)]
  let inertCore := RuntimeValue.ofCore (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
  let mut count := 0
  for p in [saved,RuntimeValue.pair (.word Core.Word.maximum) saved] do
    for tail in [[],[(sid 7,inertCore),(sid 3,.unit),(foreign,saved)]] do
      for store in [[],[saved,inertCore,RuntimeValue.hostFunction .storageWrite,RuntimeValue.cellRef (.function .word .word) 900]] do
        let witness ← tupleWitness tuple (.bool false) p inertCore saved tail store
        successful witness 4 4
        conditionalCase conditional p inertCore saved tail store
        count := count+4
  check (count==32) "two spellings / eight mixed contexts / success and both selected failure lanes"

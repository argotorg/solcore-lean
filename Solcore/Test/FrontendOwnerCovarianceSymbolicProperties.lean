import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalReference
import Solcore.Resolved.LocalScope

/- Independent original constructors and direct depth equations precede covariance.
Ordered rows, arbitrary opaque values and whole stores are never projected away.
The selected literal count is not an evaluator budget or a runtime cost. -/
set_option autoImplicit false
namespace Tests.OwnerCovarianceSymbolic
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def result (value : RuntimeValue) (word : Core.Word) : RuntimeValue :=
  .pair value (.pair (.word (word.add word)) (.bool false))
private def nested (s ts os : Syntax.SourceSpan) (x w b : Syntax.Identifier) (bad : Syntax.Expr) : Syntax.Expr :=
  ⟨s,.tuple ⟨ts,[ref s x,⟨s,.binary (ref s w) ⟨os,.add⟩ (ref s w)⟩,
    ⟨s,.binary (ref s b) ⟨os,.logicalAnd⟩ bad⟩]⟩⟩
private theorem reference_run {s name owner names captured store id value}
    (n : Nat) (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceExpression? (n+1) owner names captured store (ref s name) = some (value,store) := by
  simp only [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,
    Resolved.LocalScope.lookup?_iff.mpr found,bind,Option.bind_some,pure]
private theorem nested_original {s ts os x w b bad owner names captured store xid wid bid value word}
    (xn : LocalNameTable.Lookup names x.value xid) (xf : Resolved.LocalScope.Lookup captured xid value)
    (wn : LocalNameTable.Lookup names w.value wid) (wf : Resolved.LocalScope.Lookup captured wid (.word word))
    (bn : LocalNameTable.Lookup names b.value bid) (bf : Resolved.LocalScope.Lookup captured bid (.bool false)) :
    E owner names captured store (nested s ts os x w b bad) (result value word) store := by
  have addition : E owner names captured store ⟨s,.binary (ref s w) ⟨os,.add⟩ (ref s w)⟩
      (.word (word.add word)) store := by
    simpa only [RuntimeValue.ofCore] using
      (ClosedSourceExpressionEvaluates.strictWordBinary (span:=s) (operatorSpan:=os)
        (left:=ref s w) (right:=ref s w) (.reference wn wf) (.reference wn wf) .add)
  exact .many (.reference xn xf) (.pair addition (.andFalse (.reference bn bf)))
private theorem nested_run {s ts os x w b bad owner names captured store xid wid bid value word}
    (n : Nat) (xn : LocalNameTable.Lookup names x.value xid) (xf : Resolved.LocalScope.Lookup captured xid value)
    (wn : LocalNameTable.Lookup names w.value wid) (wf : Resolved.LocalScope.Lookup captured wid (.word word))
    (bn : LocalNameTable.Lookup names b.value bid) (bf : Resolved.LocalScope.Lookup captured bid (.bool false)) :
    evaluateClosedSourceExpression? (n+4) owner names captured store (nested s ts os x w b bad) =
      some (result value word,store) := by
  simp only [nested,evaluateClosedSourceExpression?,ref,LocalNameTable.lookup?_iff.mpr xn,
    LocalNameTable.lookup?_iff.mpr wn,LocalNameTable.lookup?_iff.mpr bn,
    Resolved.LocalScope.lookup?_iff.mpr xf,Resolved.LocalScope.lookup?_iff.mpr wf,
    Resolved.LocalScope.lookup?_iff.mpr bf,bind,Option.bind_some,evaluateStrictWordBinary?,
    RuntimeValue.ofCore,Bool.false_eq_true,↓reduceIte,pure,result]

/-- A right-associated tuple returns an opaque value, an actual Word sum and a
short-circuit Boolean at the same depth after every injective owner relabeling. -/
theorem nested_word_and_skipped_child_covary
    (s ts os : Syntax.SourceSpan) (x w b : Syntax.Identifier) (bad : Syntax.Expr)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (xid wid bid : Resolved.LocalId) (value : RuntimeValue) (word : Core.Word)
    (xn : LocalNameTable.Lookup names x.value xid) (xf : Resolved.LocalScope.Lookup captured xid value)
    (wn : LocalNameTable.Lookup names w.value wid) (wf : Resolved.LocalScope.Lookup captured wid (.word word))
    (bn : LocalNameTable.Lookup names b.value bid) (bf : Resolved.LocalScope.Lookup captured bid (.bool false))
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    E owner names captured store (nested s ts os x w b bad) (result value word) store ∧
    evaluateClosedSourceExpression? 3 owner names captured store (nested s ts os x w b bad) = none ∧
    (∀ extra, evaluateClosedSourceExpression? (extra+4) owner names captured store (nested s ts os x w b bad) =
      some (result value word,store)) ∧
    (∀ extra, evaluateClosedSourceExpression? (extra+4) (mapping owner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) (mapRuntimeCapturedOwners mapping captured)
      (store.map (RuntimeValue.mapOwners mapping)) (nested s ts os x w b bad) =
      some (result (value.mapOwners mapping) word,store.map (RuntimeValue.mapOwners mapping))) ∧
    (∀ budget, evaluateClosedSourceExpression? budget (mapping owner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) (mapRuntimeCapturedOwners mapping captured)
      (store.map (RuntimeValue.mapOwners mapping)) (nested s ts os x w b bad) =
      (evaluateClosedSourceExpression? budget owner names captured store (nested s ts os x w b bad)).map
        (fun ep => (ep.1.mapOwners mapping,ep.2.map (RuntimeValue.mapOwners mapping)))) := by
  have original : E owner names captured store (nested s ts os x w b bad) (result value word) store :=
    nested_original xn xf wn wf bn bf
  have direct := fun extra => nested_run (s:=s) (ts:=ts) (os:=os) (bad:=bad) (owner:=owner) (store:=store)
    extra xn xf wn wf bn bf
  have low : evaluateClosedSourceExpression? 3 owner names captured store (nested s ts os x w b bad) = none := by
    simp only [nested,evaluateClosedSourceExpression?,ref,LocalNameTable.lookup?_iff.mpr xn,
      Resolved.LocalScope.lookup?_iff.mpr xf,bind,Option.bind_some,Option.bind_none,pure]
  have covariance := fun budget => evaluateClosedSourceExpression?_mapOwners mapping injective
    budget owner names captured store (nested s ts os x w b bad)
  refine ⟨original,low,direct,?_,covariance⟩
  intro extra
  simpa only [direct extra,Option.map_some,result,RuntimeValue.mapOwners] using covariance (extra+4)

private def one : Core.Word := ⟨1,by decide⟩
private def literal (s : Syntax.SourceSpan) (text : String) : Syntax.CoreLiteral := ⟨s,.decimal text⟩
private def returning (s : Syntax.SourceSpan) (x : Syntax.Identifier) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (ref s x))⟩]⟩
private def arm (s : Syntax.SourceSpan) (text : String) (body : Syntax.Block) : Syntax.MatchCase :=
  ⟨s,⟨⟨s,.literal (literal s text)⟩,body⟩⟩
private def arms (s : Syntax.SourceSpan) (x : Syntax.Identifier) (bad : Syntax.Block) : Nat → List Syntax.MatchCase
  | 0 => [arm s "1" (returning s x),arm s "1" bad]
  | n+1 => arm s "0" bad :: arms s x bad n
private def matching (s : Syntax.SourceSpan) (x : Syntax.Identifier) (bad : Syntax.Block) (n : Nat) : Syntax.Block :=
  ⟨s,[⟨s,.matchWith ⟨s,⟨⟨s,.literal (literal s "1")⟩,[]⟩⟩ ⟨s,⟨arms s x bad n,some bad⟩⟩⟩]⟩
private theorem one_meaning (s : Syntax.SourceSpan) : WordLiteralDenotes (literal s "1") one :=
  .decimal (by decide) (.cons (.decimal (digit:=1) (by decide) rfl) .nil)
private theorem zero_meaning (s : Syntax.SourceSpan) : WordLiteralDenotes (literal s "0") Core.Word.zero :=
  .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
private theorem original_choice (s : Syntax.SourceSpan) (x : Syntax.Identifier) (bad : Syntax.Block) (n : Nat) :
    RuntimeWordMatchChooses (.word one) (arms s x bad n) (some bad) (returning s x) (n+1) := by
  induction n with
  | zero => exact .hit (.literal ⟨literal s "1",rfl,one_meaning s⟩)
  | succ n ih => exact .miss (.literal ⟨literal s "0",rfl,zero_meaning s⟩) (by decide) ih
private theorem matching_run {s x bad n owner names captured store id value}
    (extra : Nat) (named : LocalNameTable.Lookup names x.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceBody? (extra+3) owner names captured store (matching s x bad n) = some (value,store) := by
  simp only [matching,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,
    interpretWordLiteral?_iff.mpr (one_meaning s),chooseRuntimeWordMatch?_iff.mpr (original_choice s x bad n),
    bind,Option.bind_some,pure,returning,evaluateClosedSourceBody?]
  exact reference_run extra named found

/-- Arbitrarily many ordered literal misses still select the first hit and the
whole opaque result at depth three; relabeling keeps that exact budget and store. -/
theorem ordered_match_keeps_selected_endpoint_and_budget
    (s : Syntax.SourceSpan) (x : Syntax.Identifier) (bad : Syntax.Block) (n : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names x.value id) (found : Resolved.LocalScope.Lookup captured id value)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping) :
    RuntimeWordMatchChooses (.word one) (arms s x bad n) (some bad) (returning s x) (n+1) ∧
    B owner names captured store (matching s x bad n) value store ∧
    evaluateClosedSourceBody? 2 owner names captured store (matching s x bad n) = none ∧
    (∀ extra, evaluateClosedSourceBody? (extra+3) owner names captured store (matching s x bad n) = some (value,store)) ∧
    (∀ extra, evaluateClosedSourceBody? (extra+3) (mapping owner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) (mapRuntimeCapturedOwners mapping captured)
      (store.map (RuntimeValue.mapOwners mapping)) (matching s x bad n) =
      some (value.mapOwners mapping,store.map (RuntimeValue.mapOwners mapping))) ∧
    (∀ budget, evaluateClosedSourceBody? budget (mapping owner)
      (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) (mapRuntimeCapturedOwners mapping captured)
      (store.map (RuntimeValue.mapOwners mapping)) (matching s x bad n) =
      (evaluateClosedSourceBody? budget owner names captured store (matching s x bad n)).map
        (fun ep => (ep.1.mapOwners mapping,ep.2.map (RuntimeValue.mapOwners mapping)))) := by
  have choice := original_choice s x bad n
  have original : B owner names captured store (matching s x bad n) value store :=
    .wordMatch (.wordLiteral (one_meaning s)) choice (.expression (.reference named found))
  have direct := fun extra => matching_run (s:=s) (bad:=bad) (n:=n) (owner:=owner) (store:=store) extra named found
  have low : evaluateClosedSourceBody? 2 owner names captured store (matching s x bad n) = none := by
    simp only [matching,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,
      interpretWordLiteral?_iff.mpr (one_meaning s),chooseRuntimeWordMatch?_iff.mpr choice,
      bind,Option.bind_some,pure,returning,evaluateClosedSourceBody?,evaluateClosedSourceExpression?]
  have covariance := fun budget => evaluateClosedSourceBody?_mapOwners mapping injective
    budget owner names captured store (matching s x bad n)
  exact ⟨choice,original,low,direct,fun extra => by
    simpa only [direct extra,Option.map_some] using covariance (extra+3),covariance⟩

private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"OwnerCovariance",by decide⟩],by decide⟩⟩,n⟩
private def lid (o n : Nat) : Resolved.LocalId := ⟨owner o,n⟩
private def shift (o : Resolved.DeclarationId) : Resolved.DeclarationId := ⟨o.moduleId,o.declarationIndex+1⟩
private theorem shift_injective : Function.Injective shift := by
  intro left right same
  have modules := congrArg Resolved.DeclarationId.moduleId same
  have indices := congrArg Resolved.DeclarationId.declarationIndex same
  cases left; cases right
  simp only [shift] at modules indices
  cases modules
  have equal := Nat.add_right_cancel indices
  cases equal
  rfl
private def span (n : Nat) : Syntax.SourceSpan := ⟨⟨.main,"owner-covariance.sol"⟩,n,n+1⟩
private def name (text : String) : Syntax.Identifier := ⟨span 0,text⟩
private def inertSource : Syntax.Expr := ref (span 10) (name "inert")
private def core (k : Nat) : RuntimeValue := .coreClosure .unit .word (.var 99)
  [.sourceClosure inertSource (owner (9+k)) [("q",lid (9+k) 7),("q",lid (2+k) 7)]
    [(lid (9+k) 7,.cellRef .word 700),(lid (9+k) 7,.unit)],.hostFunction .storageWrite]
private def payload (k : Nat) : RuntimeValue := .sourceClosure inertSource (owner (2+k))
  [("p",lid (2+k) 3),("p",lid (9+k) 3)]
  [(lid (2+k) 3,core k),(lid (2+k) 3,.bool false)]
private def store (k : Nat) : List RuntimeValue := [payload k,core k,.cellRef .word 900,.hostFunction .storageWrite]
private def names : LocalNameTable :=
  [("x",lid 2 0),("w",lid 2 1),("b",lid 2 2),("x",lid 9 0),("b",lid 2 9)]
private def rows : Resolved.LocalScope RuntimeValue :=
  [(lid 9 0,.unit),(lid 2 0,payload 0),(lid 2 0,.bool false),
    (lid 2 1,.word one),(lid 2 2,.bool false),(lid 2 2,.bool true)]
private theorem xn : LocalNameTable.Lookup names "x" (lid 2 0) := .head
private theorem wn : LocalNameTable.Lookup names "w" (lid 2 1) := .tail (by decide) .head
private theorem bn : LocalNameTable.Lookup names "b" (lid 2 2) := .tail (by decide) (.tail (by decide) .head)
private theorem xf : Resolved.LocalScope.Lookup rows (lid 2 0) (payload 0) := .tail (by decide) .head
private theorem wf : Resolved.LocalScope.Lookup rows (lid 2 1) (.word one) :=
  .tail (by decide) (.tail (by decide) (.tail (by decide) .head))
private theorem bf : Resolved.LocalScope.Lookup rows (lid 2 2) (.bool false) :=
  .tail (by decide) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
private theorem payload_mapped : (payload 0).mapOwners shift = payload 1 := by
  simp [payload,core,RuntimeValue.mapOwners,LocalNameTable.mapIds,ownerLocalIdMap,shift,lid,owner]
private theorem store_mapped : (store 0).map (RuntimeValue.mapOwners shift) = store 1 := by
  simp [store,payload,core,RuntimeValue.mapOwners,LocalNameTable.mapIds,ownerLocalIdMap,shift,lid,owner]

example : ¬ Function.Surjective shift ∧ store 0 ≠ [] ∧ owner 2 ≠ owner 9 := by
  refine ⟨?_,by decide,by decide⟩
  intro onto
  obtain ⟨before,equal⟩ := onto (owner 0)
  have impossible := congrArg Resolved.DeclarationId.declarationIndex equal
  change before.declarationIndex+1=0 at impossible
  omega

example (extra : Nat) :
    E (owner 2) names rows (store 0)
      (nested (span 1) (span 2) (span 3) (name "x") (name "w") (name "b") inertSource)
      (result (payload 0) one) (store 0) ∧
    evaluateClosedSourceExpression? (extra+4) (owner 3)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) names) (mapRuntimeCapturedOwners shift rows) (store 1)
      (nested (span 1) (span 2) (span 3) (name "x") (name "w") (name "b") inertSource) =
      some (result (payload 1) one,store 1) := by
  have original : E (owner 2) names rows (store 0)
      (nested (span 1) (span 2) (span 3) (name "x") (name "w") (name "b") inertSource)
      (result (payload 0) one) (store 0) := nested_original xn xf wn wf bn bf
  have checked := nested_word_and_skipped_child_covary (span 1) (span 2) (span 3)
    (name "x") (name "w") (name "b") inertSource (owner 2) names rows (store 0)
    (lid 2 0) (lid 2 1) (lid 2 2) (payload 0) one xn xf wn wf bn bf shift shift_injective
  exact ⟨original,by simpa only [payload_mapped,store_mapped,shift,owner] using checked.2.2.2.1 extra⟩

example (n extra : Nat) :
    B (owner 2) names rows (store 0) (matching (span 4) (name "x") ⟨span 5,[]⟩ n) (payload 0) (store 0) ∧
    evaluateClosedSourceBody? (extra+3) (owner 3)
      (LocalNameTable.mapIds (ownerLocalIdMap shift) names) (mapRuntimeCapturedOwners shift rows) (store 1)
      (matching (span 4) (name "x") ⟨span 5,[]⟩ n) = some (payload 1,store 1) := by
  have original : B (owner 2) names rows (store 0) (matching (span 4) (name "x") ⟨span 5,[]⟩ n)
      (payload 0) (store 0) := .wordMatch (.wordLiteral (one_meaning _))
    (original_choice _ _ _ n) (.expression (.reference xn xf))
  have checked := ordered_match_keeps_selected_endpoint_and_budget (span 4) (name "x") ⟨span 5,[]⟩ n
    (owner 2) names rows (store 0) (lid 2 0) (payload 0) xn xf shift shift_injective
  exact ⟨original,by simpa only [payload_mapped,store_mapped,shift,owner] using checked.2.2.2.2.1 extra⟩

end Tests.OwnerCovarianceSymbolic

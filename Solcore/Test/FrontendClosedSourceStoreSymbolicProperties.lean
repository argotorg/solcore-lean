import Solcore.Frontend.ClosedSourceStoreProperties
import Solcore.Frontend.ClosedSourceEvaluatorStoreProperties
import Solcore.Frontend.ClosedSourceEvaluator
import Solcore.Frontend.LocalReferenceProperties
import Solcore.Frontend.SourceLambdaEvaluationProperties
import Solcore.Resolved.LocalScopeProperties

/- Independent original constructors and direct finite runners precede replay.
Stores are replaced only at endpoints, never inside captured values. Arbitrary
mixed payloads, duplicate lexical rows and opaque cell references are retained. -/
set_option autoImplicit false
namespace Tests.ClosedSourceStoreSymbolic
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private abbrev B := ClosedSourceBodyEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def returning (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some (ref s name))⟩]⟩
private def lambda (s : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) : Syntax.Expr :=
  ⟨s,.lambda s ⟨s,[⟨s,.inferred name⟩]⟩ annotation (returning s name)⟩
private def call (s : Syntax.SourceSpan) (f x : Syntax.Expr) : Syntax.Expr := ⟨s,.call f ⟨s,[x]⟩⟩
private def nested (s : Syntax.SourceSpan) (f x : Syntax.Identifier) : Syntax.Expr :=
  call s (ref s f) (call s (ref s f) (ref s x))
private theorem shape (s : Syntax.SourceSpan) (name : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) :
    SourceUnaryLambdaShape (lambda s name annotation) name (returning s name) := .inferred
private theorem reference_run {s name owner names captured store id value}
    (n : Nat) (named : LocalNameTable.Lookup names name.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceExpression? (n+1) owner names captured store (ref s name) = some (value,store) := by
  simp only [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,
    Resolved.LocalScope.lookup?_iff.mpr found,bind,Option.bind_some,pure]
private theorem fresh_body_run (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (value : RuntimeValue) :
    evaluateClosedSourceBody? (n+2) owner ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured) store (returning s name) = some (value,store) := by
  simp only [returning,evaluateClosedSourceBody?]
  exact reference_run (n:=n) .head .head
private theorem nested_original {s name f x annotation co so cn sn cc sc store fid aid value}
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    E co cn cc store (nested s f x) value store :=
  .call (shape s name annotation) (.reference fn ff)
    (.call (shape s name annotation) (.reference fn ff) (.reference an af) (.expression (.reference .head .head)))
    (.expression (.reference .head .head))
private theorem nested_run {s name f x annotation co so cn sn cc sc store fid aid value}
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    evaluateClosedSourceExpression? 4 co cn cc store (nested s f x) = some (value,store) := by
  have f3 := reference_run (s:=s) (owner:=co) (store:=store) 2 fn ff
  have f2 := reference_run (s:=s) (owner:=co) (store:=store) 1 fn ff
  have x2 := reference_run (s:=s) (owner:=co) (store:=store) 1 an af
  have b2 := fresh_body_run s name 0 so sn sc store value
  have b3 := fresh_body_run s name 1 so sn sc store value
  simp only [nested,call,evaluateClosedSourceExpression?,f3,f2,x2,
    sourceUnaryLambdaShape?_iff.mpr (shape s name annotation),b2,b3,bind,Option.bind_some]

/-- Creation and two nested saved identity calls retain every captured field and
arbitrary mixed result when only the external store is replaced. -/
theorem saved_creation_and_nested_calls_replay
    (s : Syntax.SourceSpan) (name f x : Syntax.Identifier) (annotation : Option Syntax.TypeExpr)
    (co so : Resolved.DeclarationId) (cn sn : LocalNameTable) (cc sc : Resolved.LocalScope RuntimeValue)
    (creationStore invocationStore replacement : List RuntimeValue) (fid aid : Resolved.LocalId) (value : RuntimeValue)
    (fn : LocalNameTable.Lookup cn f.value fid)
    (ff : Resolved.LocalScope.Lookup cc fid (.sourceClosure (lambda s name annotation) so sn sc))
    (an : LocalNameTable.Lookup cn x.value aid) (af : Resolved.LocalScope.Lookup cc aid value) :
    E so sn sc creationStore (lambda s name annotation) (.sourceClosure (lambda s name annotation) so sn sc) creationStore ∧
    E co cn cc invocationStore (nested s f x) value invocationStore ∧
    evaluateClosedSourceExpression? 4 co cn cc invocationStore (nested s f x) = some (value,invocationStore) ∧
    E so sn sc replacement (lambda s name annotation) (.sourceClosure (lambda s name annotation) so sn sc) replacement ∧
    E co cn cc replacement (nested s f x) value replacement ∧
    (∀ actual final, E co cn cc invocationStore (nested s f x) actual final → final = invocationStore) ∧
    evaluateClosedSourceExpression? 4 co cn cc replacement (nested s f x) = some (value,replacement) ∧
    (∀ budget, evaluateClosedSourceExpression? budget co cn cc replacement (nested s f x) =
      (evaluateClosedSourceExpression? budget co cn cc invocationStore (nested s f x)).map (fun ep => (ep.1,replacement))) ∧
    evaluateClosedSourceExpression? 1 so sn sc replacement (lambda s name annotation) =
      some (.sourceClosure (lambda s name annotation) so sn sc,replacement) := by
  have created : E so sn sc creationStore (lambda s name annotation)
      (.sourceClosure (lambda s name annotation) so sn sc) creationStore := .creation (shape s name annotation)
  have original : E co cn cc invocationStore (nested s f x) value invocationStore := nested_original fn ff an af
  have direct := nested_run (co:=co) (store:=invocationStore) fn ff an af
  have creationRun : evaluateClosedSourceExpression? 1 so sn sc creationStore (lambda s name annotation) =
      some (.sourceClosure (lambda s name annotation) so sn sc,creationStore) := by
    simp only [lambda,evaluateClosedSourceExpression?,sourceUnaryLambdaShape?,bind,Option.bind_some,pure]
  have replay := fun budget => evaluateClosedSourceExpression?_replay_store budget co cn cc invocationStore replacement (nested s f x)
  exact ⟨created,original,direct,created.replay_store replacement,original.replay_store replacement,
    fun _ _ evaluated => evaluated.store_eq,by simpa only [direct,Option.map_some] using replay 4,replay,
    by simpa only [creationRun,Option.map_some] using
      evaluateClosedSourceExpression?_replay_store 1 so sn sc creationStore replacement (lambda s name annotation)⟩

private def skipped (s : Syntax.SourceSpan) (guard : Syntax.Identifier) (bad : Syntax.Expr) : Syntax.Expr :=
  ⟨s,.binary (ref s guard) ⟨s,.logicalAnd⟩ bad⟩
/-- No assumption about the skipped child is needed, even when it cannot run. -/
theorem skipped_child_keeps_full_store
    (s : Syntax.SourceSpan) (guard : Syntax.Identifier) (bad : Syntax.Expr)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (initial replacement : List RuntimeValue) (id : Resolved.LocalId)
    (named : LocalNameTable.Lookup names guard.value id) (found : Resolved.LocalScope.Lookup captured id (.bool false)) :
    E owner names captured initial (skipped s guard bad) (.bool false) initial ∧
    evaluateClosedSourceExpression? 1 owner names captured initial (skipped s guard bad) = none ∧
    evaluateClosedSourceExpression? 2 owner names captured initial (skipped s guard bad) = some (.bool false,initial) ∧
    E owner names captured replacement (skipped s guard bad) (.bool false) replacement ∧
    evaluateClosedSourceExpression? 1 owner names captured replacement (skipped s guard bad) = none ∧
    evaluateClosedSourceExpression? 2 owner names captured replacement (skipped s guard bad) = some (.bool false,replacement) ∧
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured replacement (skipped s guard bad) =
      (evaluateClosedSourceExpression? budget owner names captured initial (skipped s guard bad)).map (fun ep => (ep.1,replacement))) := by
  have original : E owner names captured initial (skipped s guard bad) (.bool false) initial :=
    .andFalse (.reference named found)
  have low : evaluateClosedSourceExpression? 1 owner names captured initial (skipped s guard bad) = none := by
    simp [skipped,evaluateClosedSourceExpression?]
  have direct : evaluateClosedSourceExpression? 2 owner names captured initial (skipped s guard bad) = some (.bool false,initial) := by
    simp only [skipped,evaluateClosedSourceExpression?,reference_run 0 named found,bind,Option.bind_some,Bool.false_eq_true,↓reduceIte,pure]
  have replay := fun budget => evaluateClosedSourceExpression?_replay_store budget owner names captured initial replacement (skipped s guard bad)
  exact ⟨original,low,direct,original.replay_store replacement,
    by simpa only [low,Option.map_none] using replay 1,
    by simpa only [direct,Option.map_some] using replay 2,replay⟩

private def one : Core.Word := ⟨1,by decide⟩
private def literal (s : Syntax.SourceSpan) (text : String) : Syntax.CoreLiteral := ⟨s,.decimal text⟩
private def badBody (s : Syntax.SourceSpan) : Syntax.Block :=
  ⟨s,[⟨s,.returnStmt (some ⟨s,.literal ⟨s,.string "unselected"⟩⟩)⟩]⟩
private def arm (s : Syntax.SourceSpan) (text : String) (body : Syntax.Block) : Syntax.MatchCase :=
  ⟨s,⟨⟨s,.literal (literal s text)⟩,body⟩⟩
private def arms (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Nat → List Syntax.MatchCase
  | 0 => [arm s "1" (returning s name),arm s "1" (badBody s)]
  | n+1 => arm s "0" (badBody s) :: arms s name n
private def matching (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) : Syntax.Statement :=
  ⟨s,.matchWith ⟨s,⟨⟨s,.literal (literal s "1")⟩,[]⟩⟩ ⟨s,⟨arms s name n,some (badBody s)⟩⟩⟩
private def binding (s : Syntax.SourceSpan) (name payload : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat) : Syntax.Block :=
  ⟨s,[⟨s,.letDecl name annotation (some (ref s payload))⟩,matching s name n]⟩
private theorem one_meaning (s : Syntax.SourceSpan) : WordLiteralDenotes (literal s "1") one :=
  .decimal (by decide) (.cons (.decimal (digit:=1) (by decide) rfl) .nil)
private theorem zero_meaning (s : Syntax.SourceSpan) : WordLiteralDenotes (literal s "0") Core.Word.zero :=
  .decimal (by decide) (.cons (.decimal (digit:=0) (by decide) rfl) .nil)
private theorem original_choice (s : Syntax.SourceSpan) (name : Syntax.Identifier) (n : Nat) :
    RuntimeWordMatchChooses (.word one) (arms s name n) (some (badBody s)) (returning s name) (n+1) := by
  induction n with
  | zero => exact .hit (.literal ⟨literal s "1",rfl,one_meaning s⟩)
  | succ n ih => exact .miss (.literal ⟨literal s "0",rfl,zero_meaning s⟩) (by decide) ih
private theorem binding_original {s name payload annotation n owner names captured store id value}
    (named : LocalNameTable.Lookup names payload.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    B owner names captured store (binding s name payload annotation n) value store := by
  have tail : B owner ((name.value,Resolved.freshLocalId owner (names.map Prod.snd))::names)
      ((Resolved.freshLocalId owner (names.map Prod.snd),value)::captured) store ⟨s,[matching s name n]⟩ value store :=
    .wordMatch (.wordLiteral (one_meaning s)) (original_choice s name n) (.expression (.reference .head .head))
  cases annotation with
  | none => exact .inferred (.reference named found) tail
  | some t => exact .binding (.reference named found) tail
private theorem binding_run {s name payload annotation n owner names captured store id value}
    (named : LocalNameTable.Lookup names payload.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    evaluateClosedSourceBody? 4 owner names captured store (binding s name payload annotation n) = some (value,store) := by
  have supplied := reference_run (s:=s) (owner:=owner) (store:=store) 2 named found
  have choice := chooseRuntimeWordMatch?_iff.mpr (original_choice s name n)
  have returned := fresh_body_run s name 0 owner names captured store value
  simp only [binding,matching,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,supplied,
    interpretWordLiteral?_iff.mpr (one_meaning s),choice,returned,bind,Option.bind_some,pure]

/-- Typed or inferred fresh binding shadows duplicate rows. Ordered misses and
the first hit return the same opaque payload, not any unselected bad body. -/
theorem fresh_binding_and_ordered_match_replay
    (s : Syntax.SourceSpan) (name payload : Syntax.Identifier) (annotation : Option Syntax.TypeExpr) (n : Nat)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (initial replacement : List RuntimeValue) (id : Resolved.LocalId) (value : RuntimeValue)
    (named : LocalNameTable.Lookup names payload.value id) (found : Resolved.LocalScope.Lookup captured id value) :
    RuntimeWordMatchChooses (.word one) (arms s name n) (some (badBody s)) (returning s name) (n+1) ∧
    B owner names captured initial (binding s name payload annotation n) value initial ∧
    evaluateClosedSourceBody? 4 owner names captured initial (binding s name payload annotation n) = some (value,initial) ∧
    B owner names captured replacement (binding s name payload annotation n) value replacement ∧
    (∀ actual final, B owner names captured initial (binding s name payload annotation n) actual final → final = initial) ∧
    evaluateClosedSourceBody? 3 owner names captured initial (binding s name payload annotation n) = none ∧
    evaluateClosedSourceBody? 3 owner names captured replacement (binding s name payload annotation n) = none ∧
    evaluateClosedSourceBody? 4 owner names captured replacement (binding s name payload annotation n) = some (value,replacement) ∧
    (∀ budget, evaluateClosedSourceBody? budget owner names captured replacement (binding s name payload annotation n) =
      (evaluateClosedSourceBody? budget owner names captured initial (binding s name payload annotation n)).map (fun ep => (ep.1,replacement))) := by
  have choice := original_choice s name n
  have original : B owner names captured initial (binding s name payload annotation n) value initial := binding_original named found
  have direct := binding_run (s:=s) (name:=name) (annotation:=annotation) (n:=n) (owner:=owner) (store:=initial) named found
  have low : evaluateClosedSourceBody? 3 owner names captured initial (binding s name payload annotation n) = none := by
    have supplied := reference_run (s:=s) (owner:=owner) (store:=initial) 1 named found
    simp only [binding,matching,evaluateClosedSourceBody?,evaluateClosedSourceExpression?,supplied,
      interpretWordLiteral?_iff.mpr (one_meaning s),chooseRuntimeWordMatch?_iff.mpr choice,returning,
      evaluateClosedSourceBody?,evaluateClosedSourceExpression?,bind,Option.bind_some,pure]
  have replay := fun budget => evaluateClosedSourceBody?_replay_store budget owner names captured initial replacement (binding s name payload annotation n)
  exact ⟨choice,original,direct,original.replay_store replacement,fun _ _ evaluated => evaluated.store_eq,low,
    by simpa only [low,Option.map_none] using replay 3,
    by simpa only [direct,Option.map_some] using replay 4,replay⟩

private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"StoreReplay",by decide⟩],by decide⟩⟩,n⟩
private def co := owner 909
private def so := owner 309
private def cid (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def sid (n : Nat) : Resolved.LocalId := ⟨so,n⟩
private def cs : Syntax.SourceSpan := ⟨⟨.main,"store-replay.sol"⟩,0,1⟩
private def idn (text : String) : Syntax.Identifier := ⟨cs,text⟩
private def opaqueValue : RuntimeValue := .pair (.cellRef .word 700)
  (.coreClosure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 900])
private def sn : LocalNameTable := [("p",sid 4),("p",sid 8)]
private def sc : Resolved.LocalScope RuntimeValue := [(sid 4,opaqueValue),(sid 4,.unit),(sid 8,.bool true)]
private def saved : RuntimeValue := .sourceClosure (lambda cs (idn "p") none) so sn sc
private def payload : RuntimeValue := .pair saved opaqueValue
private def cn : LocalNameTable := [("f",cid 0),("x",cid 1),("f",cid 9),("x",cid 99)]
private def cc : Resolved.LocalScope RuntimeValue := [(cid 0,saved),(cid 0,.unit),(cid 1,payload),(cid 1,.bool false)]
private def initial : List RuntimeValue := [opaqueValue,.hostFunction .storageWrite,saved,.cellRef .word 900]

example : co ≠ so ∧ initial ≠ [] := by decide

example (replacement : List RuntimeValue) : E co cn cc replacement (nested cs (idn "f") (idn "x")) payload replacement ∧
    evaluateClosedSourceExpression? 4 co cn cc replacement (nested cs (idn "f") (idn "x")) = some (payload,replacement) := by
  have original : E co cn cc initial (nested cs (idn "f") (idn "x")) payload initial :=
    nested_original (so:=so) (sn:=sn) (sc:=sc) (name:=idn "p") (annotation:=none) .head .head
      (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
  have result := saved_creation_and_nested_calls_replay cs (idn "p") (idn "f") (idn "x") none
    co so cn sn cc sc [payload] initial replacement (cid 0) (cid 1) payload .head .head
      (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
  exact ⟨result.2.2.2.2.1,result.2.2.2.2.2.2.1⟩

example (replacement : List RuntimeValue) (n : Nat) :
    B co cn cc replacement (binding cs (idn "x") (idn "x") none n) payload replacement ∧
    evaluateClosedSourceBody? 4 co cn cc replacement (binding cs (idn "x") (idn "x") none n) = some (payload,replacement) := by
  have original : B co cn cc initial (binding cs (idn "x") (idn "x") none n) payload initial :=
    binding_original (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
  have result := fresh_binding_and_ordered_match_replay cs (idn "x") (idn "x") none n
    co cn cc initial replacement (cid 1) payload
      (.tail (by decide) .head) (.tail (by decide) (.tail (by decide) .head))
  exact ⟨result.2.2.2.1,result.2.2.2.2.2.2.2.1⟩

example (replacement : List RuntimeValue) :
    evaluateClosedSourceExpression? 1 co [("b",cid 2)] [(cid 2,.bool false)] initial (ref cs (idn "missing")) = none ∧
    E co [("b",cid 2)] [(cid 2,.bool false)] replacement
      (skipped cs (idn "b") (ref cs (idn "missing"))) (.bool false) replacement := by
  have original : E co [("b",cid 2)] [(cid 2,.bool false)] initial
      (skipped cs (idn "b") (ref cs (idn "missing"))) (.bool false) initial := .andFalse (.reference .head .head)
  have result := skipped_child_keeps_full_store cs (idn "b") (ref cs (idn "missing")) co
    [("b",cid 2)] [(cid 2,.bool false)] initial replacement (cid 2) .head .head
  exact ⟨by simp [evaluateClosedSourceExpression?,ref,idn,LocalNameTable.lookup?],result.2.2.2.1⟩
end Tests.ClosedSourceStoreSymbolic

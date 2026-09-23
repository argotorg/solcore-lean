import Solcore.Frontend.ClosedSource

/- Store contents cannot supply lexical captures or execute an opaque host value.
Independent original exclusions and direct finite runs precede replay consumers. -/
set_option autoImplicit false
namespace Tests.ClosedSourceStoreBoundaries
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates
private def ref (s : Syntax.SourceSpan) (name : Syntax.Identifier) : Syntax.Expr := ⟨s,.identifier name⟩
private def call (s : Syntax.SourceSpan) (f x : Syntax.Identifier) : Syntax.Expr :=
  ⟨s,.call (ref s f) ⟨s,[ref s x]⟩⟩
private theorem exclude_replay {owner names captured initialStore source}
    (original : ∀ value final, ¬ E owner names captured initialStore source value final) :
    ∀ replacement value final, ¬ E owner names captured replacement source value final := by
  intro replacement value final other
  exact original value initialStore (other.replay_store initialStore)

/-- A missing lexical capture stays missing even when the replacement store contains data. -/
theorem replacing_store_does_not_fill_missing_capture
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (initialStore : List RuntimeValue) (s : Syntax.SourceSpan) (name : Syntax.Identifier) (id : Resolved.LocalId)
    (named : LocalNameTable.Lookup names name.value id) (missing : Resolved.LocalScope.lookup? captured id = none) :
    (∀ value final, ¬ E owner names captured initialStore (ref s name) value final) ∧
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore (ref s name) = none) ∧
    (∀ replacement value final, ¬ E owner names captured replacement (ref s name) value final) ∧
    (∀ replacement budget, evaluateClosedSourceExpression? budget owner names captured replacement (ref s name) = none) := by
  have absent : ∀ value final, ¬ E owner names captured initialStore (ref s name) value final := by
    intro value final original
    cases original with
    | creation impossible => cases impossible
    | reference actualName actualValue =>
      cases actualName.id_unique named
      have accepted := Resolved.LocalScope.lookup?_iff.mpr actualValue
      rw [missing] at accepted
      cases accepted
  have direct : ∀ store budget, evaluateClosedSourceExpression? budget owner names captured store (ref s name) = none := by
    intro store budget
    cases budget <;> simp [ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr named,missing]
  have replayed : ∀ replacement budget, evaluateClosedSourceExpression? budget owner names captured replacement (ref s name) = none := by
    intro replacement budget
    rw [evaluateClosedSourceExpression?_replay_store budget owner names captured initialStore replacement,
      direct initialStore budget]
    rfl
  exact ⟨absent,direct initialStore,exclude_replay absent,replayed⟩

/-- Successful lexical input lookup does not make a host-function value a source closure. -/
theorem replacing_store_does_not_execute_host_callee
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (initialStore : List RuntimeValue) (s : Syntax.SourceSpan) (f x : Syntax.Identifier)
    (fid xid : Resolved.LocalId) (argument : RuntimeValue)
    (fn : LocalNameTable.Lookup names f.value fid)
    (fv : Resolved.LocalScope.Lookup captured fid (.hostFunction .storageWrite))
    (xn : LocalNameTable.Lookup names x.value xid) (xv : Resolved.LocalScope.Lookup captured xid argument) :
    E owner names captured initialStore (ref s f) (.hostFunction .storageWrite) initialStore ∧
    E owner names captured initialStore (ref s x) argument initialStore ∧
    (∀ value final, ¬ E owner names captured initialStore (call s f x) value final) ∧
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured initialStore (call s f x) = none) ∧
    (∀ replacement value final, ¬ E owner names captured replacement (call s f x) value final) ∧
    (∀ replacement budget, evaluateClosedSourceExpression? budget owner names captured replacement (call s f x) = none) := by
  have picked : E owner names captured initialStore (ref s f) (.hostFunction .storageWrite) initialStore := .reference fn fv
  have supplied : E owner names captured initialStore (ref s x) argument initialStore := .reference xn xv
  have absent : ∀ value final, ¬ E owner names captured initialStore (call s f x) value final := by
    intro value final original
    cases original with
    | creation impossible => cases impossible
    | call _ callee _ _ => cases (callee.deterministic picked).1
  have direct : ∀ store budget, evaluateClosedSourceExpression? budget owner names captured store (call s f x) = none := by
    intro store budget
    cases budget with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ budget =>
      cases budget <;> simp [call,ref,evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr fn,
        Resolved.LocalScope.lookup?_iff.mpr fv,LocalNameTable.lookup?_iff.mpr xn,Resolved.LocalScope.lookup?_iff.mpr xv]
  have replayed : ∀ replacement budget, evaluateClosedSourceExpression? budget owner names captured replacement (call s f x) = none := by
    intro replacement budget
    rw [evaluateClosedSourceExpression?_replay_store budget owner names captured initialStore replacement,
      direct initialStore budget]
    rfl
  exact ⟨picked,supplied,absent,direct initialStore,exclude_replay absent,replayed⟩

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"StoreBoundary",by decide⟩],by decide⟩⟩,309⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def s : Syntax.SourceSpan := ⟨⟨.main,"store-boundary.sol"⟩,0,1⟩
private def name (n : String) : Syntax.Identifier := ⟨s,n⟩
private def coreValue : RuntimeValue := .ofCore
  (.closure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 700])
private def saved : RuntimeValue := .sourceClosure ⟨s,.tuple ⟨s,[]⟩⟩ owner
  [("x",id 77),("x",id 88)] [(id 77,coreValue),(id 77,.unit)]
private def payload : RuntimeValue := .pair coreValue (.cellRef .word 900)
private def names : LocalNameTable := [("h",id 0),("x",id 1),("missing",id 2),("h",id 1),("x",id 0)]
private def captured : Resolved.LocalScope RuntimeValue :=
  [(id 0,.hostFunction .storageWrite),(id 0,saved),(id 1,payload),(id 1,.unit)]
private def initial : List RuntimeValue := [saved,payload]
private def replacement : List RuntimeValue := [.cellRef .word 900,.hostFunction .storageWrite,coreValue]

example : initial ≠ replacement ∧ replacement ≠ [] := by
  constructor
  · intro equal; cases equal
  · intro equal; cases equal

example : ∀ budget, evaluateClosedSourceExpression? budget owner names captured replacement (ref s (name "missing")) = none := by
  have absent := replacing_store_does_not_fill_missing_capture owner names captured initial s (name "missing") (id 2)
    (.tail (by decide) (.tail (by decide) .head)) (by rfl)
  exact absent.2.2.2 replacement

example : E owner names captured initial (ref s (name "x")) payload initial ∧
    (∀ store budget, evaluateClosedSourceExpression? budget owner names captured store (call s (name "h") (name "x")) = none) := by
  have absent := replacing_store_does_not_execute_host_callee owner names captured initial s (name "h") (name "x")
    (id 0) (id 1) payload .head .head (.tail (by decide) .head)
    (.tail (by decide) (.tail (by decide) .head))
  exact ⟨absent.2.1,absent.2.2.2.2.2⟩

end Tests.ClosedSourceStoreBoundaries

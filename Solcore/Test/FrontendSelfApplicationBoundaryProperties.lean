import Solcore.Frontend.SelfApplication
import Solcore.Frontend.ClosedSource

/- The body gate excludes self-calling return syntax by constructor inversion.
Only strict wrappers occur below: grouping and either side of a binary tuple.
No unselected child is required. Other children and all stores stay arbitrary. -/
set_option autoImplicit false
namespace Tests.SelfApplicationBoundaries
open Solcore Solcore.Frontend
private abbrev E := ClosedSourceExpressionEvaluates

/-- The saved-body data gate required by prior bounded-input laws excludes this
self-application syntax independently of its semantic non-return theorem. -/
theorem self_calling_body_is_outside_data
    {body : Syntax.Block} {name : Syntax.Identifier} (self : SourceSelfApplicationBody body name) :
    ¬ ClosedSourceDataBody body := by
  cases self
  intro admitted
  cases admitted with
  | expression child => cases child

private inductive Frame where
  | group (span : Syntax.SourceSpan)
  | left (span tupleSpan : Syntax.SourceSpan) (other : Syntax.Expr)
  | right (span tupleSpan : Syntax.SourceSpan) (other : Syntax.Expr)
private def wrap (frames : List Frame) (hole : Syntax.Expr) : Syntax.Expr :=
  match frames with
  | [] => hole
  | .group s :: rest => ⟨s,.group (wrap rest hole)⟩
  | .left s t other :: rest => ⟨s,.tuple ⟨t,[wrap rest hole,other]⟩⟩
  | .right s t other :: rest => ⟨s,.tuple ⟨t,[other,wrap rest hole]⟩⟩

private theorem strict_wrappers_none {owner names captured hole}
    (child : ∀ budget store, evaluateClosedSourceExpression? budget owner names captured store hole = none)
    (frames : List Frame) :
    ∀ budget store, evaluateClosedSourceExpression? budget owner names captured store (wrap frames hole) = none := by
  induction frames with
  | nil => exact child
  | cons frame frames ih =>
    intro budget store
    cases budget with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ n =>
      cases frame with
      | group s => simp only [wrap,evaluateClosedSourceExpression?,ih]
      | left s t other => simp only [wrap,evaluateClosedSourceExpression?,ih,bind,Option.bind_none]
      | right s t other =>
        simp only [wrap,evaluateClosedSourceExpression?]
        cases evaluateClosedSourceExpression? n owner names captured store other with
        | none => simp only [bind,Option.bind_none]
        | some endpoint => simp only [ih,bind,Option.bind_some,Option.bind_none]

private theorem strict_wrappers_no_original {owner names captured hole}
    (child : ∀ store value final, ¬ E owner names captured store hole value final)
    (frames : List Frame) :
    ∀ store value final, ¬ E owner names captured store (wrap frames hole) value final := by
  induction frames with
  | nil => exact child
  | cons frame frames ih =>
    intro store value final original
    cases frame with
    | group s =>
      cases original with
      | creation impossible => cases impossible
      | group evaluated => exact ih _ _ _ evaluated
    | left s t other =>
      cases original with
      | creation impossible => cases impossible
      | pair left right => exact ih _ _ _ left
    | right s t other =>
      cases original with
      | creation impossible => cases impossible
      | pair left right => exact ih _ _ _ right

/-- Grouping and strict tuple contexts cannot turn this exact self-application
into a successful finite endpoint; intermediate stores are never guessed. -/
theorem strict_wrappers_preserve_self_non_return
    {left right : Syntax.Expr} {leftName rightName : Syntax.Identifier} {leftBody rightBody : Syntax.Block}
    (leftShape : SourceUnaryLambdaShape left leftName leftBody) (leftSelf : SourceSelfApplicationBody leftBody leftName)
    (rightShape : SourceUnaryLambdaShape right rightName rightBody) (rightSelf : SourceSelfApplicationBody rightBody rightName)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (callSpan argumentsSpan : Syntax.SourceSpan) (frames : List Frame) (store : List RuntimeValue) :
    let whole : Syntax.Expr := ⟨callSpan,.call left ⟨argumentsSpan,[right]⟩⟩
    (∀ budget, evaluateClosedSourceExpression? budget owner names captured store (wrap frames whole) = none) ∧
    (∀ value final, ¬ E owner names captured store (wrap frames whole) value final) := by
  intro whole
  have childNone : ∀ budget store, evaluateClosedSourceExpression? budget owner names captured store whole = none :=
    fun budget store => directSelfApplication_none leftShape leftSelf rightShape rightSelf owner names captured store callSpan argumentsSpan budget
  have childAbsent : ∀ store value final, ¬ E owner names captured store whole value final :=
    fun store value final => directSelfApplication_no_original leftShape leftSelf rightShape rightSelf
      owner names captured store callSpan argumentsSpan value final
  exact ⟨fun budget => strict_wrappers_none childNone frames budget store,
    fun value final => strict_wrappers_no_original childAbsent frames store value final⟩

private def owner (n : Nat) : Resolved.DeclarationId :=
  ⟨⟨.main,⟨[⟨"SelfBoundary",by decide⟩],by decide⟩⟩,n⟩
private def co := owner 910
private def foreignOwner := owner 310
private def id (n : Nat) : Resolved.LocalId := ⟨co,n⟩
private def span (n : Nat) : Syntax.SourceSpan := ⟨⟨.main,"self-boundary.sol"⟩,n,n+1⟩
private def name (n : Nat) (text : String) : Syntax.Identifier := ⟨span n,text⟩
private def selfBody (n : Nat) (text : String) : Syntax.Block :=
  ⟨span n,[⟨span (n+1),.returnStmt (some ⟨span (n+2),.call
    ⟨span (n+3),.identifier (name (n+4) text)⟩
    ⟨span (n+5),[⟨span (n+6),.identifier (name (n+7) text)⟩]⟩⟩)⟩]⟩
private def source (n : Nat) (text : String) : Syntax.Expr :=
  ⟨span (n+8),.lambda (span (n+9)) ⟨span (n+10),[⟨span (n+11),.inferred (name (n+12) text)⟩]⟩
    none (selfBody n text)⟩
private def opaqueValue : RuntimeValue := .pair (.cellRef .word 700)
  (.coreClosure .unit .word (.var 99) [.hostFunction .storageWrite,.cellRef .word 900])
private def names : LocalNameTable := [("p",id 1),("p",id 99),("x",id 2),("x",id 2)]
private def captured : Resolved.LocalScope RuntimeValue :=
  [(id 1,opaqueValue),(id 1,.unit),(id 2,.sourceClosure (source 40 "foreign") foreignOwner [] []),(id 99,.bool false)]
private def store : List RuntimeValue := [opaqueValue,.cellRef .word 900,.hostFunction .storageWrite]
private def other : Syntax.Expr := ⟨span 90,.identifier (name 91 "x")⟩
private def frames : List Frame := [.group (span 80),.right (span 81) (span 82) other,
  .group (span 83),.left (span 84) (span 85) ⟨span 86,.literal ⟨span 87,.string "unreachable"⟩⟩]

example : co ≠ foreignOwner ∧ store ≠ [] := by decide
example : ¬ ClosedSourceDataBody (selfBody 0 "p") :=
  self_calling_body_is_outside_data (name:=name 12 "p") (.returning rfl rfl)
example : E co names captured store other (.sourceClosure (source 40 "foreign") foreignOwner [] []) store :=
  .reference (.tail (by decide) (.tail (by decide) .head))
    (.tail (by decide) (.tail (by decide) .head))
example (replacement : List RuntimeValue) :
    let whole : Syntax.Expr := ⟨span 70,.call (source 0 "p") ⟨span 71,[source 20 "r"]⟩⟩
    (∀ budget, evaluateClosedSourceExpression? budget co names captured replacement (wrap frames whole) = none) ∧
    (∀ value final, ¬ E co names captured replacement (wrap frames whole) value final) := by
  exact strict_wrappers_preserve_self_non_return
    (left:=source 0 "p") (right:=source 20 "r") (leftName:=name 12 "p") SourceUnaryLambdaShape.inferred (.returning rfl rfl)
    (rightName:=name 32 "r") SourceUnaryLambdaShape.inferred (.returning rfl rfl)
    co names captured (span 70) (span 71) frames replacement
end Tests.SelfApplicationBoundaries

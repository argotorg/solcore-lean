import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeControl
import Solcore.SourceSemantics.CoreLowering.CompatibleNamedBodyMeaning

/-! The function finish retains the same reached flow state. Ordinary results
keep its success readiness. Source faults and escaped loop control keep its
fault facet; no heap or record witness is reconstructed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.FunctionFinish
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedLexicalContracts.Stateful.WithReady (Readiness)
universe u v
variable {Records : Type v} {protocol : Protocol.{u, v} Records}
  (readiness : Readiness protocol)

def PostReady (context : SourceSemantics.Context) (outcome : Dynamic.ExpressionOutcome)
    {index : Index} (reached : protocol.State index) : Prop :=
  match outcome with
  | .value _ => readiness.Ready context reached
  | .fault _ => readiness.FaultReady reached

def Reached (context : SourceSemantics.Context) (outcome : Dynamic.ExpressionOutcome)
    {initial : Index} (first : protocol.State initial) (final : Index) : Prop :=
  ∃ reached : protocol.State final, protocol.Relates first reached ∧ PostReady readiness context outcome reached

variable {readiness}

theorem post_of_exit {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    {control : Dynamic.ControlOutcome} {outcome : Dynamic.ExpressionOutcome}
    {index : Index} {reached : protocol.State index}
    (exit : CompatibleNamedBody.Exit expected control outcome)
    (post : RecursiveNamedLexicalContracts.Stateful.WithReady.PostReady readiness context control reached) :
    PostReady readiness context outcome reached := by
  cases exit with
  | returned _ => exact post
  | unit _ _ => exact post
  | fault _ => exact post
  | breaking _ => exact readiness.ready_fault post
  | continuing _ => exact readiness.ready_fault post

theorem Reached.forget {context : SourceSemantics.Context} {outcome : Dynamic.ExpressionOutcome}
    {initial final : Index} {first : protocol.State initial}
    (post : Reached readiness context outcome first final) : Transition protocol first final := by
  obtain ⟨reached, related, _⟩ := post
  exact ⟨reached, related⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.FunctionFinish

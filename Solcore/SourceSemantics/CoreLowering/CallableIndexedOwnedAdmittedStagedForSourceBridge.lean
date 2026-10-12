import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeadContracts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForSourceInversion

/-! Ordered initialization and the finite loop reconstruct the original Source
statement, including the suffix reached in the restored outer environment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForSourceBridge
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts
variable {program : Program} {stages : Registry} {invocation : Scope}
  {context finalContext : SourceSemantics.Context} {environment inner : Dynamic.Environment}
  {before middle after : Dynamic.Heap} {initial post : List ForItemForm}
  {test : ExpressionId} {body rest : List StatementId} {size tailSize : Nat}
  {id : StatementId} {node : StatementNode} {mode : Bool} {outcome : BodyOutcome}

theorem fallthrough_environment
    (trace : Trace program stages invocation context environment before initial test post body size (.fallthrough inner) after) :
    inner = environment := by
  generalize resultEq : BodyOutcome.fallthrough inner = result at trace
  cases trace with
  | initializerFault _ => cases resultEq
  | @loop _ _ _ _ _ result _ _ _ => cases result <;> simp_all [BodyOutcome.restore]

theorem loop_restore
    (trace : Size.ForLoop program stages size invocation context environment before test post body outcome after) :
    outcome.restore environment = outcome := by
  cases outcome with
  | fallthrough inner =>
      cases CallableIndexedOwnedPreparedStagedScopedForSourceInversion.fallthrough_environment trace
      rfl
  | returned | fault => rfl

theorem returned {value : Dynamic.Value}
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial test post body)
    (trace : Trace program stages invocation context environment before initial test post body size (.returned value) after) :
    Size.StatementsIn program stages mode size invocation context environment before (id :: rest) context (.returned value) after := by
  generalize resultEq : BodyOutcome.returned value = result at trace
  cases trace with
  | initializerFault _ => cases resultEq
  | @loop initialSize loopSize loopContext loopEnvironment initialized result _ initializedTrace loopTrace =>
      cases result <;> simp_all [BodyOutcome.restore]
      exact .forReturned (lookupStatement?_sound found) form initializedTrace loopTrace

theorem fault {failure : Failure}
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial test post body)
    (trace : Trace program stages invocation context environment before initial test post body size (.fault failure) after) :
    Size.StatementsIn program stages mode size invocation context environment before (id :: rest) context (.fault failure) after := by
  generalize resultEq : BodyOutcome.fault failure = result at trace
  cases trace with
  | initializerFault initializedTrace =>
      cases resultEq
      exact .forInitializerFault (lookupStatement?_sound found) form initializedTrace
  | @loop initialSize loopSize loopContext loopEnvironment initialized result _ initializedTrace loopTrace =>
      cases result <;> simp_all [BodyOutcome.restore]
      exact .forFault (lookupStatement?_sound found) form initializedTrace loopTrace

theorem fallthrough
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial test post body)
    (trace : Trace program stages invocation context environment before initial test post body size (.fallthrough environment) middle)
    (tail : Size.StatementsIn program stages mode tailSize invocation context environment middle rest finalContext outcome after) :
    Size.StatementsIn program stages mode (size + tailSize) invocation context environment before (id :: rest) finalContext outcome after := by
  generalize resultEq : BodyOutcome.fallthrough environment = result at trace
  cases trace with
  | initializerFault _ => cases resultEq
  | @loop initialSize loopSize loopContext loopEnvironment initialized result _ initializedTrace loopTrace =>
      cases result <;> simp_all [BodyOutcome.restore]
      have same := CallableIndexedOwnedPreparedStagedScopedForSourceInversion.fallthrough_environment loopTrace
      subst same
      simpa only [Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, Nat.add_comm tailSize 1] using
        (Size.StatementsIn.forFallthrough (mode := mode) (rest := rest)
          (lookupStatement?_sound found) form initializedTrace loopTrace tail)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForSourceBridge

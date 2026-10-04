import Solcore.SourceSemantics.CoreLowering.CoreEvaluationSize
import Solcore.Frontend.SourceCoreCallableContracts
import Solcore.SourceSemantics.CoreLowering.CallStageBoundary

/-! Original Core completion of the actual two-guard indirect call protocol.
Every child grade comes from the supplied evaluation. The guard tokens and
all intermediate stores remain explicit until actual callable representation
identifies the tokens. No called-body or source execution law is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndirectCallBounds
open Core CoreProof Frontend.SourceCoreCallableContracts

inductive BindCompletion (budget : Nat) (environment : Core.Environment)
    (before : Store) (output : Ty) (computation body : Expr) : Value → Store → Prop where
  | failed {size : Nat} {input : Ty} {payload : Value} {after : Store}
      (child : EvaluationSize size environment before computation (.inLeft input payload) after)
      (strict : size < budget) :
      BindCompletion budget environment before output computation body (.inLeft output payload) after
  | continued {childSize bodySize : Nat} {input : Ty} {payload : Value} {middle after : Store} {value : Value}
      (child : EvaluationSize childSize environment before computation (.inRight input payload) middle)
      (bodyTrace : EvaluationSize bodySize (payload :: environment) middle body value after)
      (childStrict : childSize < budget) (bodyStrict : bodySize < budget) :
      BindCompletion budget environment before output computation body value after

/-- Invert the existing sum case; the failure branch is its original var read. -/
theorem bind_completed {size budget : Nat} {environment : Core.Environment} {before after : Store}
    {output : Ty} {computation body : Expr} {value : Value}
    (evaluation : EvaluationSize size environment before
      (LanguageResult.bind output computation body) value after)
    (within : size ≤ budget) :
    BindCompletion budget environment before output computation body value after := by
  cases evaluation with
  | caseLeft child failure =>
      cases failure with
      | inLeft payload =>
          cases payload with
          | var selected =>
              simp only [List.getElem?_cons_zero] at selected
              cases Option.some.inj selected
              exact .failed child (by omega)
  | caseRight child body => exact .continued child body (by omega) (by omega)

/-- The four successive binds expose the exact hidden environment prefixes. -/
inductive Completion (budget : Nat) (gates : List CallableContract.Gate) (unknown : Word)
    (result : Ty) (callee arguments : Expr) (environment : Core.Environment) (before : Store) :
    Value → Store → Prop where
  | calleeFailure {size : Nat} {input : Ty} {payload : Value} {after : Store}
      (calleeTrace : EvaluationSize size environment before callee (.inLeft input payload) after)
      (strict : size < budget) : Completion budget gates unknown result callee arguments environment before
        (.inLeft result payload) after
  | stageRejected {calleeSize gateSize : Nat} {input gateInput : Ty}
      {function fault : Value} {calleeStore after : Store}
      (calleeTrace : EvaluationSize calleeSize environment before callee (.inRight input function) calleeStore)
      (gate : EvaluationSize gateSize (function :: environment) calleeStore
        (CallableContract.dispatch gates .beforeArguments unknown (.second (.var 0)))
        (.inLeft gateInput fault) after)
      (calleeStrict : calleeSize < budget) (gateStrict : gateSize < budget) :
      Completion budget gates unknown result callee arguments environment before (.inLeft result fault) after
  | argumentFailure {calleeSize gateSize argumentsSize : Nat} {input gateInput argumentInput : Ty}
      {function token fault : Value} {calleeStore argumentStore after : Store}
      (calleeTrace : EvaluationSize calleeSize environment before callee (.inRight input function) calleeStore)
      (gate : EvaluationSize gateSize (function :: environment) calleeStore
        (CallableContract.dispatch gates .beforeArguments unknown (.second (.var 0)))
        (.inRight gateInput token) argumentStore)
      (argumentsTrace : EvaluationSize argumentsSize (token :: function :: environment) argumentStore
        ((arguments.weakenAt 0).weakenAt 0) (.inLeft argumentInput fault) after)
      (calleeStrict : calleeSize < budget) (gateStrict : gateSize < budget)
      (argumentsStrict : argumentsSize < budget) :
      Completion budget gates unknown result callee arguments environment before (.inLeft result fault) after
  | arityRejected {calleeSize gateSize argumentsSize aritySize : Nat}
      {input gateInput argumentInput arityInput : Ty} {function token argument fault : Value}
      {calleeStore argumentStore arityStore after : Store}
      (calleeTrace : EvaluationSize calleeSize environment before callee (.inRight input function) calleeStore)
      (gate : EvaluationSize gateSize (function :: environment) calleeStore
        (CallableContract.dispatch gates .beforeArguments unknown (.second (.var 0)))
        (.inRight gateInput token) argumentStore)
      (argumentsTrace : EvaluationSize argumentsSize (token :: function :: environment) argumentStore
        ((arguments.weakenAt 0).weakenAt 0) (.inRight argumentInput argument) arityStore)
      (arity : EvaluationSize aritySize (argument :: token :: function :: environment) arityStore
        (CallableContract.dispatch gates .beforeApplication unknown (.second (.var 2)))
        (.inLeft arityInput fault) after)
      (calleeStrict : calleeSize < budget) (gateStrict : gateSize < budget)
      (argumentsStrict : argumentsSize < budget) (arityStrict : aritySize < budget) :
      Completion budget gates unknown result callee arguments environment before (.inLeft result fault) after
  | applied {calleeSize gateSize argumentsSize aritySize functionSize parameterSize bodySize : Nat}
      {input gateInput argumentInput arityInput parameter resultType : Ty}
      {function token argument arityToken parameterValue value : Value}
      {captured : Core.Environment} {body : Expr}
      {calleeStore argumentStore arityStore applicationStore parameterStore bodyStore after : Store}
      (calleeTrace : EvaluationSize calleeSize environment before callee (.inRight input function) calleeStore)
      (gate : EvaluationSize gateSize (function :: environment) calleeStore
        (CallableContract.dispatch gates .beforeArguments unknown (.second (.var 0)))
        (.inRight gateInput token) argumentStore)
      (argumentsTrace : EvaluationSize argumentsSize (token :: function :: environment) argumentStore
        ((arguments.weakenAt 0).weakenAt 0) (.inRight argumentInput argument) arityStore)
      (arity : EvaluationSize aritySize (argument :: token :: function :: environment) arityStore
        (CallableContract.dispatch gates .beforeApplication unknown (.second (.var 2)))
        (.inRight arityInput arityToken) applicationStore)
      (functionTrace : EvaluationSize functionSize (arityToken :: argument :: token :: function :: environment) applicationStore
        (.second (.first (.var 3))) (.closure parameter resultType body captured) parameterStore)
      (parameterTrace : EvaluationSize parameterSize (arityToken :: argument :: token :: function :: environment) parameterStore
        (.var 1) parameterValue bodyStore)
      (bodyTrace : EvaluationSize bodySize (parameterValue :: captured) bodyStore body value after)
      (calleeStrict : calleeSize < budget) (gateStrict : gateSize < budget)
      (argumentsStrict : argumentsSize < budget) (arityStrict : aritySize < budget)
      (functionStrict : functionSize < budget) (parameterStrict : parameterSize < budget)
      (bodyStrict : bodySize < budget) :
      Completion budget gates unknown result callee arguments environment before value after

theorem call_completed {size budget : Nat} {environment : Core.Environment} {before after : Store}
    {gates : List CallableContract.Gate} {unknown : Word} {result : Ty} {callee arguments : Expr} {value : Value}
    (evaluation : EvaluationSize size environment before (CallableContract.call gates unknown result callee arguments) value after)
    (within : size ≤ budget) : Completion budget gates unknown result callee arguments environment before value after := by
  cases bind_completed evaluation within with
  | failed callee strict => exact .calleeFailure callee strict
  | continued callee remaining calleeStrict remainingStrict =>
      cases bind_completed remaining (Nat.le_of_lt remainingStrict) with
      | failed gate strict => exact .stageRejected callee gate calleeStrict strict
      | continued gate remaining gateStrict remainingStrict =>
          cases bind_completed remaining (Nat.le_of_lt remainingStrict) with
          | failed arguments strict => exact .argumentFailure callee gate arguments calleeStrict gateStrict strict
          | continued arguments remaining argumentsStrict remainingStrict =>
              cases bind_completed remaining (Nat.le_of_lt remainingStrict) with
              | failed arity strict => exact .arityRejected callee gate arguments arity calleeStrict gateStrict argumentsStrict strict
              | continued arity application arityStrict applicationStrict =>
                  cases application with
                  | apply function parameter body =>
                      exact .applied callee gate arguments arity function parameter body calleeStrict gateStrict
                        argumentsStrict arityStrict (by omega) (by omega) (by omega)

/-- The actual projection/var children determine the original closure and
argument, including the complete captured suffix. Only those pure reads are
identified; the body is the original graded child. -/
theorem application_completed {size budget : Nat} {environment : Core.Environment}
    {before after : Store} {function token argument arityToken value : Value}
    (evaluation : EvaluationSize size (arityToken :: argument :: token :: function :: environment) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after)
    (within : size ≤ budget) :
    ∃ identity contract parameter result body captured bodySize,
      function = .pair (.pair identity (.closure parameter result body captured)) contract ∧
      bodySize < budget ∧ EvaluationSize bodySize (argument :: captured) before body value after := by
  cases evaluation with
  | apply selected parameter body =>
      cases selected with
      | second tagged =>
          cases tagged with
          | first lookup =>
              cases lookup with
              | var found =>
                  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at found
                  cases Option.some.inj found
                  cases parameter with
                  | var read =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at read
                      cases Option.some.inj read
                      exact ⟨_, _, _, _, _, _, _, rfl, by omega, body⟩

/-- Actual prepared site lowering uses the same completion with the same rows. -/
theorem Callsite.completed {size budget : Nat} {environment : Core.Environment} {before after : Store}
    {site : Callsite} {unknown : Word} {result : Ty} {callee arguments : Expr} {value : Value}
    (evaluation : EvaluationSize size environment before (site.lower unknown result callee arguments) value after)
    (within : size ≤ budget) : Completion budget site.gates unknown result callee arguments environment before value after :=
  call_completed evaluation within

/-- Pure dispatch identifies its result and store from an explicit native word
read. It does not identify source origin, history, or authority. -/
theorem dispatch_decision {size : Nat} {environment : Core.Environment} {before after : Store}
    {gates : List CallableContract.Gate} {phase : CallableContract.Phase} {unknown contract : Word}
    {expression : Expr} {value : Value}
    (read : Evaluates environment before expression (.word contract) before)
    (evaluation : EvaluationSize size environment before
      (CallableContract.dispatch gates phase unknown expression) value after) :
    value = CallableContract.resultValue (CallableContract.decision gates phase unknown contract) ∧ after = before :=
  (CallableContract.dispatch_iff gates phase unknown contract read).mp evaluation.sound

/-- A native rejected gate and the independent actual source dispatch recover
the exact staged-source rejection. Arguments have not been evaluated here.
The conclusion is GuardRejects, with no projection to plain Dynamic. -/
theorem stage_rejection {size : Nat} {environment : Core.Environment} {before after : Store}
    {frame : Staging.CallBoundary.Frame} {site : Callsite}
    {call : Frontend.SourceInference.ExpressionId} {arguments : List Frontend.SourceInference.ExpressionId}
    {source : Dynamic.Value} {carrier : Value} {unknown token : Word} {input : Ty}
    (dispatch : CallStageBoundary.Dispatch frame site call arguments source carrier)
    (evaluation : EvaluationSize size (carrier :: environment) before
      (CallableContract.dispatch site.gates .beforeArguments unknown (.second (.var 0)))
      (.inLeft input (.word token)) after) :
    ∃ reason, Staging.CallBoundary.GuardRejects frame call arguments source reason ∧
      CallStageBoundary.ReasonRepresents site reason token ∧ after = before := by
  have read : Evaluates (carrier :: environment) before (.second (.var 0)) (.word dispatch.contract) before := by
    exact .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
  have exactGate := site.dispatch_known .beforeArguments unknown dispatch.contract dispatch.row dispatch.found read
  cases answer : dispatch.row.beforeArguments with
  | ok unitValue =>
      cases unitValue
      rw [reason_accepted dispatch.row site.reasonAt .beforeArguments answer] at exactGate
      have identical := (evaluation_deterministic evaluation.sound exactGate).1
      cases identical
  | error diagnostic =>
      rw [reason_rejected dispatch.row site.reasonAt .beforeArguments diagnostic answer] at exactGate
      obtain ⟨same, store⟩ := evaluation_deterministic evaluation.sound exactGate
      obtain ⟨reason, rejected, errorEq⟩ := dispatch.rejected_of_error diagnostic answer
      have tokenEq : token = dispatch.reason reason := by
        cases same
        simp only [CallStageBoundary.Dispatch.reason, errorEq]
      exact ⟨reason, rejected, by simpa only [tokenEq] using dispatch.reason_represents reason, store⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndirectCallBounds

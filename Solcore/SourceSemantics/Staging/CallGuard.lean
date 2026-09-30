import Solcore.SourceSemantics.Staging.Stage
import Solcore.Frontend.SourceInference.TypedIR

/-! Independent runtime call-stage guards. The frame contains retained caller
facts and occurrence stages; its authenticity is a separate static obligation.
These rules do not call the executable guard, run source code, or inspect Core.

Argument checks occur in source order. A mismatch in the remaining list lengths
is reported only after all preceding arguments pass. The result-stage check
comes last. Effectful-staging callers bypass this entire pre-argument guard;
the ordinary callable arity check still belongs after argument evaluation. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.CallGuard
open Frontend.SourceInference

structure Frame where
  callerReturnComptime : Bool
  callerResultType : TypeSystem.Ty
  stages : ExpressionId → Option Stage

structure Contract where
  parameters : List TypedBinder
  stagedResult : Bool

inductive Fault where
  | missingStage (expression : ExpressionId)
  | argumentStage (index : Nat) (expression : ExpressionId) (actual : Stage)
  | resultStage (actual : Stage)
  | arity (remainingParameters remainingArguments : Nat)
  deriving Repr, DecidableEq

def Effectful (frame : Frame) : Prop :=
  frame.callerReturnComptime = true ∨ ComptimeOnlyType frame.callerResultType

def RequiresComptime (force : Bool) (parameter : TypedBinder) : Prop :=
  force = true ∨ parameter.comptime = true ∨ ComptimeOnlyType parameter.scheme.body

inductive ArgumentAccepts (frame : Frame) (force : Bool) (parameter : TypedBinder)
    (argument : ExpressionId) : Prop where
  | ordinary (runtime : ¬ RequiresComptime force parameter) : ArgumentAccepts frame force parameter argument
  | comptime (stage : frame.stages argument = some .comptime) : ArgumentAccepts frame force parameter argument

inductive ArgumentRejects (frame : Frame) (force : Bool) (index : Nat)
    (parameter : TypedBinder) (argument : ExpressionId) : Fault → Prop where
  | missing (required : RequiresComptime force parameter) (absent : frame.stages argument = none) :
      ArgumentRejects frame force index parameter argument (.missingStage argument)
  | wrongStage (required : RequiresComptime force parameter) {actual : Stage}
      (found : frame.stages argument = some actual) (notComptime : actual ≠ .comptime) :
      ArgumentRejects frame force index parameter argument (.argumentStage index argument actual)

inductive ArgumentsAccept (frame : Frame) (force : Bool) : Nat → List TypedBinder → List ExpressionId → Prop where
  | nil (index : Nat) : ArgumentsAccept frame force index [] []
  | cons {index parameter parameters argument arguments}
      (head : ArgumentAccepts frame force parameter argument)
      (tail : ArgumentsAccept frame force (index + 1) parameters arguments) :
      ArgumentsAccept frame force index (parameter :: parameters) (argument :: arguments)

inductive ArgumentsReject (frame : Frame) (force : Bool) :
    Nat → List TypedBinder → List ExpressionId → Fault → Prop where
  | parametersRemain (index : Nat) (parameter : TypedBinder) (parameters : List TypedBinder) :
      ArgumentsReject frame force index (parameter :: parameters) [] (.arity (parameters.length + 1) 0)
  | argumentsRemain (index : Nat) (argument : ExpressionId) (arguments : List ExpressionId) :
      ArgumentsReject frame force index [] (argument :: arguments) (.arity 0 (arguments.length + 1))
  | head {index parameter parameters argument arguments reason}
      (rejected : ArgumentRejects frame force index parameter argument reason) :
      ArgumentsReject frame force index (parameter :: parameters) (argument :: arguments) reason
  | tail {index parameter parameters argument arguments reason}
      (accepted : ArgumentAccepts frame force parameter argument)
      (rejected : ArgumentsReject frame force (index + 1) parameters arguments reason) :
      ArgumentsReject frame force index (parameter :: parameters) (argument :: arguments) reason

inductive ResultAccepts (frame : Frame) (call : ExpressionId) (staged : Bool) : Prop where
  | ordinary (runtime : staged = false) : ResultAccepts frame call staged
  | comptime (found : frame.stages call = some .comptime) : ResultAccepts frame call staged

inductive ResultRejects (frame : Frame) (call : ExpressionId) (staged : Bool) : Fault → Prop where
  | missing (required : staged = true) (absent : frame.stages call = none) :
      ResultRejects frame call staged (.missingStage call)
  | wrongStage (required : staged = true) {actual : Stage}
      (found : frame.stages call = some actual) (notComptime : actual ≠ .comptime) :
      ResultRejects frame call staged (.resultStage actual)

inductive Accepts (frame : Frame) (contract : Contract) (call : ExpressionId) (arguments : List ExpressionId) : Prop where
  | effectful (caller : Effectful frame) : Accepts frame contract call arguments
  | ordinary (caller : ¬ Effectful frame)
      (argumentsPass : ArgumentsAccept frame contract.stagedResult 0 contract.parameters arguments)
      (resultPass : ResultAccepts frame call contract.stagedResult) : Accepts frame contract call arguments

inductive Rejects (frame : Frame) (contract : Contract) (call : ExpressionId) (arguments : List ExpressionId) : Fault → Prop where
  | arguments (caller : ¬ Effectful frame) {reason : Fault}
      (rejected : ArgumentsReject frame contract.stagedResult 0 contract.parameters arguments reason) :
      Rejects frame contract call arguments reason
  | result (caller : ¬ Effectful frame) {reason : Fault}
      (argumentsPass : ArgumentsAccept frame contract.stagedResult 0 contract.parameters arguments)
      (rejected : ResultRejects frame call contract.stagedResult reason) :
      Rejects frame contract call arguments reason

theorem ArgumentAccepts.not_rejects {frame : Frame} {force : Bool} {index : Nat}
    {parameter : TypedBinder} {argument : ExpressionId} {reason : Fault}
    (accepted : ArgumentAccepts frame force parameter argument)
    (rejected : ArgumentRejects frame force index parameter argument reason) : False := by
  cases accepted with
  | ordinary notRequired => cases rejected <;> contradiction
  | comptime found =>
    cases rejected with
    | missing _ absent => rw [found] at absent; cases absent
    | wrongStage _ other notComptime => exact notComptime (Option.some.inj (other.symm.trans found))

theorem ArgumentRejects.functional {frame : Frame} {force : Bool} {index : Nat}
    {parameter : TypedBinder} {argument : ExpressionId} {left right : Fault}
    (first : ArgumentRejects frame force index parameter argument left)
    (second : ArgumentRejects frame force index parameter argument right) : left = right := by
  cases first with
  | missing _ absent =>
    cases second with
    | missing => rfl
    | wrongStage _ found _ => rw [absent] at found; cases found
  | wrongStage _ found _ =>
    cases second with
    | missing _ absent => rw [found] at absent; cases absent
    | wrongStage _ other _ => cases Option.some.inj (found.symm.trans other); rfl

theorem argument_complete (frame : Frame) (force : Bool) (index : Nat) (parameter : TypedBinder) (argument : ExpressionId) :
    ArgumentAccepts frame force parameter argument ∨ ∃ reason, ArgumentRejects frame force index parameter argument reason := by
  classical
  by_cases required : RequiresComptime force parameter
  · cases found : frame.stages argument with
    | none => exact .inr ⟨_, .missing required found⟩
    | some stage =>
      by_cases same : stage = .comptime
      · subst stage; exact .inl (.comptime found)
      · exact .inr ⟨_, .wrongStage required found same⟩
  · exact .inl (.ordinary required)

theorem ArgumentsAccept.not_rejects {frame : Frame} {force : Bool} {index : Nat}
    {parameters : List TypedBinder} {arguments : List ExpressionId} {reason : Fault}
    (accepted : ArgumentsAccept frame force index parameters arguments)
    (rejected : ArgumentsReject frame force index parameters arguments reason) : False := by
  induction accepted with
  | nil => cases rejected
  | cons head tail ih =>
    cases rejected with
    | head rejected => exact head.not_rejects rejected
    | tail _ rejected => exact ih rejected

theorem ArgumentsReject.functional {frame : Frame} {force : Bool} {index : Nat}
    {parameters : List TypedBinder} {arguments : List ExpressionId} {left right : Fault}
    (first : ArgumentsReject frame force index parameters arguments left)
    (second : ArgumentsReject frame force index parameters arguments right) : left = right := by
  induction first with
  | parametersRemain => cases second; rfl
  | argumentsRemain => cases second; rfl
  | head rejected =>
    cases second with
    | head other => exact rejected.functional other
    | tail accepted _ => exact False.elim (accepted.not_rejects rejected)
  | tail accepted rejected ih =>
    cases second with
    | head other => exact False.elim (accepted.not_rejects other)
    | tail _ other => exact ih other

theorem arguments_complete (frame : Frame) (force : Bool) (index : Nat)
    (parameters : List TypedBinder) (arguments : List ExpressionId) :
    ArgumentsAccept frame force index parameters arguments ∨
      ∃ reason, ArgumentsReject frame force index parameters arguments reason := by
  induction parameters generalizing index arguments with
  | nil =>
    cases arguments with
    | nil => exact .inl (.nil _)
    | cons argument arguments => exact .inr ⟨_, .argumentsRemain _ _ _⟩
  | cons parameter parameters ih =>
    cases arguments with
    | nil => exact .inr ⟨_, .parametersRemain _ _ _⟩
    | cons argument arguments =>
      rcases argument_complete frame force index parameter argument with accepted | ⟨reason, rejected⟩
      · rcases ih (index + 1) arguments with tail | ⟨reason, rejected⟩
        · exact .inl (.cons accepted tail)
        · exact .inr ⟨reason, .tail accepted rejected⟩
      · exact .inr ⟨reason, .head rejected⟩

theorem ResultAccepts.not_rejects {frame : Frame} {call : ExpressionId} {staged : Bool} {reason : Fault}
    (accepted : ResultAccepts frame call staged) (rejected : ResultRejects frame call staged reason) : False := by
  cases accepted with
  | ordinary runtime => cases rejected <;> simp_all
  | comptime found =>
    cases rejected with
    | missing _ absent => rw [found] at absent; cases absent
    | wrongStage _ other notComptime => exact notComptime (Option.some.inj (other.symm.trans found))

theorem ResultRejects.functional {frame : Frame} {call : ExpressionId} {staged : Bool} {left right : Fault}
    (first : ResultRejects frame call staged left) (second : ResultRejects frame call staged right) : left = right := by
  cases first with
  | missing _ absent =>
    cases second with
    | missing => rfl
    | wrongStage _ found _ => rw [absent] at found; cases found
  | wrongStage _ found _ =>
    cases second with
    | missing _ absent => rw [found] at absent; cases absent
    | wrongStage _ other _ => cases Option.some.inj (found.symm.trans other); rfl

theorem result_complete (frame : Frame) (call : ExpressionId) (staged : Bool) :
    ResultAccepts frame call staged ∨ ∃ reason, ResultRejects frame call staged reason := by
  cases staged with
  | false => exact .inl (.ordinary rfl)
  | true =>
    cases found : frame.stages call with
    | none => exact .inr ⟨_, .missing rfl found⟩
    | some stage =>
      by_cases same : stage = .comptime
      · subst stage; exact .inl (.comptime found)
      · exact .inr ⟨_, .wrongStage rfl found same⟩

theorem Accepts.not_rejects {frame : Frame} {contract : Contract} {call : ExpressionId}
    {arguments : List ExpressionId} {reason : Fault}
    (accepted : Accepts frame contract call arguments) (rejected : Rejects frame contract call arguments reason) : False := by
  cases accepted with
  | effectful caller => cases rejected <;> contradiction
  | ordinary _ argumentsPass resultPass =>
    cases rejected with
    | arguments _ rejected => exact argumentsPass.not_rejects rejected
    | result _ _ rejected => exact resultPass.not_rejects rejected

theorem Rejects.functional {frame : Frame} {contract : Contract} {call : ExpressionId}
    {arguments : List ExpressionId} {left right : Fault}
    (first : Rejects frame contract call arguments left) (second : Rejects frame contract call arguments right) : left = right := by
  cases first with
  | arguments _ rejected =>
    cases second with
    | arguments _ other => exact rejected.functional other
    | result _ accepted _ => exact False.elim (accepted.not_rejects rejected)
  | result _ accepted rejected =>
    cases second with
    | arguments _ other => exact False.elim (accepted.not_rejects other)
    | result _ _ other => exact rejected.functional other

theorem complete (frame : Frame) (contract : Contract) (call : ExpressionId) (arguments : List ExpressionId) :
    Accepts frame contract call arguments ∨ ∃ reason, Rejects frame contract call arguments reason := by
  classical
  by_cases effectful : Effectful frame
  · exact .inl (.effectful effectful)
  · rcases arguments_complete frame contract.stagedResult 0 contract.parameters arguments with accepted | ⟨reason, rejected⟩
    · rcases result_complete frame call contract.stagedResult with resultPass | ⟨reason, rejected⟩
      · exact .inl (.ordinary effectful accepted resultPass)
      · exact .inr ⟨reason, .result effectful accepted rejected⟩
    · exact .inr ⟨reason, .arguments effectful rejected⟩

end Solcore.SourceSemantics.Staging.CallGuard

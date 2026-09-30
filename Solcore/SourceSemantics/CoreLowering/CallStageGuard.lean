import Solcore.SourceSemantics.Staging.CallGuard
import Solcore.Frontend.SourceCoreStageContracts

/-! The executable metadata validator agrees with independent call-stage
judgments. Only this compiler bridge mentions the old validator. The source
rules themselves are in Staging.CallGuard and have no execution-function
premise. Sealed receipts recover the same diagnostic and check precedence. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallStageGuard
open Frontend Frontend.SourceInference
open Staging.CallGuard

abbrev Caller := SourceSpecialization.SpecializedFunction
abbrev RuntimeError := SourceCompilationPlan.Error
abbrev Key := SourceSpecialization.SpecializationKey

def frame (caller : Caller) : Frame := {
  callerReturnComptime := caller.function.returnComptime
  callerResultType := caller.function.inferredBodyType
  stages := fun expression => (caller.stageAnalysis.expressionStage? expression).map SourceStageAnalysis.Stage.toSemantic }

def toFrontend : Staging.Stage → SourceStageAnalysis.Stage
  | .comptime => .comptime
  | .runtime => .runtime
  | .deferred => .deferred

def error (caller : Caller) (node : ExpressionNode) (callee : Key) : Fault → RuntimeError
  | .missingStage expression => .missingExpressionStage caller.key node.id expression
  | .argumentStage index expression actual => .comptimeArgumentStageMismatch caller.key node.id index expression (toFrontend actual)
  | .resultStage actual => .comptimeResultStageMismatch caller.key node.id callee (toFrontend actual)
  | .arity parameters arguments => .argumentArityMismatch parameters arguments

private theorem comptimeOnly (type : TypeSystem.Ty) :
    SourceCompilationPlan.sourceTypeIsComptimeOnly type = true ↔ Staging.ComptimeOnlyType type := by
  exact SourceStageAnalysis.typeIsComptimeOnly_eq_true_iff type

private theorem required_iff (force : Bool) (parameter : TypedBinder) :
    (force || parameter.comptime || SourceCompilationPlan.sourceTypeIsComptimeOnly parameter.scheme.body) = true ↔
      RequiresComptime force parameter := by
  simp only [Bool.or_eq_true, comptimeOnly, RequiresComptime, or_assoc]

private theorem effectful_iff (caller : Caller) :
    (caller.function.returnComptime || SourceCompilationPlan.sourceTypeIsComptimeOnly caller.function.inferredBodyType) = true ↔
      Effectful (frame caller) := by
  simp only [Bool.or_eq_true, comptimeOnly, Effectful, frame]

private theorem stage_found {caller : Caller} {expression : ExpressionId} {stage : Staging.Stage}
    (found : (frame caller).stages expression = some stage) :
    caller.stageAnalysis.expressionStage? expression = some (toFrontend stage) := by
  cases actual : caller.stageAnalysis.expressionStage? expression with
  | none => simp [frame, actual] at found
  | some value =>
    cases value <;> simp [frame, actual, SourceStageAnalysis.Stage.toSemantic] at found <;>
      subst stage <;> rfl

private theorem stage_absent {caller : Caller} {expression : ExpressionId}
    (absent : (frame caller).stages expression = none) : caller.stageAnalysis.expressionStage? expression = none := by
  cases actual : caller.stageAnalysis.expressionStage? expression with
  | none => rfl
  | some value => simp [frame, actual] at absent

private def argumentCheck (caller : Caller) (node : ExpressionNode) (force : Bool)
    (index : Nat) (parameter : TypedBinder) (argument : ExpressionId) : Except RuntimeError Unit :=
  if force || parameter.comptime || SourceCompilationPlan.sourceTypeIsComptimeOnly parameter.scheme.body then
    SourceCompilationPlan.requireComptimeArgumentStage caller node index argument
  else pure ()

private theorem argument_accepts {caller : Caller} {node : ExpressionNode} {force : Bool} {index : Nat}
    {parameter : TypedBinder} {argument : ExpressionId}
    (accepted : ArgumentAccepts (frame caller) force parameter argument) :
    argumentCheck caller node force index parameter argument = .ok () := by
  cases accepted with
  | ordinary notRequired =>
    have skipped : (force || parameter.comptime || SourceCompilationPlan.sourceTypeIsComptimeOnly parameter.scheme.body) ≠ true :=
      fun checked => notRequired ((required_iff force parameter).mp checked)
    simp [argumentCheck, skipped]
  | comptime found =>
    have actual := stage_found found
    simp only [argumentCheck]
    split
    · simp [SourceCompilationPlan.requireComptimeArgumentStage, actual, toFrontend]
    · rfl

private theorem argument_rejects {caller : Caller} {node : ExpressionNode} {callee : Key}
    {force : Bool} {index : Nat} {parameter : TypedBinder} {argument : ExpressionId} {reason : Fault}
    (rejected : ArgumentRejects (frame caller) force index parameter argument reason) :
    argumentCheck caller node force index parameter argument = .error (error caller node callee reason) := by
  cases rejected with
  | missing required absent =>
    have test := (required_iff force parameter).mpr required
    simp [argumentCheck, test, SourceCompilationPlan.requireComptimeArgumentStage, stage_absent absent, error]
    rfl
  | @wrongStage required actual found notComptime =>
    have test := (required_iff force parameter).mpr required
    have selected := stage_found found
    cases actual with
    | comptime => exact False.elim (notComptime rfl)
    | runtime | deferred =>
      simp [argumentCheck, test, SourceCompilationPlan.requireComptimeArgumentStage, selected, error, toFrontend]
      rfl

private theorem arguments_cons (caller : Caller) (node : ExpressionNode) (force : Bool) (index : Nat)
    (parameter : TypedBinder) (parameters : List TypedBinder) (argument : ExpressionId) (arguments : List ExpressionId) :
    SourceCompilationPlan.validateStagedArguments caller node force index (parameter :: parameters) (argument :: arguments) =
      (do
        argumentCheck caller node force index parameter argument
        SourceCompilationPlan.validateStagedArguments caller node force (index + 1) parameters arguments) := by
  rw [SourceCompilationPlan.validateStagedArguments]
  unfold argumentCheck
  split <;> rfl

theorem arguments_accept {caller : Caller} {node : ExpressionNode} {force : Bool} {index : Nat}
    {parameters : List TypedBinder} {arguments : List ExpressionId}
    (accepted : ArgumentsAccept (frame caller) force index parameters arguments) :
    SourceCompilationPlan.validateStagedArguments caller node force index parameters arguments = .ok () := by
  induction accepted with
  | nil => rfl
  | cons head tail ih =>
    rw [arguments_cons, argument_accepts head]
    exact ih

theorem arguments_reject {caller : Caller} {node : ExpressionNode} {callee : Key}
    {force : Bool} {index : Nat} {parameters : List TypedBinder} {arguments : List ExpressionId} {reason : Fault}
    (rejected : ArgumentsReject (frame caller) force index parameters arguments reason) :
    SourceCompilationPlan.validateStagedArguments caller node force index parameters arguments = .error (error caller node callee reason) := by
  induction rejected with
  | parametersRemain => rfl
  | argumentsRemain => rfl
  | head rejected =>
    rw [arguments_cons, argument_rejects (callee := callee) rejected]
    rfl
  | tail accepted rejected ih =>
    rw [arguments_cons, argument_accepts accepted]
    exact ih

private theorem result_accepts {caller : Caller} {node : ExpressionNode} {callee : Key} {staged : Bool}
    (accepted : ResultAccepts (frame caller) node.id staged) :
    (if staged then match caller.stageAnalysis.expressionStage? node.id with
      | none => Except.error (.missingExpressionStage caller.key node.id node.id)
      | some .comptime => .ok ()
      | some actual => .error (.comptimeResultStageMismatch caller.key node.id callee actual)
     else .ok ()) = (Except.ok () : Except RuntimeError Unit) := by
  cases accepted with
  | ordinary runtime => simp [runtime]
  | comptime found => simp [stage_found found, toFrontend]

private theorem result_rejects {caller : Caller} {node : ExpressionNode} {callee : Key} {staged : Bool} {reason : Fault}
    (rejected : ResultRejects (frame caller) node.id staged reason) :
    (if staged then match caller.stageAnalysis.expressionStage? node.id with
      | none => Except.error (.missingExpressionStage caller.key node.id node.id)
      | some .comptime => .ok ()
      | some actual => .error (.comptimeResultStageMismatch caller.key node.id callee actual)
     else .ok ()) = (Except.error (error caller node callee reason) : Except RuntimeError Unit) := by
  cases rejected with
  | missing required absent => simp [required, stage_absent absent, error]
  | @wrongStage required actual found notComptime =>
    have selected := stage_found found
    cases actual with
    | comptime => exact False.elim (notComptime rfl)
    | runtime | deferred => simp [required, selected, error, toFrontend]

/-- Every independent acceptance produces the executable validator's success. -/
theorem accepts {caller : Caller} {node : ExpressionNode} {callee : Key} {contract : Contract}
    {arguments : List ExpressionId} (accepted : Accepts (frame caller) contract node.id arguments) :
    SourceCompilationPlan.validateStagedCallableContract caller node arguments contract.parameters contract.stagedResult callee = .ok () := by
  cases accepted with
  | effectful effectful =>
    simp [SourceCompilationPlan.validateStagedCallableContract, (effectful_iff caller).mpr effectful]
  | ordinary notEffectful argumentsPass resultPass =>
    have test : (caller.function.returnComptime || SourceCompilationPlan.sourceTypeIsComptimeOnly caller.function.inferredBodyType) ≠ true :=
      fun checked => notEffectful ((effectful_iff caller).mp checked)
    simp only [SourceCompilationPlan.validateStagedCallableContract, test, arguments_accept argumentsPass, bind, Except.bind]
    exact result_accepts resultPass

/-- Every independent rejection gives the same first diagnostic. -/
theorem rejects {caller : Caller} {node : ExpressionNode} {callee : Key} {contract : Contract}
    {arguments : List ExpressionId} {reason : Fault} (rejected : Rejects (frame caller) contract node.id arguments reason) :
    SourceCompilationPlan.validateStagedCallableContract caller node arguments contract.parameters contract.stagedResult callee =
      .error (error caller node callee reason) := by
  cases rejected with
  | arguments notEffectful rejected =>
    have test : (caller.function.returnComptime || SourceCompilationPlan.sourceTypeIsComptimeOnly caller.function.inferredBodyType) ≠ true :=
      fun checked => notEffectful ((effectful_iff caller).mp checked)
    simp [SourceCompilationPlan.validateStagedCallableContract, test, arguments_reject (callee := callee) rejected, bind, Except.bind]
  | result notEffectful argumentsPass rejected =>
    have test : (caller.function.returnComptime || SourceCompilationPlan.sourceTypeIsComptimeOnly caller.function.inferredBodyType) ≠ true :=
      fun checked => notEffectful ((effectful_iff caller).mp checked)
    simp only [SourceCompilationPlan.validateStagedCallableContract, test, arguments_accept argumentsPass, bind, Except.bind]
    exact result_rejects rejected

/-- The compiler validator accepts exactly the independent judgment. -/
theorem accepts_iff {caller : Caller} {node : ExpressionNode} {callee : Key} {contract : Contract}
    {arguments : List ExpressionId} :
    SourceCompilationPlan.validateStagedCallableContract caller node arguments contract.parameters contract.stagedResult callee = .ok () ↔
      Accepts (frame caller) contract node.id arguments := by
  constructor
  · intro accepted
    rcases complete (frame caller) contract node.id arguments with yes | ⟨reason, no⟩
    · exact yes
    · have different := rejects (callee := callee) no
      rw [accepted] at different
      cases different
  · exact accepts

/-- Every executable failure is represented by an independent rejection. -/
theorem rejects_iff {caller : Caller} {node : ExpressionNode} {callee : Key} {contract : Contract}
    {arguments : List ExpressionId} {diagnostic : RuntimeError} :
    SourceCompilationPlan.validateStagedCallableContract caller node arguments contract.parameters contract.stagedResult callee = .error diagnostic ↔
      ∃ reason, Rejects (frame caller) contract node.id arguments reason ∧ diagnostic = error caller node callee reason := by
  constructor
  · intro failed
    rcases complete (frame caller) contract node.id arguments with yes | ⟨reason, no⟩
    · have different := accepts (callee := callee) yes
      rw [failed] at different
      cases different
    · exact ⟨reason, no, Except.error.inj (failed.symm.trans (rejects no))⟩
  · rintro ⟨reason, no, rfl⟩
    exact rejects no

/-- The sealed receipt's exact metadata result is interpreted independently. -/
theorem guard_accepts_iff (guard : SourceCoreStageContracts.Guard) :
    guard.decision = .ok () ↔
      Accepts (frame guard.sidecar.caller) ⟨guard.contract.parameters, guard.contract.stagedResult⟩ guard.node.id guard.arguments := by
  rw [← guard.exact]
  exact accepts_iff (caller := guard.sidecar.caller) (node := guard.node) (callee := guard.contract.owner)
    (contract := ⟨guard.contract.parameters, guard.contract.stagedResult⟩) (arguments := guard.arguments)

theorem guard_rejects_iff (guard : SourceCoreStageContracts.Guard) (diagnostic : RuntimeError) :
    guard.decision = .error diagnostic ↔
      ∃ reason, Rejects (frame guard.sidecar.caller) ⟨guard.contract.parameters, guard.contract.stagedResult⟩
        guard.node.id guard.arguments reason ∧ diagnostic = error guard.sidecar.caller guard.node guard.contract.owner reason := by
  rw [← guard.exact]
  exact rejects_iff (caller := guard.sidecar.caller) (node := guard.node) (callee := guard.contract.owner)
    (contract := ⟨guard.contract.parameters, guard.contract.stagedResult⟩) (arguments := guard.arguments)

end Solcore.SourceSemantics.CoreLowering.CallStageGuard

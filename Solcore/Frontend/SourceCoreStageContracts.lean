import Solcore.Frontend.SourceCompilationPlan
import Solcore.Frontend.SourceCoreLocalEvidence
import Solcore.Core.LanguageResult

/-! Retained source staging contracts for Core compilation. These sealed
receipts preserve the original caller sidecar and the existing callable guard;
they neither evaluate source nor erase staging admission rules. The enclosing
artifact authenticates its canonical prepared plan. This module checks exact
plan lookup, source ownership, the analyzer's retained output, and callable
occurrence provenance within that plan.

`Guard.lower` is the static known-contract fragment: it evaluates the callee
first and skips arguments on rejection. Dynamic callable contract transport is
a separate representation boundary. These laws describe the existing metadata
validator and Core evaluation; the declarative source call rules currently do
not include this runtime stage guard. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreStageContracts

open SourceInference

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev RuntimeError := SourceCompilationPlan.Error

inductive Error where
  | plan (error : RuntimeError)
  | analysis (error : SourceStageAnalysis.Error)
  | sidecarMismatch (key : Key)
  | ownerMismatch (expected actual : Resolved.DeclarationId)
  | missingExpression (id : ExpressionId)
  | duplicateExpression (id : ExpressionId) (count : Nat)
  | expectedLambda (id : ExpressionId)
  | openLambda (id : ExpressionId)
  | expectedIndirectCall (id : ExpressionId)
  | planMismatch
  | contextualCallerMismatch (key : Key)
  deriving Repr

/-- A retained original specialization and its exact analyzer output. Public
clients cannot substitute an edited stage table into this receipt. -/
structure Sidecar where private mk ::
  plan : Plan
  caller : SourceSpecialization.SpecializedFunction
  analyzed : SourceStageAnalysis.analyzeFunction caller.function = .ok caller.stageAnalysis

namespace Sidecar

def source (sidecar : Sidecar) : TypedSource := sidecar.caller.function.typedBody

theorem certificate (sidecar : Sidecar) :
    SourceStageAnalysis.FunctionAnalysisCertificate sidecar.caller.function sidecar.caller.stageAnalysis :=
  SourceStageAnalysis.analyzeFunction_success_certificate _ _ sidecar.analyzed

end Sidecar

/-- Metadata admission is checked before a contract is projected. Resolving
closed trait assumptions and authenticating the whole plan remain the owning
artifact's preparation responsibilities. -/
def prepareSidecar (plan : Plan) (key : Key) : Except Error Sidecar := do
  let caller ← (SourceCompilationPlan.exactSpecialization plan key).mapError Error.plan
  discard <| (SourceCompilationPlan.validateSpecializationMetadataWith true caller).mapError Error.plan
  match analyzed : SourceStageAnalysis.analyzeFunction caller.function with
  | .error error => .error (.analysis error)
  | .ok analysis =>
      if same : analysis = caller.stageAnalysis then
        .ok (.mk plan caller (same ▸ analyzed))
      else .error (.sidecarMismatch key)

def expression (sidecar : Sidecar) (id : ExpressionId) : Except Error ExpressionNode := do
  if id.occurrence.owner ≠ sidecar.source.owner then
    throw (.ownerMismatch sidecar.source.owner id.occurrence.owner)
  match sidecar.source.nodes.filterMap (fun
      | .expression node => if node.id = id then some node else none
      | .statement _ => none) with
  | [] => .error (.missingExpression id)
  | [node] => .ok node
  | nodes => .error (.duplicateExpression id nodes.length)

/-- The source types and flags stay together until the existing guard has been
decided. A source function type alone does not encode parameter comptime flags. -/
structure Contract where private mk ::
  plan : Plan
  parameters : List TypedBinder
  stagedResult : Bool
  owner : Key

namespace Contract

/-- Arbitrary source arity is retained; each flag includes an outer staged
source type, rather than just the binder's explicit marker. -/
def parameterStages (contract : Contract) : List Bool :=
  contract.parameters.map fun parameter => parameter.comptime ||
    SourceCompilationPlan.sourceTypeIsComptimeOnly parameter.scheme.body

def named (plan : Plan) (key : Key) : Except Error Contract := do
  let callee ← prepareSidecar plan key
  pure (.mk callee.plan callee.caller.function.typedBody.inputs
    (callee.caller.function.returnComptime ||
      SourceCompilationPlan.sourceTypeIsComptimeOnly callee.caller.function.inferredBodyType)
    callee.caller.key)

/-- Monomorphic original lambda contracts. Flexible local instances need a
separate authenticated contextual receipt before their flags can be projected. -/
def lambda (sidecar : Sidecar) (id : ExpressionId) : Except Error Contract := do
  let node ← expression sidecar id
  match node.form with
  | .lambda parameters resultType _ =>
      if parameters.any (fun parameter => !parameter.scheme.body.freeVariables.isEmpty) ||
          !resultType.freeVariables.isEmpty then
        throw (.openLambda id)
      pure (.mk sidecar.plan parameters (SourceCompilationPlan.sourceTypeIsComptimeOnly resultType) sidecar.caller.key)
  | _ => .error (.expectedLambda id)

/-- A generalized lambda is projected only through an authenticated complete
local context. The receipt must reconstruct this exact original caller,
including its retained sidecar and obligation ledger; a caller-selected type
substitution is insufficient. -/
def contextualLambda (sidecar : Sidecar) (prepared : SourceCoreLocalEvidence.Prepared)
    (id : ExpressionId) : Except Error Contract := do
  let original := sidecar.caller
  let expected := { original with function := { original.function with
    typedBody := sidecar.source.applySubstitution prepared.substitution
    solvedRequirements := SourceCoreLocalEvidence.rewriteLedger prepared.substitution
      prepared.witnesses original.function.solvedRequirements } }
  unless prepared.caller == expected do
    throw (.contextualCallerMismatch sidecar.caller.key)
  let node ← expression sidecar id
  match node.form with
  | .lambda parameters resultType _ =>
      let parameters := parameters.map (TypedBinder.applySubstitution prepared.substitution)
      let resultType := prepared.substitution.apply resultType
      if parameters.any (fun parameter => !parameter.scheme.body.freeVariables.isEmpty) ||
          !resultType.freeVariables.isEmpty then
        throw (.openLambda id)
      pure (.mk sidecar.plan parameters (SourceCompilationPlan.sourceTypeIsComptimeOnly resultType) sidecar.caller.key)
  | _ => .error (.expectedLambda id)

end Contract

/-- A static decision retains the exact original use occurrence, parameter
contract, and diagnostic. Stage rejection is a language result, not a Core
machine fault or an instruction to run the source evaluator. -/
structure Guard where private mk ::
  sidecar : Sidecar
  contract : Contract
  node : ExpressionNode
  arguments : List ExpressionId
  decision : Except RuntimeError Unit
  exact : SourceCompilationPlan.validateStagedCallableContract sidecar.caller node arguments
    contract.parameters contract.stagedResult contract.owner = decision

def prepareGuard (sidecar : Sidecar) (call : ExpressionId) (contract : Contract) : Except Error Guard := do
  unless sidecar.plan == contract.plan do throw .planMismatch
  let node ← expression sidecar call
  match node.form with
  | .call _ arguments (.indirect _) =>
      pure (.mk sidecar contract node arguments
        (SourceCompilationPlan.validateStagedCallableContract sidecar.caller node arguments
          contract.parameters contract.stagedResult contract.owner) rfl)
  | _ => .error (.expectedIndirectCall call)

namespace Guard

theorem decision_exact (guard : Guard) :
    SourceCompilationPlan.validateStagedCallableContract guard.sidecar.caller guard.node guard.arguments
      guard.contract.parameters guard.contract.stagedResult guard.contract.owner = guard.decision :=
  guard.exact

/-- `successBody` lives under the callee binder and owns argument evaluation.
The codebook maps the retained exact source diagnostic to a nonwrapping reason.
No source computation occurs when this decision is used by native execution. -/
def lower (guard : Guard) (resultType : Core.Ty) (callee successBody : Core.Expr)
    (reasonFor : RuntimeError → Core.Word) : Core.Expr :=
  Core.LanguageResult.bind resultType callee
    (match guard.decision with
    | .ok () => successBody
    | .error error => Core.LanguageResult.failure resultType (.word (reasonFor error)))

theorem lower_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {calleeType resultType : Core.Ty} {callee successBody : Core.Expr}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (wellFormed : Core.Ty.WellFormed definitions resultType)
    (calleeTyped : Core.HasType context callee (Core.LanguageResult.resultType calleeType) definitions)
    (bodyTyped : Core.HasType (calleeType :: context) successBody
      (Core.LanguageResult.resultType resultType) definitions) :
    Core.HasType context (guard.lower resultType callee successBody reasonFor)
      (Core.LanguageResult.resultType resultType) definitions := by
  apply Core.LanguageResult.bind_hasType wellFormed calleeTyped
  cases guard.decision with
  | ok value => cases value; exact bodyTyped
  | error error => exact Core.LanguageResult.failure_hasType wellFormed .word

theorem lower_callee_failure {environment : Core.Environment} {before after : Core.Store}
    {calleeType resultType : Core.Ty} {callee body : Core.Expr} {reason : Core.Word}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (evaluation : Core.Evaluates environment before callee (.inLeft calleeType (.word reason)) after) :
    Core.Evaluates environment before (guard.lower resultType callee body reasonFor)
      (.inLeft resultType (.word reason)) after :=
  Core.LanguageResult.bind_failure resultType evaluation

theorem lower_callee_failure_iff {environment : Core.Environment} {before calleeStore after : Core.Store}
    {calleeType resultType : Core.Ty} {callee body : Core.Expr} {reason : Core.Word} {result : Core.Value}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (evaluation : Core.Evaluates environment before callee (.inLeft calleeType (.word reason)) calleeStore) :
    Core.Evaluates environment before (guard.lower resultType callee body reasonFor) result after ↔
      result = .inLeft resultType (.word reason) ∧ after = calleeStore :=
  Core.LanguageResult.bind_failure_iff evaluation

theorem lower_rejected_hasType {definitions : Core.DataEnvironment} {context : Core.Context}
    {calleeType resultType : Core.Ty} {callee body : Core.Expr} {error : RuntimeError}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (rejected : guard.decision = .error error)
    (wellFormed : Core.Ty.WellFormed definitions resultType)
    (calleeTyped : Core.HasType context callee (Core.LanguageResult.resultType calleeType) definitions) :
    Core.HasType context (guard.lower resultType callee body reasonFor)
      (Core.LanguageResult.resultType resultType) definitions := by
  apply Core.LanguageResult.bind_hasType wellFormed calleeTyped
  simp only [rejected]
  exact Core.LanguageResult.failure_hasType wellFormed .word

theorem lower_rejected {environment : Core.Environment} {before after : Core.Store}
    {resultType : Core.Ty} {callee body : Core.Expr} {value : Core.Value} {error : RuntimeError}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (rejected : guard.decision = .error error)
    (evaluation : Core.Evaluates environment before callee (.inRight .word value) after) :
    Core.Evaluates environment before (guard.lower resultType callee body reasonFor)
      (.inLeft resultType (.word (reasonFor error))) after := by
  apply Core.LanguageResult.bind_success resultType evaluation
  simp only [rejected]
  exact Core.LanguageResult.failure_evaluates resultType .word

/-- A rejected known contract fixes the final heap to the callee's heap. The
argument/body expression is arbitrary and need not terminate. -/
theorem lower_rejected_iff {environment : Core.Environment} {before calleeStore after : Core.Store}
    {resultType : Core.Ty} {callee body : Core.Expr} {value result : Core.Value} {error : RuntimeError}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (rejected : guard.decision = .error error)
    (evaluation : Core.Evaluates environment before callee (.inRight .word value) calleeStore) :
    Core.Evaluates environment before (guard.lower resultType callee body reasonFor) result after ↔
      result = .inLeft resultType (.word (reasonFor error)) ∧ after = calleeStore := by
  constructor
  · intro evaluated
    exact Core.evaluation_deterministic evaluated (lower_rejected guard reasonFor rejected evaluation)
  · rintro ⟨rfl, rfl⟩
    exact lower_rejected guard reasonFor rejected evaluation

theorem lower_accepted {environment : Core.Environment} {before middle after : Core.Store}
    {resultType : Core.Ty} {callee body : Core.Expr} {value result : Core.Value}
    (guard : Guard) (reasonFor : RuntimeError → Core.Word)
    (accepted : guard.decision = .ok ())
    (calleeEvaluation : Core.Evaluates environment before callee (.inRight .word value) middle)
    (bodyEvaluation : Core.Evaluates (value :: environment) middle body result after) :
    Core.Evaluates environment before (guard.lower resultType callee body reasonFor) result after := by
  apply Core.LanguageResult.bind_success resultType calleeEvaluation
  simpa only [accepted] using bodyEvaluation

end Guard

end Solcore.Frontend.SourceCoreStageContracts

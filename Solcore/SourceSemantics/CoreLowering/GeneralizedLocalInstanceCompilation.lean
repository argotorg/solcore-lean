import Solcore.Frontend.SourceCoreGeneralFunctions

/-! Receipts for the literal instance callback used by generalized local
initializers. The actual evidence preparation and recursive contextual
compilation retain the candidate's full key and its distinct read parent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceCompilation
open Core Frontend SourceInference SourceCoreLocalPolymorphism

structure Inputs where
  program : CheckedProgram
  representation : SourceCoreGeneralFunctions.Representation
  signatures : ProgramSignatures
  locals : Catalog
  candidateParents : List SourceCoreLocalEvidence.Prepared
  assignments : SourceCoreAssignmentFaultSites.Table
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  current : SourceCoreFunctions.Context
  native : Option SourceCoreGeneralFunctions.CallableContext
  parent : Option SourceCoreLocalEvidence.Prepared
  budget : Nat
  fuel : Nat
  initializer : ExpressionId
  scope : SourceCoreBasic.Scope
  reasonAt : ExpressionId → Core.Word

def Inputs.child (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared) :
    Except SourceCoreBasic.Error SourceCoreBasic.LoweredExpr :=
  SourceCoreGeneralFunctions.lowerContextualExpression inputs.program inputs.representation inputs.signatures
    inputs.locals inputs.candidateParents inputs.assignments inputs.diagnostics
    { inputs.current with solvedRequirements := prepared.caller.function.solvedRequirements } inputs.native
    (some prepared) (some inputs.initializer) (min inputs.budget inputs.fuel)
    prepared.source inputs.scope inputs.initializer inputs.reasonAt

/-- This is the same callback passed to lowerInitializer by the contextual
compiler, with its inputs named for use in static certificates. -/
def compile (inputs : Inputs) (candidate : Instance) : Except SourceCoreLocalPolymorphism.Error Core.Expr := do
  let emission ← (SourceCoreLocalEvidence.prepareForEmission inputs.program inputs.current.plan candidate
    inputs.parent inputs.candidateParents).mapError fun _ =>
      SourceCoreLocalPolymorphism.Error.initializerMetadataMismatch inputs.initializer
  let lowered ← (inputs.child emission.prepared).mapError SourceCoreLocalPolymorphism.Error.metadata
  (SourceCoreBasic.ensureType (.occurrence inputs.initializer.occurrence) candidate.type lowered.type)
    |>.mapError SourceCoreLocalPolymorphism.Error.metadata
  match lowered.expression with
  | .inRight .word closure => pure closure
  | _ => throw (.initializerMetadataMismatch inputs.initializer)

structure Receipt (inputs : Inputs) (candidate : Instance) (raw : Core.Expr) where
  emission : SourceCoreLocalEvidence.Emission inputs.program inputs.current.plan candidate inputs.parent
  prepared : SourceCoreLocalEvidence.prepareForEmission inputs.program inputs.current.plan candidate
    inputs.parent inputs.candidateParents = .ok emission
  lowered : SourceCoreBasic.LoweredExpr
  compiled : inputs.child emission.prepared = .ok lowered
  nativeType : candidate.type = lowered.type
  extracted : lowered.expression = .inRight .word raw

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ} {result : α}
    (accepted : action.mapError change = .ok result) : action = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

theorem of_accepted {inputs : Inputs} {candidate : Instance} {raw : Core.Expr}
    (accepted : compile inputs candidate = .ok raw) : Nonempty (Receipt inputs candidate raw) := by
  unfold compile at accepted
  obtain ⟨emission, prepared, accepted⟩ := bind_ok accepted
  have prepared := mapError_ok prepared
  obtain ⟨lowered, compiled, accepted⟩ := bind_ok accepted
  have compiled := mapError_ok compiled
  obtain ⟨_, checked, accepted⟩ := bind_ok accepted
  have nativeType : candidate.type = lowered.type := by
    by_cases same : candidate.type = lowered.type
    · exact same
    · simp [SourceCoreBasic.ensureType, same, Except.mapError] at checked
  split at accepted
  · next expression extracted =>
      cases accepted
      exact ⟨⟨emission, prepared, lowered, compiled, nativeType, extracted⟩⟩
  · cases accepted

/-- Reconstructing the successful callback uses the same factory receipt and
recursive compiler result; no alternate metadata or candidate is introduced. -/
theorem Receipt.accepted {inputs : Inputs} {candidate : Instance} {raw : Core.Expr}
    (receipt : Receipt inputs candidate raw) : compile inputs candidate = .ok raw := by
  simp [compile, receipt.prepared, receipt.compiled, SourceCoreBasic.ensureType,
    receipt.nativeType, receipt.extracted, Except.mapError, bind, Except.bind, pure, Except.pure]

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInstanceCompilation

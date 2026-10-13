import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGenericMethodSelection

/-! Selection formation and full raw replacement typing do not require an
empty method dictionary. Actual caller coverage is retained separately from
the method's own evidence assumptions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport
open Core Frontend SourceInference
open CallableCoercionMethodInstantiation (Formation)
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)

structure Catalog (program : CheckedProgram) : Prop where
  formed : ∀ implementation, implementation ∈ program.signatures.implementations →
    ∀ method, method ∈ implementation.methods → Formation implementation method

/-- Existing generic catalogs retain their original APIs. -/
theorem Catalog.of_generic {program : CheckedProgram}
    (catalog : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog program) :
    Catalog program := ⟨catalog.formed⟩

variable {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy lowerBody fuel compilation values source scope id reasonAt lowered)

/-- Source instantiation retains the selected declaration's complete body and
the same checked replacement range. -/
theorem support_of_range {loaded : LoadedProgram}
    (checked : Frontend.checkLoadedProgram loaded 1024 = .ok receipt.program)
    (wellFormed : ProgramWellFormed (Program.ofChecked receipt.program))
    (catalog : Catalog receipt.program)
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered receipt.caller receipt.method)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures receipt.program.signatures)
      receipt.method.specialized.parameterSubstitution) :
    CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.SelectionCore receipt selected := by
  let chosen := selected.certificate.selected
  have formed : Formation chosen.implementation chosen.declaration :=
    catalog.formed chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  obtain ⟨definition, _member, _id, instantiated⟩ := chosen.instantiates checked formed.parameters range
  obtain ⟨types, lexical, facts, typing⟩ := instantiated.certificate wellFormed
  exact ⟨formed, range, covered, typing.graph_closed.wellFormed.nodeOccurrencesUnique⟩

/-- Genuine original parent typing and current requirement identities establish
the range before the selected method Source body is instantiated. -/
theorem selection_support {loaded : LoadedProgram}
    (checked : Frontend.checkLoadedProgram loaded 1024 = .ok receipt.program)
    (wellFormed : ProgramWellFormed (Program.ofChecked receipt.program))
    (catalog : Catalog receipt.program)
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered receipt.caller receipt.method)
    {context : SourceSemantics.Context}
    (signatures : context.signatures = receipt.program.signatures)
    (ledger : context.solvedRequirements = receipt.caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ receipt.caller.assumptions → goal ∈ context.assumptions)
    (unique : NodeOccurrencesUnique source)
    (idsUnique : RequirementIdsUnique context)
    (typed : ExpressionHasType source context id receipt.node.type) :
    CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.SelectionCore receipt selected := by
  have goalAdmitted := CallableIndexedOwnedPreparedStagedMethodSelectionGoal.admissible
    receipt selected signatures ledger assumptions unique idsUnique typed
  have formed := catalog.formed _ selected.certificate.selected.implementationMember
    _ selected.certificate.selected.methodMember
  have range := CallableIndexedOwnedPreparedStagedMethodSelectionRanges.of_selected
    selected.certificate.selected wellFormed formed signatures goalAdmitted
  exact support_of_range receipt checked wellFormed catalog selected covered range

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport

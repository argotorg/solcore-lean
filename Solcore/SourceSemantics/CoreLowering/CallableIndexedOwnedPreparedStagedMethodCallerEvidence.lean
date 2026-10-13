import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGenericMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory

/-! The genuine method selector and implementation catalog determine
its complete caller dictionary. Parameter and lexical contexts preserve the
actual ledger and requirement identities used by later direct calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerEvidence
open Frontend SourceInference
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (ResolvedCaller)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : Principal compiled method)

structure CallerAt (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) where
  resolved : ResolvedCaller compiled.sourceProgram principal.named.specialized evidence
  signatures : context.signatures = compiled.sourceProgram.signatures
  ledger : context.solvedRequirements = principal.named.specialized.function.solvedRequirements
  assumptions : ∀ goal, goal ∈ principal.named.specialized.assumptions → goal ∈ context.assumptions
  unique : RequirementIdsUnique context

/-- The selected method's complete assumption list follows from its real
trait, implementation and method catalog entries. -/
theorem assumptions_empty_generic
    (catalog : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram) :
    principal.sourceBody.context.assumptions = [] := by
  obtain ⟨implementation, declaration, trait, definition, substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro implementationMember methodMember traitMember _owner _member _id _bodyOwner _exact _range _source _result context =>
    have empty := catalog.assumptions implementation implementationMember declaration methodMember trait traitMember
    rw [context]
    change List.map _ (implementation.methodAssumptions trait declaration) = []
    rw [empty]
    rfl

/-- Actual selection assembles precisely the empty method dictionary; no
statement about resolver agreement is inferred from coverage alone. -/
def of_selected_generic
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (catalog : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context}
    (fields : Dynamic.RuntimeContextFields sourceAt.context context) :
    CallerAt principal context child.evidence := by
  have empty := assumptions_empty_generic principal catalog
  have dictionary := RecursiveMethodSelectionIdentity.dictionary_empty principal.selected empty
  have callerEmpty : principal.named.specialized.assumptions = [] := by
    rw [principal.cached.same]
    exact empty
  have parameters := RecursiveNamedInitialContextValidity.mono_fields sourceAt.extended
  refine ⟨⟨[], ?_, ?_⟩, ?_, fields.solvedRequirements.trans sourceAt.valid.ledger, ?_, ?_⟩
  · rw [callerEmpty]
    rfl
  · rw [stages.evidence selected]
    exact dictionary
  · exact fields.signatures.trans (parameters.signatures.trans rfl)
  · intro goal member
    rw [callerEmpty] at member
    cases member
  · exact (fields.runtimeRequirementLedger sourceAt.valid.runtime).idsUnique

/-- The closed-catalog entry point retains its original signature. -/
theorem assumptions_empty
    (catalog : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram) :
    principal.sourceBody.context.assumptions = [] :=
  assumptions_empty_generic principal (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed catalog)

/-- Existing callers use the same authentic selected frame and dictionary. -/
def of_selected
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (catalog : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog compiled.sourceProgram)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure principal.sourceFunction child)
    {context : SourceSemantics.Context}
    (fields : Dynamic.RuntimeContextFields sourceAt.context context) :
    CallerAt principal context child.evidence :=
  of_selected_generic principal sourceAt
    (CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog.of_closed catalog) selected fields

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodCallerEvidence

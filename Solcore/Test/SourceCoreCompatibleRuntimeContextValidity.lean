import Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity

/-! Actual source frames and lexical binder changes supply the runtime context
condition before a Header exists. All rows and residual modes are preserved. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleRuntimeContextValidity
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleRuntimeContextValidity

theorem actual_frame {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {solved : List SolvedRequirement}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved) :
    Valid solved context function.evidence :=
  of_frame frame extended programTyped sameLedger

/-- An unused row stays in the complete list after an actual binder extension.
The execution-facing condition cannot silently shorten a template ledger. -/
theorem unused_row_retained {solved : List SolvedRequirement} {source target : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {owner : Resolved.DeclarationId} {binder : TypedBinder}
    (valid : Valid solved source evidence) (extended : BinderExtends owner source binder target)
    {row : SolvedRequirement} (unused : row ∈ solved) : row ∈ target.solvedRequirements := by
  rw [(valid.extend extended).ledger]
  exact unused

theorem residual_mode_retained {source target : SourceSemantics.Context} {owner : Resolved.DeclarationId}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner source parameters types target)
    (actualMode : source.residualTypeVariables = true) : target.residualTypeVariables = true :=
  (RecursiveNamedInitialContextValidity.mono_fields extended).targetResidualVariablesOpen actualMode

abbrev same_ordinary_context := @of_ordinary
abbrev same_context_transport := @Valid.transport

end Tests.SourceCoreCompatibleRuntimeContextValidity

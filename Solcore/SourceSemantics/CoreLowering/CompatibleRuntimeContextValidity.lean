import Solcore.SourceSemantics.CoreLowering.RecursiveNamedInitialContextValidity

/-! Runtime context conditions retain the complete solved ledger and its actual
covering dictionary. Lexical changes transport these fields without removing
unused assumptions or qualified template rows. Ordinary validity is a one-way
adapter; the runtime interface does not imply ordinary ledger validity. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity
open Frontend SourceInference

structure Valid (solved : List SolvedRequirement) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) : Prop where
  ledger : context.solvedRequirements = solved
  runtime : RuntimeRequirementLedgerValid context
  covers : evidence.Covers context

/-- The old full ordinary ledger implies the execution-facing condition for
the same entire row list. This adapter never runs in the opposite direction. -/
theorem of_ordinary {solved : List SolvedRequirement} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) :
    Valid solved context evidence :=
  ⟨valid.ledger, ⟨valid.valid.idsUnique, fun row _ member _ => valid.valid.entriesValid row member⟩,
    valid.covers⟩

/-- Only non-lexical fields are needed; full solved-row equality transports
the same ledger and dictionary into the actual target context. -/
theorem Valid.transport {solved : List SolvedRequirement} {source target : Context}
    {evidence : Dynamic.EvidenceEnvironment} (valid : Valid solved source evidence)
    (fields : Dynamic.RuntimeContextFields source target) : Valid solved target evidence :=
  ⟨fields.solvedRequirements.trans valid.ledger, fields.runtimeRequirementLedger valid.runtime,
    fields.covers valid.covers⟩

theorem Valid.extend {solved : List SolvedRequirement} {source target : Context}
    {evidence : Dynamic.EvidenceEnvironment} {owner : Resolved.DeclarationId} {binder : TypedBinder}
    (valid : Valid solved source evidence) (extended : BinderExtends owner source binder target) :
    Valid solved target evidence :=
  valid.transport (Dynamic.RuntimeContextFields.ofBinderExtends extended)

theorem Valid.mono {solved : List SolvedRequirement} {source target : Context}
    {evidence : Dynamic.EvidenceEnvironment} {owner : Resolved.DeclarationId}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (valid : Valid solved source evidence) (extended : MonoBindersExtend owner source parameters types target) :
    Valid solved target evidence :=
  valid.transport (RecursiveNamedInitialContextValidity.mono_fields extended)

/-- Independent program validity supplies runtime rows and the actual source
frame supplies coverage. No Header.valid or template-empty test is an input. -/
theorem of_frame {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : Context}
    {types : List TypeSystem.Ty} {solved : List SolvedRequirement}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved) :
    Valid solved context function.evidence :=
  ⟨(RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger,
    RecursiveNamedInitialContextValidity.runtime frame extended programTyped,
    RecursiveNamedInitialContextValidity.covers frame extended⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity

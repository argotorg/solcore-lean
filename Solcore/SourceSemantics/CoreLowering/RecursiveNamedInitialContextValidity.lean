import Solcore.SourceSemantics.CoreLowering.NamedCallSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralMeaning
import Solcore.SourceSemantics.Dynamic.Preservation

/-! Initial named source contexts are derived before constructing a catalog
Header. The actual frame and parameter extension retain scoped requirements
and evidence coverage. Full ledger validity is obtained only under an explicit
empty-template check on the complete source; unused rows are never removed.
No runtime trace, native typing or Header.valid is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedInitialContextValidity
open Frontend SourceInference

/-- Parameter installation changes only lexical fields, retaining the same
signature catalog, assumptions, complete ledger and residual-variable mode. -/
theorem mono_fields {owner : Resolved.DeclarationId} {initial final : Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner initial parameters types final) :
    Dynamic.RuntimeContextFields initial final := by
  induction extended with
  | nil => exact .refl _
  | cons _ head _ ih => exact (Dynamic.RuntimeContextFields.ofBinderExtends head).trans ih

variable {program : Program} {instantiation : DeclarationInstantiation}
  {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
  {context : Context} {types : List TypeSystem.Ty}

/-- Independent program validity supplies the whole scoped ledger. Its source
identity and actual parameter context are fixed by the real frame. -/
theorem scoped_ledger (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) :
    ScopedRequirementLedgerWellFormed context function.source := by
  obtain ⟨_, _, _, certificate⟩ := frame.instantiated.certificate programTyped
  have original : ScopedRequirementLedgerWellFormed function.context function.source := by
    simpa only [frame.context, frame.source] using certificate.requirement_ledger
  exact (mono_fields extended).scopedRequirementLedger original

/-- Execution-facing ledger validity keeps every row, including assumption
and qualified template rows. It is not full ordinary ledger validity. -/
theorem runtime (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) :
    RuntimeRequirementLedgerValid context :=
  (scoped_ledger frame extended programTyped).toRuntime

/-- The same frame dictionary covers the actual installed parameter context.
Neither equality with another dictionary nor evidence uniqueness is needed. -/
theorem covers (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context) :
    function.evidence.Covers context := by
  apply (mono_fields extended).covers
  simpa only [frame.context] using frame.covers

/-- A check of the complete retained source, including unused nodes, removes
only the template alternative in scoped validity. No ledger row is dropped. -/
theorem ordinary {source : TypedSource}
    (ledger : ScopedRequirementLedgerWellFormed context source)
    (templatesEmpty : source.localSchemeTemplateIds = []) :
    RequirementLedgerWellFormed context := by
  refine ⟨ledger.idsUnique, ?_⟩
  intro row member
  exact ledger.ordinary_valid member (by
    simp only [← typedSourceLocalSchemeTemplateIds_eq_carrier, templatesEmpty, List.not_mem_nil, not_false_eq_true])

/-- This bounded entry constructs the existing semantic context condition
without a Header or prior context-validity callback. Template-bearing sources
remain outside this conversion even when their templates are unreachable. -/
theorem of_templates_empty (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) {solved : List SolvedRequirement}
    (sameLedger : function.context.solvedRequirements = solved)
    (templatesEmpty : function.source.localSchemeTemplateIds = []) :
    CompatibleExpressionLiterals.ContextValid solved context function.evidence :=
  ⟨(mono_fields extended).solvedRequirements.trans sameLedger,
    ordinary (scoped_ledger frame extended programTyped) templatesEmpty, covers frame extended⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedInitialContextValidity

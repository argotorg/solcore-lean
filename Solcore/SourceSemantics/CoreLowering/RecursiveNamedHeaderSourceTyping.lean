import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSourceContextFacts
import Solcore.SourceSemantics.TraitSubstitutionProperties
import Solcore.SourceSemantics.Dynamic.Preservation

/-! Independent program typing and the Header's actual source instantiation
give body typing in its real parameter context. The two parameter extensions
have the same source binders, so functionality identifies their contexts.
Native types, decoding, and runtime completion do not authenticate source data.
Syntax admission, compiler policies, and runtime frames remain separate facts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

/-- The complete source invocation package uses the Header's actual raw input
types and lexical context, rather than a separately supplied body judgment. -/
theorem certificate (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ facts, Dynamic.FunctionInstanceTypingCertificate program header.instantiation header.sourceBody
      header.types header.context facts := by
  obtain ⟨types, lexical, facts, certified⟩ := header.frame.instantiated.certificate programTyped
  have extended := header.extended
  rw [header.frame.source, header.frame.context, header.frame.parameters] at extended
  have contextEq := Dynamic.MonoBindersExtend.functional certified.typing.inputs_extend extended
  have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq certified.typing.inputs_extend).symm.trans
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended)
  exact ⟨facts, typesEq ▸ contextEq ▸ certified⟩

/-- Source typing is transported along real frame attribution only. -/
theorem body (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ facts, BodyHasType header.function.source header.context header.function.resultType facts := by
  obtain ⟨facts, certified⟩ := certificate header programTyped
  rw [header.frame.source, header.frame.result]
  exact ⟨facts, certified.typing.body_typed⟩

/-- The same body belongs to the complete prepared specialization. -/
theorem prepared_body (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ facts, BodyHasType header.named.specialized.function.typedBody header.context
      header.named.specialized.function.inferredBodyType facts := by
  obtain ⟨facts, typed⟩ := body header programTyped
  exact ⟨facts, by simpa only [header.agreement.source, header.agreement.result] using typed⟩

/-- The normative statement judgment is for the actual invocation roots.
This does not manufacture a lowerer's more restricted Syntax certificate. -/
theorem statements (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ final facts, StatementsHaveType header.function.source
      {returnType := header.function.resultType} header.context header.function.body final facts ∧
      BodyCompletes header.function.resultType facts := by
  obtain ⟨facts, final, typed, _, completes⟩ := body header programTyped
  refine ⟨final, facts, ?_, completes⟩
  simpa [header.agreement.roots, List.filterMap_map, Function.comp_def] using typed

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping

import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

/-- The certificate is for this Header's original source instance and parameter context. -/
def Certified (header : Header prepared values definitions program) : Prop :=
  ∃ facts, Dynamic.FunctionInstanceTypingCertificate program header.instantiation header.sourceBody
    header.types header.context facts

theorem Certified.body {header : Header prepared values definitions program}
    (certified : Certified header) :
    ∃ facts, BodyHasType header.function.source header.context header.function.resultType facts := by
  obtain ⟨facts, certificate⟩ := certified
  rw [header.frame.source, header.frame.result]
  exact ⟨facts, certificate.typing.body_typed⟩

theorem Certified.statements {header : Header prepared values definitions program}
    (certified : Certified header) :
    ∃ final facts, StatementsHaveType header.function.source
      {returnType := header.function.resultType} header.context header.function.body final facts ∧
      BodyCompletes header.function.resultType facts := by
  obtain ⟨facts, final, typed, _, completes⟩ := certified.body
  refine ⟨final, facts, ?_, completes⟩
  simpa [header.agreement.roots, List.filterMap_map, Function.comp_def] using typed

theorem Certified.runtime {header : Header prepared values definitions program}
    (certified : Certified header) :
    Dynamic.SourceRuntimeValid program header.function.context header.function.source := by
  obtain ⟨facts, certificate⟩ := certified
  rw [header.frame.context, header.frame.source]
  exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping

import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSpecializationValidity

/-! These consumers obtain independent source body judgments from actual
instantiation receipts. They do not take a prior body typing package, change
residual source scope, or infer source authority from native values. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedHeaderSourceTyping
open Solcore SourceSemantics SourceSemantics.CoreLowering Core Frontend SourceInference
open CallableAncestryPairedLookup RecursiveNamedCatalog

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : SourceSemantics.Program}

theorem header_raw_call_type (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    header.instantiation.type = .function (TypeSystem.Ty.productMany header.types) header.sourceBody.resultType := by
  obtain ⟨_, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header programTyped
  exact certified.callable_type

theorem original_header_body (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ facts, BodyHasType header.function.source header.context header.function.resultType facts :=
  RecursiveNamedHeaderSourceTyping.body header programTyped

theorem actual_parameter_context (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ facts, BodyHasType header.named.specialized.function.typedBody header.context
      header.named.specialized.function.inferredBodyType facts :=
  RecursiveNamedHeaderSourceTyping.prepared_body header programTyped

theorem original_statement_roots (header : Header prepared values definitions program)
    (programTyped : ProgramWellFormed program) :
    ∃ final facts, StatementsHaveType header.function.source
      {returnType := header.function.resultType} header.context header.function.body final facts ∧
      BodyCompletes header.function.resultType facts :=
  RecursiveNamedHeaderSourceTyping.statements header programTyped

section ActualSpecialization
variable {compilerProgram : CheckedProgram} {signature : ProgramFunctionSignature} {generic : CheckedFunction}
  {supplied : TypeSystem.ParameterSubstitution} {specialized : SourceSpecialization.SpecializedFunction}
  (programTyped : ProgramWellFormed (Program.ofChecked compilerProgram))
  (signatureMember : signature ∈ compilerProgram.signatures.functions)
  (genericMember : generic ∈ compilerProgram.functions)
  (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok specialized)
  (range : ParameterSubstitution.RangeWellFormed (Context.ofSignatures compilerProgram.signatures)
    specialized.parameterSubstitution)

include programTyped signatureMember genericMember accepted range in
theorem actual_canonical_body :
    ∃ types context facts, Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compilerProgram)
      (CallableNamedMetadata.instantiation specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compilerProgram specialized) types context facts := by
  exact (RecursiveNamedSpecializationValidity.instantiated signatureMember genericMember accepted
    (programTyped.signatures.function_parameters signature signatureMember).1 range).certificate programTyped

include programTyped signatureMember genericMember accepted range in
theorem actual_retained_body :
    ∃ types context facts, Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compilerProgram)
      (CallableNamedCanonicalOrder.retainedInstantiation specialized)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compilerProgram specialized) types context facts := by
  exact (RecursiveNamedSpecializationValidity.retained_instantiated signatureMember genericMember accepted
    (programTyped.signatures.function_parameters signature signatureMember).1 range).certificate programTyped

end ActualSpecialization
end Tests.SourceCoreRecursiveNamedHeaderSourceTyping

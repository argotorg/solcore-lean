import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders

/-! Ordinary closure formation retains the actual named preparation and its
complete dictionary. Lexical changes retain runtime context fields; native
capture typing alone does not establish this receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryCallerReceipts
open Core Frontend SourceInference

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The original actual named caller, reached lexical context and full evidence
are retained together before the capture environment is chosen. -/
structure CallerAt
    (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) where
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled caller.named.specialized
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared caller.instantiation caller
  fields : Dynamic.RuntimeContextFields caller.context context
  dictionary : evidence = prepared.view.evidence

variable {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {context next : SourceSemantics.Context} {evidence other : Dynamic.EvidenceEnvironment}

/-- Reindexing the actual preparation uses its retained Header identity. -/
def CallerAt.of_header
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation caller)
    (fields : Dynamic.RuntimeContextFields caller.context context)
    (dictionary : evidence = prepared.view.evidence) : CallerAt caller context evidence := by
  have same : row = caller.named.specialized :=
    prepared.same.symm.trans (congrArg (fun named => named.specialized) aligned.named.symm)
  subst row
  exact ⟨prepared, aligned.metadata.symm ▸ aligned, fields, dictionary⟩

/-- Parameter and lexical extensions preserve the original caller identity. -/
def CallerAt.extend (receipt : CallerAt caller context evidence)
    (fields : Dynamic.RuntimeContextFields context next) : CallerAt caller next evidence :=
  { receipt with fields := receipt.fields.trans fields }

/-- A selected stage supplies the same complete evidence environment. -/
def CallerAt.with_evidence (receipt : CallerAt caller context evidence)
    (same : other = evidence) : CallerAt caller context other :=
  { receipt with dictionary := same.trans receipt.dictionary }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryCallerReceipts

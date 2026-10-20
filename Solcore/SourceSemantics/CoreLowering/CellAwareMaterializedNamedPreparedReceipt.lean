import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedInvocation
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedPreparedReceipt
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedBodyReceipt
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures

/-! The actual selected row and installed physical capture fix every static
input used by the mixed named invocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedPreparedReceipt
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header NamedCapture)
open CellAwareNamedPreparedReceipt (administrative cast_generation cast_generation_body)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {key : CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {header : Header whole (Program.ofChecked whole.sourceProgram)}

def cast_body {first second : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {code : Expr} (same : first = second)
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed first diagnostics code)
    {administrative : Core.Context} {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body generation (CellAwareMaterializedBodyProducer.Certificate generation)
      administrative context expected) :
    CellAwareNamedBodySupport.Body (cast_generation same generation)
      (CellAwareMaterializedBodyProducer.Certificate (cast_generation same generation)) administrative context expected := by
  cases same
  exact body

variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers key header mapping world store)

structure Receipt where
  generation : CallableIndexedNamedGeneration.Compilation whole.indexed header.named prepared.diagnostics prepared.code
  emitted : header.body = generation.body
  body : CellAwareNamedBodySupport.Body generation (CellAwareMaterializedBodyProducer.Certificate generation)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative)
    header.context header.function.resultType
  issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed header.named
    (prepared.diagnostics.reasonAt header.named.signature.key)

include aligned in
theorem of_header_selected {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies whole)
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareMaterializedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
      prepared.named.specialized.function.inferredBodyType) :
    Nonempty (Receipt prepared capture) := by
  obtain ⟨body⟩ := CellAwareMaterializedNamedBodyReceipt.of_header_selected prepared aligned ready bodyTyping member profile
  let generation := cast_generation aligned.named.symm prepared.compilation
  have actual := cast_body aligned.named.symm prepared.compilation body
  have prefixEq : RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header =
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative := by
    simp only [RecursiveNamedLambdaFormationHeads.nativePrefix, administrative capture, header.parameterType, List.cons_append]
  have issuer := CellAwareNamedDiagnosticIssuer.of_prepared prepared diagnostic aligned
  rw [aligned.reasonAt] at issuer
  have issuerAt : CellAwareNamedDiagnosticIssuer.Named whole.indexed header.named
      (prepared.diagnostics.reasonAt header.named.signature.key) := by
    simpa only [aligned.named] using issuer
  exact ⟨⟨generation, aligned.body.trans (cast_generation_body aligned.named.symm prepared.compilation).symm,
    prefixEq ▸ actual, issuerAt⟩⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include aligned in
theorem of_header {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareMaterializedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
      prepared.named.specialized.function.inferredBodyType) :
    Nonempty (Receipt prepared capture) := by
  apply of_header_selected (bodyTyping := SelectedCompilationBodyTyping.Bodies.of_program wellFormed) (aligned := aligned) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedNamedPreparedReceipt

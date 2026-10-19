import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedInvocation
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedBodyReceipt
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedPreparedReceipt

/-! The actual selected row and installed physical capture fix every static
input used by the mixed named invocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedPreparedReceipt
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header NamedCapture)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {key : CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {header : Header whole (Program.ofChecked whole.sourceProgram)}

open CellAwareNamedPreparedReceipt (administrative cast_generation cast_generation_body)

def cast_body {first second : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {code : Expr} (same : first = second)
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed first diagnostics code)
    {administrative : Core.Context} {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareImperativeBodyProducer.Body generation (CellAwareImperativeBodyProducer.Certificate generation)
      administrative context expected) :
    CellAwareImperativeBodyProducer.Body (cast_generation same generation)
      (CellAwareImperativeBodyProducer.Certificate (cast_generation same generation)) administrative context expected := by
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
  body : CellAwareImperativeBodyProducer.Body generation (CellAwareImperativeBodyProducer.Certificate generation)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.named.administrative)
    header.context header.function.resultType
  projection : whole.compatible.checked.catalog.project header.function.resultType = .ok header.named.signature.resultType
  issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed header.named
    (prepared.diagnostics.reasonAt header.named.signature.key)
  issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed prepared.diagnostics

include aligned in
theorem of_header {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (profile : CellAwareImperativeBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
      prepared.named.specialized.function.inferredBodyType) :
    Nonempty (Receipt prepared capture) := by
  obtain ⟨body⟩ := CellAwareImperativeNamedBodyReceipt.of_program prepared aligned ready diagnostic wellFormed member profile
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
    prefixEq ▸ actual, (by simpa only [← header.resultType] using aligned.projection), issuerAt, CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared prepared diagnostic⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedPreparedReceipt

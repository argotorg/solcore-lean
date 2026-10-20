import Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaderCertificates
import Solcore.SourceSemantics.CoreLowering.SelectedStagedPostAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedInvocation
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodyReceipt
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures

/-! The actual selected row and installed physical capture fix every static
input used by the mixed named invocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedPreparedReceipt
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header NamedCapture)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {key : CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {store : Store}
  {header : Header whole (Program.ofChecked whole.sourceProgram)}

private theorem globals_types (globals : List SourceCoreCalls.Signature) (base : Nat) :
    (SourceCoreLambdaTemplates.freshGlobals globals base).map Value.type = globals.map (·.referenceType) := by
  simp only [SourceCoreLambdaTemplates.freshGlobals, List.map_map]
  change globals.zipIdx.map (fun pair => pair.1.referenceType) = _
  change globals.zipIdx.map ((fun signature => signature.referenceType) ∘ Prod.fst) = _
  rw [← List.map_map, List.zipIdx_map_fst]

/-- Runtime tags fix the types of the actual canonical physical references.
No unused administrative suffix is invented. -/
theorem administrative
    (capture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers key header mapping world store) :
    capture.named.administrative = whole.indexed.base.globals.map (·.referenceType) ++
      [.cell whole.indexed.ancestry.layout.frame.type] := by
  have tags := capture.named.environments.runtime_hasTypes.type_tags
  change capture.named.canonical.map Value.type = capture.named.administrative at tags
  rw [capture.canonical_eq] at tags
  have eq : (CallableIndexedOwnedPhysicalGlobals.environment whole).map Value.type =
      whole.indexed.base.globals.map (·.referenceType) ++ [.cell whole.indexed.ancestry.layout.frame.type] := by
    simp only [CallableIndexedOwnedPhysicalGlobals.environment, SourceCoreCallableIndexedTemplates.globalEnvironment,
      List.map_append, globals_types, List.map_cons, List.map_nil, Value.type]
  exact tags.symm.trans eq

def cast_generation {first second : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {code : Expr} (same : first = second)
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed first diagnostics code) :
    CallableIndexedNamedGeneration.Compilation whole.indexed second diagnostics code := same ▸ generation

@[simp] theorem cast_generation_body {first second : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {code : Expr} (same : first = second)
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed first diagnostics code) :
    (cast_generation same generation).body = generation.body := by cases same; rfl

def cast_body {first second : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {code : Expr} (same : first = second)
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed first diagnostics code)
    {administrative : Core.Context} {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body generation (CellAwareNamedBodyProducer.Certificate generation)
      administrative context expected) :
    CellAwareNamedBodySupport.Body (cast_generation same generation)
      (CellAwareNamedBodyProducer.Certificate (cast_generation same generation)) administrative context expected := by
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
  body : CellAwareNamedBodySupport.Body generation (CellAwareNamedBodyProducer.Certificate generation)
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
    (profile : CellAwareNamedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
      prepared.named.specialized.function.inferredBodyType) :
    Nonempty (Receipt prepared capture) := by
  obtain ⟨body⟩ := CellAwareNamedBodyReceipt.of_header_selected prepared aligned ready bodyTyping member profile
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
    (profile : CellAwareNamedBodyProducer.Profile whole.indexed prepared.named prepared.compilation.statements
      prepared.named.specialized.function.inferredBodyType) :
    Nonempty (Receipt prepared capture) := by
  apply of_header_selected (bodyTyping := SelectedCompilationBodyTyping.Bodies.of_program wellFormed) (aligned := aligned) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedPreparedReceipt

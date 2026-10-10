import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNamedProfileExtraction
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedProfileFamilies

/-! The literal finite issued Header and a genuine bootstrap owner construct
rich profiles through the paired enclosing-code collector. Both child native
contexts remain available to the static certificate factory. Diagnostic tokens
are derived by the existing finite issuer bridge; no completed body law or
caller-supplied Profile is a static input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedCatalogNamedProfileFamilies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Header)
open CallableIndexedOwnedPreparedNamedDiagnosticSources
open CallableIndexedOwnedNamedBootstrapReceipts (NamedOwner)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {input : Input compiled}
  (packet : Issued input)
  {headers : List (Header compiled)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {certificates : Header compiled → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled → ExpressionId → Prop}
  {recipe : SourceCoreIndexedSession.Recipe}
  (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (origin : NamedOwner (headers := headers) keys functions registry)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (children : ∀ administrative, CallableIndexedOwnedPreparedPairedNamedProfileExtraction.Children
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (header := packet.header) (administrative := administrative))

/-- One genuine parameter entry drives one paired extraction. The returned
rich Profile keeps the original actual administrative context and issuer. -/
noncomputable def profiles :
    CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := headers) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions origin.owner (header := packet.header) := by
  intro arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost entry
  have captureZero := origin.capture_zero
  rw [captureZero] at entry
  let extraction := Classical.choice (CallableIndexedOwnedPreparedPairedNamedProfileExtraction.extract_at
    (prepared packet) packet.aligned (issuer packet).typing.2 (assignments_prepared packet)
    accepted nativeMember functions origin.owner complete entry wellFormed (children administrative))
  exact CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles.of_collected packet extraction

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedCatalogNamedProfileFamilies

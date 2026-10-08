import Solcore.SourceSemantics.CoreLowering.RecursiveNamedEmittedRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPublicProfileExtraction

/-! The genuine public compiler and its actual parameter entry produce the
retained diagnostic plan. Concrete local static receipts interpret that plan
internally; the authentic output then supplies the closed named family profile. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedEmittedProfileExtraction
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedPublicSpecializationMeaning RecursiveNamedCatalogRuntimeProfileFactory
open CallableIndexedOwnedNamedPublicProfileExtraction
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

variable {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (compilation : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → SourceCoreFunctions.Context)
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
    administrative actualContext actual ξ frameLocation current ghost)
  {tracked : Bool}
  (sites : InputsWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    true tracked .reachable headers header (compilation header) (expressionSyntax header)
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))

include recipeAccepted prepared aligned nativeMember functions owner complete entry sites in
/-- Genuine emitted diagnostics are interpreted from concrete local static
receipts at the exact ordinary parameter entry. -/
theorem interpreted_at
    (localReceipts : EmittedDiagnosticPlan.Plan.LocalReceipts (factory := sites.factory) registry faults) :
    ∃ receipt : ReceiptWith (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      true .reachable headers header (compilation header) (expressionSyntax header)
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      receipt.extracted.diagnostics registry faults := by
  exact interpreted_source_with (cached_typed prepared aligned nativeMember)
    (cached_supported recipeAccepted prepared aligned) complete aligned.globals entry sites localReceipts

include recipeAccepted aligned nativeMember complete in
omit entry sites in
/-- Each actual body entry supplies original Source Syntax and child static
receipts; the retained compiler plan derives its own diagnostic interpretation. -/
theorem interpreted_receipts_for
    (children : SitesFor (header := header) (headers := headers) (expressionSyntax := expressionSyntax)
      prepared compilation functions owner tracked)
    (localReceipts : ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost}
      (actualEntry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
        administrative actualContext actual ξ frameLocation current ghost),
      EmittedDiagnosticPlan.Plan.LocalReceipts (factory := (children actualEntry).factory) registry faults) :
    InterpretedReceiptsFor (headers := headers) (expressionSyntax := expressionSyntax) (registry := registry) (faults := faults)
      compilation functions owner (header := header) := by
  intro arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost actualEntry
  let inputs := policy_inputs prepared aligned compilation (children actualEntry)
  exact interpreted_at recipeAccepted prepared aligned nativeMember compilation functions owner complete actualEntry inputs
    (localReceipts actualEntry)

include recipeAccepted aligned nativeMember complete in
omit entry sites in
/-- The actual public emitted receipts construct the static profile provider
as a proposition. No completed body or diagnostic-output provider is requested. -/
theorem profiles_for_emitted
    (ordinary : owner.key.capturePrefix = 0)
    (children : SitesFor (header := header) (headers := headers) (expressionSyntax := expressionSyntax)
      prepared compilation functions owner tracked)
    (localReceipts : ∀ {arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost}
      (actualEntry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
        administrative actualContext actual ξ frameLocation current ghost),
      EmittedDiagnosticPlan.Plan.LocalReceipts (factory := (children actualEntry).factory) registry faults)
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures) :
    Nonempty (CallableIndexedOwnedAdmittedNamedExpressionHeads.ProfilesFor (headers := headers) (owner := owner)
      (functions := functions) (registry := registry) (faults := faults)
      (certificates := CallableIndexedOwnedReadyNamedFamilyClosure.certificates (headers := headers) compilation)
      (expressionSyntax := expressionSyntax) (diagnosticPolicy := .reachable) (runtime := true) header) :=
  profiles_for compilation functions owner ordinary
    (interpreted_receipts_for recipeAccepted prepared aligned nativeMember compilation functions owner complete children localReceipts) catalog
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedEmittedProfileExtraction

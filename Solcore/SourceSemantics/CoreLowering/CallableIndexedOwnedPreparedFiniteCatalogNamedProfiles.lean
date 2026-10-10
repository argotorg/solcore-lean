import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedDiagnosticSources
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedProfiles

/-! Finite named Headers and their actual selected diagnostic issuers construct
the rich catalog profile at a genuine parameter entry. The enclosing native
collector supplies the coupled Tree and prepared plan once. Diagnostic table
identity and structural token equations are derived from the retained issuer;
no completed expression or body execution is a construction premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedPreparedFiniteNamedInventories
open CallableIndexedOwnedPreparedNamedDiagnosticSources

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {input : Input compiled}
  (packet : Issued input)
  {certificates : Header compiled → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled → ExpressionId → Prop}
  {administrative : Core.Context}

/-- Project the authentic coupled compiler receipt into a rich profile. All
diagnostic alignment fields come from the same selected Header construction. -/
def of_collected
    (extraction : CallableIndexedOwnedPreparedDirectNamedProfileExtraction.Receipt
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (administrative := administrative) (prepared packet) (issuer packet).typing.2
      (assignments_prepared packet)) :
    CallableIndexedOwnedPreparedCatalogNamedProfiles.Profile
      (certificates := certificates) (expressionSyntax := expressionSyntax) packet.header administrative where
  row := input.row
  prepared := prepared packet
  instantiation := CallableNamedCanonicalOrder.retainedInstantiation input.row
  aligned := packet.aligned
  first := (issuer packet).first
  operandsTyped := (issuer packet).typing.2
  assignmentsPrepared := assignments_prepared packet
  extraction := extraction
  issued := issuer packet
  assignments := assignments packet
  operand := operand packet
  unary := unary packet
  projection := projection packet
  missing := missing packet

variable {headers : List (Header compiled)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 functions registry packet.header arguments before initialStore mapping world
    administrative actualContext actual ξ frameLocation current ghost)

include recipeAccepted nativeMember functions owner complete entry in
/-- Invoke the actual enclosing-code collector once at the real parameter
state, then construct the profile without caller-supplied diagnostic identities. -/
theorem extract_at
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (children : CallableIndexedOwnedPreparedDirectNamedProfileExtraction.Children
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (header := packet.header) (administrative := administrative)) :
    Nonempty (CallableIndexedOwnedPreparedCatalogNamedProfiles.Profile
      (certificates := certificates) (expressionSyntax := expressionSyntax) packet.header administrative) := by
  obtain ⟨extraction⟩ := CallableIndexedOwnedPreparedDirectNamedProfileExtraction.extract_at
    (prepared packet) packet.aligned (issuer packet).typing.2 (assignments_prepared packet)
    recipeAccepted nativeMember functions owner complete entry wellFormed children
  exact ⟨of_collected packet extraction⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles

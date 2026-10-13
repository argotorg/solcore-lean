import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport

/-! Existing compiler support embeds into the Association-specific support.
The new nested-formation branch cannot be produced by the original support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association
      headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) (stages : Staging.Recursive.Registry)
    (packet : PacketFor association stages)

/-- The original body support at the actual Association's entry context. -/
def GenericSupportFor : Type :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
      Support headers code support.body.toContext stages packet semanticFaults
  | .principal _ _ code _ support _ _ _ _ _ _ =>
      Support headers code support.body.toContext stages packet semanticFaults

/-- Original support uses every unchanged branch without any extra premise. -/
def SupportFor.of_generic (supported : GenericSupportFor association stages packet) :
    SupportFor association stages packet := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      cases packet <;> first | exact supported | exact nomatch supported
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      exact supported

/-- A compiler-selected original packet embeds without choosing a new packet. -/
theorem SupportFor.of_generic_packets
    (supported : Nonempty (Σ current : PacketFor association stages,
      GenericSupportFor association stages current)) :
    Nonempty (Σ current : PacketFor association stages, SupportFor association stages current) := by
  obtain ⟨current, supported⟩ := supported
  exact ⟨⟨current, SupportFor.of_generic association stages current supported⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport

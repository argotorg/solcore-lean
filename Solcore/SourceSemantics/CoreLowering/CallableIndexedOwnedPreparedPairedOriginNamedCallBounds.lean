import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOriginGlobalsCarriers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedCatalogNamedProfileFamilies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds

/-! The actual Origin packet supplies Globals at its original caller bridge.
Literal finite issued rows and paired compiler children construct every rich
named profile at the real parameter entry. The genuine bootstrap owner proves
zero prefix and global count. Named leaves retain the original optional
caller dictionary and consume only the strict body induction family. No
completed Profile, body law or weak-model inverse is a static input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedOriginNamedCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input issue)
open CallableIndexedOwnedNamedBootstrapReceipts (NamedOwner)
open CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds (SourceFlows NativeFlows CallerEvidence)
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (inputs : List (Input compiled))


variable {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {recipe : SourceCoreIndexedSession.Recipe}
  (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (seed : NamedOwner (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs)) keys functions registry)
  (sameOwner : seed.owner = owner)
  (origin : Origin compiled)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs))
  (staticChildren : ∀ input, input ∈ inputs → ∀ administrative,
    CallableIndexedOwnedPreparedPairedNamedProfileExtraction.Children
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (header := (issue wellFormed input).header) (administrative := administrative))

include accepted nativeMember complete staticChildren in
private theorem profiles_exists (header) (member : header ∈ (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs)) :
    Nonempty (CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs)) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions seed.owner (header := header)) := by
  obtain ⟨input, inputMember, same⟩ := List.mem_map.mp member
  subst header
  exact ⟨CallableIndexedOwnedPreparedPairedCatalogNamedProfileFamilies.profiles
    (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs)) (certificates := certificates) (expressionSyntax := expressionSyntax)
    (issue wellFormed input) accepted nativeMember functions seed complete wellFormed (staticChildren input inputMember)⟩

private noncomputable def profiles :
    ∀ header, header ∈ (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs) → CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs)) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions seed.owner (header := header) := by
  intro header member arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost entry
  let chosen := @Classical.choice _ (profiles_exists (accepted := accepted) (nativeMember := nativeMember)
    (complete := complete) (staticChildren := staticChildren) wellFormed inputs functions seed header member)
  exact chosen entry

private theorem layouts : ∀ header, header ∈ (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs) → header.layouts = compiled.indexed.layouts := by
  intro header member
  obtain ⟨input, _member, same⟩ := List.mem_map.mp member
  subst header
  exact (issue wellFormed input).aligned.layouts

include staticChildren in
private theorem syntaxTree : ∀ header, header ∈ (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs) →
    GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
      header.context (.statements true header.function.body) header.function.resultType := by
  intro header member
  obtain ⟨input, inputMember, same⟩ := List.mem_map.mp member
  subst header
  exact (staticChildren input inputMember []).syntaxTree

variable {named : CallableIndexedNamedGeneration.Named}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  (evidence : Dynamic.EvidenceEnvironment)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source named))
  (covers : evidence.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source named))
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (sameEvidence : CallerEvidence callerEvidence evidence)

local notation "bridge" => Origin.bridge (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs)) origin owner
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "calls" => RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
  callerEvidence (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs) (CallableIndexedNamedGeneration.context compiled.indexed named)
  (CallableIndexedNamedGeneration.source named) context certificate

include accepted nativeMember seed sameOwner complete staticChildren runtime covers unique sameEvidence in
/-- The same real named call leaf preserves the original caller protocol and
returned pool. Profiles are constructed from finite issuer-aligned children. -/
theorem preserves_calls (idsUnique : RequirementIdsUnique context)
    (budget size : Nat) (within : size ≤ budget)
    (children : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence (CallableIndexedNamedGeneration.source named) certificate faults))
    (bodies : ∀ header, header ∈ (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs) → SourceFlows (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs)) (keys := keys)
      (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence
      (CallableIndexedNamedGeneration.source named) calls faults size := by
  cases sameOwner
  have original := CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds.preserves_calls
    (functions := functions) (faults := faults) (owner := seed.owner) (captureZero := seed.capture_zero)
    (compilation := CallableIndexedNamedGeneration.context compiled.indexed named)
    (source := CallableIndexedNamedGeneration.source named) (context := context) (certificate := certificate)
    (globals := fun header member => seed.globals member) evidence
    (CallableIndexedOwnedPreparedOriginGlobalsCarriers.carrier (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs)) origin seed.owner)
    wellFormed runtime covers unique idsUnique (layouts wellFormed inputs)
    (syntaxTree wellFormed inputs staticChildren)
    (profiles (accepted := accepted) (nativeMember := nativeMember) (complete := complete)
      (staticChildren := staticChildren) wellFormed inputs functions seed)
    wellFormed.function_ids callerEvidence sameEvidence budget size within
  cases origin <;> exact @original children bodies

include accepted nativeMember seed sameOwner complete staticChildren runtime covers unique sameEvidence in
/-- Reflection keeps the independent Source grade returned by the actual typed
finish and restores the original complete caller packet. -/
theorem reflects_calls (budget size : Nat) (within : size ≤ budget)
    (children : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence (CallableIndexedNamedGeneration.source named) certificate faults))
    (bodies : ∀ header, header ∈ (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs) → NativeFlows (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs)) (keys := keys)
      (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence
      (CallableIndexedNamedGeneration.source named) calls faults size := by
  cases sameOwner
  have original := CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds.reflects_calls
    (functions := functions) (faults := faults) (owner := seed.owner) (captureZero := seed.capture_zero)
    (compilation := CallableIndexedNamedGeneration.context compiled.indexed named)
    (source := CallableIndexedNamedGeneration.source named) (context := context) (certificate := certificate)
    (globals := fun header member => seed.globals member) evidence
    (CallableIndexedOwnedPreparedOriginGlobalsCarriers.carrier (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers wellFormed inputs)) origin seed.owner)
    wellFormed runtime covers unique (layouts wellFormed inputs)
    (syntaxTree wellFormed inputs staticChildren)
    (profiles (accepted := accepted) (nativeMember := nativeMember) (complete := complete)
      (staticChildren := staticChildren) wellFormed inputs functions seed)
    callerEvidence sameEvidence budget size within
  cases origin <;> exact @original children bodies

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedOriginNamedCallBounds

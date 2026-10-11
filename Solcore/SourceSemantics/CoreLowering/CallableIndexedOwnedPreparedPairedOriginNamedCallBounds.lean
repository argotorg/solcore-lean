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
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory)
open CallableIndexedOwnedNamedBootstrapReceipts (NamedOwner)
open CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds (SourceFlows NativeFlows CallerEvidence)
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (inputs : List (Input compiled))
  (rows : Inventory inputs)


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
  (seed : NamedOwner (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)) keys functions registry)
  (sameOwner : seed.owner = owner)
  (origin : Origin compiled)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
  (staticChildren : ∀ {input} (packet : Issued input), Inventory.HasRow packet rows → ∀ administrative,
    CallableIndexedOwnedPreparedPairedNamedProfileExtraction.Children
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (header := packet.header) (administrative := administrative))

include wellFormed accepted nativeMember complete staticChildren in
private theorem profiles_exists (header)
    (member : header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) :
    Nonempty (CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions seed.owner (header := header)) := by
  obtain ⟨input, packet, retained, same⟩ := rows.mem_headers header member
  subst header
  exact CallableIndexedOwnedPreparedPairedCatalogNamedProfileFamilies.profiles
    (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    packet accepted nativeMember functions seed complete wellFormed (staticChildren packet retained)

include wellFormed accepted nativeMember complete staticChildren in
private theorem profiles :
    Nonempty (∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
      CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
        functions seed.owner (header := header)) := by
  refine ⟨?_⟩
  intro header member arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost entry
  let chosen := @Classical.choice _ (profiles_exists (wellFormed := wellFormed) (inputs := inputs) (rows := rows)
    (accepted := accepted) (nativeMember := nativeMember) (functions := functions)
    (seed := seed) (complete := complete) (staticChildren := staticChildren) header member)
  exact chosen entry

private theorem layouts :
    ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
      header.layouts = compiled.indexed.layouts := by
  intro header member
  obtain ⟨input, packet, retained, same⟩ := rows.mem_headers header member
  subst header
  exact packet.aligned.layouts

include staticChildren in
private theorem syntaxTree :
    ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
      GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
        header.context (.statements true header.function.body) header.function.resultType := by
  intro header member
  obtain ⟨input, packet, retained, same⟩ := rows.mem_headers header member
  subst header
  exact (staticChildren packet retained []).syntaxTree

variable {named : CallableIndexedNamedGeneration.Named}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  (evidence : Dynamic.EvidenceEnvironment)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source named))
  (covers : evidence.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source named))
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (sameEvidence : CallerEvidence callerEvidence evidence)

local notation "bridge" => Origin.bridge (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)) origin owner
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "calls" => RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
  callerEvidence (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (CallableIndexedNamedGeneration.context compiled.indexed named)
  (CallableIndexedNamedGeneration.source named) context certificate

include wellFormed accepted nativeMember seed sameOwner complete staticChildren runtime covers unique sameEvidence in
/-- The same real named call leaf preserves the original caller protocol and
returned pool. Profiles are constructed from finite issuer-aligned children. -/
theorem preserves_calls (idsUnique : RequirementIdsUnique context)
    (budget size : Nat) (within : size ≤ budget)
    (children : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence (CallableIndexedNamedGeneration.source named) certificate faults))
    (bodies : ∀ header, header ∈ (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) → SourceFlows (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)) (keys := keys)
      (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence
      (CallableIndexedNamedGeneration.source named) calls faults size := by
  cases sameOwner
  obtain ⟨issuedProfiles⟩ := profiles (wellFormed := wellFormed) (inputs := inputs) (rows := rows)
    (accepted := accepted) (nativeMember := nativeMember) (functions := functions)
    (seed := seed) (complete := complete) (staticChildren := staticChildren)
  have original := CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds.preserves_calls
    (functions := functions) (faults := faults) (owner := seed.owner) (captureZero := seed.capture_zero)
    (compilation := CallableIndexedNamedGeneration.context compiled.indexed named)
    (source := CallableIndexedNamedGeneration.source named) (context := context) (certificate := certificate)
    (globals := fun header member => seed.globals member) evidence
    (CallableIndexedOwnedPreparedOriginGlobalsCarriers.carrier (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)) origin seed.owner)
    wellFormed runtime covers unique idsUnique (layouts (rows := rows))
    (syntaxTree (rows := rows) (staticChildren := staticChildren))
    issuedProfiles
    wellFormed.function_ids callerEvidence sameEvidence budget size within
  cases origin <;> exact @original children bodies

include wellFormed accepted nativeMember seed sameOwner complete staticChildren runtime covers unique sameEvidence in
/-- Reflection keeps the independent Source grade returned by the actual typed
finish and restores the original complete caller packet. -/
theorem reflects_calls (budget size : Nat) (within : size ≤ budget)
    (children : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence (CallableIndexedNamedGeneration.source named) certificate faults))
    (bodies : ∀ header, header ∈ (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) → NativeFlows (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)) (keys := keys)
      (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence
      (CallableIndexedNamedGeneration.source named) calls faults size := by
  cases sameOwner
  obtain ⟨issuedProfiles⟩ := profiles (wellFormed := wellFormed) (inputs := inputs) (rows := rows)
    (accepted := accepted) (nativeMember := nativeMember) (functions := functions)
    (seed := seed) (complete := complete) (staticChildren := staticChildren)
  have original := CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds.reflects_calls
    (functions := functions) (faults := faults) (owner := seed.owner) (captureZero := seed.capture_zero)
    (compilation := CallableIndexedNamedGeneration.context compiled.indexed named)
    (source := CallableIndexedNamedGeneration.source named) (context := context) (certificate := certificate)
    (globals := fun header member => seed.globals member) evidence
    (CallableIndexedOwnedPreparedOriginGlobalsCarriers.carrier (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)) origin seed.owner)
    wellFormed runtime covers unique (layouts (rows := rows))
    (syntaxTree (rows := rows) (staticChildren := staticChildren))
    issuedProfiles
    callerEvidence sameEvidence budget size within
  cases origin <;> exact @original children bodies

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedOriginNamedCallBounds

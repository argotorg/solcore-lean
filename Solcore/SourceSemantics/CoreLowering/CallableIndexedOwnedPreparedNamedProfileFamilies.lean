import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogNamedBodyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBootstrapReceipts

/-! A selected finite row and positive bootstrap owner construct the named
profile family at actual parameter entries. Each request runs the enclosing
native collector on that entry and retains its original diagnostic issuer.
The continuations consume the resulting family internally. Strict body flow
remains an induction hypothesis; no static input contains a body execution law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedProfileFamilies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Header)
open CallableIndexedOwnedPreparedCatalogNamedBodyContinuations (Profile FlowPreserves FlowReflects)
open CallableIndexedOwnedNamedBootstrapReceipts (NamedOwner)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {input : Input compiled}
  (packet : Issued input)
  {headers : List (Header compiled)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
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
  (children : ∀ administrative, CallableIndexedOwnedPreparedDirectNamedProfileExtraction.Children
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (header := packet.header) (administrative := administrative))

include accepted nativeMember complete wellFormed children in
/-- Construct the same rich profile from the real parameter entry. The zero
capture prefix is proved by the retained bootstrap token and key embedding. -/
theorem profiles :
    Nonempty (CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := headers) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions origin.owner (header := packet.header)) := by
  refine ⟨?_⟩
  intro arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost entry
  have captureZero := origin.capture_zero
  rw [captureZero] at entry
  exact Classical.choice (CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles.extract_at
    packet accepted nativeMember functions origin.owner complete entry wellFormed (children administrative))

variable (member : packet.header ∈ headers)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : CallableIndexedOwnedFunctionState.State headers keys
    ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value}
  (beforeTyped : Dynamic.HeapWellTyped packet.header.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes packet.header.function.context before arguments packet.header.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include accepted nativeMember complete wellFormed children member beforeTyped argumentsTyped stable in
/-- Source continuation has no externally supplied profile family, capture
equality, global size, or Source body syntax. The actual collector supplies the
family and its local static children supply the syntax. -/
theorem source_continuation (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) packet.header administrative),
      FlowPreserves (registry := registry) (faults := faults) (headers := headers)
        functions origin.owner profile child)) :
    CallableIndexedOwnedInvocationBounds.SourceContinuation
      (functions := functions) (registry := registry) (faults := faults)
      (header := packet.header) (arguments := arguments) origin.owner caller
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := origin.owner.key.locations) (capturePrefix := origin.owner.key.capturePrefix)
        functions registry packet.header) budget := by
  obtain ⟨issuedProfiles⟩ := profiles packet accepted nativeMember functions origin complete wellFormed children
  exact CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.source_continuation
    functions origin.owner origin.capture_zero (origin.globals member) caller
    beforeTyped argumentsTyped stable wellFormed
    issuedProfiles
    (children []).syntaxTree budget below

include accepted nativeMember complete wellFormed children member beforeTyped argumentsTyped stable in
/-- Reflection retains strict native flow grades and the independent Source
grade returned by the original typed finish at that same parameter entry. -/
theorem native_continuation (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) packet.header administrative),
      FlowReflects (registry := registry) (faults := faults) (headers := headers)
        functions origin.owner profile child)) :
    CallableIndexedOwnedInvocationBounds.NativeContinuation
      (functions := functions) (registry := registry) (faults := faults)
      (header := packet.header) (arguments := arguments) origin.owner caller
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := origin.owner.key.locations) (capturePrefix := origin.owner.key.capturePrefix)
        functions registry packet.header) budget := by
  obtain ⟨issuedProfiles⟩ := profiles packet accepted nativeMember functions origin complete wellFormed children
  exact CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.native_continuation
    functions origin.owner origin.capture_zero (origin.globals member) caller
    beforeTyped argumentsTyped stable wellFormed
    issuedProfiles
    (children []).syntaxTree budget below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedProfileFamilies

import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInvocationBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMatchProfiles
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds

/-! The actual catalog parameter entry supplies the source heap/environment,
renaming, typed native environment and protected frame observations to function
finish. Static profiles are indexed by that entry's real administrative context.
Flow meaning remains a separate pointwise input for later mutual induction;
these adapters do not close all catalog bodies or change static profile fields. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogBodyFinishBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations}
  {capturePrefix : Nat} {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat} {expressionSyntax : ExpressionId → Prop}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (escapedFault : faults .controlEscapedFunction header.escaped)

include escapedFault

/-- The same source cost reaches the actual finish. Every administrative and
frame fact comes from the retained marked parameter entry. -/
theorem state_preserves_at_for (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P) (validity : SourceSemantics.Context → Prop)
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : MatchProfileWith validity certificates diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAtFor
      (entry := P) functions program header.function.evidence validity
      (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
      (frameLayout := prepared.layout.frame) (globals := header.globals)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      true header.function.body header.function.resultType header.output profile.flow)
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (entryP : P (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entry.mapping entry.world entry.heap entry.store entry.canonical)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      P
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical := by
  have reference : entry.canonical[(header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + header.globals]? =
      some (.cellRef prepared.layout.frame.type frameLocation) := by
    simpa only [List.length_map, List.length_reverse] using entry.reference
  have unmapped : frameLocation ∉ entry.mapping := by
    exact Eq.mp (congrArg (fun location => location ∉ entry.mapping) entry.catalog_frame) entry.catalog.authority.unmapped
  exact RecursiveNamedFunctionFinishBounds.preserves_at_with functions program profile.accepted profile.generated profile.tree
    profile.projection header.unique escapedFault transport validity size meaning profile.initialValid
    entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped reference entry.state.read unmapped entryP trace

theorem state_preserves_at_with (validity : SourceSemantics.Context → Prop)
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : MatchProfileWith validity certificates diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAtFor
      (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence validity
      (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
      (frameLayout := prepared.layout.frame) (globals := header.globals)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      true header.function.body header.function.resultType header.output profile.flow)
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      protectedEntry headers locations capturePrefix (capturePrefix + 1)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical :=
  state_preserves_at_for functions escapedFault _ entry_transport validity profile size meaning entry ⟨entry.catalog⟩ trace

/-- Finish reflection selects its strict child from the original native
witness. The resulting source cost remains independent. -/
theorem state_reflects_at_for (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P) (validity : SourceSemantics.Context → Prop)
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : MatchProfileWith validity certificates diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAtFor
        (entry := P) functions program header.function.evidence validity
        (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
        (frameLayout := prepared.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        true header.function.body header.function.resultType header.output profile.flow))
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (entryP : P (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entry.mapping entry.world entry.heap entry.store entry.canonical)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      P
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical := by
  have reference : entry.canonical[(header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + header.globals]? =
      some (.cellRef prepared.layout.frame.type frameLocation) := by
    simpa only [List.length_map, List.length_reverse] using entry.reference
  have unmapped : frameLocation ∉ entry.mapping := by
    exact Eq.mp (congrArg (fun location => location ∉ entry.mapping) entry.catalog_frame) entry.catalog.authority.unmapped
  exact RecursiveNamedFunctionFinishBounds.reflects_at_with functions program profile.accepted profile.generated profile.tree
    profile.projection header.unique escapedFault transport validity budget size within meaning profile.initialValid
    entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped reference entry.state.read unmapped entryP completed

theorem state_reflects_at_with (validity : SourceSemantics.Context → Prop)
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : MatchProfileWith validity certificates diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAtFor
        (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence validity
        (source := header.function.source) (context := header.context) (registry := registry) (faults := faults)
        (frameLayout := prepared.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        true header.function.body header.function.resultType header.output profile.flow))
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      protectedEntry headers locations capturePrefix (capturePrefix + 1)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical :=
  state_reflects_at_for functions escapedFault _ entry_transport validity profile budget size within meaning entry ⟨entry.catalog⟩ completed

/-- The same source cost reaches the actual finish. Every administrative and
frame fact comes from the retained marked parameter entry. -/
theorem state_preserves_at_match
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : MatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAt
      (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
      (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
      (frameLayout := prepared.layout.frame) (globals := header.globals)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      true header.function.body header.function.resultType header.output profile.flow)
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      protectedEntry headers locations capturePrefix (capturePrefix + 1)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical := by
  exact state_preserves_at_with functions escapedFault
    (fun context => CompatibleExpressionLiterals.ContextValid header.solved context header.function.evidence)
    profile.toMatchProfileWith size meaning entry trace

/-- Finish reflection selects its strict child from the original native
witness. The resulting source cost remains independent. -/
theorem state_reflects_at_match
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : MatchProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAt
        (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
        (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
        (frameLayout := prepared.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        true header.function.body header.function.resultType header.output profile.flow))
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      protectedEntry headers locations capturePrefix (capturePrefix + 1)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical := by
  exact state_reflects_at_with functions escapedFault
    (fun context => CompatibleExpressionLiterals.ContextValid header.solved context header.function.evidence)
    profile.toMatchProfileWith budget size within meaning entry completed

theorem state_preserves_at
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAt
      (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
      (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
      (frameLayout := prepared.layout.frame) (globals := header.globals)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      true header.function.body header.function.resultType header.output profile.flow)
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyTrace program size header.function header.context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      protectedEntry headers locations capturePrefix (capturePrefix + 1)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical := by
  exact state_preserves_at_match functions escapedFault profile.to_match size meaning entry trace

theorem state_reflects_at
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
    (profile : ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAt
        (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
        (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
        (frameLayout := prepared.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        true header.function.body header.function.resultType header.output profile.flow))
    (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size entry.actualBody entry.store (header.body.rename entry.embedding) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize header.function header.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) program header.function
        header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome ∧
      protectedEntry headers locations capturePrefix (capturePrefix + 1)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after finalStore entry.canonical := by
  exact state_reflects_at_match functions escapedFault profile.to_match budget size within meaning entry completed

/-- Each real parameter entry chooses its own static administrative profile;
no fixed context is cast to an arbitrary typed capture. -/
theorem body_preserves_at
    (profiles : ∀ administrative, ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (size : Nat)
    (meaning : ∀ administrative, RecursiveNamedLoopContracts.PreservesAt
      (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
      (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
      (frameLayout := prepared.layout.frame) (globals := header.globals)
      (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      true header.function.body header.function.resultType header.output (profiles administrative).flow) :
    BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, completed, related, heaps, maps, worlds, frame, metadata, _, _⟩ :=
    state_preserves_at functions escapedFault (profiles administrative) size (meaning administrative) entry trace
  exact ⟨value, finalStore, finalMap, finalWorld, completed, related, heaps, maps, worlds, frame, metadata⟩

/-- The same outer budget is retained for every captured administrative
context; only the actual finish subderivation selects a smaller obligation. -/
theorem body_reflects_at
    (profiles : ∀ administrative, ProfileFor diagnosticPolicy headers header compilation expressionFuel expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (budget size : Nat) (within : size ≤ budget)
    (meaning : ∀ administrative, RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAt
        (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
        (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
        (frameLayout := prepared.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        true header.function.body header.function.resultType header.output (profiles administrative).flow)) :
    BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, _, _⟩ :=
    state_reflects_at functions escapedFault (profiles administrative) budget size within (meaning administrative) entry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogBodyFinishBounds

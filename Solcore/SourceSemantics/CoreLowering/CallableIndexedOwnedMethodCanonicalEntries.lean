import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyCanonicalEntries

/-! The actual installed method capture and real ordered parameter spine
supply canonical slots at the original body entry. Only the slot proof wrapper
is forgotten at the same actual returned pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCanonicalEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedExpressionHeads CallableIndexedOwnedMethodInvocationBounds
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

variable {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Expr} (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor generation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) sourceBody dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction generation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed generation (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := sourceBody) (administrative := administrative)
    functions mapping world before store callerEnvironment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

variable (callerPrefix : Nat)
  (observed : Globals (headers := headers) owner callerPrefix [] installed.canonical)

include observed in
/-- The argument bundle occupies one administrative slot. Actual ordered
parameter additions account for every remaining slot shift. -/
theorem globals_after_prefix {canonical : Environment} (added : Environment)
    (length : added.length = named.inputs.length)
    (spine : canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical) :
    Globals (headers := headers) owner (callerPrefix + 1)
      (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) canonical := by
  intro header member
  rw [spine]
  simp only [List.length_map, List.length_reverse]
  have index : named.inputs.length + (callerPrefix + 1) + header.slot =
      added.length + (callerPrefix + header.slot + 1) := by omega
  rw [index, List.getElem?_append_right (by omega)]
  have slot : callerPrefix + header.slot + 1 = Nat.succ (callerPrefix + header.slot) := by omega
  simp only [Nat.add_sub_cancel_left]
  rw [slot, Nat.succ_eq_add_one, List.getElem?_cons_succ]
  simpa using observed header member

include observed in
/-- Every dynamic field and the reached pool come from the actual source parameter receipt. -/
def source_entry {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body)
    (added : Environment) (length : added.length = named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (gate : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    CallableRuntimeBodyOrigins.Stateful.Entry (argumentProtocol (headers := headers) owner (callerPrefix + 1))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin generation profile escaped extend runtimeOf) functions :=
  CallableIndexedOwnedBodyCanonicalEntries.wrap functions owner (callerPrefix + 1)
    (parameter_entry_origin generation profile functions escaped extend runtimeOf entry reached gate)
    (globals_after_prefix (generation := generation) (functions := functions)
      (installed := installed) (owner := owner) (callerPrefix := callerPrefix)
      (observed := observed) (added := added) (length := length) (spine := spine))

/-- The shared strict family is requested only at this authentic parameter
entry; its underlying actual pool is returned verbatim. -/
theorem source_continuation_of_canonical (budget : Nat)
    (meaning : ∀ {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
      (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body)
      (added : Environment) (length : added.length = named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (gate : CallableIndexedOwnedAllocationProducer.StableOwner keys location native),
      Below budget (CallableRuntimeBodyEntryContracts.PreservesAt
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := argumentProtocol (headers := headers) owner (callerPrefix + 1))
        (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
        functions program (source_entry (generation := generation) (profile := profile) (functions := functions)
        (escaped := escaped) (extend := extend) (runtimeOf := runtimeOf) (installed := installed)
        (owner := owner) (callerPrefix := callerPrefix) (observed := observed)
        (entry := entry) (added := added) (length := length) (spine := spine) (reached := reached) (gate := gate)))) :
    SourceContinuation (program := program) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads)
      generation profile functions escaped extend runtimeOf installed budget := by
  intro initialStore location native actualContext actual ξ entry added length spine reached gate child strict
  exact CallableIndexedOwnedBodyCanonicalEntries.preserves_of_canonical functions owner (callerPrefix + 1)
    (parameter_entry_origin generation profile functions escaped extend runtimeOf entry reached gate)
    _ (meaning entry added length spine reached gate child strict)

include observed in
/-- Every dynamic field and the reached pool come from the actual native parameter receipt. -/
def native_entry {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {size : Nat} {value : Value} {finalStore : Store}
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body size value finalStore)
    (added : Environment) (length : added.length = named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (gate : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    CallableRuntimeBodyOrigins.Stateful.Entry (argumentProtocol (headers := headers) owner (callerPrefix + 1))
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) (origin generation profile escaped extend runtimeOf) functions :=
  CallableIndexedOwnedBodyCanonicalEntries.wrap functions owner (callerPrefix + 1)
    (prefix_entry_origin generation profile functions escaped extend runtimeOf entry reached gate)
    (globals_after_prefix (generation := generation) (functions := functions)
      (installed := installed) (owner := owner) (callerPrefix := callerPrefix)
      (observed := observed) (added := added) (length := length) (spine := spine))

/-- The shared strict family is requested only at this authentic parameter
entry; its underlying actual pool is returned verbatim. -/
theorem native_continuation_of_canonical (budget : Nat)
    (meaning : ∀ {initialStore : Store} {location : Location} {native : NativeFrame}
    {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {size : Nat} {value : Value} {finalStore : Store}
      (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      location native (.initial compiled.compatible.checked) functions registry
      (methodFunction generation sourceBody dictionary) profile.context named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ generation.parameterCode generation.body size value finalStore)
      (added : Environment) (length : added.length = named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (gate : CallableIndexedOwnedAllocationProducer.StableOwner keys location native),
      Below budget (CallableRuntimeBodyEntryContracts.ReflectsAt
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (protocol := argumentProtocol (headers := headers) owner (callerPrefix + 1))
        (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
        functions program (native_entry (generation := generation) (profile := profile) (functions := functions)
        (escaped := escaped) (extend := extend) (runtimeOf := runtimeOf) (installed := installed)
        (owner := owner) (callerPrefix := callerPrefix) (observed := observed)
        (entry := entry) (added := added) (length := length) (spine := spine) (reached := reached) (gate := gate)))) :
    NativeContinuation (program := program) (headers := headers) (keys := keys)
      (arguments := arguments) (payloads := payloads)
      generation profile functions escaped extend runtimeOf installed budget := by
  intro initialStore location native actualContext actual ξ size value finalStore entry added length spine reached gate child strict
  exact CallableIndexedOwnedBodyCanonicalEntries.reflects_of_canonical functions owner (callerPrefix + 1)
    (prefix_entry_origin generation profile functions escaped extend runtimeOf entry reached gate)
    _ (meaning entry added length spine reached gate child strict)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCanonicalEntries

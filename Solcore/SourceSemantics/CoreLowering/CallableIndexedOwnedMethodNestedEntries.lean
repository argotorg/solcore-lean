import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOriginCanonicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipal
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodCanonicalEntries

/-! Authentic method selectors retain an independent raw Source body and
complete dictionary. Their emitted compiler seed and real parameter prefix
supply the origin packet at the same actual reached pool, without a Header. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodNestedEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedExpressionHeads CallableIndexedOwnedMethodInvocationBounds
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : CallablePreparedMethodCatalogHookMeaning.ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (escaped : faults .controlEscapedFunction principal.cached.compilation.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed principal.cached.compilation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := principal.sourceBody)
    (administrative := administrative) functions mapping world before store callerEnvironment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (observed : Globals (headers := headers) owner 0 [] installed.canonical)
  {originId : Word} {native : NativeFrame} {metadata : MetadataState}
  (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? (.named principal.named.signature.key) = some originId)
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    native (.named originId) (some metadata))

include profile observed selected history in
/-- The real Source parameter spine supplies canonical globals, bundle tag and
physical frame read; the reached row authenticates its own full Source seed. -/
theorem source_packet {initialStore : Store} {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation native (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedOriginCanonicalState.Packet owner principal.named _ reached := by
  apply CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner principal.named reached
  · exact ⟨CallableIndexedOwnedMethodCanonicalEntries.globals_after_prefix
      (generation := principal.cached.compilation) (functions := functions) (installed := installed)
      (owner := owner) (callerPrefix := 0) (observed := observed) added length spine, entry.reference⟩
  · exact entry.environments
  · simpa only [List.getElem?_cons_zero] using congrArg some profile.parameterType.symm
  · exact principal.history_source selected history
  · exact entry.read

include profile observed selected history in
/-- Native parameters retain their own measured prefix and exact reached pool. -/
theorem native_packet {initialStore : Store} {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {size : Nat} {value : Value} {finalStore : Store}
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation native (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body size value finalStore)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableIndexedOwnedOriginCanonicalState.Packet owner principal.named _ reached := by
  apply CallableIndexedOwnedOriginCanonicalState.packet_of_stable_read owner principal.named reached
  · exact ⟨CallableIndexedOwnedMethodCanonicalEntries.globals_after_prefix
      (generation := principal.cached.compilation) (functions := functions) (installed := installed)
      (owner := owner) (callerPrefix := 0) (observed := observed) added length spine, entry.reference⟩
  · exact entry.environments
  · simpa only [List.getElem?_cons_zero] using congrArg some profile.parameterType.symm
  · exact principal.history_source selected history
  · exact entry.read

include observed selected history in
/-- Every actual Source field and the same reached pool enter the generic
principal protocol. The independent method Source profile is preserved verbatim. -/
def source_entry {initialStore : Store} {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    (entry : ParameterEntry compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation native (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin principal.cached.compilation profile escaped extend runtimeOf) functions :=
  { parameter_entry_origin principal.cached.compilation profile functions escaped extend runtimeOf entry reached
      ⟨owner.position, _, _, rfl, principal.history_source selected history⟩ with
    initial := ⟨reached, source_packet principal profile functions installed owner observed selected history entry added length spine reached⟩ }

include observed selected history in
/-- Native entry fields retain the original source dictionary, actual prefix
continuation and reached pool; only the proven principal packet is added. -/
def native_entry {initialStore : Store} {actualContext : Core.Context} {actual : Environment} {ξ : Renaming}
    {size : Nat} {value : Value} {finalStore : Store}
    (entry : Prefix compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      owner.key.frameLocation native (.initial compiled.compatible.checked) functions registry
      principal.sourceFunction profile.context principal.named.inputs arguments before initialStore mapping world
      administrative actualContext actual ξ principal.cached.compilation.parameterCode principal.cached.compilation.body size value finalStore)
    (added : Environment) (length : added.length = principal.named.inputs.length)
    (spine : entry.canonical = added ++ DataPatternValues.packValues payloads :: installed.canonical)
    (reached : State headers keys ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩) :
    CallableRuntimeBodyOrigins.Stateful.Entry
      (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (origin principal.cached.compilation profile escaped extend runtimeOf) functions :=
  { prefix_entry_origin principal.cached.compilation profile functions escaped extend runtimeOf entry reached
      ⟨owner.position, _, _, rfl, principal.history_source selected history⟩ with
    initial := ⟨reached, native_packet principal profile functions installed owner observed selected history entry added length spine reached⟩ }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodNestedEntries

import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogEntries
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyKernel

/-! The actual method prefix supplies the original native body child and the
complete catalog at that same state. The shared kernel reflects that child at
its original dictionary. Body effects then restore the caller's full catalog,
including unused captures and snapshots. The expression premises are internal
bounded induction interfaces; no body execution law or evidence reindexing is
introduced here. Source and native grades remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallablePreparedMethodRuntimeMeaning
open CallablePreparedMethodCatalogEntries

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}
  {named : SourceCoreGeneralFunctions.Function} {sourceBody : Dynamic.BodyInstance} {function : Dynamic.Closure}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {bindings : List CallableIndexedParameterCertificates.Binding}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
  {parameterCode body : Expr} {size : Nat} {result : Value} {bodyStore : Store}
  {location : Location} {next current : NativeFrame} {currentGhost : GhostFrame}
  (reached : Prefix prepared.layout.frame base.globals.length location next values functions registry function context bindings
    arguments before (store.set location (encode prepared.layout.frame next)) mapping world administrative actualContext
    actual ξ parameterCode body size result bodyStore)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)
  {added : Environment} (length : added.length = bindings.length)
  (spine : reached.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical)
  {origin : Word} {metadata : MetadataState}
  (owned : prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
  (history : Carries prepared.graph.inputs prepared.graph.table next (.named origin) (some metadata))
  (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)
  (sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named)

section Reflection
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {solved : List SolvedRequirement} {output : Ty} {fellThrough escaped : Word}
  {faults : FunctionCalls.FaultRep}
  (kernel : CallableRuntimeBodyKernel.BodyFor layouts owner active prepared.layout.frame base.globals.length onError
    values function expressionSyntax certificates validity diagnosticPolicy ambient
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) context
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) output body fellThrough escaped registry faults)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : prepared.layout.frame.Registered ambient.definitions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) (escapedFault : faults .controlEscapedFunction escaped)
  (extend : ∀ {context next binder}, validity context → BinderExtends function.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context → CompatibleRuntimeContextValidity.Valid solved context function.evidence)

include initial sameFrame length spine owned history sourceFrame sameSource kernel definitions registered extension
  faithful observations functionTypes escapedFault extend runtimeOf in
/-- Reflect the exact body child extracted from the original hook. The strict
bound is supplied by that hook, even for an empty parameter list. The source
trace, reached method entry, full heap and restored caller catalog are returned
from one kernel invocation and the existing restore proof. -/
theorem reflects_prefix_sized (budget : Nat) (strict : reached.childSize < budget)
    (expressions : ∀ context, validity context → RecursiveNamedBoundedContracts.Below budget
      (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence function.source
        (certificates context) faults (protectedEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1))))
    (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function context reached.environment reached.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after bodyStore ∧
      LocationMap.Extends reached.mapping finalMap ∧ WorldExtends reached.world finalWorld ∧
      AdministrativePreserved reached.mapping reached.store finalMap bodyStore ∧ Dynamic.HeapMetadataExtend reached.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) reached.environment reached.heap after outcome ∧
      Nonempty (SourceEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1)
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after bodyStore reached.canonical) ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after
        (bodyStore.set location (encode prepared.layout.frame current)) ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after
        (bodyStore.set location (encode prepared.layout.frame current)) canonical) ∧
      AdministrativePreserved mapping store finalMap (bodyStore.set location (encode prepared.layout.frame current)) ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost
        (bodyStore.set location (encode prepared.layout.frame current)) ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧ Dynamic.HeapMetadataExtend before after := by
  let installed := source_entry reached initial sameFrame length spine owned history sourceFrame sameSource
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, reachedExit, retained⟩ :=
    kernel.reflects_sized functions definitions registered extension program faithful observations functionTypes escapedFault
      (transport (named := named) (sourceBody := sourceBody) (function := function))
      (binds (named := named) (sourceBody := sourceBody) (function := function)) extend runtimeOf
      budget reached.childSize (Nat.le_of_lt strict) expressions reached.environments reached.heaps reached.locals
      reached.lookups reached.actualTyped reached.reference reached.read reached.unmapped ⟨installed⟩ reached.completed
  obtain ⟨restoredHeaps, restoredCatalog, restoredFrame, restoredCaller⟩ :=
    restore_catalog reached initial sameFrame caller registered heaps maps worlds frame metadata
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata,
    reachedExit, retained, restoredHeaps, restoredCatalog, restoredFrame, restoredCaller,
    reached.maps.trans maps, reached.worlds.trans worlds, reached.metadata.trans metadata⟩

end Reflection
end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogBodyMeaning

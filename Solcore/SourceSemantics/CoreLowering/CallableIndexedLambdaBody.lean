import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaPrefix
import Solcore.SourceSemantics.CoreLowering.BuiltinNamedBodyMeaning

/-! A concrete lexical builtin statement tree discharges the body after the
actual lambda parameter fold. Both directions preserve the original captures,
source allocation order and every retained native temporary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
  {scope : Scope} {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
  (program : Program)
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {bindings : List Binding} {output : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming}

include definitions registered extension contextValid unique uninitialized missing faithful functionLeaves functionTypes in
/-- Finite source body execution completes the actual parameter prefix. The
source allocation is the one retained by the constructed entry. -/
theorem preserves
    (entry : CallableIndexedLambdaPrefix.Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (certificate : BuiltinNamedBody.Certificate layouts owner active layout globals onError readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : FunctionCallBody.Trace program function context entry.environment entry.heap outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (parameterCode.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        administrative program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) entry.environment entry.heap after outcome := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, reached⟩ :=
    certificate.preserves functions extension definitions registered program contextValid unique uninitialized missing faithful functionLeaves functionTypes entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped trace
  exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, represented, heaps,
    entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata, reached⟩

include definitions registered extension contextValid unique uninitialized missing faithful functionLeaves functionTypes in
/-- Completed native prefix execution constructs the independent source trace
at the installed call context, without a universal body reflection premise. -/
theorem reflects
    (entry : CallableIndexedLambdaPrefix.Entry layout globals contextLocation native values functions registry function context scope bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body)
    (certificate : BuiltinNamedBody.Certificate layouts owner active layout globals onError readFuel values function.source context solved reasonAt
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) function.body function.resultType output
      policy fuel fellThrough escaped body)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates actual store (parameterCode.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        administrative program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) entry.environment entry.heap after outcome := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, reached⟩ :=
    certificate.reflects functions extension definitions registered program contextValid unique uninitialized missing faithful functionLeaves functionTypes entry.environments entry.heaps
      entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped (entry.agreement.unwrap evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, entry.maps.trans maps,
    entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans metadata, reached⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaBody

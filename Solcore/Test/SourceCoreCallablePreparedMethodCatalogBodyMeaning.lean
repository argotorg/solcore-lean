import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogBodyMeaning

/-! Concrete builtin certificates close the method bridge without an external
body execution law. The original strict prefix child and the arbitrary complete
catalog are retained. This formal test adds no runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodCatalogBodyMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallablePreparedMethodRuntimeMeaning
open CallablePreparedMethodCatalogEntries CallablePreparedMethodCatalogBodyMeaning

abbrev actual_hook := @hook_catalog_entry
abbrev finite_body := @reflects_prefix_sized

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program}
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

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {expressionSyntax : ExpressionId → Prop} {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {output : Ty} {fellThrough escaped : Word} {faults : FunctionCalls.FaultRep}
  (profile : CallablePreparedMethodRuntimeMeaning.Body layouts owner active prepared.layout.frame base.globals.length onError
    values function expressionSyntax readFuel solved reasonAt ambient
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) context
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) output body fellThrough escaped registry faults)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : prepared.layout.frame.Registered ambient.definitions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (escapedFault : faults .controlEscapedFunction escaped)

include initial sameFrame length spine owned history sourceFrame sameSource profile definitions registered extension
  faithful observations functionTypes uninitialized missing escapedFault in
/-- The expression induction interface is closed by concrete static leaves;
there is no body meaning premise in this test. -/
theorem closed_builtin_prefix (budget : Nat) (strict : reached.childSize < budget)
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
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid solved context function.evidence →
      RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence function.source
        (CompatibleExpressionBuiltinRuntime.Certificate readFuel values function.source context solved reasonAt) faults
        (protectedEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1))) := by
    intro context valid
    exact RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed _
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes
          program function.evidence valid.ledger valid.runtime uninitialized missing)) budget
  exact reflects_prefix_sized reached initial sameFrame length spine owned history sourceFrame sameSource
    profile.toKernel definitions registered extension faithful observations functionTypes escapedFault
    (fun valid extended => valid.extend extended) (fun valid => valid) budget strict expressions caller

#check_failure CallableRuntimeBodyKernel.BodyFor.with_evidence

end Tests.SourceCoreCallablePreparedMethodCatalogBodyMeaning

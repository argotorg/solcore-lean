import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogBodyMeaning
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogHookMeaning
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodOriginMeaning
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedOperatorCorpus
import Solcore.Test.SourceSemantics.CoreLowering.Callable.Coercion
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogEntries
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSourceHookMeaning
import Solcore.SourceSemantics.CoreLowering.BuiltinNamedCallMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceBounds
import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceMeaning
import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSuffixMeaning

/-!
# Prepared callable tests

Prepared methods and operators.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePreparedMethodCatalogBodyMeaning
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePreparedMethodCatalogHookMeaning
/-! The actual compiled hook is consumed with concrete builtin certificates.
The formal consumer keeps its complete caller state and independent source
outcome, and takes no body or expression execution law. No new runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodCatalogHookMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates
open CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries
open CallablePreparedMethodCatalogHookMeaning

abbrev original_hook := @reflects_hook_sized
abbrev generic_compiled := @ProfileFor.reflects_sized

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable (profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary
    administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) ((diagnostics.reasonAt named.signature.key) id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((diagnostics.reasonAt named.signature.key) id).add tag))

include profile extension faithful observations functionTypes escaped uninitialized missing in
theorem closed_builtin_compiled {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {size : Nat} {value : Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (compiled.output.rename installed.embedding.lift) value finalStore) :
    ∃ sourceSize environment bound outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize (methodFunction compiled sourceBody dictionary)
        profile.context environment bound outcome after ∧
      CallableCoercionMethodFrame.BodyOutcome program sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) program
        (methodFunction compiled sourceBody dictionary) profile.context
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after finalStore installed.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary →
      RecursiveNamedBoundedContracts.Below size (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context dictionary sourceBody.source
        (CompatibleExpressionBuiltinRuntime.Certificate profile.readFuel values sourceBody.source context
          named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key)) faults
        (protectedEntry named sourceBody (methodFunction compiled sourceBody dictionary)
          headers locations capturePrefix (callerPrefix + 1))) := by
    intro context valid
    exact RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed _
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes
          program dictionary valid.ledger valid.runtime uninitialized missing)) size
  exact ProfileFor.reflects_sized compiled (of_builtin compiled profile) functions extension
    faithful observations functionTypes escaped (fun valid extended => valid.extend extended) (fun valid => valid)
    installed initial sameFrame represented heaps expressions completed

/-- The generic receipt preserves the actual compilation output and full dictionary. -/
theorem builtin_dictionary : (of_builtin compiled profile).body.initialValid = profile.body.valid := rfl

include profile in
/-- A zero-arity hook still has its actual pack slot; no strict grade is inferred from arity. -/
theorem empty_parameter_pack (empty : named.inputs = []) : named.signature.parameterType = .unit := by
  simpa only [empty, List.map_nil, SourceCoreCompatibleCatalog.packTypes] using profile.parameterType

-- No dictionary-only reindexing operation is exposed for a generic certificate family.
#check_failure CallablePreparedMethodCatalogHookMeaning.ProfileFor.with_evidence

end Tests.SourceCoreCallablePreparedMethodCatalogHookMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePreparedMethodOriginMeaning
/-! The actual compiled hook is consumed with concrete builtin certificates.
The formal consumer keeps its complete caller state and independent source
outcome, and takes no body or expression execution law. No new runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodOriginMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates
open CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries
open CallablePreparedMethodCatalogHookMeaning

open CallablePreparedMethodOriginMeaning

abbrev original_hook := @CallablePreparedMethodOriginMeaning.ProfileFor.reflects_hook_of_below
abbrev actual_prefix := @CallablePreparedMethodOriginMeaning.entry_of_prefix
abbrev source_child := @CallablePreparedMethodOriginMeaning.ProfileFor.preserves_reached_of_below

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable (profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary
    administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) ((diagnostics.reasonAt named.signature.key) id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((diagnostics.reasonAt named.signature.key) id).add tag))


def builtinOrigin : CallableRuntimeBodyOrigins.Origin values ambient registry faults :=
  CallablePreparedMethodOriginMeaning.ProfileFor.origin
    (headers := headers) (locations := locations) (capturePrefix := capturePrefix) (callerPrefix := callerPrefix)
    compiled (of_builtin compiled profile) escaped (fun valid extended => valid.extend extended) (fun valid => valid)

include profile extension faithful observations functionTypes escaped uninitialized missing in
/-- Concrete builtin leaves internally close the source family at the original body grade. -/
theorem closed_builtin_source (size : Nat) : CallableRuntimeBodyOrigins.PreservesAt functions program
    (builtinOrigin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped) size := by
  apply CallableRuntimeBodyMutualMeaning.preserves_at
    (fun _ : Unit => builtinOrigin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped) functions extension program faithful observations ?_ size ()
  intro _ context valid budget child within _ scope id lowered
  exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
    (ProtectedExpressionMeaning.preserves_of_typed _
      (CompatibleExpressionBuiltinRuntime.preserves (fuel := profile.readFuel) functions extension faithful observations functionTypes
        program dictionary valid.ledger valid.runtime profile.body.unique uninitialized missing)) child
    (scope := scope) (id := id) (lowered := lowered)

include profile extension faithful observations functionTypes escaped uninitialized missing in
/-- The native family starts from its own completed body and returns an independent source grade. -/
theorem closed_builtin_native (size : Nat) : CallableRuntimeBodyOrigins.ReflectsAt functions program
    (builtinOrigin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped) size := by
  apply CallableRuntimeBodyMutualMeaning.reflects_at
    (fun _ : Unit => builtinOrigin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped) functions extension program faithful observations functionTypes ?_ size ()
  intro _ context valid budget child within _ scope id lowered
  exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
    (ProtectedExpressionMeaning.reflects_of_typed _
      (CompatibleExpressionBuiltinRuntime.reflects (fuel := profile.readFuel) functions extension faithful observations functionTypes
        program dictionary valid.ledger valid.runtime uninitialized missing)) child
    (scope := scope) (id := id) (lowered := lowered)

include profile extension faithful observations functionTypes escaped uninitialized missing in
theorem closed_builtin_compiled {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {size : Nat} {value : Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (compiled.output.rename installed.embedding.lift) value finalStore) :
    ∃ sourceSize environment bound outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize (methodFunction compiled sourceBody dictionary)
        profile.context environment bound outcome after ∧
      CallableCoercionMethodFrame.BodyOutcome program sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) program
        (methodFunction compiled sourceBody dictionary) profile.context
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after finalStore installed.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact CallablePreparedMethodOriginMeaning.ProfileFor.reflects_hook_of_below compiled (of_builtin compiled profile)
    functions escaped (fun valid extended => valid.extend extended) (fun valid => valid) size
    installed initial sameFrame represented heaps (Nat.le_refl size)
    (fun child _ => closed_builtin_native compiled profile functions extension faithful observations functionTypes
      escaped uninitialized missing child) completed

/-- The dictionary is exactly the one in the actual selected method profile. -/
theorem same_dictionary :
    (builtinOrigin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped).function.evidence = dictionary := rfl

/-- Full method provenance is protected, including the actual source frame and history. -/
theorem same_protected_entry :
    (builtinOrigin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped).protectedEntry =
      protectedEntry named sourceBody (methodFunction compiled sourceBody dictionary)
        headers locations capturePrefix (callerPrefix + 1) := rfl

include profile in
/-- Zero parameters retain the real packed slot. -/
theorem empty_pack (empty : named.inputs = []) : named.signature.parameterType = .unit := by
  simpa only [empty, List.map_nil, SourceCoreCompatibleCatalog.packTypes] using profile.parameterType

#check_failure CallablePreparedMethodOriginMeaning.ProfileFor.preserves_hook
#check_failure CallablePreparedMethodOriginMeaning.ProfileFor.with_evidence

end Tests.SourceCoreCallablePreparedMethodOriginMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePreparedMethodRuntimeProfileFactory
/-! Formal consumers retain actual selection, the same dictionary, cache and
returned diagnostic receipt. Existing operator suites supply the runtime checks. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodRuntimeProfileFactory
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload
open CallablePreparedMethodSelection CallableCoercionMethodInstantiation
open CallablePreparedMethodCatalogHookMeaning CallablePreparedMethodRuntimeProfileFactory

abbrev actual_source := @source_at
abbrev actual_parameters := @parameter_pack
abbrev actual_cached_body := @cached_body_native
abbrev actual_extraction := @extract_cached
abbrev good_profile := @profile_of_interpreted

section Formal
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  (source : SourceAt compilation values sourceBody dictionary)
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {administrative : Core.Context}
  (receipt : Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative))
  (catalog : SignatureCatalogWellFormed values.checked.signatures)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (interpreted : receipt.extracted.diagnostics registry faults)

include catalog definitions registered interpreted in
theorem actual_profile :
    ∃ profile : ProfileFor compilation values ambient sourceBody dictionary administrative registry faults
      expressionSyntax certificates
      (fun context => CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)
      diagnosticPolicy,
      profile.context = source.context ∧ profile.body.flow = receipt.flow ∧
      HEq profile.body.tree receipt.extracted.tree ∧
      HEq profile.body.initialValid source.valid ∧
      profile.parameters = source.parameters := by
  exact ⟨receipt.profile source catalog definitions registered interpreted, rfl, rfl, HEq.rfl, HEq.rfl, rfl⟩

theorem actual_source_frame :
    (receipt.profile source catalog definitions registered interpreted).sourceFrame = source.frame := rfl

theorem full_unused_ledger :
    (receipt.profile source catalog definitions registered interpreted).context.solvedRequirements =
      named.specialized.function.solvedRequirements := source.valid.ledger

include source in
theorem ordered_parameters :
    sourceBody.source.inputs.map (fun binder => (binder.id, binder.scheme, binder.comptime)) =
      named.inputs.map (fun binding => (binding.1.id, binding.1.scheme, binding.1.comptime)) := by
  rw [source.parameters]
  simp only [List.map_map, Function.comp_def]

/-- A receipt can carry an impossible interpretation while retaining the same Tree. -/
def blocked : Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) :=
  { receipt with extracted := {
      tree := receipt.extracted.tree
      diagnostics := fun _ _ => False
      materialize := fun _ _ impossible => impossible.elim } }

theorem blocked_same_tree : HEq (blocked source receipt).extracted.tree receipt.extracted.tree := HEq.rfl

theorem blocked_uninterpreted : ¬ (blocked source receipt).extracted.diagnostics registry faults := fun impossible => impossible

include receipt interpreted in
theorem good_is_not_all :
    (∃ result : Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative),
      result.extracted.diagnostics registry faults) ∧
    ¬ (∀ result : Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative),
      result.extracted.diagnostics registry faults) := by
  exact ⟨⟨receipt, interpreted⟩, fun every => blocked_uninterpreted source receipt (every _)⟩

end Formal

/-- Packing alone does not identify the source arity. -/
theorem pack_not_arity : SourceCoreCompatibleCatalog.packTypes [] =
    SourceCoreCompatibleCatalog.packTypes [.unit] ∧ ([] : List Core.Ty) ≠ [.unit] := ⟨rfl, by simp⟩

/-- Ordered duplicate evidence is retained; neither set equality nor length
is sufficient to identify the actual selected dictionary. -/
theorem dictionary_order {α : Type} (a b : α) (different : a ≠ b) :
    [a, a, b] ≠ [a, b, a] := by simp [different]

#check_failure CallablePreparedMethodCatalogHookMeaning.ProfileFor.with_evidence
#check_failure CallablePreparedMethodRuntimeProfileFactory.SourceAt.ordinary

end Tests.SourceCoreCallablePreparedMethodRuntimeProfileFactory
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePreparedMethodSelection
/-! Actual operator receipt tests. Static source judgments retain independent
formation and whole-program assumptions. Public runtime checks use the original
compiled source; marker callbacks below audit only the selected lowering shape. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreCallablePreparedMethodSelection
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallablePreparedMethodSelection
open CallableNamedMetadata (environment)
open CallableCoercionMethodInstantiation (Formation bodyInstance)
open SourceCompilerFeatureSupport

abbrev actual_unary := @CallablePreparedMethodSelection.unary_of_accepted
abbrev actual_binary := @CallablePreparedMethodSelection.binary_of_accepted
abbrev actual_lowering := @CallablePreparedMethodSelection.of_accepted

variable {program : CheckedProgram} {project : CallableCoercionExpressionCertificates.Projector}
  {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
  {child : SourceCoreEvidence.Child} {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Core.Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  {receipt : Operator program project caller compilation child fuel source scope id reasonAt policy node output}

/-- The same actual selector gives the source judgment and the existing method
body typing certificate, including runtime validity of its complete ledger. -/
theorem actual_source {loaded : LoadedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
    (selected : SourceReceipt receipt)
    (formed : Formation selected.certificate.selected.implementation selected.certificate.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures program.signatures) receipt.selection.method.specialized.parameterSubstitution)
    {context : SourceSemantics.Context} (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller receipt.selection.method)
    (programTyped : ProgramWellFormed (Program.ofChecked program)) :
    Dynamic.OperatorMethodSelected (Program.ofChecked program) context (environment receipt.available)
      selected.traitName selected.methodName receipt.requirements (bodyInstance program receipt.selection.method)
      (environment receipt.dictionary) ∧
    ∃ types lexicalContext facts,
      Dynamic.BodyInstanceTypingCertificate (Program.ofChecked program) (bodyInstance program receipt.selection.method)
        types lexicalContext facts ∧
      CompatibleRuntimeContextValidity.Valid (bodyInstance program receipt.selection.method).context.solvedRequirements
        lexicalContext (environment receipt.dictionary) := by
  have sourceSelected := selected.selects (CallableMethodBodyCoherence.of_loaded loadedAccepted) formed range signatures ledger assumptions covered
  exact ⟨sourceSelected, selected_typed sourceSelected programTyped⟩

abbrev actual_cache := @CallablePreparedMethodSelection.cached_row
abbrev actual_frame := @CallablePreparedMethodSelection.Cached.frame

theorem ordered_children (actual : Operator program project caller compilation child fuel source scope id reasonAt policy node output) :
    actual.arguments.mapM (fun id => child fuel source scope id reasonAt) = .ok actual.loweredArguments ∧
      SourceCoreEvidence.applyCoercions program project compilation caller actual.available scope node policy
        actual.operand node.coercions = .ok output :=
  ⟨actual.argumentsAccepted, actual.suffix.accepted⟩

theorem full_target (actual : Operator program project caller compilation child fuel source scope id reasonAt policy node output) :
    SourceCompilationPlan.exactSpecialization compilation.plan actual.key = .ok actual.target.specialized ∧
      compilation.globals.zipIdx.filter (fun row => decide (row.1.key = actual.key)) = [(actual.native.signature, actual.native.index)] :=
  ⟨actual.target.selected, actual.target.global⟩

/-- The actual staged guard allows marked methods under the enabled policy.
This static receipt does not assert that all methods are ordinary. -/
theorem staged_guard_allows (returnComptime : Bool) (parameters : List TypedBinder) :
    (!true && (returnComptime || parameters.any (·.comptime))) = false := rfl

theorem dictionary_order (first second : TypedTraitResolution.Evidence) (different : first ≠ second) :
    [first, second, first] ≠ [first, first, second] := by
  intro same
  exact different (List.cons.inj (List.cons.inj same).2).1.symm

abbrev range_stays_explicit := @SourceCoreCallableCoercionSourceSelection.ground_is_not_range
abbrev retained_parameter_order := @SourceCoreCallableCoercionSourceSelection.reversed_collector


/-- The actual preparation removes the former independent final-row premise.
Its staged boundary uses the emitter's exact argument order and full method. -/
theorem actual_prepared
    (actual : Operator program project caller compilation child fuel source scope id reasonAt policy node output)
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes) :
    actual.target.specialized = actual.selection.method.specialized ∧
      SourceCompilationPlan.validateStagedCallBoundary caller
        (CallableCoercionExpressionCertificates.rawNode node actual.requirements)
        actual.arguments actual.selection.method.specialized = .ok () := by
  obtain ⟨visit, requirements, selection, arguments, _, same⟩ := actual.prepared prepared callerMember nodeMember
  refine ⟨same, ?_⟩
  simpa only [CallableCoercionPreparationSteps.operatorOwnedNode, CallableCoercionExpressionCertificates.rawNode,
    requirements, selection, arguments] using visit.staged

abbrev actual_prepared_frame := @CallablePreparedMethodSelection.SourceReceipt.prepared_frame

private def content := String.intercalate "\n" [
  "trait Marker<T> {}", "trait Witness<T> {}",
  "impl<A, B> Marker<(A, B)> {}", "impl<A, B> Witness<(A, B)> {}",
  "trait Add<T> where T: Marker { function add(left: T, right: T) returns (T) where T: Witness; }",
  "trait BitNot<T> where T: Marker { function bnot(value: T) returns (T) where T: Witness; }",
  "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
  "impl<B, A> Add<(A, B)> where (A, B): Marker { function add(left: (A, B), right: (A, B)) returns ((A, B)) where (A, B): Witness { let unused: Word = 11; return right; } }",
  "impl<B, A> BitNot<(A, B)> where (A, B): Marker { function bnot(value: (A, B)) returns ((A, B)) where (A, B): Witness { let unused: Word = 13; return value; } }",
  "impl<B, A> Coerce<(A, B), Word> { function coerce(value: (A, B)) returns (Word) { return 19; } }",
  "function via<T>(left: T, right: T) returns (T) where T: Add, T: Marker, T: Witness, T: Marker { return left + right; }",
  "function binary(a: Word, b: Bool) returns ((Word, Bool)) { let left: (Word, Bool) = (a, b); let right: (Word, Bool) = (7, false); return via(left, right); }",
  "function unary(a: Word, b: Bool) returns ((Word, Bool)) { let value: (Word, Bool) = (a, b); return ~value; }",
  "function coerced(a: Word, b: Bool) returns (Word) { let value: (Word, Bool) = (a, b); return value + value; }",
  "function firstFault() returns ((Word, Bool)) { let left: (Word, Bool); let right: (Word, Bool) = (7, false); return left + right; }"
]

/-- Marker children audit the real lowering branch and its exact ordered call
code. Public execution below uses the original compiler callbacks and bodies. -/
private def inspect (cached : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let base := cached.indexed.base
  let program := cached.sourceProgram
  let representation := SourceCoreCompatibleFunctions.representation (.initial cached.compatible.checked) cached.compilationFuel
  let project := representation.expressions.projectType
  let policy : SourceCoreFunctions.CallablePolicy := {allowStaged := representation.allowStaged}
  let mut unaryCount := 0
  let mut binaryCount := 0
  let mut suffixCount := 0
  let mut coveredCount := 0
  let mut uncoveredCount := 0
  for named in base.functions do
    let caller := named.specialized
    let available ← get "actual operator caller" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
    for item in caller.function.typedBody.nodes do
      match item with
      | .expression node =>
        let ids? := match node.form with
          | .unary _ operand => some [operand]
          | .binary left _ right => some [left, right]
          | _ => none
        match ids?, SourceCompilationPlan.ordinaryOwnedRequirements? node with
        | some ids, some requirements =>
          if requirements.isEmpty then continue
          let owned := CallableCoercionExpressionCertificates.rawNode node requirements
          let selection ← get "actual operator selector" (match node.form with
            | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod program caller owned available operator
            | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod program caller owned available operator
            | _ => .error (.unsupportedRequirements requirements))
          if ids.length == 1 then unaryCount := unaryCount + 1 else binaryCount := binaryCount + 1
          let method := selection.method
          let dictionary ← get "actual ordered operator dictionary" (SourceCompilationPlan.operatorMethodRuntimeEvidence program caller owned selection)
          let headers ← get "actual method header roots" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program method.specialized.key method.traitPredicates)
          require (dictionary == headers ++ method.implementationPremises ++ method.methodPremises &&
            dictionary.length == 3 && dictionary[0]? == dictionary[1]? && dictionary[1]? != dictionary[2]?)
            "operator complete dictionary order changed"
          if method.traitPredicates.all caller.assumptions.contains then coveredCount := coveredCount + 1
          else uncoveredCount := uncoveredCount + 1
          let implementation ← match program.signatures.implementations.filter (·.id == method.id.implementation) with
            | [value] => pure value | _ => throw (IO.userError "operator impl singleton missing")
          let retained ← match program.methods.filter (·.id == method.id) with
            | [value] => pure value | _ => throw (IO.userError "operator retained checker body missing")
          require (TypedTraitResolution.ruleParameters implementation.implRule == implementation.parameters.reverse &&
            implementation.parameters != implementation.parameters.reverse &&
            method.specialized.parameterSubstitution.map Prod.fst == implementation.parameters)
            "operator raw substitution order became trivial"
          let selected ← get "operator full selected carrier" (SourceCompilationPlan.exactSpecialization base.plan method.specialized.key)
          require (selected == method.specialized &&
            selected.function.typedBody == StructuralSubstitution.applyTypedSource selected.parameterSubstitution retained.checked.typedBody &&
            selected.function.solvedRequirements == retained.checked.solvedRequirements.map
              (StructuralSubstitution.applySolvedRequirement selected.parameterSubstitution)) "operator full body/unused ledger changed"
          let namedRows := base.functions.zipIdx.filter (fun row => row.1.specialized == selected)
          let (actual, index) ← match namedRows with
            | [row] => pure row | _ => throw (IO.userError "operator full named cache row missing")
          require (actual.inputs.map Prod.fst == selected.function.typedBody.inputs &&
            (base.plan.specializations.reverse[index]?) == some selected &&
            (cached.indexed.secondPass.closures[index]?).isSome) "operator physical slot/raw binder/cache changed"
          let compilation : SourceCoreFunctions.Context := {
            plan := base.plan, owner := caller.key, globals := base.globals, administrativePrefix := 0,
            solvedRequirements := caller.function.solvedRequirements, internalReason := word 29 }
          let reasonAt := fun id : ExpressionId => word (1000 + id.occurrence.index)
          let child : SourceCoreEvidence.Child := fun remaining source _ childId _ => do
            if remaining != 37 then throw (.unsupportedExpression node.id node.form)
            let childNode ← match source.lookupExpression? childId with
              | some value => pure value | none => throw (.unsupportedExpression node.id node.form)
            let type ← project (.occurrence childId.occurrence) childNode.type
            pure ⟨type, .inLeft type (.word (reasonAt childId))⟩
          let codes ← ids.mapM (fun id => get "actual ordered marker child" (child 37 caller.function.typedBody [] id reasonAt))
          let signature := actual.signature
          let operand : SourceCoreBasic.LoweredExpr := ⟨signature.resultType,
            SourceCoreCalls.call signature index (SourceCoreCalls.packArguments codes).expression compilation.internalReason⟩
          let expected ← get "actual result coercion suffix" (SourceCoreEvidence.applyCoercions program project compilation caller available [] node policy operand node.coercions)
          let lowered ← get "actual operator lowering" (SourceCoreEvidence.lowerWithProjector program project caller compilation child
            37 caller.function.typedBody [] node.id reasonAt policy)
          require (lowered == some expected) "operator same ordered call/suffix/fuel changed"
          require (SourceCoreEvidence.lowerWithProjector program project caller compilation child 36
            caller.function.typedBody [] node.id reasonAt policy).toOption.isNone "operator child fuel was not preserved"
          suffixCount := suffixCount + node.coercions.length
          let ledger := caller.function.solvedRequirements
          let first ← match ledger with | first :: _ => pure first | _ => throw (IO.userError "operator ledger empty")
          let extra := {first with id := ⟨(ledger.map (fun (row : SolvedRequirement) => row.id.index)).foldl max 0 + 1⟩, evidence := .assumption first.predicate}
          for complete in [extra :: ledger, ledger ++ [extra]] do
            let retainedCaller := {caller with function := {caller.function with solvedRequirements := complete}}
            let same ← get "operator full unused row" (SourceCoreEvidence.lowerWithProjector program project retainedCaller
              {compilation with solvedRequirements := complete} child 37 caller.function.typedBody [] node.id reasonAt policy)
            require (same == lowered) "unused retained row changed actual operator materialization"
        | _, _ => pure ()
      | _ => pure ()
  require (unaryCount > 0 && binaryCount > 1 && suffixCount > 0 && coveredCount > 0 && uncoveredCount > 0)
    s!"operator actual inventory not exercised {unaryCount}/{binaryCount}/{suffixCount}/{coveredCount}/{uncoveredCount}"

private def full_native (cached : SourceCoreUnifiedCompilation.Compiled)
    (root : SourceSpecialization.SpecializationKey) (arguments : List SourceTypedRuntime.Value)
    (fuel : Nat) : IO (String × String × Bool) := do
  let first ← get "operator native startup" (cached.run root arguments 1024 fuel)
  let final ← get "operator native resume" (first.resume 300000)
  let execution ← match final.execution with
    | some execution => pure execution | none => throw (IO.userError "operator execution rejected")
  let failed ← match execution.completion.result.native.observation with
    | .succeeded _ _ => pure false | .failed _ _ => pure true
    | _ => throw (IO.userError "operator native did not complete")
  pure (reprStr final.observation, reprStr execution.completion.result.native.observation, failed)

def run : IO Unit := do
  let program ← get "actual operator source" (checkProgram {entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}]})
  let names := ["binary", "unary", "coerced", "firstFault"]
  let roots ← names.mapM (SourceCoreUnifiedCorpusSupport.key program)
  let compiled ← get "actual public operator compile" (SourceCoreCompiler.compileChecked program
    (roots.map fun key => SourceCoreCompiler.Seed.declaration key.declaration []) {specializationBudget := 512, compilationFuel := 1000})
  let cached ← match compiled.artifact? with | some value => pure value | none => throw (IO.userError "operator actual cache absent")
  inspect cached
  for index in [0, 1, 2] do
    let entry ← SourceCompilerFeatureSupport.fromCompiled compiled index
    let expected : SourceCoreExecution.Value := if index == 0 then .product (scalar 7) (.bool false)
      else if index == 1 then .product (scalar 5) (.bool true) else scalar 19
    require ((← entry.run [scalar 5, .bool true]) == expected) "operator original public result changed"
    entry.checkResume [scalar 5, .bool true] expected 7
  for (name, root) in names.zip roots do
    let arguments : List SourceTypedRuntime.Value := if name == "firstFault" then [] else [.word (word 5), .bool true]
    let baseline ← full_native cached root arguments 300000
    require (baseline.2.2 == (name == "firstFault")) "operator public source/native fault boundary changed"
    for fuel in [0, 1, 31, 300000] do
      require ((← full_native cached root arguments fuel) == baseline) "operator full native/source heaps or resume changed"
  let faultKey ← SourceCoreUnifiedCorpusSupport.key program "firstFault"
  let faultCaller ← get "fault original source" (SourceCompilationPlan.exactSpecialization cached.indexed.base.plan faultKey)
  let missing ← match (SourceCoreDataPlaces.declaredBinders faultCaller.function.typedBody).filter (·.name == "left") with
    | [binder] => pure binder.id | _ => throw (IO.userError "operator first missing binder absent")
  let fault ← get "operator exact first fault" (cached.run faultKey [] 1024 300000)
  match fault.observation with
  | .fault (.uninitializedLocal actual) state =>
    let type := TypeSystem.Ty.product .word .bool
    let expected : List SourceTypedRuntime.Cell := [⟨type, none⟩, ⟨type, some (.product (.word (word 7)) (.bool false))⟩]
    require (actual == missing && reprStr state.heap == reprStr expected)
      "operator first missing binder/ordered source heap/suffix skip changed"
  | _ => throw (IO.userError "operator first fault kind changed")
  IO.println "prepared methods: actual unary/binary selection/full dictionaries/raw substitution order/unused rows/physical cache/suffix; original public full heap/resume GREEN"

end Tests.SourceCoreCallablePreparedMethodSelection
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePreparedMethodCatalogEntries
/-! Actual marked prefixes keep the packed-argument slot, complete source heap,
ordered catalog, and physical history. Pure list fixtures below check offsets;
they do not construct catalog authority or source provenance. The runtime
runner reuses the existing four actual operator programs once. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodCatalogEntries
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries

abbrev actual_hook := @hook_catalog_entry
abbrev original_hook_spine := @hook_prefix_with_spine
abbrev caller_catalog_restore := @restore_catalog

theorem actual_parameter_prefix
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {bindings : List Binding} {output : Ty} {body parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source [] bindings output SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (parameterCode.rename ξ) result afterStore) :
    ∃ entry : Prefix layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body size result afterStore,
      ∃ added : Environment, added.length = bindings.length ∧
        entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical ∧
        entry.canonical[bindings.length]? = some (DataPatternValues.packValues nativeArguments) ∧
        entry.canonical.drop (bindings.length + 1) = canonical := by
  obtain ⟨entry, added, length, spine⟩ := parameter_prefix_with_spine functions onError accepted parameters inputs extended
    definitions registered represented environments heaps initialLocals actualLayout actualTyped reference read unmapped completed
  refine ⟨entry, added, length, spine, ?_, ?_⟩
  · simp [spine, ← length]
  · simp [spine, ← length]

section Catalog
variable {checked : Checked} {base : Base checked} {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope}
  {named : SourceCoreGeneralFunctions.Function} {body : Dynamic.BodyInstance} {function : Dynamic.Closure}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {canonical : Environment}
  (entry : SourceEntry named body function headers locations capturePrefix callerPrefix scope mapping world heap store canonical)

include entry in
theorem actual_catalog_globals : ∀ header, header ∈ headers →
    canonical[scope.length + callerPrefix + header.slot]? = some
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) := entry.catalog.globals

include entry in
theorem actual_source_dictionary : function.evidence.Covers body.context ∧
    function.source = body.source ∧ body.source = CallableIndexedNamedGeneration.source named :=
  ⟨entry.sourceFrame.covers, entry.sourceFrame.source, entry.sameSource⟩

include entry in
theorem actual_frame_and_history :
    canonical[scope.length + 1 + base.globals.length]? =
      some (.cellRef prepared.layout.frame.type entry.catalog.authority.frameLocation) ∧
    store.read? entry.catalog.authority.frameLocation = some
      (encode prepared.layout.frame entry.catalog.authority.current) ∧
    Carries prepared.graph.inputs prepared.graph.table entry.catalog.authority.current (.named entry.origin) (some entry.metadata) :=
  ⟨entry.reference, entry.catalog.authority.frame.read, entry.carried⟩

theorem retained_original_source {futureMap : LocationMap} {futureWorld : StoreTyping}
    {after : Dynamic.Heap} {futureStore : Store}
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    (entry.extend maps worlds frame metadata).sourceFrame = entry.sourceFrame ∧
    (entry.extend maps worlds frame metadata).origin = entry.origin ∧
    (entry.extend maps worlds frame metadata).metadata = entry.metadata ∧
    (entry.extend maps worlds frame metadata).catalog.authority.frameLocation = entry.catalog.authority.frameLocation :=
  ⟨rfl, rfl, rfl, rfl⟩
end Catalog

section Boundaries

theorem packed_slot_and_full_suffix (added canonical : Environment) (arguments : List Value) :
    let reached := added ++ DataPatternValues.packValues arguments :: canonical
    reached[added.length]? = some (DataPatternValues.packValues arguments) ∧
      reached.drop (added.length + 1) = canonical := by simp

theorem empty_arity_keeps_pack (added canonical : Environment) (empty : added.length = 0) :
    added ++ DataPatternValues.packValues [] :: canonical = Value.unit :: canonical := by
  cases added with
  | nil => rfl
  | cons head tail => simp at empty

/-- Two actual lookup positions and the independent frame index are preserved
under an arbitrary unused suffix; this fixture asserts no authority. -/
theorem ordered_globals_with_unused_suffix (unused : Environment) (bundle : Value) :
    let initial : Environment := [.bool true, .cellRef .word 3, .cellRef .bool 4, .cellRef .unit 5] ++ unused
    let reached := [Value.cellRef .word 7, .cellRef .bool 8] ++ bundle :: initial
    reached[2]? = some bundle ∧ reached[4]? = some (.cellRef .word 3) ∧
      reached[5]? = some (.cellRef .bool 4) ∧ reached[6]? = some (.cellRef .unit 5) ∧ reached.drop 7 = unused := by simp

theorem empty_parameters_with_unused_suffix (unused : Environment) :
    let initial : Environment := [.bool true, .cellRef .word 3, .cellRef .bool 4, .cellRef .unit 5] ++ unused
    let reached := Value.unit :: initial
    reached[0]? = some .unit ∧ reached[2]? = some (.cellRef .word 3) ∧
      reached[3]? = some (.cellRef .bool 4) ∧ reached[4]? = some (.cellRef .unit 5) ∧ reached.drop 5 = unused := by simp

end Boundaries

def run : IO Unit := Tests.SourceCoreCallablePreparedMethodSelection.run
end Tests.SourceCoreCallablePreparedMethodCatalogEntries
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePreparedMethodRuntimeMeaning
/-! The same actual method compilation, runtime body tree, selected dictionary
and installed histories close both call directions. Ordinary ledger validity
and external child/body execution laws are not inputs. Nonempty output coercion
paths remain a separate consumer; existing public operator IO is reused. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodRuntimeMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload CallableIndexedHistory
open CallablePreparedMethodRuntimeMeaning

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure CallablePreparedMethodRuntimeMeaning.Profile.ordinary

section Actual
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  (profile : Profile compiled values ambient sourceBody dictionary administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  (callerValid : CompatibleRuntimeContextValidity.Valid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {checkedProgram : CheckedProgram} {project : CallableCoercionExpressionCertificates.Projector}
  {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
  {child : SourceCoreEvidence.Child} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (receipt : CallablePreparedMethodSelection.Operator checkedProgram project caller compilation child fuel
    callerSource scope id callerReasonAt policy node output)

variable (alignment : OperatorAlignment (named := named) (sourceBody := sourceBody) (dictionary := dictionary) receipt)
  (selected : OperatorSource receipt)
  (selection : Dynamic.OperatorMethodSelected program callerContext callerEvidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope receipt.arguments (named.inputs.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
  (nativeTypes : receipt.loweredArguments.map (·.type) = named.inputs.map Prod.snd)

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection in
theorem actual_source {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (coercions : node.coercions = [])
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : NamedCalls.Arguments.Trace program callerContext callerEvidence dictionary callerSource sourceEnvironment
      before receipt.arguments sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact operator_preserves (compiled := compiled) (profile := profile) (functions := functions) (extension := extension)
    (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (uninitialized := uninitialized) (missing := missing) (escaped := escaped)
    (callerValid := callerValid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing)
    (receipt := receipt) (alignment := alignment) (selected := selected) (selection := selection)
    (children := children) (nativeTypes := nativeTypes)
    coercions installed located environments heaps locals layout actualTyped unique execution

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection in
theorem actual_native {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {value : Value} {size : Nat}
    (coercions : node.coercions = [])
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : EvaluationSize size callerEnvironment store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact operator_reflects_sized (compiled := compiled) (profile := profile) (functions := functions) (extension := extension)
    (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (uninitialized := uninitialized) (missing := missing) (escaped := escaped)
    (callerValid := callerValid) (callerUninitialized := callerUninitialized) (callerMissing := callerMissing)
    (receipt := receipt) (alignment := alignment) (selected := selected) (selection := selection)
    (children := children) (nativeTypes := nativeTypes)
    coercions installed located environments heaps locals layout actualTyped completed


include alignment in
theorem retained_full_method : named.specialized = receipt.selection.method.specialized := alignment.retained

include alignment in
theorem actual_dictionary : dictionary = CallableNamedMetadata.environment receipt.dictionary := alignment.dictionary

include profile in
theorem same_full_ledger : profile.context.solvedRequirements = named.specialized.function.solvedRequirements :=
  profile.body.valid.ledger

include profile in
theorem runtime_context : RuntimeRequirementLedgerValid profile.context := profile.body.valid.runtime

include profile in
theorem actual_body_source : sourceBody.source = CallableIndexedNamedGeneration.source named := profile.sameSource

include profile in
theorem ordered_inputs : sourceBody.source.inputs = named.inputs.map Prod.fst := profile.parameters

end Actual

abbrev actual_selected_dispatch := @CallablePreparedMethodRuntimeMeaning.OperatorSource.of_accepted
abbrev original_hook_child := @CallablePreparedMethodRuntimeMeaning.hook_prefix
abbrev original_body_child := @CallablePreparedMethodRuntimeMeaning.Profile.reflects_sized
abbrev same_dictionary_cover := @CallablePreparedMethodRuntimeMeaning.Body.with_evidence

/-- Packing cannot recover source arity: an empty bundle and one Unit payload
have the same native value. Ordered source binders remain explicit. -/
theorem pack_does_not_identify_arity :
    DataPatternValues.packValues [] = DataPatternValues.packValues [Core.Value.unit] ∧
      ([] : List Core.Value) ≠ [.unit] := by
  constructor
  · rfl
  · intro equal; cases equal

/-- Actual public unary/binary methods retain nonempty ordered dictionaries,
unused rows, body effects, a later coercion suffix, and first argument faults.
This reuses their original full source/native heap and resume oracle. -/
def run : IO Unit := Tests.SourceCoreCallablePreparedMethodSelection.run

end Tests.SourceCoreCallablePreparedMethodRuntimeMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePreparedMethodSourceHookMeaning
/-! Actual source body children execute the real method hook with concrete
builtin leaves. Parameter spines retain the packed slot and full global suffix;
source and native grades remain separate. No new runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodSourceHookMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates
open CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries
open CallablePreparedMethodCatalogHookMeaning CallablePreparedMethodOriginMeaning CallablePreparedMethodSourceHookMeaning

abbrev actual_hook := @CallablePreparedMethodSourceHookMeaning.ProfileFor.preserves_hook_of_below
abbrev actual_parameters := @CallablePreparedMethodSourceHookMeaning.entry_of_parameters
abbrev catalog_effects := @CallablePreparedMethodCatalogEntries.catalog_entry_of_effects
abbrev source_effects := @CallablePreparedMethodCatalogEntries.source_entry_of_effects

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable (profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary
    administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : SourceSemantics.Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) ((diagnostics.reasonAt named.signature.key) id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((diagnostics.reasonAt named.signature.key) id).add tag))


include profile extension faithful observations functionTypes escaped uninitialized missing in
theorem closed_builtin_hook (budget child : Nat) (strict : child < budget)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program child (methodFunction compiled sourceBody dictionary)
      profile.context environment bound outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (compiled.output.rename installed.embedding.lift) value finalStore ∧
      CallableCoercionMethodFrame.BodyOutcome program sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) program
        (methodFunction compiled sourceBody dictionary) profile.context
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after finalStore installed.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact CallablePreparedMethodSourceHookMeaning.ProfileFor.preserves_hook_of_below
    compiled (of_builtin compiled profile) functions escaped
    (fun valid extended => valid.extend extended) (fun valid => valid) budget child strict
    installed initial sameFrame represented heaps
    (fun smaller _ => Tests.SourceCoreCallablePreparedMethodOriginMeaning.closed_builtin_source
      compiled profile functions extension faithful observations functionTypes escaped uninitialized missing smaller)
    allocated trace

include profile extension faithful observations functionTypes escaped uninitialized missing in
/-- The parent source derivation supplies the original child and strict bound.
The resulting native hook is ungraded; no native grade is inferred from it. -/
theorem original_method_body (size : Nat)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : RecursiveNamedCallBounds.BodyOutcome program size sourceBody dictionary before arguments outcome after) :
    ∃ child environment bound,
      child < size ∧
      Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program child (methodFunction compiled sourceBody dictionary)
        profile.context environment bound outcome after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (compiled.output.rename installed.embedding.lift) value finalStore ∧
      CallableCoercionMethodFrame.BodyOutcome program sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) program
        (methodFunction compiled sourceBody dictionary) profile.context
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after finalStore installed.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have arity : (methodFunction compiled sourceBody dictionary).parameters.length = arguments.length := by
    change sourceBody.source.inputs.length = arguments.length
    rw [profile.parameters, List.length_map]
    exact represented.length.1
  obtain ⟨child, environment, bound, allocated, trace, strict⟩ :=
    RecursiveNamedCallBounds.body_trace_of_fields profile.sourceFrame.source profile.sourceFrame.context
      profile.sourceFrame.parameters profile.sourceFrame.result profile.sourceFrame.roots profile.extended arity executed
  refine ⟨child, environment, bound, strict, allocated, trace, ?_⟩
  exact closed_builtin_hook compiled profile functions extension faithful observations functionTypes escaped
    uninitialized missing size child strict installed initial sameFrame represented heaps allocated trace

section ActualParameters
variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {arguments : List Dynamic.Value} {payloads : List Value} {actualContext : Core.Context}
  {canonical actual : Environment} {ξ : Renaming}
  {location : Location} {next : NativeFrame}
  (reached : TypedMixedNamedParameters.Entry prepared.ancestry.layout.frame prepared.base.globals.length location next values functions registry
    (methodFunction compiled sourceBody dictionary) profile.context named.inputs arguments before
    (store.set location (encode prepared.ancestry.layout.frame next)) mapping world administrative actualContext
    actual ξ compiled.parameterCode compiled.body)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)
  {added : Environment} (length : added.length = named.inputs.length)
  (spine : reached.canonical = added ++ DataPatternValues.packValues payloads :: canonical)
  {originId : Word} {metadata : MetadataState}
  (owned : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some originId)
  (history : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next (.named originId) (some metadata))

/-- The actual parameter entry is embedded without a native body completion. -/
theorem same_parameter_state :
    (entry_of_parameters compiled (of_builtin compiled profile) functions escaped (fun valid extended => valid.extend extended) (fun valid => valid) reached initial sameFrame length spine owned history).environment = reached.environment ∧
    (entry_of_parameters compiled (of_builtin compiled profile) functions escaped (fun valid extended => valid.extend extended) (fun valid => valid) reached initial sameFrame length spine owned history).heap = reached.heap ∧
    (entry_of_parameters compiled (of_builtin compiled profile) functions escaped (fun valid extended => valid.extend extended) (fun valid => valid) reached initial sameFrame length spine owned history).store = reached.store ∧
    (entry_of_parameters compiled (of_builtin compiled profile) functions escaped (fun valid extended => valid.extend extended) (fun valid => valid) reached initial sameFrame length spine owned history).canonical = reached.canonical := ⟨rfl, rfl, rfl, rfl⟩

include length spine in
theorem global_suffix : reached.canonical.drop (named.inputs.length + 1) = canonical := by
  rw [spine, ← length]
  simp

include length spine in
theorem empty_parameters (empty : named.inputs = []) :
    reached.canonical = DataPatternValues.packValues payloads :: canonical := by
  have noAdded : added = [] := by
    cases added with
    | nil => rfl
    | cons head tail => simp [empty] at length
  simpa [noAdded] using spine

include length spine in
theorem ordered_globals (first second : Value) (unused : Environment)
    (original : canonical = first :: second :: unused) :
    reached.canonical[named.inputs.length + 1]? = some first ∧
    reached.canonical[named.inputs.length + 2]? = some second ∧
    reached.canonical.drop (named.inputs.length + 3) = unused := by
  rw [spine, original, ← length]
  simp [Nat.add_assoc]
end ActualParameters

/-- Empty source arguments retain the actual native unit carrier. -/
theorem empty_pack_slot (canonical : Environment) :
    DataPatternValues.packValues [] :: canonical = Value.unit :: canonical := rfl
end Tests.SourceCoreCallablePreparedMethodSourceHookMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePreparedMethodSourcePrefix
/-! The common hook envelope retains the actual parameter spine and a source
trace's original grade. The prefix continuation remains the internal interface;
this file does not assert a closed method body semantics. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedMethodSourcePrefix
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload CallableAncestryPairedLookup CallableIndexedHistory
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames

abbrev actual_parameters := @TypedMixedNamedParameters.entry_of_accepted_with_spine
abbrev legacy_parameters := @TypedMixedNamedParameters.entry_of_accepted
abbrev actual_hook := @BuiltinNamedCalls.hook_preserves_with_spine
abbrev legacy_hook := @BuiltinNamedCalls.hook_preserves_with

section Graded
variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (certificate : BuiltinNamedBody.Certificate layouts owner active prepared.layout.frame allocationGlobals onError readFuel values function.source context solved reasonAt
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) function.body function.resultType output
    policy fuel fellThrough escaped body)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame allocationGlobals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[allocationGlobals]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[ξ (base.globals.length + 1)]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)

include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook actualTyped in
theorem original_source_grade (child : Nat)
    (prefixMeaning : ∀ (origin : Word) (index : Int) (metadata : MetadataState),
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin →
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) →
      ∀ {prefixContext : Core.Context} {prefixActual : Environment} {embedding : Renaming}
      (entry : TypedMixedNamedParameters.Entry prepared.layout.frame allocationGlobals location (.state index)
        values functions registry function context bindings arguments before
        (store.set location (encode prepared.layout.frame (.state index))) mapping world
        administrative prefixContext prefixActual embedding parameterCode body)
      (added : Environment), added.length = bindings.length →
      entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical →
      ∀ {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
      RecursiveNamedCallBounds.BodyTrace program child function context entry.environment entry.heap outcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates prefixActual (store.set location (encode prepared.layout.frame (.state index)))
          (parameterCode.rename embedding) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld function.resultType output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping (store.set location (encode prepared.layout.frame (.state index))) finalMap finalStore ∧
        Dynamic.HeapMetadataExtend before after ∧
        TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
          (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
          (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.heap after outcome)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program child function context environment bound outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  exact BuiltinNamedCalls.hook_preserves_with_spine (prepared := prepared) (functions := functions) (program := program)
    (onError := onError) (parameters := parameters) (inputs := inputs) (extended := extended)
    (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered)
    (acceptedHook := acceptedHook) (represented := represented) (environments := environments)
    (heaps := heaps) (initialLocals := initialLocals) (actualLayout := actualLayout)
    (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
    (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
    (RecursiveNamedCallBounds.BodyTrace program child function context) prefixMeaning allocated trace
end Graded

section ActualSpine
variable {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {location : Location} {native : NativeFrame}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {bindings : List Binding}
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {store : Store}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {actual canonical added : Environment} {nativeArguments : List Value} {ξ : Renaming} {parameterCode body : Expr}
  (entry : TypedMixedNamedParameters.Entry layout globals location native values functions registry function context bindings arguments before store mapping world
    administrative actualContext actual ξ parameterCode body)
  (length : added.length = bindings.length)
  (spine : entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical)

include length spine in
theorem ordered_suffix : entry.canonical.drop (bindings.length + 1) = canonical := by
  rw [spine, ← length]
  simp

include length spine in
theorem physical_global (index : Nat) :
    entry.canonical[bindings.length + 1 + index]? = canonical[index]? := by
  rw [spine, ← length]
  rw [List.getElem?_append_right (by omega)]
  have offset : added.length + 1 + index - added.length = index + 1 := by omega
  rw [offset]
  rfl

include length spine in
theorem empty_parameters (empty : bindings = []) :
    entry.canonical = DataPatternValues.packValues nativeArguments :: canonical := by
  have noAdded : added = [] := by
    cases added with
    | nil => rfl
    | cons head tail => simp [empty] at length
  simpa [noAdded] using spine

include length spine in
theorem globals_and_unused_suffix (first second : Value) (unused : Environment)
    (original : canonical = first :: second :: unused) :
    entry.canonical[bindings.length + 1]? = some first ∧
    entry.canonical[bindings.length + 2]? = some second ∧
    entry.canonical.drop (bindings.length + 3) = unused := by
  rw [spine, original, ← length]
  simp [Nat.add_assoc]

include entry in
theorem full_reached_state :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions entry.mapping entry.world entry.heap entry.store ∧
    Dynamic.HeapMetadataExtend before entry.heap ∧
    AdministrativePreserved mapping store entry.mapping entry.store :=
  ⟨entry.heaps, entry.metadata, entry.frame⟩
end ActualSpine

/-- Empty parameter lists still use the actual one-slot packed argument carrier. -/
theorem empty_pack_slot (canonical : Environment) :
    DataPatternValues.packValues [] :: canonical = Value.unit :: canonical := rfl
end Tests.SourceCoreCallablePreparedMethodSourcePrefix
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePreparedOperatorSourceBounds
/-! These consumers keep the original raw, operand, body and suffix witnesses.
In particular a synthetic two-operand fault list is not a strict child of the
original whole binary-right fault. This unit adds no runtime runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedOperatorSourceBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallablePreparedOperatorSourceBounds CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableCoercionExpressionCertificates (Projector Specialized Lowered)

abbrev legacy_raw := @CallablePreparedOperatorSourceMeaning.OperatorSource.raw_inv
abbrev legacy_whole := @CallablePreparedOperatorSourceMeaning.OperatorSource.source_inv

section OriginalChildren
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence invocation : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
  {left right : ExpressionId} {leftSize rightSize : Nat} {value : Dynamic.Value}
  {reason : Dynamic.SemanticFault}
  (leftEvaluated : SourceExecutionSize.ExpressionEvaluates program leftSize context evidence source environment
    before left value middle)
  (rightFailed : SourceExecutionSize.ExpressionFaults program rightSize context evidence source environment
    middle right reason after)

include leftEvaluated rightFailed in
/-- Both operands retain strict bounds under the original raw parent. -/
theorem right_fault_original_children :
    ArgumentsFaultAt program (SourceExecutionSize.stepSize [leftSize, rightSize]) context evidence source environment
      before [left, right] reason after :=
  .tail leftEvaluated (SourceExecutionSize.child_lt_stepSize (by simp))
    (.head rightFailed (SourceExecutionSize.child_lt_stepSize (by simp)))

include leftEvaluated rightFailed in
/-- The synthetic list adds a constructor. Its grade equals the whole form
fault, so claiming a strict bound for that list would be incorrect. -/
theorem synthetic_right_fault :
    SourceExecutionSize.ExpressionsFault program
      (SourceExecutionSize.stepSize [leftSize, SourceExecutionSize.stepSize [rightSize]])
      context evidence source environment before [left, right] reason after :=
  .tail leftEvaluated (.head rightFailed)

theorem synthetic_fault_grade (leftSize rightSize : Nat) :
    SourceExecutionSize.stepSize [leftSize, SourceExecutionSize.stepSize [rightSize]] =
      SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [leftSize, rightSize]] ∧
    ¬ SourceExecutionSize.stepSize [leftSize, SourceExecutionSize.stepSize [rightSize]] <
      SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [leftSize, rightSize]] := by
  simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]
  omega

include leftEvaluated rightFailed in
theorem repeated_occurrence (same : right = left) :
    ArgumentsFaultAt program (SourceExecutionSize.stepSize [leftSize, rightSize]) context evidence source environment
      before [left, left] reason after := by
  simpa only [same] using right_fault_original_children leftEvaluated rightFailed

variable {budget bodySize : Nat} {body : Dynamic.BodyInstance} {ids : List ExpressionId}
  {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}

include leftEvaluated rightFailed in
/-- The view comes from exactly the original binary-right constructor; the
right fault leaves the method body uninvoked. -/
theorem right_fault_form (operator : Syntax.BinaryOp) (requirements : List RequirementId)
    (coercions : List CoercionStep) (owned : List RequirementId)
    (layout : Dynamic.OrdinaryRequirementLayout requirements coercions owned)
    (evaluateRight : Dynamic.EvaluatesRightOperand operator value) :
    SourceExecutionSize.ExpressionFormFaults program (SourceExecutionSize.stepSize [leftSize, rightSize])
      context evidence source environment before (.binary left operator right) requirements coercions reason after ∧
    RawTraceAt program (SourceExecutionSize.stepSize [leftSize, rightSize]) context evidence invocation source environment
      before [left, right] body (.fault reason) after :=
  ⟨.binaryRight layout leftEvaluated evaluateRight rightFailed,
    .argumentFault (right_fault_original_children leftEvaluated rightFailed)⟩

/-- The original body witness and source dictionary remain available without
rerunning the source or choosing a new grade. -/
theorem actual_body_child
    (operands : ArgumentsAt program budget context evidence source environment before ids arguments middle)
    (called : RecursiveNamedCallBounds.BodyOutcome program bodySize body invocation middle arguments outcome after)
    (strict : bodySize < budget) :
    RawTraceAt program budget context evidence invocation source environment before ids body outcome after :=
  .apply operands called strict

theorem full_dictionary_and_heap
    (trace : RawTraceAt program budget context evidence invocation source environment before ids body outcome after) :
    NamedCalls.Arguments.Trace program context evidence invocation source environment before ids body outcome after :=
  trace.sound

end OriginalChildren

section Whole
variable {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
  {outcome : Dynamic.ExpressionOutcome} {size : Nat}

/-- The original suffix size and its input heap are returned separately. -/
theorem whole_children
    (found : source.lookupExpression? id = some node) (unique : NodeOccurrencesUnique source)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder))
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    TraceForAt (fun child => RawOutcomeAt program child context evidence source environment before node)
      (fun child heap value => PathAt program child context evidence heap node.coercions value) size outcome after :=
  raw_source_inv_sized found unique notLocal trace

end Whole

section ActualSelected
variable {checkedProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  {receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output}
  (selected : OperatorSource receipt)
  {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence dictionary : Dynamic.EvidenceEnvironment}
  {sourceBody : Dynamic.BodyInstance}
  (catalog : CallableCoercionSelectionIdentity.Catalog program)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)
  (selection : Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)

include selected catalog ledger selection in
theorem actual_raw {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (raw : RawOutcomeAt program size context evidence source environment before node outcome after) :
    ∃ actualDictionary,
      Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
        receipt.requirements sourceBody actualDictionary ∧
      RawTraceAt program size context evidence actualDictionary source environment before
        receipt.arguments sourceBody outcome after :=
  CallablePreparedOperatorSourceBounds.OperatorSource.raw_inv_sized selected catalog ledger selection raw

include selected catalog ledger selection in
theorem actual_whole {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (unique : NodeOccurrencesUnique source)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    TraceForAt
      (fun rawSize rawOutcome rawHeap => ∃ actualDictionary,
        Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
          receipt.requirements sourceBody actualDictionary ∧
        RawTraceAt program rawSize context evidence actualDictionary source environment before
          receipt.arguments sourceBody rawOutcome rawHeap)
      (fun pathSize heap value => PathAt program pathSize context evidence heap node.coercions value)
      size outcome after :=
  CallablePreparedOperatorSourceBounds.OperatorSource.source_inv_sized selected catalog ledger selection unique trace

end ActualSelected

end Tests.SourceCoreCallablePreparedOperatorSourceBounds
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePreparedOperatorSuffixMeaning
/-! Selected raw operator traces and selected output paths are the source
preservation boundary. Runtime fixtures exercise actual public compilation,
nonempty ordered suffixes and first/later faults with complete stores. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreCallablePreparedOperatorSuffixMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload CallableIndexedHistory
open CallablePreparedOperatorSuffixMeaning
open SourceCompilerFeatureSupport (get require)

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure CallablePreparedOperatorSuffixMeaning.Method.ordinary

section Actual
open CallablePreparedMethodRuntimeMeaning
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  (profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  (callerValid : CompatibleRuntimeContextValidity.Valid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {checkedProgram : CheckedProgram} {project : CallableCoercionExpressionCertificates.Projector}
  {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
  {child : SourceCoreEvidence.Child} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (receipt : CallablePreparedMethodSelection.Operator checkedProgram project caller compilation child fuel
    callerSource scope id callerReasonAt policy node output)

variable (alignment : OperatorAlignment (named := named) (sourceBody := sourceBody) (dictionary := dictionary) receipt)
  (selected : OperatorSource receipt)
  (selection : Dynamic.OperatorMethodSelected program callerContext callerEvidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope receipt.arguments (named.inputs.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
  (nativeTypes : receipt.loweredArguments.map (·.type) = named.inputs.map Prod.snd)


variable {methods : Methods (prepared := prepared) (values := values) (ambient := ambient)
    (registry := registry) (faults := faults) (program := program) (context := callerContext) (evidence := callerEvidence)}
  (suffixUninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (suffixMissing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  (suffixEscaped : ∀ method ∈ methods, faults .controlEscapedFunction method.compiled.own.table.escapedReason)
  {ξ : Renaming} {calls : List CallableCoercionSpine.Call}
  (emitted : Emitted checkedProgram project compilation caller receipt.available scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : CallableCoercionPathMeaning.ChainFor Method.row sourceBody.resultType receipt.operand.type methods node.type output.type)


include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection suffixUninitialized suffixMissing suffixEscaped emitted steps chain in
/-- The original raw operator and every selected output conversion are closed
by their actual runtime trees. No child or body execution law is an input. -/
theorem actual_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {outcome : Dynamic.ExpressionOutcome}
    (installed : CallablePreparedMethodRuntimeMeaning.Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (suffixEntry : Entry methods functions callerEnvironment mapping world before store)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : CallablePreparedOperatorSuffixMeaning.Trace (sourceBody := sourceBody) (dictionary := dictionary) (program := program) (receipt := receipt) (methods := methods) sourceEnvironment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions callerEnvironment finalMap finalWorld after finalStore) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact CallablePreparedOperatorSuffixMeaning.preserves
    (compiled := compiled) (profile := profile) (functions := functions) (extension := extension)
    (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (uninitialized := uninitialized) (missing := missing) (escaped := escaped) (callerValid := callerValid)
    (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt) (alignment := alignment)
    (selected := selected) (selection := selection) (children := children) (nativeTypes := nativeTypes)
    (suffixUninitialized := suffixUninitialized) (suffixMissing := suffixMissing) (suffixEscaped := suffixEscaped) (emitted := emitted)
    (steps := steps) (chain := chain)
    installed located suffixEntry environments heaps locals layout actualTyped unique execution
include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection suffixUninitialized suffixMissing suffixEscaped emitted steps chain in
/-- Completed output code supplies the original measured operand and each
actual suffix body. Reflection does not require a source completion. -/
theorem actual_reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {value : Value} {size : Nat}
    (installed : CallablePreparedMethodRuntimeMeaning.Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (suffixEntry : Entry methods functions callerEnvironment mapping world before store)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : EvaluationSize size callerEnvironment store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions callerEnvironment finalMap finalWorld after finalStore) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact CallablePreparedOperatorSuffixMeaning.reflects_sized
    (compiled := compiled) (profile := profile) (functions := functions) (extension := extension)
    (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (uninitialized := uninitialized) (missing := missing) (escaped := escaped) (callerValid := callerValid)
    (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt) (alignment := alignment)
    (selected := selected) (selection := selection) (children := children) (nativeTypes := nativeTypes)
    (suffixUninitialized := suffixUninitialized) (suffixMissing := suffixMissing) (suffixEscaped := suffixEscaped) (emitted := emitted)
    (steps := steps) (chain := chain)
    installed located suffixEntry environments heaps locals layout actualTyped completed

end Actual

abbrev original_suffix_children := @CallableCoercionSpine.Spine.renamed_completed_sized
abbrev original_stored_body := @CallablePreparedOperatorSuffixMeaning.Capture.completed_sized
abbrev actual_suffix_receipt := @CallablePreparedOperatorSuffixMeaning.actual_suffix

section Boundaries
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  (method : CallablePreparedOperatorSuffixMeaning.Method prepared values ambient registry faults program context evidence)

theorem full_dictionary : method.row.dictionary = method.dictionary := rfl

theorem same_full_runtime_ledger :
    method.profile.context.solvedRequirements = method.named.specialized.function.solvedRequirements :=
  method.profile.body.valid.ledger

theorem repeated_rows : ([method, method].map (fun row => row.row.dictionary)) = [method.dictionary, method.dictionary] := rfl

theorem original_selected : Dynamic.OperatorMethodSelected program context evidence "Coerce" "coerce"
    method.step.requirements method.sourceBody method.dictionary := method.selected

end Boundaries

private def content (mode : Nat) : String := String.intercalate "\n" [
  "trait Marker<T> {}", "trait Witness<T> {}",
  "impl Marker<(Word, Bool)> {}", "impl Witness<(Word, Bool)> {}",
  "impl Marker<Bool> {}", "impl Witness<Bool> {}",
  "trait Add<T> where T: Marker { function add(left: T, right: T) returns (T) where T: Witness; }",
  "trait Coerce<From, To> where From: Marker { function coerce(value: From) returns (To) where From: Witness; }",
  "impl Add<(Word, Bool)> where (Word, Bool): Marker { function add(left: (Word, Bool), right: (Word, Bool)) returns ((Word, Bool)) where (Word, Bool): Witness { let rawEffect: Word = 101; return right; } }",
  "impl Coerce<(Word, Bool), Bool> where (Word, Bool): Marker { function coerce(value: (Word, Bool)) returns (Bool) where (Word, Bool): Witness { let firstEffect: Word = 103; " ++
    (if mode == 1 then "let firstGap: Bool; return firstGap;" else "return true;") ++ " } }",
  "impl Coerce<Bool, Word> where Bool: Marker { function coerce(value: Bool) returns (Word) where Bool: Witness { let secondEffect: Word = 107; " ++
    (if mode == 2 then "let secondGap: Word; return secondGap;" else "return 19;") ++ " } }",
  "function root(a: Word, b: Bool) returns (Word) { " ++
    (if mode == 3 then "let rawGap: (Word, Bool);" else "let rawGap: (Word, Bool) = (a, b);") ++
    " let right: (Word, Bool) = (7, false); return rawGap + right; }"
]

private def inspect (cached : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let base := cached.indexed.base
  let root ← SourceCoreUnifiedCorpusSupport.key cached.sourceProgram "root"
  let named ← match base.functions.find? (·.signature.key == root) with
    | some value => pure value | none => throw (IO.userError "suffix actual root missing")
  let caller := named.specialized
  let program := cached.sourceProgram
  let representation := SourceCoreCompatibleFunctions.representation (.initial cached.compatible.checked) cached.compilationFuel
  let project := representation.expressions.projectType
  let policy : SourceCoreFunctions.CallablePolicy := {allowStaged := representation.allowStaged}
  let available ← get "suffix caller" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions)
  let mut found := false
  for item in caller.function.typedBody.nodes do
    if let .expression node := item then
      if let .binary left operator right := node.form then
        let requirements ← match SourceCompilationPlan.ordinaryOwnedRequirements? node with
          | some value => pure value | none => throw (IO.userError "suffix requirement layout missing")
        if requirements.isEmpty then continue
        require (node.coercions.length == 2) "actual operator suffix length changed"
        let raw := CallableCoercionExpressionCertificates.rawNode node requirements
        let selected ← get "suffix raw operator selector"
          (SourceCompilationPlan.checkedBinaryOperatorMethod program caller raw available operator)
        let actual ← get "suffix raw fullrow" (SourceCompilationPlan.exactSpecialization base.plan selected.method.specialized.key)
        require (actual == selected.method.specialized) "raw method full row changed"
        let mut expectedTypes : List TypeSystem.Ty := []
        let mut indices : List Nat := []
        for step in node.coercions do
          let method ← get "suffix selected method" (SourceCompilationPlan.checkedCoercionMethod program caller node available step)
          let dictionary ← get "suffix full dictionary" (SourceCompilationPlan.coercionMethodRuntimeEvidence program caller node step method)
          let key ← get "suffix actual edge" (SourceCompilationPlan.exactCallKey base.plan caller.key node.id method.specialized.key)
          let complete ← get "suffix complete row" (SourceCompilationPlan.exactSpecialization base.plan key)
          let row ← match base.functions.zipIdx.filter (fun row => row.1.specialized == complete) with
            | [row] => pure row | _ => throw (IO.userError "suffix physical row missing")
          require (complete == method.specialized && dictionary.length == 3 && dictionary[0]? == dictionary[1]? &&
            dictionary[1]? != dictionary[2]? && dictionary.map SourceCompilationPlan.runtimeEvidenceGoal == complete.assumptions &&
            base.plan.specializations.reverse[row.2]? == some complete &&
            (cached.indexed.secondPass.closures[row.2]?).isSome && row.1.inputs.length == 1)
            "suffix full record/dictionary order/cache changed"
          expectedTypes := expectedTypes ++ [step.source, step.target]
          indices := indices ++ [row.2]
        require (expectedTypes == [.product .word .bool, .bool, .bool, .word] && indices.length == 2)
          "suffix raw endpoint order changed"
        let compilation : SourceCoreFunctions.Context := {
          plan := base.plan, owner := caller.key, globals := base.globals, administrativePrefix := 0, solvedRequirements := caller.function.solvedRequirements,
          internalReason := Word.ofNatModulo 29}
        let reasonAt := fun id : ExpressionId => Word.ofNatModulo (1000 + id.occurrence.index)
        let child : SourceCoreEvidence.Child := fun remaining source _ id _ => do
          if remaining != 37 then throw (.unsupportedExpression node.id node.form)
          let childNode ← match source.lookupExpression? id with
            | some value => pure value | none => throw (.unsupportedExpression node.id node.form)
          let type ← project (.occurrence id.occurrence) childNode.type
          pure ⟨type, .inLeft type (.word (reasonAt id))⟩
        let actual ← get "suffix actual lowering" (SourceCoreEvidence.lowerWithProjector program project caller compilation child
          37 caller.function.typedBody [] node.id reasonAt policy)
        let codes ← [left, right].mapM (fun id => get "suffix ordered operands" (child 37 caller.function.typedBody [] id reasonAt))
        let row ← match base.functions.zipIdx.filter (fun row => row.1.specialized == selected.method.specialized) with
          | [row] => pure row | _ => throw (IO.userError "operator physical row missing")
        let operand : SourceCoreBasic.LoweredExpr := ⟨row.1.signature.resultType,
          SourceCoreCalls.call row.1.signature row.2 (SourceCoreCalls.packArguments codes).expression compilation.internalReason⟩
        let expected ← get "suffix same emitter" (SourceCoreEvidence.applyCoercions program project compilation caller available [] node policy operand node.coercions)
        require (actual == some expected && Core.infer? (base.globals.map SourceCoreCalls.Signature.referenceType)
          expected.expression cached.indexed.layouts.definitions == some (LanguageResult.resultType expected.type))
          "suffix actual ordered emission/type changed"
        require ((SourceCoreEvidence.lowerWithProjector program project caller compilation child 36
          caller.function.typedBody [] node.id reasonAt policy).toOption.isNone) "suffix child fuel changed"
        let ledger := caller.function.solvedRequirements
        let first ← match ledger with | first :: _ => pure first | _ => throw (IO.userError "suffix full ledger empty")
        let extra := {first with
          id := ⟨(ledger.map (fun (row : SolvedRequirement) => row.id.index)).foldl max 0 + 1⟩,
          evidence := .assumption first.predicate}
        for complete in [extra :: ledger, ledger ++ [extra]] do
          let retained := {caller with function := {caller.function with solvedRequirements := complete}}
          require ((SourceCoreEvidence.lowerWithProjector program project retained {compilation with solvedRequirements := complete}
            child 37 caller.function.typedBody [] node.id reasonAt policy).toOption == some actual)
            "suffix unused full ledger changed selected rows"
        found := true
  require found "actual nonempty operator suffix missing"

private def execute (cached : SourceCoreUnifiedCompilation.Compiled) (root : SourceSpecialization.SpecializationKey)
    (fuel : Nat) : IO (SourceCoreUnifiedCompilation.Result cached) := do
  let first ← get "suffix start" (cached.run root [.word (Word.ofNatModulo 5), .bool true] 1024 fuel)
  get "suffix resume" (first.resume 300000)

private def expected_cells (mode : Nat) : List SourceTypedRuntime.Cell :=
  let word := fun value => SourceTypedRuntime.Value.word (Word.ofNatModulo value)
  let pairType := TypeSystem.Ty.product .word .bool
  let first := SourceTypedRuntime.Value.product (word 5) (.bool true)
  let second := SourceTypedRuntime.Value.product (word 7) (.bool false)
  let initial := [⟨.word, some (word 5)⟩, ⟨.bool, some (.bool true)⟩,
    ⟨pairType, if mode == 3 then none else some first⟩, ⟨pairType, some second⟩]
  if mode == 3 then initial else
    let raw := initial ++ [⟨pairType, some first⟩, ⟨pairType, some second⟩, ⟨.word, some (word 101)⟩]
    let converted := raw ++ [⟨pairType, some second⟩, ⟨.word, some (word 103)⟩]
    if mode == 1 then converted ++ [⟨.bool, none⟩] else
      converted ++ [⟨.bool, some (.bool true)⟩, ⟨.word, some (word 107)⟩] ++
        (if mode == 2 then [⟨.word, none⟩] else [])

private def audit (mode : Nat) : IO Unit := do
  let program ← get "suffix source" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := content mode}]})
  let key ← SourceCoreUnifiedCorpusSupport.key program "root"
  let compiled ← get "suffix public compile" (SourceCoreCompiler.compileChecked program
    [.declaration key.declaration []] {specializationBudget := 512, compilationFuel := 1000})
  let cached ← match compiled.artifact? with | some value => pure value | none => throw (IO.userError "suffix cache absent")
  inspect cached
  let baseline ← execute cached key 300000
  let native ← match baseline.execution with | some value => pure value | none => throw (IO.userError "suffix native observation missing")
  let expectedGap := if mode == 1 then "firstGap" else if mode == 2 then "secondGap" else "rawGap"
  match baseline.observation with
  | .done value state =>
    require (reprStr state.heap == reprStr (expected_cells mode)) "suffix exact success heap changed"
    require (mode == 0 && reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 19))) "suffix expected success changed"
    require ((state.heap.filterMap (fun cell => cell.value)).any (fun value => reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 101))) &&
      (state.heap.filterMap (fun cell => cell.value)).any (fun value => reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 103))) &&
      (state.heap.filterMap (fun cell => cell.value)).any (fun value => reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 107)))) "suffix body effect missing"
  | .fault (.uninitializedLocal actual) state =>
    let gaps := cached.indexed.base.functions.flatMap (fun named =>
      (SourceCoreDataPlaces.declaredBinders named.specialized.function.typedBody).filter (·.name == expectedGap))
    let expected ← match gaps with | [binder] => pure binder.id | _ => throw (IO.userError "suffix exact fault binder missing")
    require (mode != 0 && actual == expected && reprStr state.heap == reprStr (expected_cells mode))
      s!"suffix first/later original fault changed: mode={mode}, actual={reprStr actual}, expected={reprStr expected}, heap={reprStr state.heap}"
    require (!(state.heap.filterMap (fun cell => cell.value)).any (fun value => reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 107))) || mode == 2)
      "suffix executed a skipped body"
    if mode == 3 then
      require (!(state.heap.filterMap (fun cell => cell.value)).any (fun value => reprStr value == reprStr (SourceTypedRuntime.Value.word (Word.ofNatModulo 101))))
        "raw argument failure entered operator body"
  | _ => throw (IO.userError "suffix execution did not complete")
  for fuel in [0, 1, 31, 300000] do
    let actual ← execute cached key fuel
    let actualNative ← match actual.execution with | some value => pure value | none => throw (IO.userError "suffix resumed native missing")
    require (reprStr actual.observation == reprStr baseline.observation &&
      reprStr actualNative.completion.result.native.observation == reprStr native.completion.result.native.observation)
      "suffix full source/native ordered stores or resume changed"

def run : IO Unit := do
  for mode in [0, 1, 2, 3] do audit mode
  IO.println "operator output suffix: actual two-step source/native/full dictionary/first-later faults/ordered stores/resume GREEN"

end Tests.SourceCoreCallablePreparedOperatorSuffixMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallablePreparedOperatorSourceMeaning
/-! Independent source completion and the original native completion meet at
one actual operator and ordered suffix. Static profiles retain full runtime
ledgers when source selection chooses its own covered dictionary. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePreparedOperatorSourceMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload CallableIndexedHistory
open CallablePreparedOperatorSuffixMeaning

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure CallablePreparedOperatorSuffixMeaning.Method.ordinary

section Actual
open CallablePreparedMethodRuntimeMeaning
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  (profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  (callerValid : CompatibleRuntimeContextValidity.Valid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {checkedProgram : CheckedProgram} {project : CallableCoercionExpressionCertificates.Projector}
  {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
  {child : SourceCoreEvidence.Child} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (receipt : CallablePreparedMethodSelection.Operator checkedProgram project caller compilation child fuel
    callerSource scope id callerReasonAt policy node output)

variable (alignment : OperatorAlignment (named := named) (sourceBody := sourceBody) (dictionary := dictionary) receipt)
  (selected : OperatorSource receipt)
  (selection : Dynamic.OperatorMethodSelected program callerContext callerEvidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope receipt.arguments (named.inputs.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
  (nativeTypes : receipt.loweredArguments.map (·.type) = named.inputs.map Prod.snd)


variable {methods : Methods (prepared := prepared) (values := values) (ambient := ambient)
    (registry := registry) (faults := faults) (program := program) (context := callerContext) (evidence := callerEvidence)}
  (suffixUninitialized : ∀ method ∈ methods, ∀ id location,
    faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (suffixMissing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
  (suffixEscaped : ∀ method ∈ methods, faults .controlEscapedFunction method.compiled.own.table.escapedReason)
  {ξ : Renaming} {calls : List CallableCoercionSpine.Call}
  (emitted : Emitted checkedProgram project compilation caller receipt.available scope node policy ξ receipt.operand methods output calls)
  (steps : methods.map (·.step) = node.coercions)
  (chain : CallableCoercionPathMeaning.ChainFor Method.row sourceBody.resultType receipt.operand.type methods node.type output.type)


include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection suffixUninitialized suffixMissing suffixEscaped emitted steps chain in
/-- The original raw operator and every selected output conversion are closed
by their actual runtime trees. No child or body execution law is an input. -/
theorem actual_preserves {rawWorkspace : Workspace.RawWorkspace} {checkFuel : Nat}
    (checkedAccepted : checkProgram rawWorkspace checkFuel = .ok checkedProgram)
    (sourceProgram : program = SourceSemantics.Program.ofChecked checkedProgram)
    (ledger : callerContext.solvedRequirements = caller.function.solvedRequirements) {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {outcome : Dynamic.ExpressionOutcome}
    (installed : CallablePreparedMethodRuntimeMeaning.Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (suffixEntry : Entry methods functions callerEnvironment mapping world before store)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions callerEnvironment finalMap finalWorld after finalStore) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact CallablePreparedOperatorSourceMeaning.preserves
    (compiled := compiled) (profile := profile) (functions := functions) (extension := extension)
    (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (uninitialized := uninitialized) (missing := missing) (escaped := escaped) (callerValid := callerValid)
    (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt) (alignment := alignment)
    (selected := selected) (selection := selection) (children := children) (nativeTypes := nativeTypes)
    (suffixUninitialized := suffixUninitialized) (suffixMissing := suffixMissing) (suffixEscaped := suffixEscaped) (emitted := emitted)
    (steps := steps) (chain := chain)
    (catalog := by simpa only [sourceProgram] using CallableCoercionSelectionIdentity.Catalog.of_checked checkedAccepted)
    (ledger := ledger) installed located suffixEntry environments heaps locals layout actualTyped unique execution
include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection suffixUninitialized suffixMissing suffixEscaped emitted steps chain in
/-- Completed output code supplies the original measured operand and each
actual suffix body. Reflection does not require a source completion. -/
theorem actual_reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {value : Value} {size : Nat}
    (installed : CallablePreparedMethodRuntimeMeaning.Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (suffixEntry : Entry methods functions callerEnvironment mapping world before store)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : EvaluationSize size callerEnvironment store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type output.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods functions callerEnvironment finalMap finalWorld after finalStore) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact CallablePreparedOperatorSourceMeaning.reflects_sized
    (compiled := compiled) (profile := profile) (functions := functions) (extension := extension)
    (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
    (uninitialized := uninitialized) (missing := missing) (escaped := escaped) (callerValid := callerValid)
    (callerUninitialized := callerUninitialized) (callerMissing := callerMissing) (receipt := receipt) (alignment := alignment)
    (selected := selected) (selection := selection) (children := children) (nativeTypes := nativeTypes)
    (suffixUninitialized := suffixUninitialized) (suffixMissing := suffixMissing) (suffixEscaped := suffixEscaped) (emitted := emitted)
    (steps := steps) (chain := chain)
    installed located suffixEntry environments heaps locals layout actualTyped completed

end Actual

abbrev original_native_children := @CallableCoercionSpine.Spine.renamed_completed_sized
abbrev independent_raw_dictionary := @CallablePreparedOperatorSourceMeaning.OperatorSource.raw_inv
abbrev original_raw_middle_heap := @CallablePreparedOperatorSourceMeaning.OperatorSource.source_inv

section Boundaries
open CallablePreparedMethodRuntimeMeaning
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {oldDictionary dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : Profile compiled values ambient sourceBody oldDictionary administrative registry faults)
  (covers : dictionary.Covers sourceBody.context)

theorem same_runtime_tree :
    (profile.with_evidence dictionary covers).body.tree = profile.body.tree := rfl

theorem same_emitted_body :
    (profile.with_evidence dictionary covers).body.flow = profile.body.flow := rfl

theorem full_runtime_ledger :
    (profile.with_evidence dictionary covers).context.solvedRequirements =
      named.specialized.function.solvedRequirements := profile.body.valid.ledger

theorem actual_covered_dictionary :
    dictionary.Covers (profile.with_evidence dictionary covers).context :=
  (profile.with_evidence dictionary covers).body.valid.covers

variable {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  (method : Method prepared values ambient registry faults program context evidence)
  (selected : Dynamic.OperatorMethodSelected program context evidence "Coerce" "coerce"
    method.step.requirements method.sourceBody dictionary)

theorem same_actual_row :
    (CallablePreparedOperatorSourceMeaning.method_with_evidence method dictionary selected).call = method.call := rfl

theorem source_dictionary :
    (CallablePreparedOperatorSourceMeaning.method_with_evidence method dictionary selected).dictionary = dictionary := rfl

theorem repeated_order (other : Dynamic.EvidenceEnvironment)
    (otherSelected : Dynamic.OperatorMethodSelected program context evidence "Coerce" "coerce"
      method.step.requirements method.sourceBody other) :
    [CallablePreparedOperatorSourceMeaning.method_with_evidence method dictionary selected,
     CallablePreparedOperatorSourceMeaning.method_with_evidence method other otherSelected].map (·.dictionary) =
      [dictionary, other] := rfl

/-- The generic outer trace keeps the successful raw heap distinct from the
suffix's final heap; no equality between the two is needed. -/
theorem raw_middle_heap {rawTrace : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop}
    {pathTrace : Dynamic.Heap → Dynamic.Value → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop}
    {value : Dynamic.Value} {middle after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (raw : rawTrace (.value value) middle) (suffix : pathTrace middle value outcome after) :
    CallableCoercionExpressionMeaning.TraceFor rawTrace pathTrace outcome after := .path raw suffix

end Boundaries

/-- Reuse the actual public success/raw/first/later-fault fixture once. -/
def run : IO Unit := SourceCoreCallablePreparedOperatorSuffixMeaning.run

end Tests.SourceCoreCallablePreparedOperatorSourceMeaning
end

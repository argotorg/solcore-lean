import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaStaticBodySupport

/-! The shared kernel consumes the original source/native grade and retains
an arbitrary protected entry. Concrete builtin leaves close both consumers
without an external execution law. A lambda receipt supplies the same static
fields at its original dictionary; no Code or source-attribution cast is used.
Runtime IO is provided by the existing operator suites. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableRuntimeBodyKernel
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CoreProof ReadOnly CompatiblePayload

abbrev finite_source := @CallableRuntimeBodyKernel.BodyFor.preserves_sized
abbrev finite_native := @CallableRuntimeBodyKernel.BodyFor.reflects_sized
abbrev old_body := @CallablePreparedMethodRuntimeMeaning.Body.mk

section Concrete
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {expressionSyntax : ExpressionId → Prop} {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {output : Ty} {code : Expr} {fellThrough escaped : Word}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : CallablePreparedMethodRuntimeMeaning.Body layouts owner active frameLayout globals onError values function expressionSyntax readFuel solved reasonAt
    ambient administrative context scope output code fellThrough escaped registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (escapedFault : faults .controlEscapedFunction escaped)

variable {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry) (binders : ProtectedExpressionMeaning.Binds entry)

include body definitions registered extension faithful observations functionTypes uninitialized missing escapedFault transport binders in
theorem closed_source (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      entry scope finalMap finalWorld after finalStore canonical := by
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid solved context function.evidence →
      RecursiveNamedHeaderContracts.AtMost budget (fun child => RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence
        function.source (CompatibleExpressionBuiltinRuntime.Certificate readFuel values function.source context solved reasonAt)
        faults entry) := by
    intro context valid child _
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed entry
        (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations functionTypes
          program function.evidence valid.ledger valid.runtime body.unique uninitialized missing)) child
  exact body.toKernel.preserves_sized functions definitions registered extension program faithful observations escapedFault
    transport binders (fun valid extended => valid.extend extended) (fun valid => valid)
    budget size within expressions environments heaps locals agrees typed reference read unmapped installed trace

include body definitions registered extension faithful observations functionTypes uninitialized missing escapedFault transport binders in
theorem closed_native (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      entry scope finalMap finalWorld after finalStore canonical := by
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid solved context function.evidence →
      RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence
        function.source (CompatibleExpressionBuiltinRuntime.Certificate readFuel values function.source context solved reasonAt)
        faults entry) := by
    intro context valid
    exact RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed entry
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes
          program function.evidence valid.ledger valid.runtime uninitialized missing)) budget
  exact body.toKernel.reflects_sized functions definitions registered extension program faithful observations functionTypes escapedFault
    transport binders (fun valid extended => valid.extend extended) (fun valid => valid)
    budget size within expressions environments heaps locals agrees typed reference read unmapped installed evaluated

theorem same_tree : body.toKernel.flow = body.flow ∧ HEq body.toKernel.tree body.tree ∧
    HEq body.toKernel.sites body.sites := ⟨rfl, HEq.rfl, HEq.rfl⟩

theorem full_runtime : body.toKernel.initialValid.ledger = body.valid.ledger ∧
    body.toKernel.initialValid.runtime = body.valid.runtime ∧
    body.toKernel.initialValid.covers = body.valid.covers := ⟨rfl, rfl, rfl⟩

/-- This existing dictionary transport is only the concrete builtin family. -/
theorem builtin_evidence (dictionary : Dynamic.EvidenceEnvironment) (covers : dictionary.Covers context) :
    (body.with_evidence dictionary covers).toKernel.flow = body.flow ∧
    HEq (body.with_evidence dictionary covers).toKernel.tree body.tree := ⟨rfl, HEq.rfl⟩
end Concrete

section Lambda
variable {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {values : SourceCoreCompatibleValues.Context} {prepared : CallableIndexedLambdaValues.Prepared values.checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : CallableIndexedLambdaValues.Code prepared function scope administrative}
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Actual/canonical source transport remains in BodyWith; the kernel consumes
only its already established canonical static fields at the same dictionary. -/
theorem lambda_fields
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith expressionSyntax certificates code program registry faults) :
    ∃ kernel : CallableRuntimeBodyKernel.BodyFor prepared.layouts code.compilation.owner code.active
      prepared.ancestry.layout.frame prepared.base.globals.length code.allocationError values function
      (expressionSyntax function.source) (certificates body.readFuel function.source)
      (fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence)
      .reachable (CallableIndexedAmbient.ambientDefinitions prepared) administrative body.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      code.receipt.resultCore code.receipt.body code.compilation.internalReason code.compilation.internalReason registry faults,
      kernel.flow = body.flow ∧ HEq kernel.tree body.tree ∧ HEq kernel.sites body.sites := by
  exact ⟨{
    flow := body.flow
    tree := body.tree
    sites := body.sites
    initialValid := body.valid
    projection := body.projection
    unique := body.unique
    emitted := body.emitted }, rfl, HEq.rfl, HEq.rfl⟩
end Lambda

-- A family indexed by its dictionary has no general Covers-only reindex API.
#check_failure CallableRuntimeBodyKernel.BodyFor.with_evidence

end Tests.SourceCoreCallableRuntimeBodyKernel

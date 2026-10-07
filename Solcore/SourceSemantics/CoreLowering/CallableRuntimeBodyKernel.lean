import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForReflection

/-! A static body has no named, method, or lambda origin. Its actual Tree, sites,
finish code, and initial context feed the same finite flow and finish proofs.
The bounded expression premises are internal induction interfaces for the one
mutual caller proof. Closed public consumers must supply them from their static
certificates; this module does not postulate a body execution law.
Source and native grades stay independent. Reflection consumes only the original
native witness. Code-specific views, prefix installation, and restoration stay
with their actual origin adapters. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyKernel
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload

structure BodyFor (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frameLayout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : SourceCoreCompatibleValues.Context) (function : Dynamic.Closure)
    (expressionSyntax : ExpressionId → Prop)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (validity : SourceSemantics.Context → Prop) (diagnosticPolicy : AssignmentDiagnosticPolicy) (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (administrative : Core.Context) (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (output : Ty) (code : Expr) (fellThrough escaped : Word)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  flow : Expr
  tree : GenericImperativeMatch.Tree layouts owner active frameLayout globals onError values function.source
    expressionSyntax certificates ambient.definitions administrative context scope
    (.statements true function.body) function.resultType output flow
  sites : tree.CatalogSites diagnosticPolicy registry faults
  initialValid : validity context
  projection : values.checked.catalog.project function.resultType = .ok output
  unique : NodeOccurrencesUnique function.source
  emitted : code = CompatibleStatements.finish output flow fellThrough escaped

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {solved : List SolvedRequirement} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {output : Ty} {code : Expr} {fellThrough escaped : Word}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : BodyFor layouts owner active frameLayout globals onError values function expressionSyntax
    certificates validity diagnosticPolicy ambient administrative context scope output code fellThrough escaped registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (escapedFault : faults .controlEscapedFunction escaped)
  {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry) (binders : ProtectedExpressionMeaning.Binds entry)
  (extend : ∀ {context next binder}, validity context →
    BinderExtends function.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context → CompatibleRuntimeContextValidity.Valid solved context function.evidence)

include body definitions registered extension faithful observations escapedFault transport binders extend runtimeOf in
/-- Preserve at the original source body grade, retaining the actual entry. -/
theorem BodyFor.preserves_sized (budget size : Nat) (within : size ≤ budget)
    (expressions : ∀ context, validity context → RecursiveNamedHeaderContracts.AtMost budget (fun child =>
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context function.evidence function.source (certificates context) faults entry))
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
  have flow := RecursiveNamedImperativeFor.preservesAt_match_with
    (validity := validity) (extend := extend) (runtimeOf := fun _ valid => runtimeOf valid)
    (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
    (program := program) (evidence := function.evidence) (transport := transport) (bindings := binders)
    (budget := budget) (faithful := faithful) (observations := observations) (meaningMost := expressions)
    diagnosticPolicy body.unique body.tree body.sites size within
  exact RecursiveNamedFunctionFinishBounds.preserves_at_emitted functions program body.tree body.projection body.unique
    escapedFault transport body.emitted validity size flow body.initialValid
    environments heaps locals agrees typed reference read unmapped installed trace

include body definitions registered extension faithful observations functionTypes escapedFault transport binders extend runtimeOf in
/-- Reflect the original native finish and return an independent source grade. -/
theorem BodyFor.reflects_sized (budget size : Nat) (within : size ≤ budget)
    (expressions : ∀ context, validity context → RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context function.evidence function.source (certificates context) faults entry))
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
  have flow := RecursiveNamedImperativeFor.reflectsAt_match_with
    (validity := validity) (extend := extend) (runtimeOf := fun _ valid => runtimeOf valid)
    functions definitions registered extension program function.evidence transport binders
    budget expressions faithful observations diagnosticPolicy functionTypes body.unique body.tree body.sites
  exact RecursiveNamedFunctionFinishBounds.reflects_at_emitted functions program body.tree body.projection body.unique
    escapedFault transport body.emitted validity budget size within flow body.initialValid
    environments heaps locals agrees typed reference read unmapped installed evaluated

namespace Stateful
universe u v
variable {Records : Type v}
  (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frameLayout
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (acquire : ∀ location native, conditionGate location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)

include body definitions registered extension faithful observations escapedFault producer acquire stateTransport stateBindings extend runtimeOf in
/-- Preserve at the original source body grade, retaining the actual reached state. -/
theorem BodyFor.preserves_sized (budget size : Nat) (within : size ≤ budget)
    (expressions : ∀ context, validity context → RecursiveNamedHeaderContracts.AtMost budget (fun child =>
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context function.evidence function.source (certificates context) faults child))
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
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : conditionGate contextLocation native)
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
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have flow := RecursiveNamedImperativeFor.Stateful.preservesAt_match_with
    (validity := validity) (extend := extend) (runtimeOf := fun _ valid => runtimeOf valid)
    (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
    (program := program) (evidence := function.evidence) (protocol := protocol) (producer := producer) (conditionGate := conditionGate)
    (acquire := acquire) (stateTransport := stateTransport) (stateBindings := stateBindings)
    (budget := budget) (faithful := faithful) (observations := observations) (meaningMost := expressions)
    diagnosticPolicy body.unique body.tree body.sites size within
  exact RecursiveNamedFunctionFinishBounds.preserves_at_emitted_with_state_when
    (functions := functions) (program := program) (tree := body.tree)
    (projection := body.projection) (unique := body.unique) (escapedFault := escapedFault)
    protocol conditionGate body.emitted validity size flow body.initialValid
    environments heaps locals agrees typed reference read unmapped initial gate trace

include body definitions registered extension faithful observations functionTypes escapedFault producer acquire stateTransport stateBindings extend runtimeOf in
/-- Reflect the original native finish and return an independent source grade. -/
theorem BodyFor.reflects_sized (budget size : Nat) (within : size ≤ budget)
    (expressions : ∀ context, validity context → RecursiveNamedBoundedContracts.Below budget (fun child =>
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context function.evidence function.source (certificates context) faults child))
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
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : conditionGate contextLocation native)
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
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have flow := RecursiveNamedImperativeFor.Stateful.reflectsAt_match_with
    (validity := validity) (extend := extend) (runtimeOf := fun _ valid => runtimeOf valid)
    (functions := functions) (definitions := definitions) (registered := registered)
    (extension := extension) (program := program) (evidence := function.evidence)
    (protocol := protocol) (conditionGate := conditionGate) (producer := producer)
    (stateTransport := stateTransport) (stateBindings := stateBindings) (acquire := acquire)
    (budget := budget) (reflection := expressions) (faithful := faithful) (observations := observations)
    diagnosticPolicy functionTypes body.unique body.tree body.sites
  exact RecursiveNamedFunctionFinishBounds.reflects_at_emitted_with_state_when
    (functions := functions) (program := program) (tree := body.tree)
    (projection := body.projection) (unique := body.unique) (escapedFault := escapedFault)
    protocol conditionGate body.emitted validity budget size within flow body.initialValid
    environments heaps locals agrees typed reference read unmapped initial gate evaluated

end Stateful

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyKernel

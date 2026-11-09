import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements

/-!
# Callable runtime: bodies

The runtime body kernel, its origins, ready inputs, mutual meaning and entry contracts.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyKernel
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
theorem BodyFor.preserves_sized [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
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
theorem BodyFor.reflects_sized [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
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

namespace WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateImperativeCatalogReady
variable
  (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts headFacts exprFacts program function.evidence function.source)
  (initializerSites : InitializerSites initializerFacts loopFacts function.source)
  (assignmentSites : AssignmentSites headFacts assignmentFacts snapshotFacts function.source)
  (transfers : AllocationTransfers protocol readiness stateBindings function.source)
  (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program function.evidence function.source)

include body definitions registered escapedFault producer acquire stateTransport stateBindings extend sites initializerSites assignmentSites transfers snapshots in
/-- Preserve at the original source body grade, retaining the actual reached state. -/
theorem BodyFor.preserves_sized (budget size : Nat) (within : size ≤ budget)
    (assignments : ∀ context, validity context → Assignment.AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions
      (registry := registry) program function.evidence function.source (certificates context) context administrative budget)
    (assignmentFaults : ∀ context, validity context → Assignment.AssignmentFaultPreservesAt protocol readiness assignmentFacts functions
      (registry := registry) program function.evidence function.source (certificates context) context administrative faults budget)
    (headFor : PreservingHeads protocol readiness conditionGate headFacts functions program function.evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frameLayout) (globals := globals) (onError := onError)
      (source := function.source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (RecursiveNamedImperativeFor.Stateful.WithReady.PreservesAtWith protocol readiness conditionGate facts loopFacts initializerFacts
        (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (layouts := layouts)
        (owner := owner) (active := active) (frame := frameLayout) (globals := globals) (onError := onError)
        (source := function.source) (administrative := administrative) (registry := registry) (faults := faults)
        functions program function.evidence budget))
    (loopFor : PreservingLoops protocol readiness conditionGate loopFacts functions program function.evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frameLayout) (globals := globals) (onError := onError)
      (source := function.source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (RecursiveNamedImperativeFor.Stateful.WithReady.PreservesAtWith protocol readiness conditionGate facts loopFacts initializerFacts
        (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (layouts := layouts)
        (owner := owner) (active := active) (frame := frameLayout) (globals := globals) (onError := onError)
        (source := function.source) (administrative := administrative) (registry := registry) (faults := faults)
        functions program function.evidence budget) diagnosticPolicy)
    (expressions : ∀ context, validity context → RecursiveNamedHeaderContracts.AtMost budget (fun child =>
      ExpressionPreservesAt protocol readiness program function.evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (context := context) (source := function.source) (faults := faults) child))
    (bodyFacts : facts context true function.body function.resultType)
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
    (gate : conditionGate contextLocation native) (ready : readiness.Ready context initial)
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
      ProtectedStateTransition.FunctionFinish.Reached readiness context outcome initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have flow := RecursiveNamedImperativeFor.Stateful.WithReady.preservesAt_match_with
    (validity := validity) (extend := extend)
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := function.evidence) (protocol := protocol) (producer := producer) (conditionGate := conditionGate)
    (acquire := acquire) (stateTransport := stateTransport) (stateBindings := stateBindings)
    (budget := budget) (meaningMost := expressions)
    (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts)
    (loopFacts := loopFacts) (initializerFacts := initializerFacts) (initializerSites := initializerSites)
    (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts) (sites := sites)
    (assignmentSites := assignmentSites) (transfers := transfers) (snapshots := snapshots)
    (assignments := assignments) (assignmentFaults := assignmentFaults)
    diagnosticPolicy body.unique headFor loopFor body.tree body.sites size within
  exact RecursiveNamedFunctionFinishBounds.WithReady.preserves_at_emitted_with_state_when
    (functions := functions) (program := program) (tree := body.tree)
    (projection := body.projection) (unique := body.unique) (escapedFault := escapedFault)
    protocol readiness conditionGate facts body.emitted validity size flow body.initialValid bodyFacts
    environments heaps locals agrees typed reference read unmapped initial gate ready trace

include body definitions registered escapedFault producer acquire stateTransport stateBindings extend sites initializerSites assignmentSites transfers snapshots in
/-- Reflect the original native finish and return an independent source grade. -/
theorem BodyFor.reflects_sized (budget size : Nat) (within : size ≤ budget)
    (assignments : ∀ context, validity context → Assignment.AssignmentReflectsAt protocol readiness assignmentFacts functions
      (registry := registry) program function.evidence function.source (certificates context) context administrative faults budget)
    (headFor : ReflectingHeads protocol readiness conditionGate headFacts functions program function.evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frameLayout) (globals := globals) (onError := onError)
      (source := function.source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (RecursiveNamedImperativeFor.Stateful.WithReady.ReflectsAtWith protocol readiness conditionGate facts loopFacts initializerFacts
        (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (layouts := layouts)
        (owner := owner) (active := active) (frame := frameLayout) (globals := globals) (onError := onError)
        (source := function.source) (administrative := administrative) (registry := registry) (faults := faults)
        functions program function.evidence budget))
    (loopFor : ReflectingLoops protocol readiness conditionGate loopFacts functions program function.evidence validity budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frameLayout) (globals := globals) (onError := onError)
      (source := function.source) (expressionSyntax := expressionSyntax) (certificates := certificates) (administrative := administrative)
      (registry := registry) (faults := faults)
      (RecursiveNamedImperativeFor.Stateful.WithReady.ReflectsAtWith protocol readiness conditionGate facts loopFacts initializerFacts
        (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) (layouts := layouts)
        (owner := owner) (active := active) (frame := frameLayout) (globals := globals) (onError := onError)
        (source := function.source) (administrative := administrative) (registry := registry) (faults := faults)
        functions program function.evidence budget) diagnosticPolicy)
    (expressions : ∀ context, validity context → RecursiveNamedBoundedContracts.Below budget (fun child =>
      ExpressionReflectsAt protocol readiness program function.evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (context := context) (source := function.source) (faults := faults) child))
    (bodyFacts : facts context true function.body function.resultType)
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
    (gate : conditionGate contextLocation native) (ready : readiness.Ready context initial)
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
      ProtectedStateTransition.FunctionFinish.Reached readiness context outcome initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have flow := RecursiveNamedImperativeFor.Stateful.WithReady.reflectsAt_match_with
    (validity := validity) (extend := extend)
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := function.evidence)
    (protocol := protocol) (conditionGate := conditionGate) (producer := producer)
    (stateTransport := stateTransport) (stateBindings := stateBindings) (acquire := acquire)
    (budget := budget) (reflection := expressions)
    (readiness := readiness) (facts := facts) (headFacts := headFacts) (exprFacts := exprFacts)
    (loopFacts := loopFacts) (initializerFacts := initializerFacts) (initializerSites := initializerSites)
    (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts) (sites := sites)
    (assignmentSites := assignmentSites) (transfers := transfers) (snapshots := snapshots) (assignments := assignments)
    diagnosticPolicy body.unique headFor loopFor body.tree body.sites
  exact RecursiveNamedFunctionFinishBounds.WithReady.reflects_at_emitted_with_state_when
    (functions := functions) (program := program) (tree := body.tree)
    (projection := body.projection) (unique := body.unique) (escapedFault := escapedFault)
    protocol readiness conditionGate facts body.emitted validity budget size within flow body.initialValid bodyFacts
    environments heaps locals agrees typed reference read unmapped initial gate ready evaluated

end WithReady

include body definitions registered extension faithful observations escapedFault producer acquire stateTransport stateBindings extend runtimeOf in
/-- Preserve at the original source body grade, retaining the actual reached state. -/
theorem BodyFor.preserves_sized [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
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
  have assignments := RecursiveNamedImperativeFor.Stateful.WithReady.assignment_prefix_uniform
    (administrative := administrative) (functions := functions) (extension := extension) (program := program) (evidence := function.evidence)
    (protocol := protocol) (stateTransport := stateTransport) (validity := validity)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := expressions)
  have assignmentFaults := RecursiveNamedImperativeFor.Stateful.WithReady.assignment_fault_uniform
    (administrative := administrative) (functions := functions) (extension := extension) (program := program) (evidence := function.evidence)
    (protocol := protocol) (stateTransport := stateTransport) (validity := validity)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := expressions)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ :=
    WithReady.BodyFor.preserves_sized
    (body := body) (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (protocol := protocol) (conditionGate := conditionGate) (producer := producer)
    (acquire := acquire) (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := validity) (extend := extend) (escapedFault := escapedFault)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (loopFacts := fun _ _ _ _ _ => True) (initializerFacts := fun _ _ _ _ _ _ => True)
    (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program function.evidence function.source)
    (initializerSites := ProtectedStateImperativeCatalogReady.InitializerSites.trivial function.source)
    (assignmentSites := ProtectedStateImperativeCatalogReady.AssignmentSites.trivial function.source)
    (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings function.source)
    (snapshots := ProtectedForHeader.Stateful.WithReady.SnapshotTransfers.trivial protocol validity program function.evidence function.source)
    budget size within
    (fun context valid => ProtectedForHeader.Stateful.WithReady.assignment_prefix_trivial protocol functions program function.evidence
      function.source (certificates context) context administrative budget (assignments context valid))
    (fun context valid => ProtectedForHeader.Stateful.WithReady.assignment_fault_trivial protocol functions program function.evidence
      function.source (certificates context) context administrative faults budget (assignmentFaults context valid))
    (RecursiveNamedImperativeFor.Stateful.WithReady.preserving_heads_trivial
    (administrative := administrative) (functions := functions) (definitions := definitions) (registered := registered)
    (extension := extension) (program := program) (evidence := function.evidence)
    (protocol := protocol) (producer := producer) (conditionGate := conditionGate) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := validity) (extend := extend) (solved := solved)
    (faithful := faithful) (observations := observations) (budget := budget) (runtimeOf := fun _ valid => runtimeOf valid) (meaningMost := expressions)
    diagnosticPolicy body.unique)
    (RecursiveNamedImperativeFor.Stateful.WithReady.preserving_loops_trivial
    (administrative := administrative) (functions := functions) (definitions := definitions) (registered := registered)
    (extension := extension) (program := program) (evidence := function.evidence)
    (protocol := protocol) (producer := producer) (conditionGate := conditionGate) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := validity) (extend := extend) (solved := solved)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := expressions) diagnosticPolicy body.unique)
    (fun context valid child bounded => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt.of_true
      (protocol := protocol) (program := program) (evidence := function.evidence)
      (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (certificate := certificates context) (expressions context valid child bounded)) True.intro
    environments heaps locals agrees typed reference read unmapped initial gate True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
    ProtectedStateTransition.FunctionFinish.Reached.forget reached⟩

include body definitions registered extension faithful observations functionTypes escapedFault producer acquire stateTransport stateBindings extend runtimeOf in
/-- Reflect the original native finish and return an independent source grade. -/
theorem BodyFor.reflects_sized [FunctionCalls.FaultTokens faults] (budget size : Nat) (within : size ≤ budget)
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
  have assignments := RecursiveNamedImperativeFor.Stateful.WithReady.assignment_reflection_uniform
    (administrative := administrative) (functions := functions) (extension := extension) (program := program) (evidence := function.evidence)
    (protocol := protocol) (stateTransport := stateTransport) (validity := validity)
    (faithful := faithful) (observations := observations) (budget := budget) (reflection := expressions) functionTypes
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ :=
    WithReady.BodyFor.reflects_sized
    (body := body) (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (protocol := protocol) (conditionGate := conditionGate) (producer := producer)
    (acquire := acquire) (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := validity) (extend := extend) (escapedFault := escapedFault)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ _ _ => True) (headFacts := fun _ _ _ => True) (exprFacts := fun _ _ _ => True)
    (loopFacts := fun _ _ _ _ _ => True) (initializerFacts := fun _ _ _ _ _ _ => True)
    (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
    (sites := RecursiveNamedLexicalContracts.Stateful.WithReady.StaticSites.trivial program function.evidence function.source)
    (initializerSites := ProtectedStateImperativeCatalogReady.InitializerSites.trivial function.source)
    (assignmentSites := ProtectedStateImperativeCatalogReady.AssignmentSites.trivial function.source)
    (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings function.source)
    (snapshots := ProtectedForHeader.Stateful.WithReady.SnapshotTransfers.trivial protocol validity program function.evidence function.source)
    budget size within
    (fun context valid => ProtectedForHeader.Stateful.WithReady.assignment_reflection_trivial protocol functions program function.evidence
      function.source (certificates context) context administrative faults budget (assignments context valid))
    (RecursiveNamedImperativeFor.Stateful.WithReady.reflecting_heads_trivial
    (administrative := administrative) (functions := functions) (definitions := definitions) (registered := registered)
    (extension := extension) (program := program) (evidence := function.evidence)
    (protocol := protocol) (producer := producer) (conditionGate := conditionGate) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := validity) (extend := extend) (solved := solved)
    (faithful := faithful) (observations := observations) (budget := budget) (runtimeOf := fun _ valid => runtimeOf valid) (reflection := expressions)
    diagnosticPolicy functionTypes body.unique)
    (RecursiveNamedImperativeFor.Stateful.WithReady.reflecting_loops_trivial
    (administrative := administrative) (functions := functions) (definitions := definitions) (registered := registered)
    (extension := extension) (program := program) (evidence := function.evidence)
    (protocol := protocol) (producer := producer) (conditionGate := conditionGate) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := validity) (extend := extend) (solved := solved)
    (faithful := faithful) (observations := observations) (budget := budget) (reflection := expressions) diagnosticPolicy functionTypes body.unique)
    (fun context valid child bounded => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt.of_true
      (protocol := protocol) (program := program) (evidence := function.evidence)
      (model := CompatibleAmbientHeap.payloadModel values.checked registry functions) (certificate := certificates context) (expressions context valid child bounded)) True.intro
    environments heaps locals agrees typed reference read unmapped initial gate True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
    ProtectedStateTransition.FunctionFinish.Reached.forget reached⟩

end Stateful

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyKernel
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyOrigins
/-! An origin retains an actual static body and its protected entry condition.
Named, lambda, and method provenance stays in the higher adapters. No execution
law is stored here. A reached entry supplies the original environments, heap,
frame, and native code context to the shared body kernel. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof

structure Origin (values : SourceCoreCompatibleValues.Context)
    (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  layouts : SourceCoreAllocationLayouts.Prepared
  owner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  frameLayout : SourceCoreCallableIndexedFrames.Layout
  globals : Nat
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  function : Dynamic.Closure
  expressionSyntax : ExpressionId → Prop
  certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate
  validity : SourceSemantics.Context → Prop
  diagnosticPolicy : AssignmentDiagnosticPolicy
  administrative : Core.Context
  context : SourceSemantics.Context
  scope : SourceCoreLocalCell.Scope
  output : Ty
  code : Expr
  fellThrough : Word
  escaped : Word
  solved : List SolvedRequirement
  protectedEntry : ProtectedExpressionMeaning.Entry
  body : CallableRuntimeBodyKernel.BodyFor layouts owner active frameLayout globals onError values function
    expressionSyntax certificates validity diagnosticPolicy ambient administrative context scope output code
    fellThrough escaped registry faults
  definitions : layouts.definitions = ambient.definitions
  registered : frameLayout.Registered ambient.definitions
  escapedFault : faults .controlEscapedFunction escaped
  transport : ProtectedExpressionMeaning.Transport protectedEntry
  binders : ProtectedExpressionMeaning.Binds protectedEntry
  extend : ∀ {context next binder}, validity context → BinderExtends function.source.owner context binder next → validity next
  runtimeOf : ∀ {context}, validity context → CompatibleRuntimeContextValidity.Valid solved context function.evidence

variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- All fields describe this reached state. They confer no new source origin. -/
structure Entry (origin : Origin values ambient registry faults)
    (functions : FunctionModel values.checked.catalog ambient) where
  mapping : LocationMap
  world : StoreTyping
  environment : Dynamic.Environment
  canonical : Environment
  actual : Environment
  heap : Dynamic.Heap
  store : Store
  embedding : Renaming
  actualContext : Core.Context
  frameLocation : Location
  native : CallableIndexedHistory.NativeFrame
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
    mapping world origin.administrative origin.scope environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap origin.context.locals environment
  lookups : EnvironmentsAgree embedding canonical actual
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions
  reference : canonical[origin.scope.length + 1 + origin.globals]? = some (.cellRef origin.frameLayout.type frameLocation)
  read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode origin.frameLayout native)
  unmapped : frameLocation ∉ mapping
  installed : origin.protectedEntry origin.scope mapping world heap store canonical

variable (functions : FunctionModel values.checked.catalog ambient) (program : Program)
  (origin : Origin values ambient registry faults)

/-- The source body grade is the original grade. All reached state is retained. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ (entry : Entry origin functions) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace program size origin.function origin.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actual entry.store (origin.code.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.environment entry.heap after outcome ∧
      origin.protectedEntry origin.scope finalMap finalWorld after finalStore entry.canonical

/-- Native completion supplies its own grade; the source grade is an output. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ (entry : Entry origin functions) {value : Value} {finalStore : Store},
    EvaluationSize size entry.actual entry.store (origin.code.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize origin.function origin.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.environment entry.heap after outcome ∧
      origin.protectedEntry origin.scope finalMap finalWorld after finalStore entry.canonical

/-- Source/native origin metadata and static support, with no legacy entry law. -/
structure StaticOrigin (values : SourceCoreCompatibleValues.Context)
    (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  layouts : SourceCoreAllocationLayouts.Prepared
  owner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  frameLayout : SourceCoreCallableIndexedFrames.Layout
  globals : Nat
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  function : Dynamic.Closure
  expressionSyntax : ExpressionId → Prop
  certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate
  validity : SourceSemantics.Context → Prop
  diagnosticPolicy : AssignmentDiagnosticPolicy
  administrative : Core.Context
  context : SourceSemantics.Context
  scope : SourceCoreLocalCell.Scope
  output : Ty
  code : Expr
  fellThrough : Word
  escaped : Word
  solved : List SolvedRequirement
  body : CallableRuntimeBodyKernel.BodyFor layouts owner active frameLayout globals onError values function
    expressionSyntax certificates validity diagnosticPolicy ambient administrative context scope output code
    fellThrough escaped registry faults
  definitions : layouts.definitions = ambient.definitions
  registered : frameLayout.Registered ambient.definitions
  escapedFault : faults .controlEscapedFunction escaped
  extend : ∀ {context next binder}, validity context → BinderExtends function.source.owner context binder next → validity next
  runtimeOf : ∀ {context}, validity context → CompatibleRuntimeContextValidity.Valid solved context function.evidence

/-- Compatibility projection retains the complete static body receipt. -/
def Origin.toStatic {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (origin : Origin values ambient registry faults) : StaticOrigin values ambient registry faults where
  layouts := origin.layouts
  owner := origin.owner
  active := origin.active
  frameLayout := origin.frameLayout
  globals := origin.globals
  onError := origin.onError
  function := origin.function
  expressionSyntax := origin.expressionSyntax
  certificates := origin.certificates
  validity := origin.validity
  diagnosticPolicy := origin.diagnosticPolicy
  administrative := origin.administrative
  context := origin.context
  scope := origin.scope
  output := origin.output
  code := origin.code
  fellThrough := origin.fellThrough
  escaped := origin.escaped
  solved := origin.solved
  body := origin.body
  definitions := origin.definitions
  registered := origin.registered
  escapedFault := origin.escapedFault
  extend := origin.extend
  runtimeOf := origin.runtimeOf

namespace Stateful
universe u v
variable {Records : Type v}
  (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)

structure Entry (origin : StaticOrigin values ambient registry faults)
    (functions : FunctionModel values.checked.catalog ambient) where
  mapping : LocationMap
  world : StoreTyping
  environment : Dynamic.Environment
  canonical : Environment
  actual : Environment
  heap : Dynamic.Heap
  store : Store
  embedding : Renaming
  actualContext : Core.Context
  frameLocation : Location
  native : CallableIndexedHistory.NativeFrame
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
    mapping world origin.administrative origin.scope environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap origin.context.locals environment
  lookups : EnvironmentsAgree embedding canonical actual
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions
  reference : canonical[origin.scope.length + 1 + origin.globals]? = some (.cellRef origin.frameLayout.type frameLocation)
  read : store.read? frameLocation = some (SourceCoreCallableIndexedFrames.encode origin.frameLayout native)
  unmapped : frameLocation ∉ mapping
  initial : protocol.State ⟨origin.scope, mapping, world, heap, store, canonical⟩
  gate : conditionGate frameLocation native
variable (functions : FunctionModel values.checked.catalog ambient) (program : Program)
  (origin : StaticOrigin values ambient registry faults)

/-- The source body grade is the original grade. All reached state is retained. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ (entry : Entry protocol conditionGate origin functions) {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace program size origin.function origin.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actual entry.store (origin.code.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.Transition protocol entry.initial
        ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- Native completion supplies its own grade; the source grade is an output. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ (entry : Entry protocol conditionGate origin functions) {value : Value} {finalStore : Store},
    EvaluationSize size entry.actual entry.store (origin.code.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize origin.function origin.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.Transition protocol entry.initial
        ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.canonical⟩

end Stateful

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyOrigins
/-! Readiness and genuine body facts accompany the original actual entry.
The static origin, protected state, environment and physical reads are retained
verbatim. Source and native contracts expose the same reached finish state and
keep their independent grades. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins
open RecursiveNamedLexicalContracts.Stateful.WithReady (Readiness)
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : Readiness protocol)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)

structure Entry (origin : StaticOrigin values ambient registry faults)
    (functions : FunctionModel values.checked.catalog ambient) where
  original : Stateful.Entry protocol conditionGate origin functions
  bodyFacts : facts origin.context true origin.function.body origin.function.resultType
  ready : readiness.Ready origin.context original.initial

variable (functions : FunctionModel values.checked.catalog ambient) (program : Program)
  (origin : StaticOrigin values ambient registry faults)

def PreservesAt (size : Nat) : Prop :=
  ∀ (entry : Entry protocol readiness conditionGate facts origin functions)
      {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace program size origin.function origin.context
      entry.original.environment entry.original.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.original.actual entry.original.store (origin.code.rename entry.original.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.original.mapping finalMap ∧ WorldExtends entry.original.world finalWorld ∧
      AdministrativePreserved entry.original.mapping entry.original.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend entry.original.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.original.environment entry.original.heap after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness origin.context outcome entry.original.initial
        ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.original.canonical⟩

def ReflectsAt (size : Nat) : Prop :=
  ∀ (entry : Entry protocol readiness conditionGate facts origin functions)
      {value : Value} {finalStore : Store},
    EvaluationSize size entry.original.actual entry.original.store
      (origin.code.rename entry.original.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize origin.function origin.context
        entry.original.environment entry.original.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.original.mapping finalMap ∧ WorldExtends entry.original.world finalWorld ∧
      AdministrativePreserved entry.original.mapping entry.original.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend entry.original.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.original.environment entry.original.heap after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness origin.context outcome entry.original.initial
        ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.original.canonical⟩

section Trivial
variable {protocol conditionGate functions program origin} {size : Nat}

theorem PreservesAt.of_trivial
    (meaning : Stateful.PreservesAt protocol conditionGate functions program origin size) :
    PreservesAt protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      functions program origin size := by
  intro entry outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, preserved, metadata, lexical, reached⟩ := meaning entry.original trace
  obtain ⟨last, related⟩ := reached
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, preserved, metadata, lexical, last, related, by cases outcome <;> exact True.intro⟩

theorem PreservesAt.forget_trivial
    (meaning : PreservesAt protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      functions program origin size) :
    Stateful.PreservesAt protocol conditionGate functions program origin size := by
  intro entry outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, preserved, metadata, lexical, reached⟩ :=
    meaning ⟨entry, True.intro, True.intro⟩ trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, preserved, metadata, lexical, reached.forget⟩

theorem ReflectsAt.of_trivial
    (meaning : Stateful.ReflectsAt protocol conditionGate functions program origin size) :
    ReflectsAt protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      functions program origin size := by
  intro entry value finalStore evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, preserved, metadata, lexical, reached⟩ := meaning entry.original evaluated
  obtain ⟨last, related⟩ := reached
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, preserved, metadata, lexical, last, related, by cases outcome <;> exact True.intro⟩

theorem ReflectsAt.forget_trivial
    (meaning : ReflectsAt protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      functions program origin size) :
    Stateful.ReflectsAt protocol conditionGate functions program origin size := by
  intro entry value finalStore evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, preserved, metadata, lexical, reached⟩ :=
    meaning ⟨entry, True.intro, True.intro⟩ evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, preserved, metadata, lexical, reached.forget⟩

end Trivial
end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyInputs
/-! Structural inputs and finite producers for the existing measured body
family. Each kit supplies only the actual assignment prefixes and individual
head or loop recipes consumed inside the shared catalog fold. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyInputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateImperativeCatalogReady
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {Records : Type v}
  (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : Readiness protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)
  (program : Program) (origin : StaticOrigin values ambient registry faults)

/-- Predicates and genuine site/transfer receipts at this exact static origin. -/
structure Inputs where
  facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop
  headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop
  exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop
  loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop
  initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop
  assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop
  snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop
  sites : StaticSites facts headFacts exprFacts program origin.function.evidence origin.function.source
  initializerSites : InitializerSites initializerFacts loopFacts origin.function.source
  assignmentSites : AssignmentSites headFacts assignmentFacts snapshotFacts origin.function.source
  transfers : AllocationTransfers protocol readiness stateBindings origin.function.source
  snapshots : SnapshotTransfers protocol readiness origin.validity snapshotFacts program origin.function.evidence origin.function.source

variable (functions : FunctionModel values.checked.catalog ambient)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (inputs : Inputs protocol readiness stateBindings program origin) (budget : Nat)

/-- Finite source producers; no completed catalog or body law is stored. -/
structure PreservingKits : Prop where
  assignments : ∀ context, origin.validity context → Assignment.AssignmentPrefixPreservesAt protocol readiness inputs.assignmentFacts functions
      (registry := registry) program origin.function.evidence origin.function.source (origin.certificates context) context origin.administrative budget
  assignmentFaults : ∀ context, origin.validity context → Assignment.AssignmentFaultPreservesAt protocol readiness inputs.assignmentFacts functions
      (registry := registry) program origin.function.evidence origin.function.source (origin.certificates context) context origin.administrative faults budget
  headFor : PreservingHeads protocol readiness conditionGate inputs.headFacts functions program origin.function.evidence origin.validity budget
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax) (certificates := origin.certificates) (administrative := origin.administrative)
      (registry := registry) (faults := faults)
      (RecursiveNamedImperativeFor.Stateful.WithReady.PreservesAtWith protocol readiness conditionGate inputs.facts inputs.loopFacts inputs.initializerFacts
        (validity := origin.validity) (diagnosticPolicy := origin.diagnosticPolicy) (certificates := origin.certificates) (layouts := origin.layouts)
        (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
        (source := origin.function.source) (administrative := origin.administrative) (registry := registry) (faults := faults)
        functions program origin.function.evidence budget)
  loopFor : PreservingLoops protocol readiness conditionGate inputs.loopFacts functions program origin.function.evidence origin.validity budget
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax) (certificates := origin.certificates) (administrative := origin.administrative)
      (registry := registry) (faults := faults)
      (RecursiveNamedImperativeFor.Stateful.WithReady.PreservesAtWith protocol readiness conditionGate inputs.facts inputs.loopFacts inputs.initializerFacts
        (validity := origin.validity) (diagnosticPolicy := origin.diagnosticPolicy) (certificates := origin.certificates) (layouts := origin.layouts)
        (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
        (source := origin.function.source) (administrative := origin.administrative) (registry := registry) (faults := faults)
        functions program origin.function.evidence budget) origin.diagnosticPolicy

/-- Finite native producers use the same real head and loop child goals. -/
structure ReflectingKits : Prop where
  assignments : ∀ context, origin.validity context → Assignment.AssignmentReflectsAt protocol readiness inputs.assignmentFacts functions
      (registry := registry) program origin.function.evidence origin.function.source (origin.certificates context) context origin.administrative faults budget
  headFor : ReflectingHeads protocol readiness conditionGate inputs.headFacts functions program origin.function.evidence origin.validity budget
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax) (certificates := origin.certificates) (administrative := origin.administrative)
      (registry := registry) (faults := faults)
      (RecursiveNamedImperativeFor.Stateful.WithReady.ReflectsAtWith protocol readiness conditionGate inputs.facts inputs.loopFacts inputs.initializerFacts
        (validity := origin.validity) (diagnosticPolicy := origin.diagnosticPolicy) (certificates := origin.certificates) (layouts := origin.layouts)
        (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
        (source := origin.function.source) (administrative := origin.administrative) (registry := registry) (faults := faults)
        functions program origin.function.evidence budget)
  loopFor : ReflectingLoops protocol readiness conditionGate inputs.loopFacts functions program origin.function.evidence origin.validity budget
      (layouts := origin.layouts) (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
      (source := origin.function.source) (expressionSyntax := origin.expressionSyntax) (certificates := origin.certificates) (administrative := origin.administrative)
      (registry := registry) (faults := faults)
      (RecursiveNamedImperativeFor.Stateful.WithReady.ReflectsAtWith protocol readiness conditionGate inputs.facts inputs.loopFacts inputs.initializerFacts
        (validity := origin.validity) (diagnosticPolicy := origin.diagnosticPolicy) (certificates := origin.certificates) (layouts := origin.layouts)
        (owner := origin.owner) (active := origin.active) (frame := origin.frameLayout) (globals := origin.globals) (onError := origin.onError)
        (source := origin.function.source) (administrative := origin.administrative) (registry := registry) (faults := faults)
        functions program origin.function.evidence budget) origin.diagnosticPolicy

/-- The compatibility specialization requests no additional proof facets. -/
def Inputs.trivial : Inputs protocol (Readiness.trivial protocol) stateBindings program origin where
  facts := fun _ _ _ _ => True
  headFacts := fun _ _ _ => True
  exprFacts := fun _ _ _ => True
  loopFacts := fun _ _ _ _ _ => True
  initializerFacts := fun _ _ _ _ _ _ => True
  assignmentFacts := fun _ _ _ _ => True
  snapshotFacts := fun _ _ => True
  sites := StaticSites.trivial program origin.function.evidence origin.function.source
  initializerSites := InitializerSites.trivial origin.function.source
  assignmentSites := AssignmentSites.trivial origin.function.source
  transfers := AllocationTransfers.trivial protocol stateBindings origin.function.source
  snapshots := ProtectedForHeader.Stateful.WithReady.SnapshotTransfers.trivial protocol origin.validity program origin.function.evidence origin.function.source

section Compatibility
variable (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol origin.layouts origin.frameLayout
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, conditionGate location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)

include extension faithful observations producer acquire stateTransport in
/-- Compatibility kits delegate the original finite producers. -/
theorem PreservingKits.trivial [FunctionCalls.FaultTokens faults]
    (expressions : ∀ context, origin.validity context → RecursiveNamedHeaderContracts.AtMost budget (fun child =>
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context origin.function.evidence origin.function.source (origin.certificates context) faults child)) :
    PreservingKits protocol (Readiness.trivial protocol) stateBindings program origin functions conditionGate
      (Inputs.trivial protocol stateBindings program origin) budget := by
  have assignments := RecursiveNamedImperativeFor.Stateful.WithReady.assignment_prefix_uniform
    (administrative := origin.administrative) (functions := functions) (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (stateTransport := stateTransport) (validity := origin.validity)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := expressions)
  have assignmentFaults := RecursiveNamedImperativeFor.Stateful.WithReady.assignment_fault_uniform
    (administrative := origin.administrative) (functions := functions) (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (stateTransport := stateTransport) (validity := origin.validity)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := expressions)
  exact {
    assignments := (fun context valid => ProtectedForHeader.Stateful.WithReady.assignment_prefix_trivial protocol functions program origin.function.evidence
      origin.function.source (origin.certificates context) context origin.administrative budget (assignments context valid))
    assignmentFaults := (fun context valid => ProtectedForHeader.Stateful.WithReady.assignment_fault_trivial protocol functions program origin.function.evidence
      origin.function.source (origin.certificates context) context origin.administrative faults budget (assignmentFaults context valid))
    headFor := (RecursiveNamedImperativeFor.Stateful.WithReady.preserving_heads_trivial
    (administrative := origin.administrative) (functions := functions) (definitions := origin.definitions) (registered := origin.registered)
    (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (producer := producer) (conditionGate := conditionGate) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := origin.validity) (extend := origin.extend) (solved := origin.solved)
    (faithful := faithful) (observations := observations) (budget := budget) (runtimeOf := fun _ valid => origin.runtimeOf valid) (meaningMost := expressions)
    origin.diagnosticPolicy origin.body.unique)
    loopFor := (RecursiveNamedImperativeFor.Stateful.WithReady.preserving_loops_trivial
    (administrative := origin.administrative) (functions := functions) (definitions := origin.definitions) (registered := origin.registered)
    (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (producer := producer) (conditionGate := conditionGate) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := origin.validity) (extend := origin.extend) (solved := origin.solved)
    (faithful := faithful) (observations := observations) (budget := budget) (meaningMost := expressions) origin.diagnosticPolicy origin.body.unique)
  }

include extension faithful observations functionTypes producer acquire stateTransport in
/-- Compatibility kits delegate the original finite producers. -/
theorem ReflectingKits.trivial [FunctionCalls.FaultTokens faults]
    (expressions : ∀ context, origin.validity context → RecursiveNamedBoundedContracts.Below budget (fun child =>
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context origin.function.evidence origin.function.source (origin.certificates context) faults child)) :
    ReflectingKits protocol (Readiness.trivial protocol) stateBindings program origin functions conditionGate
      (Inputs.trivial protocol stateBindings program origin) budget := by
  have assignments := RecursiveNamedImperativeFor.Stateful.WithReady.assignment_reflection_uniform
    (administrative := origin.administrative) (functions := functions) (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (stateTransport := stateTransport) (validity := origin.validity)
    (faithful := faithful) (observations := observations) (budget := budget) (reflection := expressions) functionTypes
  exact {
    assignments := (fun context valid => ProtectedForHeader.Stateful.WithReady.assignment_reflection_trivial protocol functions program origin.function.evidence
      origin.function.source (origin.certificates context) context origin.administrative faults budget (assignments context valid))
    headFor := (RecursiveNamedImperativeFor.Stateful.WithReady.reflecting_heads_trivial
    (administrative := origin.administrative) (functions := functions) (definitions := origin.definitions) (registered := origin.registered)
    (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (producer := producer) (conditionGate := conditionGate) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := origin.validity) (extend := origin.extend) (solved := origin.solved)
    (faithful := faithful) (observations := observations) (budget := budget) (runtimeOf := fun _ valid => origin.runtimeOf valid) (reflection := expressions)
    origin.diagnosticPolicy functionTypes origin.body.unique)
    loopFor := (RecursiveNamedImperativeFor.Stateful.WithReady.reflecting_loops_trivial
    (administrative := origin.administrative) (functions := functions) (definitions := origin.definitions) (registered := origin.registered)
    (extension := extension) (program := program) (evidence := origin.function.evidence)
    (protocol := protocol) (producer := producer) (conditionGate := conditionGate) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := origin.validity) (extend := origin.extend) (solved := origin.solved)
    (faithful := faithful) (observations := observations) (budget := budget) (reflection := expressions) origin.diagnosticPolicy functionTypes origin.body.unique)
  }

end Compatibility

section ExpressionCompatibility
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {context : SourceSemantics.Context} {source : TypedSource} {evidence : Dynamic.EvidenceEnvironment}
  {expressionFaults : FunctionCalls.FaultRep}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (certificate : GenericExpressionMeaning.Certificate)

/-- Forget only the trivial input and output facets at the same actual post. -/
theorem expression_preserves_forget_true {size : Nat}
    (meaning : ExpressionPreservesAt protocol (Readiness.trivial protocol) program evidence model (fun _ _ _ => True)
      certificate (source := source) (context := context) (faults := expressionFaults) size) :
    ProtectedStateTransition.PreservesAt protocol model program context evidence source certificate expressionFaults size := by
  intro scope id lowered certified node found mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, _post⟩ :=
    meaning certified found trivial environments heaps locals agrees actualTyped initial trivial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩

/-- The reflected Source grade and actual post are retained verbatim. -/
theorem expression_reflects_forget_true {size : Nat}
    (meaning : ExpressionReflectsAt protocol (Readiness.trivial protocol) program evidence model (fun _ _ _ => True)
      certificate (source := source) (context := context) (faults := expressionFaults) size) :
    ProtectedStateTransition.ReflectsAt protocol model program context evidence source certificate expressionFaults size := by
  intro scope id lowered certified node found mapping world administrativeContext environment canonical actual actualContext before store finalStore ξ value environments heaps locals agrees actualTyped initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, _post⟩ :=
    meaning certified found trivial environments heaps locals agrees actualTyped initial trivial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, related⟩
end ExpressionCompatibility

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning
/-! One source induction and one native induction close a family of actual
static bodies. The expression interface is internal to the enclosing mutual
proof and receives only strictly smaller original body obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins

private theorem close_sized {ι : Type} (family : ι → Nat → Prop)
    (step : ∀ size, (∀ callee, RecursiveNamedBoundedContracts.Below size (family callee)) →
      ∀ i, family i size) (size : Nat) : ∀ i, family i size := by
  induction size using Nat.strongRecOn with
  | ind size ih => exact step size (fun callee smaller strict => ih smaller strict callee)

/-- Reuse the existing measured closer for a family with its own static receipts.
Each step receives only strictly smaller callee obligations. -/
theorem close_family {ι : Type} (family : ι → Nat → Prop)
    (step : ∀ size, (∀ callee, RecursiveNamedBoundedContracts.Below size (family callee)) →
      ∀ i, family i size) (size : Nat) : ∀ i, family i size :=
  close_sized family step size

variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ι : Type} (origins : ι → Origin values ambient registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include extension faithful observations in
/-- Source children may use the current budget; callee bodies are strict. -/
theorem preserves_at [FunctionCalls.FaultTokens faults]
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget (PreservesAt functions program (origins callee))) →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults (origins i).protectedEntry)
    (size : Nat) : ∀ i, PreservesAt functions program (origins i) size := by
  apply close_sized (fun i => PreservesAt functions program (origins i))
  intro size below i entry outcome after trace
  have children : ∀ context, (origins i).validity context → RecursiveNamedHeaderContracts.AtMost size
      (fun child => RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context
        (origins i).function.evidence (origins i).function.source ((origins i).certificates context)
        faults (origins i).protectedEntry) := by
    intro context valid child within
    exact expressionMeaning i context valid size child within below
  exact (origins i).body.preserves_sized functions (origins i).definitions (origins i).registered extension
    program faithful observations (origins i).escapedFault (origins i).transport (origins i).binders
    (origins i).extend (origins i).runtimeOf size size (Nat.le_refl size) children
    entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped entry.reference entry.read
    entry.unmapped entry.installed trace

include extension faithful observations functionTypes in
/-- Native finish inversion selects original strict children. Reflection
returns the source grade without a preservation or source-trace premise. -/
theorem reflects_at [FunctionCalls.FaultTokens faults]
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget (ReflectsAt functions program (origins callee))) →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults (origins i).protectedEntry)
    (size : Nat) : ∀ i, ReflectsAt functions program (origins i) size := by
  apply close_sized (fun i => ReflectsAt functions program (origins i))
  intro size below i entry value finalStore completed
  have children : ∀ context, (origins i).validity context → RecursiveNamedBoundedContracts.Below size
      (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context
        (origins i).function.evidence (origins i).function.source ((origins i).certificates context)
        faults (origins i).protectedEntry) := by
    intro context valid child smaller
    exact expressionMeaning i context valid size child (Nat.le_of_lt smaller)
      below
  exact (origins i).body.reflects_sized functions (origins i).definitions (origins i).registered extension
    program faithful observations functionTypes (origins i).escapedFault (origins i).transport (origins i).binders
    (origins i).extend (origins i).runtimeOf size size (Nat.le_refl size) children
    entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped entry.reference entry.read
    entry.unmapped entry.installed completed

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins
open CallableRuntimeBodyReadyInputs
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ι : Type} {Records : ι → Type v}
  (origins : ι → StaticOrigin values ambient registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (protocols : ∀ i, ProtectedStateTransition.Protocol.{u, v} (Records i))
  (conditionGate : ι → Location → CallableIndexedHistory.NativeFrame → Prop)
  (producers : ∀ i, ProtectedStateTransition.MarkedAllocation.Producer (protocols i)
    (origins i).layouts (origins i).frameLayout (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ i location native, conditionGate i location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producers i).toOrdinary location native)
  (stateTransport : ∀ i, ProtectedStateTransition.AdministrativeTransport (protocols i))
  (stateBindings : ∀ i, ProtectedStateTransition.Bindings (protocols i))

  (readinesses : ∀ i, Readiness (protocols i))
  (inputs : ∀ i, Inputs (protocols i) (readinesses i) (stateBindings i) program (origins i))

include producers acquire stateTransport stateBindings inputs in
/-- The original measured family closes actual ready entries through the same kernel. -/
theorem preserves_at
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.PreservesAt (protocols callee) (readinesses callee) (conditionGate callee) (inputs callee).facts functions program (origins callee))) →
      ExpressionPreservesAt (protocols i) (readinesses i) program (origins i).function.evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) (inputs i).exprFacts ((origins i).certificates context)
        (context := context) (source := (origins i).function.source) (faults := faults) child)
    (kitsFor : ∀ i budget,
      (∀ context, (origins i).validity context → RecursiveNamedHeaderContracts.AtMost budget (fun child =>
        ExpressionPreservesAt (protocols i) (readinesses i) program (origins i).function.evidence
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) (inputs i).exprFacts ((origins i).certificates context)
          (context := context) (source := (origins i).function.source) (faults := faults) child)) →
      PreservingKits (protocols i) (readinesses i) (stateBindings i) program (origins i) functions (conditionGate i) (inputs i) budget)
    (size : Nat) : ∀ i,
    CallableRuntimeBodyReadyOrigins.PreservesAt (protocols i) (readinesses i) (conditionGate i) (inputs i).facts functions program (origins i) size := by
  apply close_sized (fun i => CallableRuntimeBodyReadyOrigins.PreservesAt (protocols i) (readinesses i)
    (conditionGate i) (inputs i).facts functions program (origins i))
  intro size below i entry outcome after trace
  have children : ∀ context, (origins i).validity context → RecursiveNamedHeaderContracts.AtMost size
      (fun child => ExpressionPreservesAt (protocols i) (readinesses i) program (origins i).function.evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) (inputs i).exprFacts ((origins i).certificates context)
        (context := context) (source := (origins i).function.source) (faults := faults) child) := by
    intro context valid child within
    exact expressionMeaning i context valid size child within below
  have kit := kitsFor i size children
  exact CallableRuntimeBodyKernel.Stateful.WithReady.BodyFor.preserves_sized
    (body := (origins i).body) (functions := functions) (definitions := (origins i).definitions)
    (registered := (origins i).registered) (program := program)
    (escapedFault := (origins i).escapedFault) (extend := (origins i).extend)
    (protocol := protocols i) (producer := producers i) (conditionGate := conditionGate i)
    (acquire := acquire i) (stateTransport := stateTransport i) (stateBindings := stateBindings i)
    (readiness := readinesses i) (facts := (inputs i).facts) (headFacts := (inputs i).headFacts)
    (exprFacts := (inputs i).exprFacts) (loopFacts := (inputs i).loopFacts) (initializerFacts := (inputs i).initializerFacts)
    (assignmentFacts := (inputs i).assignmentFacts) (snapshotFacts := (inputs i).snapshotFacts)
    (sites := (inputs i).sites) (initializerSites := (inputs i).initializerSites) (assignmentSites := (inputs i).assignmentSites)
    (transfers := (inputs i).transfers) (snapshots := (inputs i).snapshots)
    size size (Nat.le_refl size) kit.assignments kit.assignmentFaults kit.headFor kit.loopFor children entry.bodyFacts
    entry.original.environments entry.original.heaps entry.original.locals entry.original.lookups entry.original.actualTyped
    entry.original.reference entry.original.read entry.original.unmapped entry.original.initial entry.original.gate entry.ready trace

include producers acquire stateTransport stateBindings inputs in
/-- The original measured family closes actual ready entries through the same kernel. -/
theorem reflects_at
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyReadyOrigins.ReflectsAt (protocols callee) (readinesses callee) (conditionGate callee) (inputs callee).facts functions program (origins callee))) →
      ExpressionReflectsAt (protocols i) (readinesses i) program (origins i).function.evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) (inputs i).exprFacts ((origins i).certificates context)
        (context := context) (source := (origins i).function.source) (faults := faults) child)
    (kitsFor : ∀ i budget,
      (∀ context, (origins i).validity context → RecursiveNamedBoundedContracts.Below budget (fun child =>
        ExpressionReflectsAt (protocols i) (readinesses i) program (origins i).function.evidence
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) (inputs i).exprFacts ((origins i).certificates context)
          (context := context) (source := (origins i).function.source) (faults := faults) child)) →
      ReflectingKits (protocols i) (readinesses i) (stateBindings i) program (origins i) functions (conditionGate i) (inputs i) budget)
    (size : Nat) : ∀ i,
    CallableRuntimeBodyReadyOrigins.ReflectsAt (protocols i) (readinesses i) (conditionGate i) (inputs i).facts functions program (origins i) size := by
  apply close_sized (fun i => CallableRuntimeBodyReadyOrigins.ReflectsAt (protocols i) (readinesses i)
    (conditionGate i) (inputs i).facts functions program (origins i))
  intro size below i entry value finalStore completed
  have children : ∀ context, (origins i).validity context → RecursiveNamedBoundedContracts.Below size
      (fun child => ExpressionReflectsAt (protocols i) (readinesses i) program (origins i).function.evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) (inputs i).exprFacts ((origins i).certificates context)
        (context := context) (source := (origins i).function.source) (faults := faults) child) := by
    intro context valid child smaller
    exact expressionMeaning i context valid size child (Nat.le_of_lt smaller) below
  have kit := kitsFor i size children
  exact CallableRuntimeBodyKernel.Stateful.WithReady.BodyFor.reflects_sized
    (body := (origins i).body) (functions := functions) (definitions := (origins i).definitions)
    (registered := (origins i).registered) (program := program)
    (escapedFault := (origins i).escapedFault) (extend := (origins i).extend)
    (protocol := protocols i) (producer := producers i) (conditionGate := conditionGate i)
    (acquire := acquire i) (stateTransport := stateTransport i) (stateBindings := stateBindings i)
    (readiness := readinesses i) (facts := (inputs i).facts) (headFacts := (inputs i).headFacts)
    (exprFacts := (inputs i).exprFacts) (loopFacts := (inputs i).loopFacts) (initializerFacts := (inputs i).initializerFacts)
    (assignmentFacts := (inputs i).assignmentFacts) (snapshotFacts := (inputs i).snapshotFacts)
    (sites := (inputs i).sites) (initializerSites := (inputs i).initializerSites) (assignmentSites := (inputs i).assignmentSites)
    (transfers := (inputs i).transfers) (snapshots := (inputs i).snapshots)
    size size (Nat.le_refl size) kit.assignments kit.headFor kit.loopFor children entry.bodyFacts
    entry.original.environments entry.original.heaps entry.original.locals entry.original.lookups entry.original.actualTyped
    entry.original.reference entry.original.read entry.original.unmapped entry.original.initial entry.original.gate entry.ready completed

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning.Stateful.WithReady.Family

namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning.Stateful.Family
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ι : Type} {Records : ι → Type v}
  (origins : ι → StaticOrigin values ambient registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (protocols : ∀ i, ProtectedStateTransition.Protocol.{u, v} (Records i))
  (conditionGate : ι → Location → CallableIndexedHistory.NativeFrame → Prop)
  (producers : ∀ i, ProtectedStateTransition.MarkedAllocation.Producer (protocols i)
    (origins i).layouts (origins i).frameLayout (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ i location native, conditionGate i location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producers i).toOrdinary location native)
  (stateTransport : ∀ i, ProtectedStateTransition.AdministrativeTransport (protocols i))
  (stateBindings : ∀ i, ProtectedStateTransition.Bindings (protocols i))

include extension faithful observations producers acquire stateTransport stateBindings in
/-- Each genuine origin uses its own state protocol and record observation.
The same measured fold supplies only strictly smaller actual callee meanings. -/
theorem preserves_at [FunctionCalls.FaultTokens faults]
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyOrigins.Stateful.PreservesAt (protocols callee) (conditionGate callee) functions program (origins callee))) →
      ProtectedStateTransition.PreservesAt (protocols i) (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults child)
    (size : Nat) : ∀ i,
    CallableRuntimeBodyOrigins.Stateful.PreservesAt (protocols i) (conditionGate i) functions program (origins i) size := by
  have closed := WithReady.Family.preserves_at
    (origins := origins) (functions := functions) (program := program)
    (protocols := protocols) (conditionGate := conditionGate) (producers := producers) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readinesses := fun i => RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial (protocols i))
    (inputs := fun i => CallableRuntimeBodyReadyInputs.Inputs.trivial (protocols i) (stateBindings i) program (origins i))
    (expressionMeaning := fun i context valid budget child within below =>
      RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt.of_true
        (protocol := protocols i) (program := program) (evidence := (origins i).function.evidence)
        (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
        (certificate := (origins i).certificates context)
        (expressionMeaning i context valid budget child within (fun callee smaller strict =>
          CallableRuntimeBodyReadyOrigins.PreservesAt.forget_trivial (below callee smaller strict))))
    (kitsFor := fun i budget children => CallableRuntimeBodyReadyInputs.PreservingKits.trivial
      (protocol := protocols i) (stateBindings := stateBindings i) (program := program) (origin := origins i)
      (functions := functions) (conditionGate := conditionGate i) (budget := budget)
      (extension := extension) (faithful := faithful) (observations := observations)
      (producer := producers i) (acquire := acquire i) (stateTransport := stateTransport i)
      (fun context valid child within => CallableRuntimeBodyReadyInputs.expression_preserves_forget_true
        (protocol := protocols i) (program := program)
        (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
        (certificate := (origins i).certificates context) (children context valid child within))) size
  intro i
  exact CallableRuntimeBodyReadyOrigins.PreservesAt.forget_trivial (closed i)

include extension faithful observations functionTypes producers acquire stateTransport stateBindings in
/-- Original native completions choose strict callees at their own protocols.
The same measured closer returns independent source grades and actual posts. -/
theorem reflects_at [FunctionCalls.FaultTokens faults]
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyOrigins.Stateful.ReflectsAt (protocols callee) (conditionGate callee) functions program (origins callee))) →
      ProtectedStateTransition.ReflectsAt (protocols i) (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults child)
    (size : Nat) : ∀ i,
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt (protocols i) (conditionGate i) functions program (origins i) size := by
  have closed := WithReady.Family.reflects_at
    (origins := origins) (functions := functions) (program := program)
    (protocols := protocols) (conditionGate := conditionGate) (producers := producers) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readinesses := fun i => RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial (protocols i))
    (inputs := fun i => CallableRuntimeBodyReadyInputs.Inputs.trivial (protocols i) (stateBindings i) program (origins i))
    (expressionMeaning := fun i context valid budget child within below =>
      RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt.of_true
        (protocol := protocols i) (program := program) (evidence := (origins i).function.evidence)
        (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
        (certificate := (origins i).certificates context)
        (expressionMeaning i context valid budget child within (fun callee smaller strict =>
          CallableRuntimeBodyReadyOrigins.ReflectsAt.forget_trivial (below callee smaller strict))))
    (kitsFor := fun i budget children => CallableRuntimeBodyReadyInputs.ReflectingKits.trivial
      (protocol := protocols i) (stateBindings := stateBindings i) (program := program) (origin := origins i)
      (functions := functions) (conditionGate := conditionGate i) (budget := budget)
      (extension := extension) (faithful := faithful) (observations := observations)
      (functionTypes := functionTypes)
      (producer := producers i) (acquire := acquire i) (stateTransport := stateTransport i)
      (fun context valid child within => CallableRuntimeBodyReadyInputs.expression_reflects_forget_true
        (protocol := protocols i) (program := program)
        (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
        (certificate := (origins i).certificates context) (children context valid child within))) size
  intro i
  exact CallableRuntimeBodyReadyOrigins.ReflectsAt.forget_trivial (closed i)

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning.Stateful.Family

namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {ι : Type} {Records : Type v}
  (origins : ι → StaticOrigin values ambient registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : ι → Location → CallableIndexedHistory.NativeFrame → Prop)
  (producers : ∀ i, ProtectedStateTransition.MarkedAllocation.Producer protocol
    (origins i).layouts (origins i).frameLayout (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ i location native, conditionGate i location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producers i).toOrdinary location native)
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)

include extension faithful observations producers acquire stateTransport stateBindings in
/-- The actual source family closes through the shared measured fold. Its
expression interface receives only strictly smaller actual callee meanings. -/
theorem preserves_at [FunctionCalls.FaultTokens faults]
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyOrigins.Stateful.PreservesAt protocol (conditionGate callee) functions program (origins callee))) →
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults child)
    (size : Nat) : ∀ i,
    CallableRuntimeBodyOrigins.Stateful.PreservesAt protocol (conditionGate i) functions program (origins i) size := by
  exact Family.preserves_at origins functions extension program faithful observations
    (fun _ => protocol) conditionGate producers acquire
    (fun _ => stateTransport) (fun _ => stateBindings) expressionMeaning size

include extension faithful observations functionTypes producers acquire stateTransport stateBindings in
/-- The actual native family consumes original completions and returns
independently graded source traces through the same measured closer. -/
theorem reflects_at [FunctionCalls.FaultTokens faults]
    (expressionMeaning : ∀ i context, (origins i).validity context → ∀ budget child, child ≤ budget →
      (∀ callee, RecursiveNamedBoundedContracts.Below budget
        (CallableRuntimeBodyOrigins.Stateful.ReflectsAt protocol (conditionGate callee) functions program (origins callee))) →
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context (origins i).function.evidence (origins i).function.source
        ((origins i).certificates context) faults child)
    (size : Nat) : ∀ i,
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt protocol (conditionGate i) functions program (origins i) size := by
  exact Family.reflects_at origins functions extension program faithful observations functionTypes
    (fun _ => protocol) conditionGate producers acquire
    (fun _ => stateTransport) (fun _ => stateBindings) expressionMeaning size

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning.Stateful
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyEntryContracts
/-! Pointwise contracts at one complete actual body entry. They keep every
original semantic field and the actual reached state, without quantifying over
unrelated canonical captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyEntryContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
  {conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop}
  (functions : FunctionModel values.checked.catalog ambient) (program : Program)
  {origin : CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults}

/-- Source meaning at the complete actual parameter entry. -/
def PreservesAt (entry : CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate origin functions)
    (size : Nat) : Prop :=
  ∀ {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace program size origin.function origin.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actual entry.store (origin.code.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.Transition protocol entry.initial
        ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- Original native completion at that same actual parameter entry. -/
def ReflectsAt (entry : CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate origin functions)
    (size : Nat) : Prop :=
  ∀ {value : Value} {finalStore : Store},
    EvaluationSize size entry.actual entry.store (origin.code.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize origin.function origin.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.Transition protocol entry.initial
        ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- The retained uniform body contract specializes to the actual entry. -/
theorem preserves_of_uniform {size : Nat}
    (meaning : CallableRuntimeBodyOrigins.Stateful.PreservesAt protocol conditionGate functions program origin size)
    (entry : CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate origin functions) :
    PreservesAt functions program entry size := meaning entry

/-- Native specialization keeps the independently reconstructed Source grade. -/
theorem reflects_of_uniform {size : Nat}
    (meaning : CallableRuntimeBodyOrigins.Stateful.ReflectsAt protocol conditionGate functions program origin size)
    (entry : CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate origin functions) :
    ReflectsAt functions program entry size := meaning entry

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyEntryContracts
end

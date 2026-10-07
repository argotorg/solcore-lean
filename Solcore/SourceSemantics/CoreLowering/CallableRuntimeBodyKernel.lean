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

include body definitions registered observations escapedFault producer acquire stateTransport stateBindings extend sites initializerSites assignmentSites transfers snapshots in
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
    (budget := budget) (observations := observations) (meaningMost := expressions)
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

include body definitions registered observations escapedFault producer acquire stateTransport stateBindings extend sites initializerSites assignmentSites transfers snapshots in
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
    (budget := budget) (reflection := expressions) (observations := observations)
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
    (validity := validity) (extend := extend) (observations := observations) (escapedFault := escapedFault)
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
  have assignments := RecursiveNamedImperativeFor.Stateful.WithReady.assignment_reflection_uniform
    (administrative := administrative) (functions := functions) (extension := extension) (program := program) (evidence := function.evidence)
    (protocol := protocol) (stateTransport := stateTransport) (validity := validity)
    (faithful := faithful) (observations := observations) (budget := budget) (reflection := expressions) functionTypes
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ :=
    WithReady.BodyFor.reflects_sized
    (body := body) (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (protocol := protocol) (conditionGate := conditionGate) (producer := producer)
    (acquire := acquire) (stateTransport := stateTransport) (stateBindings := stateBindings)
    (validity := validity) (extend := extend) (observations := observations) (escapedFault := escapedFault)
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

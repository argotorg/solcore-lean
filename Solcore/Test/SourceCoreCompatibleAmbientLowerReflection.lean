import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLowerReflection

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! An actual checked compatible lowerer result and its completed native run
recover an independent whole assignment outcome under the indexed artifact's
full definition table. The terminal Unit continuation is discharged here, so
heap correspondence reaches the actual final store. Universal child meaning,
retained source typing and diagnostic interpretation remain explicit; no source
execution, path layout, or particular child/helper run is a premise. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleAmbientLowerReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap GenericExpressionMeaning CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces

inductive Outcome (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (place : PlaceResolution)
    (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) : Value → Dynamic.Heap → Prop where
  | succeeded {updated : Dynamic.Value} {after : Dynamic.Heap}
      (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after) : Outcome program context evidence source faults environment before place operator rhs
          (.inRight .word .unit) after
  | failed {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
      (tokenRep : faults reason token) : Outcome program context evidence source faults environment before place operator rhs
        (.inLeft .unit (.word token)) after

/-- The real seven-slot continuation is pure terminal Unit, so the reflected
write heap is the final native heap; it is not mistaken for a later heap. -/
theorem terminal {checked : Checked} {ambient : AmbientDefinitions checked.catalog.definitions}
    {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {faults : FaultRep} {place : PlaceResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before : Dynamic.Heap} {store finalStore : Store}
    {mapping : LocationMap} {world : StoreTyping} {result : Value}
    (reflected : CompatiblePlaceTailReflection.Result checked registry functions program context evidence source faults place operator rhs
      environment coreEnvironment before store mapping world (LanguageResult.success .unit) .unit result finalStore) :
    ∃ after finalMap finalWorld,
      Outcome program context evidence source faults environment before place operator rhs result after ∧
      CompatibleAmbientHeap.HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases reflected with
  | fault trace resultEq tokenRep heaps maps worlds frame metadata =>
    subst result
    exact ⟨_, _, _, .failed trace tokenRep, heaps, maps, worlds, frame, metadata⟩
  | committed trace heaps maps worlds frame metadata length continuation =>
    simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] at continuation
    cases continuation with
    | inRight valueEvaluated =>
      cases valueEvaluated
      exact ⟨_, _, _, .succeeded trace, heaps, maps, worlds, frame, metadata⟩

/-- `lowerChecked` supplies the actual compiler equation and native typing.
A completed run supplies the sole execution premise; independent source traces
and every final heap invariant are outputs. -/
theorem checked_run_reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared compilation.checked)
    {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel compilation.checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {assignment : AssignmentResolution}
    {administrativeContext : Core.Context} {expression : ExpressionLowerer} {fuel : Nat}
    {rhs : ExpressionId} {operator : Syntax.ValueAssignOp}
    {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compilation.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (nonempty : assignment.target.projections ≠ [])
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code.expression
        (LanguageResult.resultType code.type) artifact.layouts.definitions)
    {certified : Certified artifact.layouts.definitions (SourceCoreLocalCell.coreContext scope ++ administrativeContext) .unit}
    (accepted : lowerChecked compilation compilation.checked.signatures expression fuel source scope site assignment operator (some rhs) .unit
      (LanguageResult.success .unit) reasonAt invalid invalidOperand missing artifact.layouts.definitions
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) = .ok certified)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {prepared root resolved reason token count},
      (∃ route, describe compilation compilation.checked.signatures source site assignment = .ok route ∧
        prepare compilation fuel route invalid missing = .ok prepared) →
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) invalid)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {result : Value} {runtimeFuel : Nat}
    (environments : DataHeap.EnvRepresents (definitions := artifact.layouts.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment coreEnvironment)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (completed : runStateful runtimeFuel (.initial certified.expression coreEnvironment store) = .done result finalStore) :
    ∃ after finalMap finalWorld,
      Outcome program context evidence source faults environment before assignment.target operator rhs result after ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  apply terminal
  exact CompatiblePlaceLowerReflection.reflects unique signatures sourceTyped rightTyped rootTyped nonempty extract
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) certified.typed registryExtension meaning functionTypes
    faithful observations missingTokens invalidTokens profile environments heaps locals (runStateful_evaluation_sound completed)

end Tests.SourceCoreCompatibleAmbientLowerReflection

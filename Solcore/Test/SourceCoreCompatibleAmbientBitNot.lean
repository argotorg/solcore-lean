import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotLowerReflection
import Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotLowering

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! RHS-free numeric assignments under an actual indexed artifact's frame and
marker definitions. Index children retain a universal induction premise, while
bare roots require no child premise. The emitted Unit RHS is administrative.
Integer is a retained-IR profile; source compound admission stays Word-only. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleAmbientBitNot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap GenericExpressionMeaning CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces

inductive Outcome (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (place : PlaceResolution) : Value → Dynamic.Heap → Prop where
  | succeeded {updated : Dynamic.Value} {after : Dynamic.Heap}
      (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
        environment before place updated after) : Outcome program context evidence source faults environment before place
          (.inRight .word .unit) after
  | failed {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after)
      (tokenRep : faults reason token) : Outcome program context evidence source faults environment before place
        (.inLeft .unit (.word token)) after

/-- The real seven-slot continuation is pure terminal Unit, so the reflected
write heap is the final native heap; it is not mistaken for a later heap. -/
theorem terminal {checked : Checked} {ambient : AmbientDefinitions checked.catalog.definitions}
    {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog ambient}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {faults : FaultRep} {place : PlaceResolution}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before : Dynamic.Heap} {store finalStore : Store}
    {mapping : LocationMap} {world : StoreTyping} {result : Value}
    (reflected : CompatiblePlaceBitNotMeaning.Result checked registry functions program context evidence source faults place
      environment coreEnvironment before store mapping world (LanguageResult.success .unit) .unit result finalStore) :
    ∃ after finalMap finalWorld,
      Outcome program context evidence source faults environment before place result after ∧
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
theorem checked_path_run_reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared compilation.checked)
    {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel compilation.checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {assignment : AssignmentResolution}
    {administrativeContext : Core.Context} {expression : ExpressionLowerer} {fuel : Nat}
    {operator : Syntax.ValueAssignOp}
    {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = compilation.checked.signatures)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (nonempty : assignment.target.projections ≠ [])
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code)
    {certified : Certified artifact.layouts.definitions (SourceCoreLocalCell.coreContext scope ++ administrativeContext) .unit}
    (accepted : lowerChecked compilation compilation.checked.signatures expression fuel source scope site assignment operator none .unit
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
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {result : Value} {runtimeFuel : Nat}
    (environments : DataHeap.EnvRepresents (definitions := artifact.layouts.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment coreEnvironment)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (completed : runStateful runtimeFuel (.initial certified.expression coreEnvironment store) = .done result finalStore) :
    ∃ after finalMap finalWorld,
      Outcome program context evidence source faults environment before assignment.target result after ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  apply terminal
  exact CompatiblePlaceBitNotLowerReflection.reflects_numeric unique signatures sourceTyped rootTyped nonempty extract
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) certified.typed registryExtension meaning functionTypes
    faithful observations missingTokens invalidTokens profile environments heaps locals (runStateful_evaluation_sound completed)

section Bare
variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  (artifact : SourceCoreCallableIndexedPrograms.Prepared compilation.checked)
  {registry : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel compilation.checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
  {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
  {faults : FaultRep} {assignment : AssignmentResolution} {administrativeContext : Core.Context}
  {expression : ExpressionLowerer} {fuel : Nat} {operator : Syntax.ValueAssignOp}
  {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
  (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
    WritableLocal context assignment.target.root binder.scheme.body)
  (bare : assignment.target.projections = [])
  (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
    SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
  {identities : Dynamic.Value → Word → Prop}
  (observations : FunctionObservations compilation.checked.catalog functions identities)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
  {before : Dynamic.Heap} {store : Store}
  (environments : DataHeap.EnvRepresents (definitions := artifact.layouts.definitions) (storageCatalog compilation.checked.catalog)
    mapping world administrativeContext scope environment coreEnvironment)
  (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  {certified : Certified artifact.layouts.definitions (SourceCoreLocalCell.coreContext scope ++ administrativeContext) .unit}
  (accepted : lowerChecked compilation compilation.checked.signatures expression fuel source scope site assignment operator none .unit
    (LanguageResult.success .unit) reasonAt invalid invalidOperand missing artifact.layouts.definitions
    (SourceCoreLocalCell.coreContext scope ++ administrativeContext) = .ok certified)

include rootTyped bare profile observations environments heaps locals accepted

/-- No universal child theorem is needed for an actual bare-root assignment.
Both initialized writes and absent-operand faults are reconstructed from the
live heap and the actual completed Core program. -/
theorem checked_bare_run_reflects
    (token : faults (.invalidUnaryOperand .bitNot) invalidOperand)
    {result : Value} {finalStore : Store} {runtimeFuel : Nat}
    (completed : runStateful runtimeFuel (.initial certified.expression coreEnvironment store) = .done result finalStore) :
    ∃ after finalMap finalWorld,
      Outcome program context evidence source faults environment before assignment.target result after ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  apply terminal
  exact CompatibleBareBitNotLowering.reflects rootTyped bare profile observations environments heaps locals
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) token (runStateful_evaluation_sound completed)

/-- The source trace constructs the actual finite Core execution and final
related heap without changing location identities or the world. -/
theorem checked_bare_preserves {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before assignment.target updated after) :
    ∃ finalStore, Evaluates coreEnvironment store certified.expression (.inRight .word .unit) finalStore ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  CompatibleBareBitNotLowering.preserves rootTyped bare profile observations environments heaps locals
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) trace

/-- The only bare numeric source fault is the missing unary operand. Its
actual lowering preserves the complete native store, including frame/marker
cells; it evaluates neither index children nor a source RHS. -/
theorem checked_bare_fault_preserves {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after) :
    reason = .invalidUnaryOperand .bitNot ∧ after = before ∧
      Evaluates coreEnvironment store certified.expression (.inLeft .unit (.word invalidOperand)) store :=
  CompatibleBareBitNotLowering.preserves_fault rootTyped bare profile observations environments heaps locals
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) trace
end Bare

end Tests.SourceCoreCompatibleAmbientBitNot

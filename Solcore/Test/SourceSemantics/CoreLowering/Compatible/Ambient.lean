import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceBitNot
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements
import Solcore.Frontend.SourceCore.Internal.CallableIndexed
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Payloads
import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Encoding
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceWriteback
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.Frontend.SourceCore.Internal.CallableOutputs
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedBareAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionTyped
import Solcore.Frontend.SourceCore.CompatibleFunctions
import Solcore.Frontend.SourceCore.Internal.Carriers

/-!
# Compatible ambient tests

Ambient closures with bare assignments, places, mappings, snapshots and write-back.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleAmbientBitNot
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
    {certificate : Certificate} {faults : FaultRep} [FunctionCalls.FaultTokens faults] {assignment : AssignmentResolution}
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

include rootTyped bare profile environments heaps locals accepted

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
  exact CompatibleBareBitNotLowering.reflects rootTyped bare profile environments heaps locals
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) token (runStateful_evaluation_sound completed)

/-- The source trace constructs the actual finite Core execution and final
related heap without changing location identities or the world. -/
theorem checked_bare_preserves {updated : Dynamic.Value} {after : Dynamic.Heap}
    (total : operator.mayPanic = false)
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before assignment.target updated after) :
    ∃ finalStore, Evaluates coreEnvironment store certified.expression (.inRight .word .unit) finalStore ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  CompatibleBareBitNotLowering.preserves rootTyped bare profile environments heaps locals total
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) trace

/-- The only bare numeric source fault is the missing unary operand. Its
actual lowering preserves the complete native store, including frame/marker
cells; it evaluates neither index children nor a source RHS. -/
theorem checked_bare_fault_preserves {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after) :
    reason = .invalidUnaryOperand .bitNot ∧ after = before ∧
      Evaluates coreEnvironment store certified.expression (.inLeft .unit (.word invalidOperand)) store :=
  CompatibleBareBitNotLowering.preserves_fault rootTyped bare profile environments heaps locals
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) trace
end Bare

end Tests.SourceCoreCompatibleAmbientBitNot
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleAmbientHeap
/-! An actual indexed snapshot-lambda contains a source allocation marker in
its body and captures a nominal frame outside the base source catalog. It is
represented and stored under the full definitions, retaining the supplied raw
source closure exactly. This is a formation/indexing regression; call meaning
and source ownership remain separate from the test's explicit leaf model. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCompatibleAmbientHeap
open Core Frontend SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem existsChecked : (SourceCoreCompatibleCatalog.prepare signatures 10 [] [] {} false).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [] [] {} false).toOption.get existsChecked
private def frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨0⟩⟩
private def marker : SourceCoreHeapMarkers.Layout := ⟨⟨1⟩, .unit⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frame.definition, marker.definition]
private theorem frameRegistered : frame.Registered ambient.definitions := ⟨rfl⟩
private theorem markerRegistered : marker.Registered ambient.definitions := ⟨.unit, rfl⟩
private theorem definitionsTyped : ambient.definitions.WellFormed := Core.DataEnvironment.isWellFormed_sound (by decide)
private def table : SourceCoreCallableIndexedDispatch.Table := ⟨[], [], [], []⟩
private def snapshot := SourceCoreCallableIndexedFrames.encode frame .empty
private def environment : Environment := [.cellRef frame.type 0]
private def world : StoreTyping := [frame.type]
private def store : Store := [snapshot]
private def body : Expr := .letE (SourceCoreHeapMarkers.allocate marker .unit .unit) (LanguageResult.success .unit)
private def emitted : Expr := SourceCoreCallableIndexedAncestry.snapshotLambda table frame Word.zero 0 .unit .unit body
private def closureBody : Expr := SourceCoreCallableIndexedFrames.withFrame (.var 2)
  (SourceCoreCallableIndexedDispatch.lambdaFrame table frame Word.zero (.var 1) (.loadCell (.var 2))) (body.weakenAt 1)
private def nativeClosure : Value := .closure .unit (LanguageResult.resultType .unit) closureBody (snapshot :: environment)
private def carrier : Value := .pair (.inLeft .word .unit) nativeClosure
private def nativeType : Ty := TaggedFunction.functionType .unit .unit

private theorem bodyTyped : HasType [.unit, .cell frame.type] body (LanguageResult.resultType .unit) ambient.definitions :=
  .letE (SourceCoreHeapMarkers.allocate_hasType markerRegistered .unit .unit) (.inRight .word .unit)
private theorem emittedTyped : HasType [.cell frame.type] emitted (.function .unit (LanguageResult.resultType .unit)) ambient.definitions :=
  SourceCoreCallableIndexedAncestry.snapshotLambda_hasType frameRegistered table Word.zero .unit .unit rfl bodyTyped

/-- The exact compiler helper runs in the actual administrative environment. -/
theorem emitted_evaluates : Evaluates environment store emitted nativeClosure store :=
  SourceCoreCallableIndexedAncestry.snapshotLambda_evaluates table Word.zero rfl rfl

private theorem nativeTyped {future : StoreTyping} (typed : future[0]? = some frame.type) :
    RuntimeValueHasType future carrier nativeType ambient.definitions := by
  have bodyTyping := emittedTyped
  cases bodyTyping with
  | letE loaded lambdaTyping =>
    cases loaded with
    | loadCell reference =>
      cases reference with
      | var selected =>
        have eqType := Option.some.inj selected
        cases eqType
        cases lambdaTyping with
        | lambda _ _ code =>
          exact .pair (.inLeft .unit) (.closure
            (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed future frameRegistered .empty)
              (.cons (.cellRef typed) .nil)) code)

/-- Native typing under the smaller source catalog is actually impossible:
the captured nominal snapshot has no constructor there. -/
theorem not_base_typed : ¬ RuntimeValueHasType world carrier nativeType checked.catalog.definitions := by
  intro typed
  cases typed with
  | pair _ closureTyping =>
    cases closureTyping with
    | closure captured _ =>
      cases captured with
      | cons snapshotTyping _ =>
        cases snapshotTyping with
        | constructed registered _ => cases registered

private def functions (source : Dynamic.Closure) : FunctionModel checked.catalog ambient where
  Represents := fun _ _ future sourceType value native type =>
    sourceType = .function .unit .unit ∧ value = .closure source ∧ native = carrier ∧ type = nativeType ∧
      future[0]? = some frame.type
  projection := by rintro _ _ _ _ _ _ _ ⟨rfl, _, _, rfl, _⟩; rfl
  runtime_hasType := by rintro _ _ _ _ _ _ _ ⟨_, _, rfl, rfl, typed⟩; exact nativeTyped typed
  source_function := by rintro _ _ _ _ _ _ _ ⟨_, rfl, _, _, _⟩; exact .closure source
  extend := by
    rintro _ _ _ _ _ _ _ _ _ _ ⟨sourceType, value, native, type, typed⟩ _ _ worlds
    exact ⟨sourceType, value, native, type, worlds.lookup typed⟩

private def model (source : Dynamic.Closure) := CompatibleAmbientHeap.payloadModel checked checked.staticRegistry (functions source)
private theorem represented (source : Dynamic.Closure) :
    ValueRep checked checked.staticRegistry (functions source) [] world (.function .unit .unit) (.closure source) carrier nativeType :=
  .function ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Snapshot and marker cells stay outside the source location map; a source
cell holds the emitted closure under the real suffix definitions. -/
theorem closure_heap (source : Dynamic.Closure) :
    GenericHeap.HeapRepresents (model source) [3]
      [frame.type, frame.type, marker.type, OptionalCell.cellType nativeType]
      ⟨[⟨.function .unit .unit, some (.closure source), none⟩]⟩
      [snapshot, snapshot, SourceCoreHeapMarkers.markerValue marker .unit, .inRight .unit carrier] ∧
    ReferenceRepresents [3] [frame.type, frame.type, marker.type, OptionalCell.cellType nativeType] ⟨0⟩ 3 nativeType := by
  have empty : GenericHeap.HeapRepresents (model source) [] [] ⟨[]⟩ [] := .empty
  have contextHeap := empty.allocate_administrative (SourceCoreCallableIndexedFrames.encode_runtime_typed [] frameRegistered .empty)
  exact CallableIndexedOrdinaryAllocation.heap_allocate contextHeap
    (SourceCoreCallableIndexedFrames.encode_runtime_typed world frameRegistered .empty)
    (.constructed markerRegistered.payloadLookup .unit) (.initialized (represented source)) .append

/-- The raw source catalog remains empty; no administrative entries are
invented to justify the larger Core table. -/
example : checked.catalog.entries = [] ∧ ambient.definitions.length = 2 := ⟨rfl, rfl⟩

/-- An already related base store and its raw staged source type transport
unchanged to the full table without admitting new function leaves. -/
private def noFunctions : FunctionModel checked.catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible

example {mapping : LocationMap} {heap : Dynamic.Heap} {store : Store} {world : StoreTyping}
    (heaps : CompatibleHeap.HeapRepresents checked checked.staticRegistry noFunctions mapping world heap store) :
    CompatibleAmbientHeap.HeapRepresents checked checked.staticRegistry
      (noFunctions.extend_definitions (after := ambient) ambient.basePrefix) mapping world heap store := by
  exact CompatibleAmbientHeap.extend_definitions
    (initial := noFunctions)
    (future := noFunctions.extend_definitions (after := ambient) ambient.basePrefix)
    (fun represented => represented) ambient.basePrefix heaps

end Solcore.Test.SourceCoreCompatibleAmbientHeap
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleAmbientLowerReflection
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
    {certificate : Certificate} {faults : FaultRep} [FunctionCalls.FaultTokens faults] {assignment : AssignmentResolution}
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
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleAmbientMappings
/-! Full-definition mapping regressions. An explicitly modeled anonymous
function captures a fresh frame constructor, so its value cannot be typed in
the base catalog. Mapping proofs retain that leaf and duplicate order. The
model does not authenticate arbitrary source closure bodies. A separate actual
indexed program supplies the real prefix/suffix receipt for raw alias/default
and duplicate update execution checks. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Solcore.Test.SourceCoreCompatibleAmbientMappings
open Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleMapping CompatibleEquality DataEquality

private def functionSource : TypeSystem.Ty := .function .unit .word
private def functionCore : Core.Ty := TaggedFunction.functionType .unit .word
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem existsChecked : (SourceCoreCompatibleCatalog.prepare signatures 30
    [.mapping .word functionSource] [] {} false).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 30
    [.mapping .word functionSource] [] {} false).toOption.get existsChecked
private def layout : Core.OrderedMapping.Layout := ⟨.word, functionCore, ⟨0⟩⟩
private def frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨1⟩⟩
private def ambient : AmbientDefinitions checked.catalog.definitions := .append _ [frame.definition]
private theorem frameRegistered : frame.Registered ambient.definitions := ⟨by cbv⟩
private theorem functionWellFormed : functionCore.WellFormed checked.catalog.definitions :=
  .product (.sum .unit .word) (.function .unit (.sum .word .word))
private theorem registered : layout.Registered checked.catalog.definitions :=
  ⟨.word, functionWellFormed, by cbv⟩
private def snapshot := SourceCoreCallableIndexedFrames.encode frame .empty
private def seven : Word := Word.ofNatModulo 7
private def closure : Value := .closure .unit (LanguageResult.resultType .word)
  (LanguageResult.success (.word seven)) [snapshot]
private def native : Value := .pair (.inLeft .word .unit) closure
private theorem nativeTyped (world : StoreTyping) : RuntimeValueHasType world native functionCore ambient.definitions :=
  .pair (.inLeft .unit) (.closure
    (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world frameRegistered .empty) .nil)
    (.inRight .word .word))

theorem fresh_capture_not_base_typed (world : StoreTyping) :
    ¬ RuntimeValueHasType world native functionCore checked.catalog.definitions := by
  intro typed
  cases typed with
  | pair _ closureTyped => cases closureTyped with
    | closure environment _ => cases environment with
      | cons captured _ => cases captured with
        | constructed selected _ => cases selected

private def functions (source : Dynamic.Closure) : FunctionModel checked.catalog ambient where
  Represents := fun _ _ _ sourceType value core type =>
    sourceType = functionSource ∧ value = .closure source ∧ core = native ∧ type = functionCore
  projection := by rintro _ _ _ _ _ _ _ ⟨rfl, _, _, rfl⟩; cbv
  runtime_hasType := by rintro _ _ _ _ _ _ _ ⟨_, _, rfl, rfl⟩; exact nativeTyped _
  source_function := by rintro _ _ _ _ _ _ _ ⟨_, rfl, _, _⟩; exact .closure source
  extend := fun related _ _ _ => related
private def identities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : IdentityFaithful identities := ⟨False.elim, fun impossible _ => False.elim impossible⟩
private theorem functionObservations (source : Dynamic.Closure) :
    FunctionObservations checked.catalog (functions source) identities := by
  rintro _ _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩
  exact .anonymous source .unit .word closure rfl
private def one : Word := Word.ofNatModulo 1
private def header : Word := Word.ofNatModulo 1
private def sources (source : Dynamic.Closure) : List (Dynamic.Value × Dynamic.Value) :=
  [(.word one, .closure source), (.word one, .closure source)]
private def entries : Core.OrderedMapping.Entries := [(.word one, native), (.word one, native)]
private theorem fields (source : Dynamic.Closure) (mapping : LocationMap) (world : StoreTyping) :
    Fields checked checked.staticRegistry (functions source) mapping world .word functionSource (sources source)
      header layout entries none := by
  refine ⟨⟨by decide⟩, by cbv, by cbv, by cbv, registered, ?_, ?_⟩
  · exact .entry (.word one) (.function ⟨rfl, rfl, rfl, rfl⟩)
      (.entry (.word one) (.function ⟨rfl, rfl, rfl, rfl⟩) (.empty _ _ _ _))
  · exact .absent (by intro impossible; cases impossible) (by cbv) functionWellFormed

/-- Both repeated function entries survive with full native typing. Their
captured frame cannot be justified by shrinking to the source catalog. -/
theorem function_entries_typed (source : Dynamic.Closure) (world : StoreTyping) :
    RuntimeValueHasType world (Core.OrderedMapping.encode layout entries) layout.type ambient.definitions :=
  (fields source [] world).stored.runtime_hasType registered

theorem function_default_absent (source : Dynamic.Closure) (world : StoreTyping) :
    RuntimeValueHasType world (.inLeft functionCore .unit) (.sum .unit functionCore) ambient.definitions :=
  (fields source [] world).default.runtime_hasType

private theorem comparatorExists : (SourceCoreCompatibleDataEquality.prepare 30 checked .word).toOption.isSome = true := by cbv
private def comparator := (SourceCoreCompatibleDataEquality.prepare 30 checked .word).toOption.get comparatorExists

/-- Actual generated helpers yield an independent first-match/default/missing
classification even when represented values contain fresh ambient closures. -/
theorem function_lookup (source : Dynamic.Closure) (store : Store) :
    ∃ result,
      ReadResult checked checked.staticRegistry (functions source) [] [] functionSource (.word one)
        (sources source) functionCore Word.zero header result ∧
      Evaluates [SourceCoreMappingWithDefault.value header none layout entries, .word one] store
        (SourceCoreMappingWithDefault.lookup layout Word.zero comparator.expression (.var 0) (.var 1)) result
        (Transport.lookupStore comparator layout
          [SourceCoreMappingWithDefault.value header none layout entries, .word one] store header none entries (.word one)) := by
  exact lookup_meaning comparator (by cbv) faithful (functionObservations source) (fields source [] []) (.word one)
    _ store Word.zero (.var 0) (.var 1) (.var rfl) (.var rfl)

private def index (id : ExpressionId) : SourceCoreCompatibleDataPlaces.PreparedIndex :=
  ⟨layout, id, 0, comparator.expression, Word.zero⟩
private def place (id : ExpressionId) : SourceCoreCompatibleDataPlaces.Prepared :=
  ⟨⟨.mapping .word functionSource, SourceCoreMappingWithDefault.type layout, functionCore,
    [.index layout id functionSource], none⟩, [.index (index id)], [(id, .word)], Word.zero⟩
private def setterInput (key : Word) : Value :=
  .pair (.inRight .unit (SourceCoreMappingWithDefault.value header none layout entries)) (.pair (.word key) native)

/-- Finite completion and reflection apply to the actual ordinary setter,
including the missing-default alternative. No child evaluation is a premise. -/
theorem function_setter_runs (source : Dynamic.Closure) (id : ExpressionId) (key : Word) (store : Store) :
    ∃ result finalStore administrative count,
      UpdateResult checked checked.staticRegistry (functions source) [] [] .word functionSource
        (.word key) (.closure source) (sources source) header layout none Word.zero result count ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (.apply (SourceCoreCompatibleDataPlaces.setter (place id) .word) (.var 0)) [setterInput key] store) =
          .done result finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (.apply (SourceCoreCompatibleDataPlaces.setter (place id) .word) (.var 0)) [setterInput key] store) =
          .done actual actualStore → actual = result ∧ actualStore = finalStore) ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  have certificate : Index checked (index id) := ⟨comparator, rfl, by cbv⟩
  exact setter_initialized_run certificate (place id) rfl rfl faithful (functionObservations source)
    (fields source [] []) (.word key) (.function ⟨rfl, rfl, rfl, rfl⟩)
    [setterInput key] store .word [.word key] (.var 0) rfl rfl (.var rfl)

private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog)
    (ambient : AmbientDefinitions catalog.definitions := .original _) : FunctionModel catalog ambient where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible

/-- The data-only codec receipt transports into any ambient function model;
no new native closure is inferred to be well typed under base definitions. -/
theorem encoded_ambient {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient}
    {expected : TypeSystem.Ty} {carrier : SourceCoreDataValues.Value}
    {encoded : SourceCoreCompatibleValues.Encoded fuel context expected carrier} {source : Dynamic.Value}
    (accepted : SourceCoreCompatibleValues.encode fuel context expected carrier = .ok encoded)
    (meaning : CompatibleEncoding.Means carrier source) (mapping : LocationMap) (world : StoreTyping) :
    ValueRep context.checked encoded.context.registry functions mapping world expected source encoded.value encoded.type :=
  (CompatibleEncoding.encode_represents_at (functions := noFunctions context.checked.catalog)
    accepted meaning mapping world).map_functions (initial := noFunctions context.checked.catalog) (future := functions) (fun impossible => False.elim impossible)

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def word (n : Nat) : Word := Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content :=
    "function main(seed: Word) returns (Word) { let cache: mapping(Word => Word); cache[0] = seed; return cache[0]; }"}] }

private def complete (code : Expr) (environment : Environment) (store : Store) : IO (Value × Store) := do
  let output ← match runStateful 100000 (.initial code environment store) with
    | .done value after => pure (value, after)
    | other => throw (IO.userError s!"ambient mapping helper: {reprStr other}")
  match runStateful 3 (.initial code environment store) with
  | .outOfFuel checkpoint =>
    match runStateful 100000 checkpoint with
    | .done value after => assertTrue (value == output.1 && after == output.2) "ambient mapping resume differs"
    | _ => throw (IO.userError "ambient mapping resume did not finish")
  | _ => throw (IO.userError "ambient mapping fixture failed to suspend")
  assertTrue (output.2.take store.length == store) "ambient mapping helper modified the existing store"
  pure output

def run : IO Unit := do
  let program ← get "ambient mapping source" (checkProgram workspace)
  let key ← match program.signatures.functions with
    | [signature] => pure (⟨signature.id, []⟩ : SourceSpecialization.SpecializationKey)
    | _ => throw (IO.userError "ambient mapping root missing")
  let plan ← match SourceSpecializationWorklist.run program [⟨key.declaration, []⟩] 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"ambient mapping plan: {reprStr other}")
  let automatic ← get "ambient mapping base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← get "ambient mapping indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let completion ← get "ambient mapping native start" (prepared.runSource key [.word (word 5)] 100000 500)
  let before := SourceCoreCallableIndexedLedger.store completion
  let full := CallableIndexedAmbient.ambientDefinitions prepared
  let context : SourceCoreCompatibleValues.Context := .initial automatic.checked
  let rawKey : TypeSystem.Ty := .comptime .word
  let rawValue : TypeSystem.Ty := .comptime .word
  let rawType : TypeSystem.Ty := .mapping rawKey rawValue
  let carrier : SourceCoreDataValues.Value := .mapping rawKey rawValue [(.word (word 1), .word (word 11)), (.word (word 1), .word (word 22))]
  let source : Dynamic.Value := .mapping rawKey rawValue [(.word (word 1), .word (word 11)), (.word (word 1), .word (word 22))]
  have sourceMeaning : CompatibleEncoding.Means carrier source := .mapping (.prepend (.word _) (.word _) (.prepend (.word _) (.word _) .empty))
  match accepted : SourceCoreCompatibleValues.encode 500 context rawType carrier with
  | .error error => throw (IO.userError s!"ambient mapping encode: {reprStr error}")
  | .ok encoded =>
    have represented := encoded_ambient (functions := noFunctions automatic.checked.catalog full) accepted sourceMeaning [] []
    have _view := mapping_fields represented rfl
    let layout ← get "ambient mapping layout" (automatic.checked.catalog.mappingLayout rawKey rawValue)
    let comparator ← get "ambient mapping comparison" (SourceCoreCompatibleDataEquality.prepare 500 automatic.checked rawKey)
    let nativeHeader ← match encoded.value with
      | .pair (.word header) _ => pure header
      | _ => throw (IO.userError "ambient mapping raw header missing")
    assertTrue (encoded.context.registry.lookup nativeHeader == some (.mapping rawKey rawValue)) "ambient mapping erased raw header"
    for sought in [1, 2] do
      let lookup := SourceCoreMappingWithDefault.lookup layout (word 1000) comparator.expression (.var 0) (.var 1)
      assertTrue (infer? [SourceCoreMappingWithDefault.type layout, .word] lookup full.definitions == some (LanguageResult.resultType .word))
        "ambient lookup failed actual full-definition checker"
      let (result, after) ← complete lookup [encoded.value, .word (word sought)] before
      assertTrue (result == .inRight .word (.word (word (if sought == 1 then 11 else 0)))) "ambient first-match/default changed"
      assertTrue (after.length == before.length + automatic.checked.catalog.entries.length + 1) "ambient lookup allocation count changed"
      let inserted := SourceCoreMappingWithDefault.insert layout comparator.expression (.var 0) (.var 1) (.var 2)
      let (result, _) ← complete inserted [encoded.value, .word (word sought), .word (word 99)] before
      let updated ← match result with
        | .inRight .word value => pure value | _ => throw (IO.userError "ambient insert failed")
      let decoded ← get "ambient inserted decode" (SourceCoreCompatibleValues.decode 500 encoded.context rawType updated)
      let expected : SourceCoreDataValues.Value := .mapping rawKey rawValue
        (if sought == 1 then [(.word (word 1), .word (word 99)), (.word (word 1), .word (word 22))]
         else [(.word (word 1), .word (word 11)), (.word (word 1), .word (word 22)), (.word (word 2), .word (word 99))])
      assertTrue (decoded == expected) "ambient insert changed ordered duplicates/raw metadata"
      let keyId : ExpressionId := ⟨⟨key.declaration, 7⟩⟩
      let route : SourceCoreCompatibleDataPlaces.Route := ⟨rawType, SourceCoreMappingWithDefault.type layout,
        layout.valueType, [.index layout keyId rawValue], none⟩
      let place ← get "ambient actual place preparation"
        (SourceCoreCompatibleDataPlaces.prepare context 500 route (word 900) (fun _ => word 1000))
      let getter := SourceCoreCompatibleDataPlaces.getter place layout.keyType
      let setter := SourceCoreCompatibleDataPlaces.setter place layout.keyType
      assertTrue (infer? [] setter full.definitions == some (.function
        (.product (OptionalCell.cellType route.rootType) (.product layout.keyType layout.valueType))
        (LanguageResult.resultType route.rootType))) "ambient setter failed actual full-definition checker"
      let (read, _) ← complete (.apply getter (.var 0))
        [.pair (.inRight .unit encoded.value) (.word (word sought))] before
      assertTrue (read == .inRight .word (.inRight .unit (.word (word (if sought == 1 then 11 else 0)))))
        "ambient getter lost snapshot selection/default"
      let (written, after) ← complete (.apply setter (.var 0))
        [.pair (.inRight .unit encoded.value) (.pair (.word (word sought)) (.word (word 99)))] before
      match written with
      | .inRight .word value =>
        let source ← get "ambient setter decode" (SourceCoreCompatibleValues.decode 500 encoded.context rawType value)
        assertTrue (source == expected) "ambient setter changed duplicate order/raw header"
      | _ => throw (IO.userError "ambient setter failed")
      assertTrue (after.length == before.length + 2 * (automatic.checked.catalog.entries.length + 1))
        "ambient setter changed lookup-before-insert allocation count"
  -- This separate explicit leaf model uses the synthetic ambient frame table.
  -- Missing function defaults must fail before insertion, preserving the header.
  let syntheticId : ExpressionId := ⟨⟨key.declaration, 8⟩⟩
  let syntheticSetter := SourceCoreCompatibleDataPlaces.setter (place syntheticId) .word
  assertTrue (infer? [] syntheticSetter ambient.definitions == some (.function
    (.product (OptionalCell.cellType (SourceCoreMappingWithDefault.type layout)) (.product .word functionCore))
    (LanguageResult.resultType (SourceCoreMappingWithDefault.type layout)))) "function-valued ambient setter failed checker"
  for sought in [1, 2] do
    let (result, after) ← complete (.apply syntheticSetter (.var 0)) [setterInput (word sought)] []
    if sought == 1 then
      assertTrue (result == .inRight .word (SourceCoreMappingWithDefault.value header none layout entries))
        "function-valued mapping changed duplicate payloads"
      assertTrue (after.length == 2 * (checked.catalog.entries.length + 1)) "function setter skipped its lookup or insertion"
    else
      assertTrue (result == .inLeft (SourceCoreMappingWithDefault.type layout) (.word header))
        "function-valued mapping changed missing-default token"
      assertTrue (after.length == checked.catalog.entries.length + 1) "function setter inserted after missing default"
  IO.println "source core compatible ambient mapping tests passed"

end Solcore.Test.SourceCoreCompatibleAmbientMappings
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleAmbientPaths
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Checked source supplies roots and index occurrences. The retained ordinal
member path is assembled explicitly (source member syntax is not asserted).
The actual indexed compiler supplies the ambient frame/marker suffix.
Actual describe/prepare/checker/run preserve raw constructor IDs, raw mapping
headers, siblings, nested defaults, and ordered duplicate entries. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleAmbientPaths
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CompatiblePayload CompatibleEquality CompatibleMapping CompatibleMapping.MixedPaths

private def w (n : Nat) : Word := Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Item(Word) }",
    "function probe(seed: Word) returns (Word) { let f = lam(item: Word) { return item; }; return f(seed); }",
    "enum Holder<T> { Wrap(mapping(Word => T), Word), Other(mapping(Word => T), Word) }",
    "function mixed(root: mapping(Word => Holder<Word>), value: Holder<Word>, key: Word) returns (Word) { root[key] = value; return 0; }",
    "function missing(root: mapping(Word => Holder<Box>), value: Holder<Box>, key: Word) returns (Word) { root[key] = value; return 0; }",
    "function nested(root: mapping(Word => mapping(Word => @Word)), value: mapping(Word => @Word), key: Word) returns (Word) { root[key] = value; return 0; }"
  ]}] }
private def sourceFor (program : CheckedProgram) (name : String) : IO TypedSource := do
  let signature ← match program.signatures.functions.find? (·.name == name) with
    | some signature => pure signature | none => throw (IO.userError "mixed function missing")
  match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 100 with
  | .ok (.complete plan) => match plan.specializations with
    | [specialized] => pure specialized.function.typedBody
    | _ => throw (IO.userError "mixed specialization count changed")
  | other => throw (IO.userError s!"mixed specialization failed: {reprStr other}")
private def assignmentFor (source : TypedSource) : IO (StatementNode × AssignmentResolution × ExpressionId) := do
  let (node, assignment) ← match source.nodes.filterMap (fun
    | .statement node => match node.form with | .assignValue assignment _ _ => some (node, assignment) | _ => none
    | _ => none) with
    | [assignment] => pure assignment | _ => throw (IO.userError "mixed assignment missing")
  match assignment.target.projections with
  | [.index key] => pure (node, assignment, key)
  | _ => throw (IO.userError "mixed original assignment path changed")
private def encode (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty) (value : SourceCoreDataValues.Value) :
    IO (SourceCoreCompatibleValues.Encoded 500 context type value) :=
  match SourceCoreCompatibleValues.encode 500 context type value with
  | .ok encoded => pure encoded | .error error => throw (IO.userError s!"mixed encode failed: {reprStr error}")
private def decode (context : SourceCoreCompatibleValues.Context) (type : TypeSystem.Ty) (native : Value) (expected : SourceCoreDataValues.Value) : IO Unit :=
  match SourceCoreCompatibleValues.decode 500 context type native with
  | .ok actual => assertTrue (actual == expected) "mixed path lost raw metadata, sibling, or ordered duplicate"
  | .error error => throw (IO.userError s!"mixed decode failed: {reprStr error}")
private def completed (code : Expr) (environment : Environment) (before : Store) : IO (Value × Store) := do
  let result ← match runStateful 500000 (.initial code environment before) with
    | .done value after => pure (value, after)
    | other => throw (IO.userError s!"mixed helper failed: {reprStr other}")
  assertTrue (result.2.take before.length == before) "mixed helper changed source store prefix"
  match runStateful 7 (.initial code environment before) with
  | .outOfFuel checkpoint =>
    match runStateful 500000 checkpoint with
    | .done value after => assertTrue (value == result.1 && after == result.2) "mixed resume changed value/store"
    | _ => throw (IO.userError "mixed resume failed")
  | _ => throw (IO.userError "mixed fixture no longer checkpoints")
  pure result

/-- Actual encoded virtual roots transport to the full indexed definition
suffix. Normalization keeps the absent source cell and the entire native store;
its child value/default is derived from the real encoder receipt. -/
theorem virtual_root_under_indexed {context : SourceCoreCompatibleValues.Context}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared context.checked)
    (functions : FunctionModel context.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions artifact))
    {prepared : SourceCoreCompatibleDataPlaces.Prepared} {key valueType : TypeSystem.Ty}
    (generated : VirtualRoot.Generated context prepared.route key valueType)
    (store : Store) (mapping : GeneralHeap.LocationMap) (world : StoreTyping) :
    ∃ header layout fallback,
      CompatiblePayload.ValueRep context.checked context.registry functions mapping world (.mapping key valueType)
        (.mapping key valueType []) (Transport.carrier header fallback layout []) (SourceCoreMappingWithDefault.type layout) ∧
      Dynamic.RootInitialValue ⟨.mapping key valueType, none, none⟩ (some (.mapping key valueType [])) ∧
      Evaluates [.inLeft prepared.route.rootType .unit] store
        (SourceCoreCompatibleDataPlaces.normalizeRoot prepared (.var 0))
        (.inRight .unit (Transport.carrier header fallback layout [])) store := by
  obtain ⟨header, layout, fallback, fields, root⟩ := generated_root generated functions mapping world (.refl _)
  exact ⟨header, layout, fallback, fields.represents, root.initial, root.normalize _ store (.var 0) (.var rfl)⟩

/-- A static mixed-path tree and the actual indexed ambient receipt suffice
for whole generated getter meaning and reflection. Runtime child evaluations
are outputs of the structural theorem, not premises in this consumer. -/
theorem mixed_read_under_indexed {checked : SourceCoreCompatibleCatalog.Checked}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared checked)
    {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {prepared : SourceCoreCompatibleDataPlaces.Prepared} {keys : List Value}
    {leafType sourceType : TypeSystem.Ty} {leafCore : Ty}
    {cell : Dynamic.Cell} {source leaf : Dynamic.Value} {optional value : Value}
    {steps : List SourceCoreCompatibleDataPlaces.PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (root : RootInput prepared cell optional source value)
    (tree : ReadTree checked registry functions mapping world prepared keys leafType leafCore sourceType source value steps projections leaf count)
    (stepsEqual : prepared.steps = steps) (nonempty : steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (keyType : Ty) (argument : Expr)
    (selected : DataEquality.Selects environment argument (.pair optional (DataPatternValues.packValues keys))) :
    ∃ native after administrative,
      Dynamic.RootInitialValue cell (some source) ∧ Dynamic.ProjectionsRead (some source) projections (some leaf) ∧
      ValueRep checked registry functions mapping world leafType leaf native leafCore ∧
      FiniteRun environment store (.apply (SourceCoreCompatibleDataPlaces.getter prepared keyType) argument)
        (.inRight .word (.inRight .unit native)) after ∧
      after = store ++ administrative ∧ administrative.length = count :=
  getter_preserves_run root tree stepsEqual nonempty faithful functionLeaves keyLength environment store keyType argument selected

private def exercise (initial : SourceCoreCompatibleValues.Context)
    (ambient : AmbientDefinitions initial.checked.catalog.definitions) (inertStore : Store) (source : TypedSource)
    (rootType leafType : TypeSystem.Ty) (rootCarrier replacement : SourceCoreDataValues.Value)
    (member : Bool) (optionalAbsent : Bool) (expectedRead : Option SourceCoreDataValues.Value)
    (expectedUpdate : Option SourceCoreDataValues.Value) (missingHeader : Option Word := none) : IO Unit := do
  let (node, assignment, key) ← assignmentFor source
  let assignment := { assignment with target := { assignment.target with
    type := leafType
    projections := if member then [.index key, .member "entries" 0, .index key] else [.index key, .index key]}}
  let root ← encode initial rootType rootCarrier
  let replacement ← encode root.context leafType replacement
  let context := replacement.context
  let route ← match SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source (.occurrence node.id.occurrence) assignment with
    | .ok route => pure route | .error error => throw (IO.userError s!"mixed describe failed: {reprStr error}")
  let prepared ← match preparedAccepted : SourceCoreCompatibleDataPlaces.prepare context 200 route (w 900) (fun _ => w 1000) with
    | .ok prepared =>
      have _receipt := CompatibleMixedPreparation.of_prepare preparedAccepted
      pure prepared | .error error => throw (IO.userError s!"mixed prepare failed: {reprStr error}")
  assertTrue (prepared.keys.map Prod.fst == [key, key]) "mixed key occurrences/positions changed"
  let keys := Value.pair (.word (w 1)) (.word (w 1))
  let keyType := Ty.product .word .word
  let optional := if optionalAbsent then Value.inLeft route.rootType .unit else .inRight .unit root.value
  let before := inertStore ++ [optional, Value.integer (-99)]
  let getter := SourceCoreCompatibleDataPlaces.getter prepared keyType
  let setter := SourceCoreCompatibleDataPlaces.setter prepared keyType
  assertTrue (infer? [] getter ambient.definitions == some (.function (.product (OptionalCell.cellType route.rootType) keyType) (LanguageResult.resultType prepared.optionalLeaf))) "mixed getter checker failed"
  assertTrue (infer? [] setter ambient.definitions == some (.function (.product (OptionalCell.cellType route.rootType) (.product keyType route.leafType)) (LanguageResult.resultType route.rootType))) "mixed setter checker failed"
  let (read, readStore) ← completed (.apply getter (.var 0)) [.pair optional keys] before
  assertTrue (readStore.length == before.length + 2 * (context.checked.catalog.entries.length + 1)) "mixed lookup allocation count changed"
  match expectedRead, read with
  | some expected, .inRight .word (.inRight .unit value) => decode context leafType value expected
  | none, .inLeft _ (.word token) => assertTrue (some token == missingHeader.map ((w 1000).add)) "mixed fault used outer raw header"
  | _, _ => throw (IO.userError s!"mixed getter outcome changed: {reprStr read}")
  let (updated, updateStore) ← completed (.apply setter (.var 0)) [.pair optional (.pair keys replacement.value)] before
  match expectedUpdate, updated with
  | some expected, .inRight .word value =>
    decode context rootType value expected
    assertTrue (updateStore.length == before.length + 4 * (context.checked.catalog.entries.length + 1)) "mixed setter skipped selection or outer insertion"
  | none, .inLeft _ (.word token) =>
    assertTrue (some token == missingHeader.map ((w 1000).add)) "mixed setter fault token changed"
    assertTrue (updateStore.length == readStore.length) "mixed setter inserted after inner failure"
  | _, _ => throw (IO.userError s!"mixed setter outcome changed: {reprStr updated}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"mixed source rejected: {reprStr error}")
  let holder ← match program.signatures.dataTypes.find? (·.name == "Holder") with
    | some holder => pure holder | none => throw (IO.userError "mixed Holder missing")
  let constructor ← match holder.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "mixed Wrap missing")
  let parameter ← match holder.parameters with
    | [parameter] => pure parameter | _ => throw (IO.userError "mixed Holder parameter changed")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "mixed Box missing")
  let boxCtor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "mixed Item missing")
  let holderWord := TypeSystem.Ty.nominal holder.id [.word]
  let rawHolder := TypeSystem.Ty.nominal holder.id [.comptime .word]
  let holderBox := TypeSystem.Ty.nominal holder.id [.nominal box.id []]
  let nested := TypeSystem.Ty.mapping .word (.mapping .word (.proxy .word))
  let requests := program.signatures.functions.map (fun signature =>
    (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request))
  let plan ← match SourceSpecializationWorklist.run program requests 500 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"ambient mixed worklist: {reprStr other}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"ambient mixed base: {reprStr error}")
  let artifact ← match SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"ambient mixed indexed compiler: {reprStr error}")
  let probe ← match program.signatures.functions.find? (·.name == "probe") with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecialization.SpecializationKey)
    | none => throw (IO.userError "ambient mixed probe missing")
  let completion ← match artifact.runSource probe [.word (w 7)] 100000 500 with
    | .ok completed => pure completed
    | .error error => throw (IO.userError s!"ambient mixed probe run: {reprStr error}")
  match completion.result.native.observation with
  | .succeeded (.word value) _ => assertTrue (value == w 7) "ambient mixed probe changed its result"
  | other => throw (IO.userError s!"ambient mixed probe did not complete: {reprStr other}")
  let before := SourceCoreCallableIndexedLedger.store completion
  let full := CallableIndexedAmbient.ambientDefinitions artifact
  have _prefix := CallableIndexedAmbient.definitions_exact artifact
  assertTrue (!artifact.layouts.entries.isEmpty) "ambient mixed actual source marker suffix missing"
  let context := SourceCoreCompatibleValues.Context.initial automatic.checked
  let metadata : DataConstructorInstantiation := ⟨constructor.id, [(parameter, .comptime .word)], [.mapping .word (.comptime .word), .word], rawHolder⟩
  let inner : SourceCoreDataValues.Value := .mapping .word (.comptime .word) [(.word (w 1), .word (w 2)), (.word (w 1), .word (w 9))]
  let held := SourceCoreDataValues.Value.constructed metadata [inner, .word (w 55)]
  let root := SourceCoreDataValues.Value.mapping .word rawHolder [(.word (w 1), held), (.word (w 1), held)]
  let updatedInner := SourceCoreDataValues.Value.mapping .word (.comptime .word) [(.word (w 1), .word (w 7)), (.word (w 1), .word (w 9))]
  let updated := SourceCoreDataValues.Value.mapping .word rawHolder [(.word (w 1), .constructed metadata [updatedInner, .word (w 55)]), (.word (w 1), held)]
  exercise context full before (← sourceFor program "mixed") (.mapping .word holderWord) .word root (.word (w 7)) true false (some (.word (w 2))) (some updated)
  let boxType := TypeSystem.Ty.nominal box.id []
  let item : DataConstructorInstantiation := ⟨boxCtor.id, [], [.word], boxType⟩
  let boxHolder : DataConstructorInstantiation := ⟨constructor.id, [(parameter, boxType)], [.mapping .word boxType, .word], holderBox⟩
  let emptyInner := SourceCoreDataValues.Value.mapping .word boxType []
  let innerEncoded ← encode context (.mapping .word boxType) emptyInner
  let header ← match innerEncoded.value with
    | .pair (.word header) _ => pure header | _ => throw (IO.userError "mixed inner raw header absent")
  let missingRoot := SourceCoreDataValues.Value.mapping .word holderBox [(.word (w 1), .constructed boxHolder [emptyInner, .word (w 55)])]
  exercise innerEncoded.context full before (← sourceFor program "missing") (.mapping .word holderBox) boxType missingRoot (.constructed item [.word (w 7)]) true false none none (some header)
  let empty := SourceCoreDataValues.Value.mapping .word (.mapping .word (.proxy .word)) []
  let updated := SourceCoreDataValues.Value.mapping .word (.mapping .word (.proxy .word))
    [(.word (w 1), .mapping .word (.proxy .word) [(.word (w 1), .proxy .word)])]
  exercise context full before (← sourceFor program "nested") nested (.proxy .word) empty (.proxy .word) false true (some (.proxy .word)) (some updated)
  IO.println "compatible ambient mixed member/mapping paths proofs GREEN"

end Tests.SourceCoreCompatibleAmbientPaths
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleAmbientPlaceEffects
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Effectful key/RHS composition under real indexed definitions. The semantic
consumer keeps the universal expression IH explicit; its source resolution and
RHS traces construct native runs, snapshot preservation and latest-root facts.
The IO fixture separately exercises actual compiler hooks and source effects.
Its closures capture `root` by value: each closure's writes stay in its call's
copy of `root`, recorded in the ledger, and only the compound write reaches the
root itself. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleAmbientPlaceEffects
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap GenericExpressionMeaning CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open CompatiblePlaceKeys SourceCoreCompatibleDataPlaces

/-- Source key effects finish before the snapshot; the RHS executes under the
actual three hidden slots and retains both the old snapshot and new live root.
No particular child execution is assumed instead of the universal IH. -/
theorem resolve_then_rhs {compilation : SourceCoreCompatibleDataPlaces.Context}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared compilation.checked)
    {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel compilation.checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (path : PreparedPath compilation.checked source site prepared.route.rootSourceType place.projections
      0 prepared.steps prepared.keys leaf)
    (views : KeyViews path sourceTypes)
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
      CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) artifact.layouts.definitions)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := artifact.layouts.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment coreEnvironment)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {outcome : Dynamic.ExpressionOutcome}
    (rhsGenerated : certificate scope rhs lowered) (rhsFound : source.lookupExpression? rhs = some node)
    (rhsTrace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap rhs outcome after) :
    ∃ resolution : CompatiblePlaceResolution.Execution compilation.checked registry functions prepared codes sourceTypes place leaf sourceTarget
      coreEnvironment store mapping world before targetHeap,
      ∃ native finalStore finalMap finalWorld,
        CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := evidence)
          (source := source) (faults := faults) resolution rhs node lowered environment outcome after native finalStore finalMap finalWorld ∧
        ValueRep compilation.checked registry functions finalMap finalWorld leaf resolution.selected resolution.snapshot prepared.route.leafType ∧
        Nonempty (CompatiblePlaceRhs.Latest compilation.checked registry functions finalMap finalWorld prepared sourceTarget
          resolution.target after finalStore) := by
  obtain ⟨resolution, _⟩ := CompatiblePlaceResolution.preserves path views children keyTypes leafProjected virtual registryExtension
    nonempty getterTyped meaning faithful observations environments heaps locals slot rootTyped resolve
  obtain ⟨native, finalStore, finalMap, finalWorld, result⟩ :=
    CompatiblePlaceRhs.preserves resolution meaning rhsGenerated rhsFound environments locals rhsTrace
  exact ⟨resolution, native, finalStore, finalMap, finalWorld, result, result.saved_snapshot, result.latest⟩

/-- An actual completed RHS yields its independent source outcome in the full
ambient model. Resolution is a prior semantic output, not a static certificate. -/
theorem rhs_reflects_under_indexed {checked : Checked}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared checked) {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : Certificate} {faults : FaultRep}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {place : PlaceResolution} {leaf : TypeSystem.Ty} {target : Dynamic.ResolvedPlace}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {store afterStore : Store}
    {mapping : LocationMap} {world : StoreTyping} {before resolvedHeap : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf target
      coreEnvironment store mapping world before resolvedHeap)
    (meaning : Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    {administrativeContext : Core.Context} {rhs : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {value : Value}
    (generated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (environments : DataHeap.EnvRepresents (definitions := artifact.layouts.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (completed : Evaluates
      (DataPlaceExecution.snapshotEnvironment prepared.route.rootType resolution.target
        (DataPatternValues.packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (SourceCoreCompatibleDataPlaces.shift 3 lowered.expression) value afterStore) :
    ∃ outcome after finalMap finalWorld,
      CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := evidence)
        (source := source) (faults := faults) resolution rhs node lowered environment outcome after value afterStore finalMap finalWorld :=
  CompatiblePlaceRhs.reflects resolution meaning generated found environments locals completed

private def w (n : Nat) : Word := Word.ofNatModulo n
private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function effects(root: mapping(Word => Word)) returns (Word) {",
    " let key = lam(x: Word) { root[1] = 20; return x; };",
    " let rhs = lam(x: Word) { root[1] = 30; root[2] = 40; return x; };",
    " root[key(1)] += rhs(3); return root[1] + root[2]; }",
    "function keyFault(root: mapping(Word => Word)) returns (Word) {",
    " let key = lam(x: Word) { root[1] = 20; let absent: Word; return absent; };",
    " let rhs = lam(x: Word) { root[2] = 40; return x; };",
    " root[key(1)] += rhs(3); root[3] = 50; return 0; }",
    "function rhsFault(root: mapping(Word => Word)) returns (Word) {",
    " let key = lam(x: Word) { root[1] = 20; return x; };",
    " let rhs = lam(x: Word) { root[2] = 40; let absent: Word; return absent; };",
    " root[key(1)] += rhs(3); root[3] = 50; return 0; }"
  ]}] }

/-- `roots` gives the entries of every ledger row of the root binder in
allocation order: the root's own row, the snapshots `key` and `rhs` take when
they are created, and the copy each call of `key` or `rhs` makes. -/
private def exercise {checked : Checked} (artifact : SourceCoreCallableIndexedPrograms.Prepared checked)
    (program : CheckedProgram) (name : String) (expected : Option Word)
    (roots : List (List (SourceCoreDataValues.Value × SourceCoreDataValues.Value))) : IO Unit := do
  let signature ← match program.signatures.functions.find? (·.name == name) with
    | some signature => pure signature | none => throw (IO.userError "effectful function absent")
  let key : SourceSpecialization.SpecializationKey := ⟨signature.id, []⟩
  let sourceCell ← match artifact.base.functions.find? (·.specialized.key == key) with
    | some function => match function.specialized.function.typedBody.inputs with
      | [input] => pure input | _ => throw (IO.userError "effectful root input changed")
    | none => throw (IO.userError "effectful prepared function absent")
  let initial : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime .word) []
  let suspended ← get "effectful start" (artifact.runSource key [initial] 1 500)
  require suspended.result.native.checkpoint?.isSome "effectful run did not checkpoint"
  let completed := suspended.resume 300000
  let direct ← get "effectful direct" (artifact.runSource key [initial] 300000 500)
  require (completed.result.native.observation == direct.result.native.observation) "effectful resume changed final observation"
  match expected, completed.result.native.observation with
  | some expected, .succeeded (.word value) _ => require (value == expected) "compound key/RHS assignment result changed"
  | none, .failed token _ => require ((completed.result.diagnostics.diagnostic? token).isSome) "effectful fault lost source diagnostic"
  | _, other => throw (IO.userError s!"effectful outcome: {reprStr other}")
  let ledger ← get "effectful source ledger" (SourceCoreCallableIndexedLedger.scan completed)
  let rows := ledger.ledger.rows.filter (·.entry.key.binder.id == sourceCell.id)
  require (rows.length == roots.length) "effectful root ledger changed its own row or its copies"
  for (row, entries) in rows.zip roots do
    let native ← match row.payload with
      | some native => pure native | none => throw (IO.userError "effectful root became uninitialized")
    let actual ← get "effectful raw root" (SourceCoreCompatibleValues.decode 500 completed.result.context sourceCell.scheme.body native)
    require (actual == .mapping (.comptime .word) (.comptime .word) entries) "effect order, write suppression or raw mapping metadata changed"
  require (artifact.layouts.definitions.length > checked.catalog.definitions.length) "effectful fixture lacks actual ambient definitions"

def run : IO Unit := do
  let program ← get "effectful source check" (checkProgram workspace)
  let requests := program.signatures.functions.map (fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request))
  let plan ← match SourceSpecializationWorklist.run program requests 500 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"effectful plan: {reprStr other}")
  let automatic ← get "effectful base compiler" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let artifact ← get "effectful indexed compiler" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let entry := fun (key value : Nat) => ((.word (w key), .word (w value)) : SourceCoreDataValues.Value × SourceCoreDataValues.Value)
  -- The key's and the RHS's writes stay in their call copies, so the compound
  -- assignment adds `rhs(3)` to the root's default 0.
  exercise artifact program "effects" (some (w 3))
    [[entry 1 3], [], [], [entry 1 20], [entry 1 30, entry 2 40]]
  exercise artifact program "keyFault" none [[], [], [], [entry 1 20]]
  exercise artifact program "rhsFault" none [[], [], [], [entry 1 20], [entry 2 40]]
  IO.println "compatible ambient place key/RHS effects GREEN"

end Tests.SourceCoreCompatibleAmbientPlaceEffects
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleAmbientSnapshot
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Live snapshots use the same generic heap under the indexed compiler's real
frame/marker suffix. Source metadata stays in the base compatible catalog.
The theorem consumers retain static path receipts and independent source
reads/faults; they do not assume generated helper execution. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleAmbientSnapshot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleMapping CompatibleMapping.MixedPaths CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces CompatiblePlaceLiveRoot

/-- No second heap relation is introduced by the live-root adapters. -/
theorem same_heap_model {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient) :
    CompatibleHeap.payloadModel checked registry functions =
      CompatibleAmbientHeap.payloadModel checked registry functions := rfl

variable {checked : Checked} (artifact : SourceCoreCallableIndexedPrograms.Prepared checked)
  {registry : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {prepared : Prepared} {location : Dynamic.Location} {target : Location}
  {cell : Dynamic.Cell} {optional nativeRoot : Value} {sourceRoot : Dynamic.Value}
  {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
  {leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
  {keySites : List (ExpressionId × Ty)} {keys : List Value} {resolved : List Dynamic.EvaluatedProjection}
  {path : PreparedPath checked source site cell.type projections position prepared.steps keySites leaf}
  {identities : Dynamic.Value → Word → Prop}
  {environment : Environment} {context : Core.Context} {keyType : Ty} {reference keyExpression : Expr}

/-- The common represented heap supplies live initialized-root facts even
when its native values mention freshly generated definitions. -/
theorem initialized_root_under_indexed {sourceType : TypeSystem.Ty}
    (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world heap store)
    (ref : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨sourceType, some sourceRoot, none⟩) :
    ∃ native, RootRead checked registry functions mapping world prepared heap store location target
      ⟨sourceType, some sourceRoot, none⟩ (.inRight .unit native) sourceRoot native :=
  CompatibleHeap.HeapRepresents.initialized_root heaps ref read

/-- Actual virtual-root generation recovers a source empty mapping without
initializing the mapped native cell or changing the common heap relation. -/
theorem virtual_root_under_indexed {carrierContext : SourceCoreCompatibleValues.Context}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared carrierContext.checked)
    {functions : FunctionModel carrierContext.checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
    {key valueType : TypeSystem.Ty}
    (heaps : CompatibleAmbientHeap.HeapRepresents carrierContext.checked registry functions mapping world heap store)
    (ref : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨.mapping key valueType, none, none⟩)
    (generated : VirtualRoot.Generated carrierContext prepared.route key valueType)
    (extension : SourceCoreRawMetadata.Extends carrierContext.registry registry) :
    ∃ native, RootRead carrierContext.checked registry functions mapping world prepared heap store location target
      ⟨.mapping key valueType, none, none⟩ (.inLeft prepared.route.rootType .unit) (.mapping key valueType []) native :=
  CompatibleHeap.HeapRepresents.virtual_root heaps ref read generated extension

/-- Successful live getters preserve every source cell and earlier native
administrative cell, while their real allocations extend the native world. -/
theorem snapshot_under_indexed
    (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world heap store)
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot nativeRoot)
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    (leafProjected : checked.catalog.project leaf = .ok prepared.route.leafType)
    {selected : Dynamic.Value} (read : Dynamic.ProjectionsRead (some sourceRoot) resolved (some selected))
    (nonempty : prepared.steps ≠ []) (faithful : DataEquality.IdentityFaithful identities)
    (leaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (envTyped : RuntimeEnvironmentHasTypes world environment context artifact.layouts.definitions)
    (typed : HasType context (.apply (getter prepared keyType) (.pair (.loadCell reference) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) artifact.layouts.definitions)
    (refSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keySelected : DataEquality.Selects environment keyExpression (DataPatternValues.packValues keys)) :
    ∃ native after futureWorld,
      CompatibleAmbientHeap.HeapRepresents checked registry functions mapping futureWorld heap after ∧
      ValueRep checked registry functions mapping futureWorld leaf selected native prepared.route.leafType ∧
      FiniteRun environment store (.apply (getter prepared keyType) (.pair (.loadCell reference) keyExpression))
        (.inRight .word (.inRight .unit native)) after ∧
      after.read? target = some optional ∧ WorldExtends world futureWorld ∧
      AdministrativePreserved mapping store mapping after := by
  obtain ⟨native, after, suffix, future, _, represented, ran, extension, storeTyped, _, finalRoot, frame, appended, _⟩ :=
    read_at root arguments leafProjected read nonempty faithful leaves keyLength heaps.runtime_hasTypes envTyped typed refSelected keySelected
  exact ⟨native, after, future, CompatibleHeap.HeapRepresents.after_snapshot heaps extension storeTyped appended,
    represented, ran, finalRoot.nativeRead, extension, frame⟩

/-- Exact raw missing-default tokens and heap preservation survive the same
ambient extension. No writeback or source mutation is inferred from failure. -/
theorem fault_under_indexed
    (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions mapping world heap store)
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot nativeRoot)
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    {reason : Dynamic.SemanticFault} (fault : Dynamic.ProjectionsFaults (some sourceRoot) resolved reason)
    (nonempty : prepared.steps ≠ []) (faithful : DataEquality.IdentityFaithful identities)
    (leaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (envTyped : RuntimeEnvironmentHasTypes world environment context artifact.layouts.definitions)
    (typed : HasType context (.apply (getter prepared keyType) (.pair (.loadCell reference) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) artifact.layouts.definitions)
    (refSelected : DataEquality.Selects environment reference (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keySelected : DataEquality.Selects environment keyExpression (DataPatternValues.packValues keys)) :
    ∃ token count after futureWorld,
      FaultToken checked registry sourceRoot prepared.steps resolved reason token count ∧
      CompatibleAmbientHeap.HeapRepresents checked registry functions mapping futureWorld heap after ∧
      FiniteRun environment store (.apply (getter prepared keyType) (.pair (.loadCell reference) keyExpression))
        (.inLeft prepared.optionalLeaf (.word token)) after ∧
      after.read? target = some optional ∧ WorldExtends world futureWorld ∧
      AdministrativePreserved mapping store mapping after := by
  obtain ⟨token, count, after, suffix, future, _, receipt, ran, extension, storeTyped, _, finalRoot, frame, appended, _⟩ :=
    fault_at root arguments fault nonempty faithful leaves keyLength heaps.runtime_hasTypes envTyped typed refSelected keySelected
  exact ⟨token, count, after, future, receipt, CompatibleHeap.HeapRepresents.after_snapshot heaps extension storeTyped appended,
    ran, finalRoot.nativeRead, extension, frame⟩

private def w (n : Nat) : Word := Word.ofNatModulo n
private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box { Item(Word) }",
    "function probe(seed: Word) returns (Word) { let f = lam(item: Word) { return item; }; return f(seed); }",
    "function selected(root: mapping(Word => Word), key: Word) returns (Word) { return root[key]; }",
    "function missing(root: mapping(Word => Box), key: Word) returns (Box) { return root[key]; }"
  ]}] }

private def exercise (initial : SourceCoreCompatibleValues.Context)
    (ambient : AmbientDefinitions initial.checked.catalog.definitions) (inertStore : Store)
    (source : TypedSource) (carrier : SourceCoreDataValues.Value) (absent : Bool)
    (expected : Option Word) : IO Unit := do
  let (root, key) ← match source.inputs with
    | [root, key] => pure (root, key) | _ => throw (IO.userError "snapshot input layout changed")
  let keyNode ← match source.nodes.findSome? (fun
    | .expression node => match node.form with
      | .reference _ (.local id) => if id == key.id then some node else none
      | _ => none
    | _ => none) with
    | some node => pure node | none => throw (IO.userError "snapshot key occurrence missing")
  let leaf ← match root.scheme.body with
    | .mapping _ value => pure value | _ => throw (IO.userError "snapshot root type changed")
  let encoded ← match SourceCoreCompatibleValues.encode 500 initial root.scheme.body carrier with
    | .ok encoded => pure encoded | .error error => throw (IO.userError s!"snapshot encode: {reprStr error}")
  let context := encoded.context
  let assignment : AssignmentResolution := ⟨⟨root.id, [.index keyNode.id], leaf⟩, []⟩
  let route ← match described : describe context context.checked.signatures source (.occurrence keyNode.id.occurrence) assignment with
    | .ok route =>
      have _description := CompatiblePlaceDescription.of_describe described
      pure route
    | .error error => throw (IO.userError s!"snapshot describe: {reprStr error}")
  let prepared ← match preparedBy : prepare context 300 route (w 900) (fun _ => w 1000) with
    | .ok prepared =>
      have _static := CompatibleMixedPreparation.of_prepare preparedBy
      pure prepared
    | .error error => throw (IO.userError s!"snapshot prepare: {reprStr error}")
  let optional := if absent then Value.inLeft route.rootType .unit else .inRight .unit encoded.value
  let before := inertStore ++ [optional, Value.integer (-99)]
  let environment := [Value.cellRef (OptionalCell.cellType route.rootType) inertStore.length, .word (w 1)]
  let coreContext := [OptionalCell.referenceType route.rootType, .word]
  let code := Expr.apply (getter prepared .word) (.pair (.loadCell (.var 0)) (.var 1))
  require (infer? coreContext code ambient.definitions == some (LanguageResult.resultType prepared.optionalLeaf)) "ambient snapshot checker rejected getter"
  let initialState := State.initial code environment before
  let (actual, after) ← match runStateful 100000 initialState with
    | .done value after => pure (value, after)
    | other => throw (IO.userError s!"ambient snapshot did not finish: {reprStr other}")
  require (after.take before.length == before) "snapshot changed live root or existing indexed cells"
  require (after.length == before.length + initial.checked.catalog.entries.length + 1) "snapshot administrative allocation count changed"
  match expected, actual with
  | some expected, .inRight .word (.inRight .unit (.word value)) => require (value == expected) "snapshot selected wrong duplicate/default"
  | none, .inLeft _ (.word token) =>
    let header ← match encoded.value with
      | .pair (.word header) _ => pure header | _ => throw (IO.userError "snapshot mapping header missing")
    require (token == (w 1000).add header) "snapshot lost exact raw missing-default token"
  | _, _ => throw (IO.userError s!"snapshot unexpected result: {reprStr actual}")
  match runStateful 2 initialState with
  | .outOfFuel checkpoint => require (runStateful 100000 checkpoint == .done actual after) "snapshot resume changed value/store"
  | _ => throw (IO.userError "snapshot fixture did not checkpoint")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"snapshot source: {reprStr error}")
  let requests := program.signatures.functions.map (fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request))
  let plan ← match SourceSpecializationWorklist.run program requests 500 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"snapshot plan: {reprStr other}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"snapshot base: {reprStr error}")
  let artifact ← match SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"snapshot indexed: {reprStr error}")
  let probe ← match program.signatures.functions.find? (·.name == "probe") with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecialization.SpecializationKey) | none => throw (IO.userError "snapshot probe missing")
  let completion ← match artifact.runSource probe [.word (w 7)] 100000 500 with
    | .ok completed => pure completed | .error error => throw (IO.userError s!"snapshot probe: {reprStr error}")
  match completion.result.native.observation with
  | .succeeded (.word value) _ => require (value == w 7) "snapshot probe returned wrong value"
  | other => throw (IO.userError s!"snapshot probe failed: {reprStr other}")
  require (!artifact.layouts.entries.isEmpty) "snapshot actual marker suffix absent"
  let before := SourceCoreCallableIndexedLedger.store completion
  let full := CallableIndexedAmbient.ambientDefinitions artifact
  let context := SourceCoreCompatibleValues.Context.initial automatic.checked
  let selectedId ← match program.signatures.functions.find? (·.name == "selected") with
    | some signature => pure signature.id | none => throw (IO.userError "snapshot signature absent")
  let selected ← match plan.specializations.find? (·.key.declaration == selectedId) with
    | some specialized => pure specialized.function.typedBody | none => throw (IO.userError "snapshot selected missing")
  let duplicate := SourceCoreDataValues.Value.mapping (.comptime .word) (.comptime .word)
    [(.word (w 1), .word (w 7)), (.word (w 1), .word (w 9))]
  exercise context full before selected duplicate false (some (w 7))
  exercise context full before selected (.mapping .word .word []) true (some Word.zero)
  let missingId ← match program.signatures.functions.find? (·.name == "missing") with
    | some signature => pure signature.id | none => throw (IO.userError "snapshot signature absent")
  let missing ← match plan.specializations.find? (·.key.declaration == missingId) with
    | some specialized => pure specialized.function.typedBody | none => throw (IO.userError "snapshot missing function absent")
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "snapshot Box absent")
  exercise context full before missing (.mapping .word (.nominal box.id []) []) false none
  exercise context full before missing (.mapping .word (.nominal box.id []) []) true none
  IO.println "compatible ambient live-root snapshots GREEN"

end Tests.SourceCoreCompatibleAmbientSnapshot
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleAmbientWriteback
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Successful whole assignment now shares the real indexed definition table
with its function model and native checker receipts. The universal expression
IH and actual static layout remain explicit intermediate obligations. Runtime
regressions store fresh capturing closures and preserve source mapping order;
this does not infer source closure authenticity from native typing alone.
Closures capture by value, so an RHS closure that assigns the root changes only
its call's copy and the setter writes the live root. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleAmbientWriteback
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap GenericExpressionMeaning CompatiblePayload CompatibleEquality CompatibleHeap
open SourceCoreCompatibleDataPlaces CompatibleMapping.MixedPaths

/-- The static native helper types use the artifact's full definitions, while
all source path, metadata and projection receipts retain their base catalog. -/
theorem whole_success_under_indexed {compilation : SourceCoreCompatibleDataPlaces.Context}
    (artifact : SourceCoreCallableIndexedPrograms.Prepared compilation.checked)
    {registry : SourceCoreRawMetadata.Registry}
    {functions : FunctionModel compilation.checked.catalog (CallableIndexedAmbient.ambientDefinitions artifact)}
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : CompatiblePlaceAssignmentSuccess.Layout compilation source certificate scope site place prepared codes sourceTypes leaf
      administrativeContext (definitions := artifact.layouts.definitions))
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := artifact.layouts.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment coreEnvironment)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      FiniteRun coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression (LanguageResult.success .unit) .unit
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inRight .word .unit) finalStore ∧
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    CompatiblePlaceAssignmentSuccess.preserves layout registryExtension meaning faithful observations rhsGenerated found rhsView
      rhsCoreType profile environments heaps locals slot rootTyped trace invalid
  exact ⟨value, finalStore, finalMap, finalWorld, .of_evaluates evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

private def w (n : Nat) : Word := Word.ofNatModulo n
private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "function inc(x: Word) returns (Word) { return x + 1; }",
    "function replace(root: mapping(Word => F), seed: Word) returns (mapping(Word => F)) {",
    " root[1] = lam(x: Word) { return x + seed; }; return root; }",
    "function invoke(root: mapping(Word => F), seed: Word) returns (Word) {",
    " root[1] = lam(x: Word) { return x + seed; }; return root[1](8) + root[2](8); }",
    "function removed(root: mapping(Word => F), seed: Word) returns (Word) {",
    " let rhs = lam() -> F { let empty: mapping(Word => F); root = empty; return lam(x: Word) { return x + seed; }; };",
    " root[1] = rhs(); return 999; }"
  ]}] }
private structure Projection (checked : SourceCoreCompatibleCatalog.Checked) (source : TypeSystem.Ty) (native : Ty) : Type where
  equation : checked.catalog.project source = .ok native
private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey :=
  match program.signatures.functions.find? (·.name == name) with
  | some signature => pure ⟨signature.id, []⟩ | none => throw (IO.userError s!"writeback fixture missing {name}")

def run : IO Unit := do
  let program ← get "writeback source" (checkProgram workspace)
  let requests := program.signatures.functions.map (fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request))
  let plan ← match SourceSpecializationWorklist.run program requests 500 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"writeback plan: {reprStr other}")
  let automatic ← get "writeback base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let artifact ← get "writeback indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let outputs ← get "writeback output cache" (SourceCoreCallableIndexedOutputs.prepare artifact)
  let inc ← key program "inc"
  let functionType := TypeSystem.Ty.function .word .word
  let rootType := TypeSystem.Ty.mapping .word functionType
  let initial : SourceTypedRuntime.Value := .mapping (.comptime .word) (.comptime functionType)
    [(.word (w 1), .global inc []), (.word (w 1), .global inc []), (.word (w 2), .global inc [])]
  require (artifact.layouts.definitions.length > automatic.checked.catalog.definitions.length) "writeback lacks real ambient suffix"
  for name in ["replace", "invoke", "removed"] do
    let owner ← key program name
    let first ← get "writeback start" (artifact.runSource owner [initial, .word (w 5)] 1 500)
    require first.result.native.checkpoint?.isSome "writeback did not checkpoint"
    let completed := first.resume 300000
    let direct ← get "writeback direct" (artifact.runSource owner [initial, .word (w 5)] 300000 500)
    require (completed.result.native.observation == direct.result.native.observation) "writeback resume differs"
    if name == "replace" then
      let projected ← match accepted : automatic.checked.catalog.project rootType with
        | .error error => throw (IO.userError s!"writeback projection: {reprStr error}")
        | .ok type =>
          if same : type = completed.entry.native.resultType then
            pure (show Projection automatic.checked rootType completed.entry.native.resultType from ⟨by simpa only [same] using accepted⟩)
          else throw (IO.userError "writeback result projection changed")
      let exported ← get "writeback mapping output" (SourceCoreCallableIndexedOutputs.decodeSuccess outputs completed rootType projected.equation [] 1024)
      match exported.decoded.source with
      | .mapping rawKey rawValue [(.word first, .closure _ _ _ _ _ captures _), (.word second, .global duplicate _), (.word third, .global other _)] =>
        require (rawKey == .comptime .word && rawValue == .comptime functionType) "writeback changed raw header"
        require (first == w 1 && second == w 1 && third == w 2 && duplicate == inc && other == inc) "writeback changed ordered duplicates or sibling"
        require (!captures.isEmpty) "writeback lost fresh closure captures"
      | other => throw (IO.userError s!"writeback lost returned function mapping: {reprStr other}")
    else if name == "invoke" then
      match completed.result.native.observation with
      | .succeeded (.word value) _ => require (value == w 22) "writeback fresh closure or named sibling changed"
      | other => throw (IO.userError s!"writeback invocation failed: {reprStr other}")
    else
      -- Closures capture by value: the RHS's `root = empty` assigns only its
      -- call's copy of `root`, so the setter still finds key 1 in the live root.
      match completed.result.native.observation with
      | .succeeded (.word value) _ => require (value == w 999) "writeback after the RHS replaced its own root copy changed the result"
      | other => throw (IO.userError s!"RHS root replacement reached the setter's root: {reprStr other}")
      let rootBinder ← match artifact.base.functions.find? (·.specialized.key == owner) with
        | some function => match function.specialized.function.typedBody.inputs with
          | root :: _ => pure root | _ => throw (IO.userError "removed root binder absent")
        | none => throw (IO.userError "removed function absent")
      let ledger ← get "writeback ledger" (SourceCoreCallableIndexedLedger.scan completed)
      -- The root's own row, the RHS's snapshot, the RHS call's copy and the
      -- returned lambda's snapshot.
      let (own, callCopy) ← match ledger.ledger.rows.filter (·.entry.key.binder.id == rootBinder.id) with
        | [own, _, callCopy, _] => pure (own, callCopy) | _ => throw (IO.userError "removed root rows changed")
      let copied ← match callCopy.payload with
        | some native => pure native | none => throw (IO.userError "removed root copy became absent")
      let replaced ← get "writeback RHS root copy" (SourceCoreCompatibleValues.decode 500 completed.result.context rootType copied)
      require (replaced == .mapping .word functionType []) "the RHS's empty root left its call's copy"
      let snapshot ← get "writeback ledger snapshot" (SourceCoreCallableIndexedOutputs.snapshot outputs completed)
      match present : own.payload with
      | none => throw (IO.userError "removed root became absent")
      | some native =>
        match accepted : automatic.checked.catalog.project rootType with
        | .error error => throw (IO.userError s!"writeback root projection: {reprStr error}")
        | .ok type =>
          if same : type = own.entry.key.payloadType then
            let after ← get "writeback remaining root" (SourceCoreCallableIndexedOutputs.decodeData outputs completed ledger
              snapshot rootType native own.entry.key.payloadType (same ▸ accepted) (own.payload_typed ledger.typed present))
            match after.source with
            | .mapping rawKey rawValue [(.word first, .closure _ _ _ _ _ captures _), (.word second, .global duplicate _), (.word third, .global other _)] =>
              require (rawKey == .comptime .word && rawValue == .comptime functionType) "setter changed the live root's raw header"
              require (first == w 1 && second == w 1 && third == w 2 && duplicate == inc && other == inc)
                "setter changed the live root's ordered duplicates or sibling"
              require (!captures.isEmpty) "setter lost the RHS closure's captures"
            | other => throw (IO.userError s!"setter did not store the RHS closure in the live root: {reprStr other}")
          else throw (IO.userError "removed root projection changed")
  IO.println "compatible ambient writeback and fresh function payloads GREEN"

end Tests.SourceCoreCompatibleAmbientWriteback
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleBareAssignment
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Concrete typed RHS trees discharge the child interface for bare assignment
success, all source faults, and completed reflection. Runtime fixtures use the
actual common compiler in a renamed environment with captured ambient values. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleBareAssignment
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatibleBareAssignment

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {faults : FaultRep}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {operator : Syntax.ValueAssignOp} {identities : Dynamic.Value → Word → Prop}

variable {fuel : Nat} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}

theorem preserves_prefix [FunctionCalls.FaultTokens faults]
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place id updated after) (invalid : Word) :
    ∃ updatedValue finalStore finalMap finalWorld slots,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  have meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions)
    program context evidence source (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing
  exact CompatibleBareAssignment.preserves_prefix layout bare extension meaning observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped slot rootTyped trace invalid

theorem preserves_fault [FunctionCalls.FaultTokens faults]
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after)
    (next : Expr) (outputType : Ty) (invalid : Word)
    (invalidToken : faults (.invalidAssignmentOperands operator) invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions)
    program context evidence source (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing
  exact CompatibleBareAssignment.preserves_fault layout bare extension meaning observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped slot rootTyped trace next outputType invalid invalidToken

theorem reflects [FunctionCalls.FaultTokens faults]
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
    (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((reasonAt id).add tag))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : faults (.invalidAssignmentOperands operator) invalid)
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) :
    Result compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
      id actual actualContext ξ next outputType value finalStore := by
  have meaning : TypedGenericExpressionMeaning.Reflects (payloadModel compilation.checked registry functions)
    program context evidence source (CompatibleExpressionTyped.Tree fuel compilation source context solved reasonAt) faults :=
    CompatibleExpressionTyped.reflects functions extension program evidence valid uninitialized missing
  exact CompatibleBareAssignment.reflects layout bare extension meaning observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped slot rootTyped invalidToken completed

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function initializeWord() returns (Word) { let root: Word; let vals: mapping(Bool => Word); root = vals[false] + 2; return root; }",
    "function initializeBool() returns (Bool) { let root: Bool; root = false; return root; }",
    "function initializePair() returns ((Word, Bool)) { let root: (Word, Bool); root = (2, false); return root; }",
    "function initializeNominal() returns (Box<Word>) { let root: Box<Word>; root = .Box(2); return root; }",
    "function initializeMapping() returns (Word) { let root: mapping(Bool => Word); let donor: mapping(Bool => Word); root = donor; return root[true]; }",
    "function compoundPresent() returns (Word) { let root: Word = 10; let vals: mapping(Bool => Word); root += vals[false] + 2; return root; }",
    "function compoundAbsent() returns (Word) { let root: Word; let vals: mapping(Bool => Word); root += vals[false] + 2; return root; }",
    "function rhsFault() returns (Word) { let root: Word; let vals: mapping(Bool => Word); let missing: Word; root += vals[false] + missing; return root; }"
  ]}] }

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (source : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (solved : List SolvedRequirement) (name : String) : IO Unit := do
  let (statement, assignment, operator, rhs) ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .assignValue assignment operator rhs => some (node, assignment, operator, rhs) | _ => none
    | _ => none with
    | some result => pure result | none => throw (IO.userError "bare assignment fixture missing")
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "bare assignment diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "bare assignment owner missing")
  let context : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for binder in SourceCoreCompatibleDataPlaces.declaredBinders source do
    let type ← get "bare assignment binder type" (checked.catalog.project binder.scheme.body)
    let expected ← match binder.scheme.body with
      | .mapping key value => do
        let encoded ← get "bare assignment mapping header" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key value []))
        values := encoded.context
        pure (some encoded.value)
      | _ => pure none
    let initial := if binder.name == "root" && name == "compoundPresent" then
        OptionalCell.allocateInitialized type (.word (Word.ofNatModulo 10))
      else OptionalCell.allocate type
    bindings := bindings ++ [(binder, type, initial, expected)]
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let representation := SourceCoreCompatibleFunctions.representation values 150
  let child : SourceCoreCompatibleDataPlaces.ExpressionLowerer := fun fuel source scope id reasonAt =>
    SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation checked.signatures prepared.locals
      prepared.contexts own.assignments diagnostics context prepared.callableContext none none fuel source scope id reasonAt
  let reasonAt := diagnostics.reasonAt owner
  let invalid := Word.ofNatModulo 999
  let nextId ← match source.nodes.findSome? fun
    | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
    | _ => none with
    | some id => pure id | none => throw (IO.userError "bare assignment return missing")
  let next ← get "bare assignment continuation" (child 150 source scope nextId reasonAt)
  match bare : assignment.target.projections with
  | _ :: _ => throw (IO.userError "bare fixture unexpectedly projected")
  | [] =>
    match accepted : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures child 150 source scope
        (.occurrence statement.id.occurrence) assignment operator (some rhs) next.type next.expression
        reasonAt invalid invalid (fun _ => invalid) with
    | .error error => throw (IO.userError s!"bare actual compiler: {reprStr error}")
    | .ok lowered =>
      have receipt := CompatibleBareAssignment.of_lower (compilation := values) (source := source) (scope := scope)
        (expression := child) bare accepted
      let _receipt := receipt
      let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
      let frameExpr := SourceCoreCallableIndexedFrames.empty frame
      let closureType := Ty.function .unit frame.type
      let closure := Expr.lambda .unit frame.type (.var 1)
      let body := bindings.foldl (fun body (_, _, initial, _) => Expr.letE initial body)
        (.letE (.integer 91) (lowered.weakenAt 0))
      let native : Core.Program := ⟨LanguageResult.resultType next.type,
        .letE frameExpr (.letE (.newCell closureType closure) body), checked.catalog.definitions ++ [frame.definition]⟩
      assertTrue native.check s!"bare assignment {name} ambient checker rejected"
      let completed ← match native.runStateful 200000 with
        | .done result store => pure (result, store)
        | other => throw (IO.userError s!"bare assignment {name} incomplete: {reprStr other}")
      for fuel in [0, 5, 40, 120] do
        let result := match native.runStateful fuel with
          | .outOfFuel checkpoint => Core.runStateful 200000 checkpoint
          | other => other
        assertTrue (result == .done completed.1 completed.2) s!"bare assignment {name} resume changed result/store"
      assertTrue (completed.2[0]? == some (.closure .unit frame.type (.var 1) [.constructed frame.empty .unit]))
        "bare assignment changed existing captured ambient closure"
      let fault := name == "compoundAbsent" || name == "rhsFault"
      if fault then
        let token ← if name == "rhsFault" then do
          let occurrence ← match source.nodes.findSome? fun
            | .expression node => match node.form with | .reference "missing" (.local _) => some node.id | _ => none
            | _ => none with
            | some id => pure id | none => throw (IO.userError "bare RHS missing occurrence")
          pure (reasonAt occurrence)
        else pure invalid
        assertTrue (completed.1 == .inLeft next.type (.word token)) s!"bare assignment {name} fault order changed"
      else
        let expected : Option Value := match name with
          | "initializeWord" => some (.word (Word.ofNatModulo 2))
          | "initializeBool" => some (.bool false)
          | "initializePair" => some (.pair (.word (Word.ofNatModulo 2)) (.bool false))
          | "initializeMapping" => some (.word Word.zero)
          | "compoundPresent" => some (.word (Word.ofNatModulo 12))
          | _ => none
        match expected with
        | some expected => assertTrue (completed.1 == .inRight .word expected) s!"bare assignment {name} wrong result"
        | none => match completed.1 with
          | .inRight .word (.constructed tag (.pair (.word header) (.word word))) =>
            let metadata ← match source.nodes.findSome? fun
              | .expression {form := .constructor metadata _, ..} => some metadata
              | _ => none with
              | some metadata => pure metadata | none => throw (IO.userError "bare nominal source metadata absent")
            assertTrue (word == Word.ofNatModulo 2 && values.registry.id? (.constructor metadata) == some header &&
              checked.catalog.constructor? metadata == some tag) "bare nominal payload/raw header changed"
          | _ => throw (IO.userError "bare nominal result lost raw carrier")
      for ((binder, type, _, expected), position) in bindings.zipIdx do
        let cell ← match completed.2[bindings.length - position]? with
          | some cell => pure cell | none => throw (IO.userError "bare assignment lost source cell")
        if binder.name == "root" then
          if fault then assertTrue (cell == .inLeft type .unit) "bare assignment wrote before fault"
          else if name == "initializeMapping" then
            let some expected := expected | throw (IO.userError "bare mapping header absent")
            assertTrue (cell == .inRight .unit expected) "bare mapping assignment changed retained metadata"
          else match completed.1 with
            | .inRight .word value => assertTrue (cell == .inRight .unit value) "bare assignment result differs from root"
            | _ => throw (IO.userError "bare successful result missing")
        else if binder.name == "missing" then
          assertTrue (cell == .inLeft type .unit) "bare RHS fault rewrote missing local"
        else
          let some expected := expected | throw (IO.userError "bare mapping effect fixture absent")
          assertTrue (cell == .inRight .unit expected) s!"bare assignment {name} lost earlier mapping effect"

-- Integer compound syntax remains rejected by source inference. This separate
-- typed IR fixture checks the already accepted compiler policy boundary.
private def integerOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"bare_integer", by decide⟩], by decide⟩⟩, 0⟩
private def integerRoot : Resolved.LocalId := ⟨integerOwner, 0⟩
private def integerRight : Resolved.LocalId := ⟨integerOwner, 1⟩
private def integerId : ExpressionId := ⟨⟨integerOwner, 0⟩⟩
private def integerSource : TypedSource := {
  owner := integerOwner
  inputs := [{id := integerRoot, name := "root", scheme := .mono .integer}, {id := integerRight, name := "rhs", scheme := .mono .integer}]
  roots := [.expression integerId]
  nodes := [.expression {
    id := integerId
    span := {source := {origin := .main, path := "bare_integer.solc"}, startByte := 0, endByte := 1}
    type := .integer
    form := .reference "rhs" (.local integerRight) }]
}

private def integerPolicy (checked : SourceCoreCompatibleCatalog.Checked) : IO Unit := do
  let values := SourceCoreCompatibleValues.Context.initial checked
  let scope : SourceCoreLocalCell.Scope := [(integerRight, .integer), (integerRoot, .integer)]
  let child : SourceCoreCompatibleDataPlaces.ExpressionLowerer := fun fuel source scope id reasonAt => do
    let (_, type) ← SourceCoreCompatibleDataExpressions.readExpression checked source id
    let expression ← SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id)
    pure ⟨type, expression⟩
  let assignment : AssignmentResolution := {target := {root := integerRoot, projections := [], type := .integer}}
  let invalid := Word.ofNatModulo 999
  let readReason := Word.ofNatModulo 777
  let next := OptionalCell.read .integer (.var 1) readReason
  for (operator, expected) in ([
      (.equal, 3), (.add, -4), (.subtract, -10), (.multiply, -21), (.divide, -3),
      (.modulo, 2), (.bitAnd, 1), (.bitOr, -5), (.bitXor, -6)] : List (Syntax.ValueAssignOp × Int)) do
    match accepted : SourceCoreCompatibleDataPlaces.lower values checked.signatures child 100 integerSource scope
        (.occurrence integerId.occurrence) assignment operator (some integerId) .integer next
        (fun _ => readReason) invalid invalid (fun _ => invalid) with
    | .error error => throw (IO.userError s!"bare Integer actual compiler: {reprStr error}")
    | .ok code =>
      have receipt := CompatibleBareAssignment.of_lower (compilation := values) (expression := child) rfl accepted
      let _receipt := receipt
      let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
      for (old, right) in ([(some (-7), some 3), (none, some 3), (none, none)] : List (Option Int × Option Int)) do
        let allocate := fun value => match value with
          | some value => OptionalCell.allocateInitialized .integer (.integer value)
          | none => OptionalCell.allocate .integer
        let body := Expr.letE (SourceCoreCallableIndexedFrames.empty frame)
          (.letE (.newCell (.function .unit frame.type) (.lambda .unit frame.type (.var 1)))
            (.letE (allocate old) (.letE (allocate right) (.letE (.integer 91) (code.weakenAt 0)))))
        let native : Core.Program := ⟨LanguageResult.resultType .integer, body, checked.catalog.definitions ++ [frame.definition]⟩
        assertTrue native.check "bare Integer ambient checker rejected"
        let changed := if right.isNone then old else if old.isNone && operator != .equal then old else some expected
        let result := if right.isNone then .inLeft .integer (.word readReason)
          else if old.isNone && operator != .equal then .inLeft .integer (.word invalid)
          else .inRight .word (.integer expected)
        let optional := fun value => match value with
          | some value => Value.inRight .unit (.integer value)
          | none => .inLeft .integer .unit
        let expectedStore := [.closure .unit frame.type (.var 1) [.constructed frame.empty .unit], optional changed, optional right]
        let completed := native.runStateful 20000
        assertTrue (completed == .done result expectedStore) s!"bare Integer result/store/order changed: {reprStr operator}"
        for fuel in [0, 4, 25, 70] do
          let resumed := match native.runStateful fuel with
            | .outOfFuel checkpoint => Core.runStateful 20000 checkpoint
            | other => other
          assertTrue (resumed == completed) "bare Integer resume changed exact store"
  let rejected : Workspace.RawWorkspace := {
    entry := "main.solc"
    externalLibraries := []
    mainSources := [{path := "main.solc", content := "function rejected(x: integer, y: integer) returns (integer) { x += y; return x; }"}]}
  match checkProgram rejected with
  | .error [.inference _] => pure ()
  | _ => throw (IO.userError "bare Integer compound source admission changed")

def run : IO Unit := do
  let program ← get "bare assignment checked source" (checkProgram workspace)
  let roots := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program roots 300 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"bare specialization: {reprStr other}")
  let automatic ← get "bare assignment factory" (SourceCoreCompatibleFunctions.prepare program plan 400)
  for function in automatic.prepared.functions do
    let name := (program.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    inspect automatic.prepared function.specialized.function.typedBody function.signature.key
      function.specialized.function.solvedRequirements name
  assertTrue (automatic.prepared.functions.length == 8) "bare assignment fixture coverage missing"
  integerPolicy automatic.checked
  IO.println "bare assignment: absent/equal, Word/Integer compound, mapping/raw carriers, effects, capture and resume GREEN"

end Tests.SourceCoreCompatibleBareAssignment
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleBareBitNot
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleBareBitNot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"bare_bitnot", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [.word, .integer]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [.word, .integer]).toOption.get catalogExists
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def binder (type : TypeSystem.Ty) : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono type, [], false, none⟩
private def source (type : TypeSystem.Ty) : TypedSource := { owner, inputs := [binder type], roots := [], nodes := [] }
private def assignment (type : TypeSystem.Ty) : AssignmentResolution := ⟨⟨(binder type).id, [], type⟩, []⟩
private def scope (type : Core.Ty) : SourceCoreLocalCell.Scope := [((binder .word).id, type)]
private def nativeEnvironment (type : Core.Ty) : Environment := [.cellRef (OptionalCell.cellType type) 0]
private def nativeContext (type : Core.Ty) : Core.Context := [OptionalCell.referenceType type]
private def wordContext := (SourceSemantics.Context.ofSignatures signatures).withLocal (binder .word).id (binder .word).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def sourceEnvironment : Dynamic.Environment := [((binder .word).id, ⟨0⟩)]
private def sourceHeap (initial : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨.word, initial, none⟩]⟩
private def world : StoreTyping := [OptionalCell.cellType .word]
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem localAgrees (initial : Option Dynamic.Value) :
    Dynamic.EnvironmentAgrees (sourceHeap initial) wordContext.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal wordContext (binder .word).id .word :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder .word).id (binder .word).scheme,
    .builtin .word⟩
private theorem writable : ∀ actual, rootBinder (source .word) (assignment .word).target.root = .ok actual →
    WritableLocal wordContext (assignment .word).target.root actual.scheme.body := by
  intro actual found
  have same := Except.ok.inj (found.symm.trans
    (show rootBinder (source .word) (assignment .word).target.root = .ok (binder .word) by cbv))
  subst actual
  exact rootWritable

/-- A child compiler which always rejects proves no source child is lowered
by this branch. It is not used as a replacement expression compiler. -/
private def noChildren : ExpressionLowerer := fun _ _ _ id _ => .error (.missingExpression id)
private def invalid : Word := Word.ofNatModulo 41
private def projectionFault : Word := Word.ofNatModulo 73
private def next : Expr := LanguageResult.success (.bool true)
private def compile (raw : TypeSystem.Ty) (type : Core.Ty) (tail : Expr := next) :=
  lowerChecked compilation checked.signatures noChildren 100 (source raw) (scope type) site (assignment raw) .equal none .bool tail
    (fun _ => Word.zero) projectionFault invalid (fun _ => Word.zero) checked.catalog.definitions (nativeContext type)

/-- Actual compiler receipt plus actual completed native execution imply an
independent source result, with no prior source execution or child IH. -/
theorem actual_reflects {certified : Certified checked.catalog.definitions (nativeContext .word) .bool}
    (accepted : compile .word .word = .ok certified)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked compilation.registry (noFunctions checked.catalog)) [] []
      ⟨.word, initial, none⟩ native .word)
    {result : Value} {after : Store}
    (completed : Evaluates (nativeEnvironment .word) [native] certified.expression result after) :
    CompatiblePlaceBitNotMeaning.Result checked compilation.registry (noFunctions checked.catalog) program wordContext [] (source .word)
      (fun _ _ => True) (assignment .word).target sourceEnvironment (nativeEnvironment .word)
      (sourceHeap initial) [native] [0] world next .bool result after := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate initialRep Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [] (scope .word) sourceEnvironment (nativeEnvironment .word) :=
    .cons reference (.nil .nil)
  exact CompatibleBareBitNotLowering.reflects writable rfl (.inl rfl) environments heaps (localAgrees initial)
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) True.intro completed

private theorem absentFault : Dynamic.SourcePlaceBitNotFaults program wordContext [] (source .word) sourceEnvironment
    (sourceHeap none) (assignment .word).target (.invalidUnaryOperand .bitNot) (sourceHeap none) :=
  .uninitialized (CompatibleBareBitNotMeaning.resolves rfl .head (.intro .head)
    (.uninitialized (by rintro ⟨a, b, impossible⟩; cases impossible))) rfl

/-- The source absent-operand rule produces the actual compiler's exact token
and preserves the store. This instantiates the independent fault direction. -/
theorem actual_absent {certified : Certified checked.catalog.definitions (nativeContext .word) .bool}
    (accepted : compile .word .word = .ok certified) :
    Evaluates (nativeEnvironment .word) [.inLeft .word .unit] certified.expression (.inLeft .bool (.word invalid)) [.inLeft .word .unit] := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate (GenericHeap.CellRepresents.uninitialized (show checked.catalog.project .word = .ok .word by rfl))
    Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [] (scope .word) sourceEnvironment (nativeEnvironment .word) :=
    .cons reference (.nil .nil)
  exact (CompatibleBareBitNotLowering.preserves_fault writable rfl (.inl rfl) environments heaps (localAgrees none)
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) absentFault).2.2

private def seven : Word := Word.ofNatModulo 7
private theorem sourceUpdate : Dynamic.SourcePlaceSnapshotUpdate program wordContext [] (source .word) Dynamic.BitNotSnapshot
    sourceEnvironment (sourceHeap (some (.word seven))) (assignment .word).target (.word seven.bitNot)
    (sourceHeap (some (.word seven.bitNot))) :=
  .intro (CompatibleBareBitNotMeaning.resolves rfl .head (.intro .head) .initialized)
    (.intro (.intro .head) rfl .initialized (.leaf (.word seven)) (DataPlaceCommitReflection.source_writes (.intro .head) _))

/-- The success direction consumes an independent snapshot update, with one
physical write and the original map/world. -/
theorem actual_preserves {code : Expr}
    (accepted : lower compilation checked.signatures noChildren 100 (source .word) (scope .word) site (assignment .word) .equal none
      .unit (LanguageResult.success .unit) (fun _ => Word.zero) projectionFault invalid (fun _ => Word.zero) = .ok code) :
    ∃ after, Evaluates (nativeEnvironment .word) [.inRight .unit (.word seven)] code (.inRight .word .unit) after ∧
      HeapRepresents checked compilation.registry (noFunctions checked.catalog) [0] world
        (sourceHeap (some (.word seven.bitNot))) after ∧
      AdministrativePreserved [0] [.inRight .unit (.word seven)] [0] after ∧
      Dynamic.HeapMetadataExtend (sourceHeap (some (.word seven))) (sourceHeap (some (.word seven.bitNot))) := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate (GenericHeap.CellRepresents.initialized (ValueRep.word seven)) Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [] (scope .word) sourceEnvironment (nativeEnvironment .word) :=
    .cons reference (.nil .nil)
  exact CompatibleBareBitNotLowering.preserves writable rfl (.inl rfl) environments heaps
    (localAgrees (some (.word seven))) (by rfl) accepted sourceUpdate

private def exercise (raw : TypeSystem.Ty) (type : Core.Ty) (initial expected : Value) (succeeds : Bool) : IO Unit := do
  match compile raw type with
  | .error error => throw (IO.userError s!"bare bit-not compile: {reprStr error}")
  | .ok certified =>
    let start := State.initial certified.expression (nativeEnvironment type) [initial]
    let wanted := if succeeds then Value.inRight .word (.bool true) else .inLeft .bool (.word invalid)
    let after := [expected]
    unless runStateful 1000 start == .done wanted after do throw (IO.userError "bare bit-not output/store mismatch")
    match runStateful 7 start with
    | .outOfFuel checkpoint => unless runStateful 1000 checkpoint == .done wanted after do
        throw (IO.userError "bare bit-not resume mismatch")
    | _ => throw (IO.userError "bare bit-not checkpoint missing")
  -- A continuation which writes the root must also be skipped on absence.
  let effect := Expr.letE (.storeCell (.var 0) (.inLeft type .unit)) (LanguageResult.success (.bool true))
  match compile raw type effect with
  | .error error => throw (IO.userError s!"bare bit-not effect compile: {reprStr error}")
  | .ok certified =>
    let empty := Value.inLeft type .unit
    unless runStateful 1000 (State.initial certified.expression (nativeEnvironment type) [empty]) ==
        .done (.inLeft .bool (.word invalid)) [empty] do throw (IO.userError "absent operand ran continuation")

def run : IO Unit := do
  match accepted : compile .word .word with
  | .error error => throw (IO.userError s!"bare bit-not Word compile: {reprStr error}")
  | .ok certified =>
    have _finite := actual_absent accepted
    match ran : runStateful 1000 (State.initial certified.expression (nativeEnvironment .word) [.inRight .unit (.word seven)]) with
    | .done result after =>
      have _source := actual_reflects accepted (.initialized (.word seven)) (runStateful_evaluation_sound ran)
      unless result == .inRight .word (.bool true) && after == [.inRight .unit (.word seven.bitNot)] do
        throw (IO.userError "bare bit-not proof consumer mismatch")
    | _ => throw (IO.userError "bare bit-not proof consumer incomplete")
  exercise .word .word (.inLeft .word .unit) (.inLeft .word .unit) false
  exercise .word .word (.inRight .unit (.word seven)) (.inRight .unit (.word seven.bitNot)) true
  -- Integer compound remains a trusted retained-IR profile, not checker admission.
  exercise .integer .integer (.inLeft .integer .unit) (.inLeft .integer .unit) false
  for value in [0, 7, -7, -(2^300 : Int)] do
    exercise .integer .integer (.inRight .unit (.integer value)) (.inRight .unit (.integer (~~~value))) true
  IO.println "bare bit-not actual lowering/independent meaning/absent store preservation/no children/single write/resume GREEN"

end Tests.SourceCoreCompatibleBareBitNot
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleBitNot
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleBitNot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_lower_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_lower_reflection.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def rootType : TypeSystem.Ty := .mapping .bool .word
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.index key], .word⟩, []⟩
private def context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem observations : FunctionObservations checked.catalog (noFunctions checked.catalog) (fun _ _ => False) := by
  intro _ _ _ _ _ _ _ impossible; exact impossible.elim
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem unique : NodeOccurrencesUnique source := by simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]
private theorem contains : ContainsExpression source key node := lookupExpression?_sound (by cbv)
private def lowered : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def Child : GenericExpressionMeaning.Certificate := fun _ id code => id = key ∧ code = lowered

/-- The child reflection IH is proved uniformly, including every hidden-slot
renaming. Its source execution is constructed from the completed Core child. -/
private theorem childReflects (registry : SourceCoreRawMetadata.Registry) (faults : GenericExpressionMeaning.FaultRep) :
    GenericExpressionMeaning.Reflects (payloadModel checked registry (noFunctions checked.catalog))
      program context [] source Child faults := by
  intro scope id code certificate n found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  obtain ⟨rfl, rfl⟩ := certificate
  have nodeEq : n = node := Option.some.inj (found.symm.trans (show source.lookupExpression? key = some node by cbv))
  subst n
  cases evaluated with
  | inRight inner =>
    cases inner
    exact ⟨.value (.bool true), before, mapping, world, .value (.intro contains (.builtinBoolean rfl) .nil),
      .value (.bool true), heaps, .refl _, .refl _, .refl _ _, .refl _⟩

private theorem functionViews : FunctionRuntimeViews (noFunctions checked.catalog) := fun impossible => False.elim impossible
private theorem rootExists : (checked.catalog.project rootType).toOption.isSome = true := by cbv
private def rootCore := (checked.catalog.project rootType).toOption.get rootExists
private theorem rootProjected : checked.catalog.project rootType = .ok rootCore := except_get _ rootExists
private def scope : SourceCoreLocalCell.Scope := [(binder.id, rootCore)]
private def coreContext : Core.Context := [OptionalCell.referenceType rootCore]
private def before (initial : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨rootType, initial, none⟩]⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def world : StoreTyping := [OptionalCell.cellType rootCore]
private def nativeEnvironment : Environment := [.cellRef (OptionalCell.cellType rootCore) 0]
private theorem localAgrees (initial : Option Dynamic.Value) : Dynamic.EnvironmentAgrees (before initial) context.locals environment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal context binder.id rootType :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme,
    .mapping (.builtin .bool) (.builtin .word)⟩
private theorem keyTyped : ExpressionHasType source context key .bool := by
  apply ExpressionHasType.ofOrdinary (node := node) (rawType := .bool) contains
    (.reference (.builtinBoolean true)) (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme))
    (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme))
  · intro id member; cases member
  · exact .nil _
  · rfl

/-- The fixture admits its only retained child occurrence and calls the real
Basic compiler in that branch. It contains no evaluator or hypothetical code. -/
private def childCompiler : ExpressionLowerer := fun fuel source scope id reasonAt =>
  if id = key then SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)
  else .error (.missingExpression id)
private theorem childReceipt (id : ExpressionId) (code : SourceCoreBasic.LoweredExpr)
    (accepted : childCompiler 100 source scope id (fun _ => Word.zero) = .ok code) :
    ∃ node, source.lookupExpression? id = some node ∧ Child scope id code ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ []) code.expression (LanguageResult.resultType code.type) checked.catalog.definitions := by
  unfold childCompiler at accepted
  split at accepted
  · rename_i same
    subst id
    have actual : SourceCoreBasic.lowerExpression 100 source scope key Word.zero = .ok lowered := by cbv
    rw [actual] at accepted
    cases accepted
    exact ⟨node, (by cbv), ⟨rfl, rfl⟩, .inRight .word .bool⟩
  · cases accepted

/-- A successful run of the real lowerer's output yields a complete source
assignment and final represented heap. Path, key views and both helper typing
receipts are extracted internally, not supplied by this fixture. -/
theorem actual_lower_reflects {code : Expr}
    (accepted : lower compilation checked.signatures childCompiler 100 source scope site assignment .equal none .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) = .ok code)
    (typed : HasType coreContext code (LanguageResult.resultType .bool) checked.catalog.definitions)
    {registry : SourceCoreRawMetadata.Registry} (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked registry (noFunctions checked.catalog)) [] []
      ⟨rootType, initial, none⟩ native rootCore)
    {after : Store}
    (completed : Evaluates nativeEnvironment [native] code (.inRight .word (.bool true)) after) :
    ∃ updated sourceAfter finalMap finalWorld,
      Dynamic.SourcePlaceSnapshotUpdate program context [] source Dynamic.BitNotSnapshot
        environment (before initial) assignment.target updated sourceAfter ∧
      HeapRepresents checked registry (noFunctions checked.catalog) finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends [0] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [0] [native] finalMap after ∧ Dynamic.HeapMetadataExtend (before initial) sourceAfter := by
  have empty : HeapRepresents checked registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate initialRep Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [] scope environment nativeEnvironment :=
    .cons reference (.nil .nil)
  have binding : ∀ actual, rootBinder source assignment.target.root = .ok actual → actual = binder := by
    intro actual found
    exact Except.ok.inj (found.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  -- The trivial relation relates every panic too.
  haveI : FunctionCalls.FaultTokens (fun _ _ => True) := ⟨fun _ => trivial⟩
  have reflected := CompatiblePlaceBitNotLowerReflection.reflects (compilation := compilation)
    (ambient := .original checked.catalog.definitions) (functions := noFunctions checked.catalog) (certificate := Child)
    unique rfl (fun actual found => by cases binding actual found; exact .index keyTyped (.nil _))
    (fun actual found => by cases binding actual found; exact rootWritable) (by simp [assignment])
    (fun id code accepted => let ⟨node, found, child, _⟩ := childReceipt id code accepted; ⟨node, found, child⟩) accepted typed
    registryExtension (childReflects registry (fun _ _ => True)) functionViews faithful observations
    (fun _ _ => True.intro) (fun _ => True.intro) rfl environments heaps (localAgrees initial) completed
  cases reflected with
  | fault _ resultEq => cases resultEq
  | committed trace heaps maps worlds frame metadata length continuation =>
    simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, lowered, LanguageResult.success] at continuation
    cases continuation with
    | inRight valueEvaluated =>
      cases valueEvaluated
      exact ⟨_, _, _, _, trace, heaps, maps, worlds, frame, metadata⟩

/-- Direct consumer of the real checked wrapper: its private compiler work
is recovered from success and its public typing field. -/
theorem checked_lower_reflects {certified : Certified checked.catalog.definitions coreContext .bool}
    (accepted : lowerChecked compilation checked.signatures childCompiler 100 source scope site assignment .equal none .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) checked.catalog.definitions coreContext = .ok certified)
    {registry : SourceCoreRawMetadata.Registry} (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked registry (noFunctions checked.catalog)) [] []
      ⟨rootType, initial, none⟩ native rootCore)
    {after : Store}
    (completed : Evaluates nativeEnvironment [native] certified.expression (.inRight .word (.bool true)) after) :
    ∃ updated sourceAfter finalMap finalWorld,
      Dynamic.SourcePlaceSnapshotUpdate program context [] source Dynamic.BitNotSnapshot
        environment (before initial) assignment.target updated sourceAfter ∧
      HeapRepresents checked registry (noFunctions checked.catalog) finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends [0] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [0] [native] finalMap after ∧ Dynamic.HeapMetadataExtend (before initial) sourceAfter :=
  actual_lower_reflects (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) certified.typed registryExtension initialRep completed

private def exercise {certified : Certified checked.catalog.definitions coreContext .bool}
    (accepted : lowerChecked compilation checked.signatures childCompiler 100 source scope site assignment .equal none .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) checked.catalog.definitions coreContext = .ok certified)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked registry (noFunctions checked.catalog)) [] []
      ⟨rootType, initial, none⟩ native rootCore)
    (expected : SourceCoreDataValues.Value) : IO Unit := do
  let start := Core.State.initial certified.expression nativeEnvironment [native]
  match ran : runStateful 200000 start with
  | .done result after =>
    if success : result = .inRight .word (.bool true) then
      have _source := checked_lower_reflects accepted extension initialRep (success ▸ runStateful_evaluation_sound ran)
      unless after.length == 1 + 3 * (checked.catalog.entries.length + 1) do
        throw (IO.userError "compatible bit-not admin count changed")
      match after.read? 0 with
      | some (.inRight .unit value) =>
        let outputContext : SourceCoreCompatibleValues.Context := ⟨checked, registry, extension⟩
        match SourceCoreCompatibleValues.decode 100 outputContext rootType value with
        | .ok actual => unless actual == expected do
            throw (IO.userError "compatible bit-not raw metadata or ordered duplicates changed")
        | .error error => throw (IO.userError s!"compatible bit-not decode failed {reprStr error}")
      | _ => throw (IO.userError "compatible bit-not missing mapped write")
      match runStateful 17 start with
      | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done result after do
          throw (IO.userError "compatible bit-not resume changed result")
      | _ => throw (IO.userError "compatible bit-not expected checkpoint")
    else throw (IO.userError "compatible bit-not expected success")
  | other => throw (IO.userError s!"compatible bit-not run failed {reprStr other}")

private def seven : Word := Word.ofNatModulo 7
private def nine : Word := Word.ofNatModulo 9
private def carrier : SourceCoreDataValues.Value :=
  .mapping (.comptime .bool) (.comptime .word) [(.bool true, .word seven), (.bool true, .word nine)]
private def sourceValue : Dynamic.Value :=
  .mapping (.comptime .bool) (.comptime .word) [(.bool true, .word seven), (.bool true, .word nine)]
private theorem carrierMeaning : CompatibleEncoding.Means carrier sourceValue :=
  .mapping (.prepend (.bool true) (.word seven) (.prepend (.bool true) (.word nine) .empty))

def run : IO Unit := do
  match accepted : lowerChecked compilation checked.signatures childCompiler 100 source scope site assignment .equal none .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) checked.catalog.definitions coreContext with
  | .error error => throw (IO.userError s!"compatible bit-not rejected {reprStr error}")
  | .ok _certified =>
      exercise accepted (.refl _) (.uninitialized rootProjected)
        (.mapping .bool .word [(.bool true, .word Word.zero.bitNot)])
      match encoded : SourceCoreCompatibleValues.encode 100 compilation rootType carrier with
      | .error error => throw (IO.userError s!"compatible bit-not encode failed {reprStr error}")
      | .ok encodedValue =>
        have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) encoded carrierMeaning [] []
        have same := Except.ok.inj (represented.projection.symm.trans rootProjected)
        exercise accepted encodedValue.preserves (.initialized (same ▸ represented))
          (.mapping (.comptime .bool) (.comptime .word) [(.bool true, .word seven.bitNot), (.bool true, .word nine)])
  IO.println "absent-RHS bit-not actual compiler/source meaning/Unit slot/raw duplicate order/virtual root/resume GREEN"

end Tests.SourceCoreCompatibleBitNot
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleIntegerBitNot
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Retained Integer IR exercises the actual compatible compiler and independent
snapshot semantics. Source checker compound admission remains Word-only. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleIntegerBitNot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_lower_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_lower_reflection.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def rootType : TypeSystem.Ty := .mapping .bool .integer
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.index key], .integer⟩, []⟩
private def context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem observations : FunctionObservations checked.catalog (noFunctions checked.catalog) (fun _ _ => False) := by
  intro _ _ _ _ _ _ _ impossible; exact impossible.elim
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem unique : NodeOccurrencesUnique source := by simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]
private theorem contains : ContainsExpression source key node := lookupExpression?_sound (by cbv)
private def lowered : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def Child : GenericExpressionMeaning.Certificate := fun _ id code => id = key ∧ code = lowered

/-- The child reflection IH is proved uniformly, including every hidden-slot
renaming. Its source execution is constructed from the completed Core child. -/
private theorem childReflects (registry : SourceCoreRawMetadata.Registry) (faults : GenericExpressionMeaning.FaultRep) :
    GenericExpressionMeaning.Reflects (payloadModel checked registry (noFunctions checked.catalog))
      program context [] source Child faults := by
  intro scope id code certificate n found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  obtain ⟨rfl, rfl⟩ := certificate
  have nodeEq : n = node := Option.some.inj (found.symm.trans (show source.lookupExpression? key = some node by cbv))
  subst n
  cases evaluated with
  | inRight inner =>
    cases inner
    exact ⟨.value (.bool true), before, mapping, world, .value (.intro contains (.builtinBoolean rfl) .nil),
      .value (.bool true), heaps, .refl _, .refl _, .refl _ _, .refl _⟩

private theorem functionViews : FunctionRuntimeViews (noFunctions checked.catalog) := fun impossible => False.elim impossible
private theorem rootExists : (checked.catalog.project rootType).toOption.isSome = true := by cbv
private def rootCore := (checked.catalog.project rootType).toOption.get rootExists
private theorem rootProjected : checked.catalog.project rootType = .ok rootCore := except_get _ rootExists
private def scope : SourceCoreLocalCell.Scope := [(binder.id, rootCore)]
private def coreContext : Core.Context := [OptionalCell.referenceType rootCore]
private def before (initial : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨rootType, initial, none⟩]⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def world : StoreTyping := [OptionalCell.cellType rootCore]
private def nativeEnvironment : Environment := [.cellRef (OptionalCell.cellType rootCore) 0]
private theorem localAgrees (initial : Option Dynamic.Value) : Dynamic.EnvironmentAgrees (before initial) context.locals environment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal context binder.id rootType :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme,
    .mapping (.builtin .bool) (.builtin .integer)⟩
private theorem keyTyped : ExpressionHasType source context key .bool := by
  apply ExpressionHasType.ofOrdinary (node := node) (rawType := .bool) contains
    (.reference (.builtinBoolean true)) (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme))
    (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme))
  · intro id member; cases member
  · exact .nil _
  · rfl

/-- The fixture admits its only retained child occurrence and calls the real
Basic compiler in that branch. It contains no evaluator or hypothetical code. -/
private def childCompiler : ExpressionLowerer := fun fuel source scope id reasonAt =>
  if id = key then SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)
  else .error (.missingExpression id)
private theorem childReceipt (id : ExpressionId) (code : SourceCoreBasic.LoweredExpr)
    (accepted : childCompiler 100 source scope id (fun _ => Word.zero) = .ok code) :
    ∃ node, source.lookupExpression? id = some node ∧ Child scope id code ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ []) code.expression (LanguageResult.resultType code.type) checked.catalog.definitions := by
  unfold childCompiler at accepted
  split at accepted
  · rename_i same
    subst id
    have actual : SourceCoreBasic.lowerExpression 100 source scope key Word.zero = .ok lowered := by cbv
    rw [actual] at accepted
    cases accepted
    exact ⟨node, (by cbv), ⟨rfl, rfl⟩, .inRight .word .bool⟩
  · cases accepted

/-- A successful run of the real lowerer's output yields a complete source
assignment and final represented heap. Path, key views and both helper typing
receipts are extracted internally, not supplied by this fixture. -/
theorem actual_lower_reflects {code : Expr}
    (accepted : lower compilation checked.signatures childCompiler 100 source scope site assignment .equal none .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) = .ok code)
    (typed : HasType coreContext code (LanguageResult.resultType .bool) checked.catalog.definitions)
    {registry : SourceCoreRawMetadata.Registry} (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked registry (noFunctions checked.catalog)) [] []
      ⟨rootType, initial, none⟩ native rootCore)
    {after : Store}
    (completed : Evaluates nativeEnvironment [native] code (.inRight .word (.bool true)) after) :
    ∃ updated sourceAfter finalMap finalWorld,
      Dynamic.SourcePlaceSnapshotUpdate program context [] source Dynamic.BitNotSnapshot
        environment (before initial) assignment.target updated sourceAfter ∧
      HeapRepresents checked registry (noFunctions checked.catalog) finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends [0] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [0] [native] finalMap after ∧ Dynamic.HeapMetadataExtend (before initial) sourceAfter := by
  have empty : HeapRepresents checked registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate initialRep Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [] scope environment nativeEnvironment :=
    .cons reference (.nil .nil)
  have binding : ∀ actual, rootBinder source assignment.target.root = .ok actual → actual = binder := by
    intro actual found
    exact Except.ok.inj (found.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  -- The trivial relation relates every panic too.
  haveI : FunctionCalls.FaultTokens (fun _ _ => True) := ⟨fun _ => trivial⟩
  have reflected := CompatiblePlaceBitNotLowerReflection.reflects_numeric (compilation := compilation)
    (ambient := .original checked.catalog.definitions) (functions := noFunctions checked.catalog) (certificate := Child)
    unique rfl (fun actual found => by cases binding actual found; exact .index keyTyped (.nil _))
    (fun actual found => by cases binding actual found; exact rootWritable) (by simp [assignment])
    (fun id code accepted => let ⟨node, found, child, _⟩ := childReceipt id code accepted; ⟨node, found, child⟩) accepted typed
    registryExtension (childReflects registry (fun _ _ => True)) functionViews faithful observations
    (fun _ _ => True.intro) (fun _ => True.intro) (.inr rfl) environments heaps (localAgrees initial) completed
  cases reflected with
  | fault _ resultEq => cases resultEq
  | committed trace heaps maps worlds frame metadata length continuation =>
    simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, lowered, LanguageResult.success] at continuation
    cases continuation with
    | inRight valueEvaluated =>
      cases valueEvaluated
      exact ⟨_, _, _, _, trace, heaps, maps, worlds, frame, metadata⟩

/-- Direct consumer of the real checked wrapper: its private compiler work
is recovered from success and its public typing field. -/
theorem checked_lower_reflects {certified : Certified checked.catalog.definitions coreContext .bool}
    (accepted : lowerChecked compilation checked.signatures childCompiler 100 source scope site assignment .equal none .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) checked.catalog.definitions coreContext = .ok certified)
    {registry : SourceCoreRawMetadata.Registry} (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked registry (noFunctions checked.catalog)) [] []
      ⟨rootType, initial, none⟩ native rootCore)
    {after : Store}
    (completed : Evaluates nativeEnvironment [native] certified.expression (.inRight .word (.bool true)) after) :
    ∃ updated sourceAfter finalMap finalWorld,
      Dynamic.SourcePlaceSnapshotUpdate program context [] source Dynamic.BitNotSnapshot
        environment (before initial) assignment.target updated sourceAfter ∧
      HeapRepresents checked registry (noFunctions checked.catalog) finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends [0] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [0] [native] finalMap after ∧ Dynamic.HeapMetadataExtend (before initial) sourceAfter :=
  actual_lower_reflects (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) certified.typed registryExtension initialRep completed

private def exercise {certified : Certified checked.catalog.definitions coreContext .bool}
    (accepted : lowerChecked compilation checked.signatures childCompiler 100 source scope site assignment .equal none .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) checked.catalog.definitions coreContext = .ok certified)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked registry (noFunctions checked.catalog)) [] []
      ⟨rootType, initial, none⟩ native rootCore)
    (expected : SourceCoreDataValues.Value) : IO Unit := do
  let start := Core.State.initial certified.expression nativeEnvironment [native]
  match ran : runStateful 200000 start with
  | .done result after =>
    if success : result = .inRight .word (.bool true) then
      have _source := checked_lower_reflects accepted extension initialRep (success ▸ runStateful_evaluation_sound ran)
      unless after.length == 1 + 3 * (checked.catalog.entries.length + 1) do
        throw (IO.userError "compatible Integer bit-not admin count changed")
      match after.read? 0 with
      | some (.inRight .unit value) =>
        let outputContext : SourceCoreCompatibleValues.Context := ⟨checked, registry, extension⟩
        match SourceCoreCompatibleValues.decode 100 outputContext rootType value with
        | .ok actual => unless actual == expected do
            throw (IO.userError "compatible Integer bit-not raw metadata or ordered duplicates changed")
        | .error error => throw (IO.userError s!"compatible Integer bit-not decode failed {reprStr error}")
      | _ => throw (IO.userError "compatible Integer bit-not missing mapped write")
      match runStateful 17 start with
      | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done result after do
          throw (IO.userError "compatible Integer bit-not resume changed result")
      | _ => throw (IO.userError "compatible Integer bit-not expected checkpoint")
    else throw (IO.userError "compatible Integer bit-not expected success")
  | other => throw (IO.userError s!"compatible Integer bit-not run failed {reprStr other}")

private def seven : Int := 7
private def nine : Int := 9
private def carrier : SourceCoreDataValues.Value :=
  .mapping (.comptime .bool) (.comptime .integer) [(.bool true, .integer seven), (.bool true, .integer nine)]
private def sourceValue : Dynamic.Value :=
  .mapping (.comptime .bool) (.comptime .integer) [(.bool true, .integer seven), (.bool true, .integer nine)]
private theorem carrierMeaning : CompatibleEncoding.Means carrier sourceValue :=
  .mapping (.prepend (.bool true) (.integer seven) (.prepend (.bool true) (.integer nine) .empty))

def run : IO Unit := do
  match accepted : lowerChecked compilation checked.signatures childCompiler 100 source scope site assignment .equal none .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) checked.catalog.definitions coreContext with
  | .error error => throw (IO.userError s!"compatible Integer bit-not rejected {reprStr error}")
  | .ok _certified =>
      exercise accepted (.refl _) (.uninitialized rootProjected)
        (.mapping .bool .integer [(.bool true, .integer (-1))])
      match encoded : SourceCoreCompatibleValues.encode 100 compilation rootType carrier with
      | .error error => throw (IO.userError s!"compatible Integer bit-not encode failed {reprStr error}")
      | .ok encodedValue =>
        have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) encoded carrierMeaning [] []
        have same := Except.ok.inj (represented.projection.symm.trans rootProjected)
        exercise accepted encodedValue.preserves (.initialized (same ▸ represented))
          (.mapping (.comptime .bool) (.comptime .integer) [(.bool true, .integer (~~~seven)), (.bool true, .integer nine)])
  IO.println "retained Integer absent-RHS bit-not actual compiler/source meaning/Unit slot/raw duplicate order/virtual root/resume GREEN"

end Tests.SourceCoreCompatibleIntegerBitNot
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatiblePlaceKeyTyping
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Independent typing authenticates repeated key occurrences of an actual
prepared nested mapping route. Canonical member substitutions also preserve
staged raw arguments when the semantic substitution is permuted. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatiblePlaceKeyTyping
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreCompatibleDataPlaces CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceKeyTyping

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_key_typing", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_key_typing.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def rootType : TypeSystem.Ty := .mapping .bool (.mapping .bool .word)
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def projections : List PlaceProjection := [.index key, .index key]
private def assignment : AssignmentResolution := ⟨⟨binder.id, projections, .word⟩, []⟩
private def semanticContext := SourceSemantics.Context.ofSignatures signatures
private theorem unique : NodeOccurrencesUnique source := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]
private theorem keyTyped : ExpressionHasType source semanticContext key .bool := by
  apply ExpressionHasType.ofOrdinary (node := node) (rawType := .bool)
    (lookupExpression?_sound (show source.lookupExpression? key = some node by cbv))
    (.reference (.builtinBoolean true))
    (.bool (.ofSignatures signatures)) (.bool (.ofSignatures signatures))
  · intro id member; cases member
  · exact .nil _
  · rfl
private theorem projectionsTyped : SourceProjectionsHaveType source semanticContext rootType projections .word :=
  .index keyTyped (.index keyTyped (.nil _))

private def lowered : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def Child : GenericExpressionMeaning.Certificate := fun scope id code =>
  SourceCoreBasic.lowerExpression 10 source scope id Word.zero = .ok code
private theorem children : DataExpressionSequence.Tree source Child [] (DataPlaceKeyOrder.sourceKeys projections)
    [.bool, .bool] [lowered, lowered] := by
  change DataExpressionSequence.Tree source Child [] [key, key] [node.type, node.type] [lowered, lowered]
  exact .cons (node := node) (by cbv) (by cbv) (.single (node := node) (by cbv) (by cbv))

/-- No hand-supplied key view or source/native type cast is required. -/
private theorem actual_views {route : Route} {prepared : Prepared}
    (described : describe context checked.signatures source site assignment = .ok route)
    (preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) = .ok prepared) :
    ∃ leaf, ∃ path : PreparedPath checked source site rootType projections 0 prepared.steps prepared.keys leaf,
      KeyViews path [.bool, .bool] ∧ SourceCoreRawMetadata.runtimeType leaf = .word := by
  obtain ⟨actualBinder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
  have binding : rootBinder source assignment.target.root = .ok binder := by cbv
  have same := Except.ok.inj (description.binding.symm.trans binding)
  subst actualBinder
  obtain ⟨_, _, path⟩ := description.prepared preparedBy
  exact ⟨selected, path, of_typing unique rfl path rfl projectionsTyped children⟩

private def p : TypeSystem.TypeParameterId := ⟨owner, 0⟩
private def q : TypeSystem.TypeParameterId := ⟨owner, 1⟩
private def permuted : TypeSystem.ParameterSubstitution := [(q, .comptime .word), (p, .comptime .bool)]
private theorem exactPermutation : ParameterSubstitution.Exact permuted [p, q] :=
  ⟨by decide, List.Perm.swap _ _ []⟩

example (type : TypeSystem.Ty) :
    SourceCoreRawMetadata.runtimeType (TypeSystem.ParameterSubstitution.apply [(p, .bool), (q, .word)] type) =
      SourceCoreRawMetadata.runtimeType (permuted.apply type) := by
  have canonical : [p, q].zip ((ParameterSubstitution.orderedArguments permuted [p, q]).map SourceCoreRawMetadata.runtimeType) =
      [(p, .bool), (q, .word)] := by cbv
  have result := canonical_substitution_view exactPermutation type
  rw [canonical] at result
  exact result

example : permuted ≠ [(p, .bool), (q, .word)] := by decide

def run : IO Unit := do
  match described : describe context checked.signatures source site assignment with
  | .error error => throw (IO.userError s!"compatible key typing describe failed: {reprStr error}")
  | .ok route =>
    match preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) with
    | .error error => throw (IO.userError s!"compatible key typing prepare failed: {reprStr error}")
    | .ok prepared =>
      have _receipt := actual_views described preparedBy
      unless prepared.keys.map Prod.fst == [key, key] do
        throw (IO.userError "compatible key typing lost repeated key order")
  IO.println "compatible place key typing GREEN"

end Tests.SourceCoreCompatiblePlaceKeyTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatiblePlaceOrder
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! The actual compatible assignment executes two repeated effectful keys,
saves a snapshot, then runs an RHS that replaces the root. Compound writeback
uses the saved leaf and the latest siblings, retaining raw staged headers and
ordered duplicate entries. Faults skip the remaining phases; resume agrees. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatiblePlaceOrder
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering SourceCoreCompatibleDataPlaces

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_order", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_order.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def rootType : TypeSystem.Ty := .mapping .bool (.mapping .bool .word)
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.index key, .index key], .word⟩, []⟩
private def w (n : Nat) : Word := Word.ofNatModulo n
private def carrier (first duplicate sibling : Nat) : SourceCoreDataValues.Value :=
  .mapping (.comptime .bool) (.mapping (.comptime .bool) .word)
    [(.bool true, .mapping (.comptime .bool) .word
      [(.bool true, .word (w first)), (.bool true, .word (w duplicate)), (.bool false, .word (w sibling))])]

private def keyCode (fail : Bool) : SourceCoreBasic.LoweredExpr := ⟨.bool,
  .letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (.word (w 1))))
    (if fail then LanguageResult.failure .bool (.word (w 31)) else LanguageResult.success (.bool true))⟩

private def code (prepared : Prepared) (initial latest : Expr) (keyFails rhsFails : Bool) : Expr :=
  .letE (OptionalCell.allocateInitialized prepared.route.rootType initial)
    (.letE (.newCell .word (.word Word.zero))
      (execute prepared (.var 1) (SourceCoreCalls.packArguments [keyCode keyFails, keyCode false])
        (.letE (.storeCell (.var 1) (.inRight .unit latest))
          (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (.word (w 10))))
            (if rhsFails then LanguageResult.failure .word (.word (w 32)) else LanguageResult.success (.word (w 5)))))
        (LanguageResult.success (.pair (.loadCell (.var 0)) (.loadCell (.var 1))))
        (.product .word (OptionalCell.cellType prepared.route.rootType)) (some (.total .wordAdd)) false (w 33)))

private def verify (prepared : Prepared) (context : SourceCoreCompatibleValues.Context)
    (initial latest : Expr) (keyFails rhsFails : Bool) (expected : SourceCoreDataValues.Value)
    (count : Nat) (reason : Option Word) : IO Unit := do
  let body := code prepared initial latest keyFails rhsFails
  unless infer? [] body checked.catalog.definitions ==
      some (LanguageResult.resultType (.product .word (OptionalCell.cellType prepared.route.rootType))) do
    throw (IO.userError "compatible assignment order code rejected by actual checker")
  let initialState : Core.State := .initial body [] []
  match runStateful 200000 initialState with
  | .done result after =>
    match reason, result with
    | none, .inRight .word (.pair (.word actualCount) (.inRight .unit _)) =>
      unless actualCount == w count do throw (IO.userError "compatible assignment returned wrong effect count")
    | some expectedReason, .inLeft _ (.word actualReason) =>
      unless actualReason == expectedReason do throw (IO.userError "compatible assignment changed fault order")
    | _, _ => throw (IO.userError s!"compatible assignment unexpected outcome: {reprStr result}")
    unless after.read? 1 == some (.word (w count)) do throw (IO.userError "compatible assignment repeated or skipped an effect")
    match after.read? 0 with
    | some (.inRight .unit value) =>
      match SourceCoreCompatibleValues.decode 100 context rootType value with
      | .error error => throw (IO.userError s!"compatible assignment decode failed: {reprStr error}")
      | .ok actual => unless actual == expected do throw (IO.userError "compatible assignment lost snapshot/latest-root/duplicate/header semantics")
    | _ => throw (IO.userError "compatible assignment lost initialized root")
    match runStateful 17 initialState with
    | .outOfFuel checkpoint =>
      unless runStateful 200000 checkpoint == .done result after do throw (IO.userError "compatible assignment resume changed observation")
    | _ => throw (IO.userError "compatible assignment expected a checkpoint")
  | other => throw (IO.userError s!"compatible assignment did not complete: {reprStr other}")

def run : IO Unit := do
  let route ← match describe context checked.signatures source site assignment with
    | .ok route => pure route
    | .error error => throw (IO.userError s!"compatible assignment describe failed: {reprStr error}")
  let prepared ← match prepare context 100 route (w 33) (fun _ => w 34) with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"compatible assignment prepare failed: {reprStr error}")
  match SourceCoreCompatibleValues.encode 100 context rootType (carrier 10 11 20) with
  | .error error => throw (IO.userError s!"compatible assignment initial encode failed: {reprStr error}")
  | .ok initial =>
    match SourceCoreCompatibleValues.encode 100 initial.context rootType (carrier 100 101 200) with
    | .error error => throw (IO.userError s!"compatible assignment latest encode failed: {reprStr error}")
    | .ok latest =>
      match SourceCoreCompatibleDataExpressions.quote initial.value, SourceCoreCompatibleDataExpressions.quote latest.value with
      | some initialCode, some latestCode =>
        verify prepared latest.context initialCode latestCode false false (carrier 15 101 200) 12 none
        verify prepared latest.context initialCode latestCode true false (carrier 10 11 20) 1 (some (w 31))
        verify prepared latest.context initialCode latestCode false true (carrier 100 101 200) 12 (some (w 32))
      | _, _ => throw (IO.userError "compatible assignment data values were not quotable")
  IO.println "compatible place snapshot/RHS/latest-root order GREEN"

end Tests.SourceCoreCompatiblePlaceOrder
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatiblePlaceSnapshot
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Actual describe/prepare receipts feed live-cell snapshots. The Core store
has an administrative prefix, so source location zero maps to Core location
one. Both initialized and virtual roots keep that slot unchanged. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreCompatiblePlaceSnapshot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreCompatibleDataPlaces CompatiblePayload CompatibleEquality CompatibleMapping CompatibleMapping.MixedPaths CompatibleMixedRoute
open CompatiblePlaceLiveRoot

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_live", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_live.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def rootType : TypeSystem.Ty := .mapping .bool .word
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def projections : List PlaceProjection := [.index key]
private def assignment : AssignmentResolution := ⟨⟨binder.id, projections, .word⟩, []⟩
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible

private def world (prepared : Prepared) : StoreTyping := [.integer, OptionalCell.cellType prepared.route.rootType]
private def environment (prepared : Prepared) : Environment := [.cellRef (OptionalCell.cellType prepared.route.rootType) 1, .bool true]
private def coreContext (prepared : Prepared) : Core.Context := [OptionalCell.referenceType prepared.route.rootType, .bool]
private def code (prepared : Prepared) : Expr := .apply (getter prepared .bool) (.pair (.loadCell (.var 0)) (.var 1))
private def keys : List Value := [.bool true]
private def resolved : List Dynamic.EvaluatedProjection := [.index (.bool true)]
private def noIdentities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : DataEquality.IdentityFaithful noIdentities := ⟨False.elim, fun impossible _ => False.elim impossible⟩
private theorem noFunctionObservations : FunctionObservations checked.catalog (noFunctions checked.catalog) noIdentities := fun impossible => False.elim impossible

private theorem leaf_word {steps : List PreparedStep} {sites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
    (path : PreparedPath checked source site rootType projections 0 steps sites leaf) : leaf = .word := by
  cases path with
  | index certificate generated tail =>
    have shape := TypeSystem.Ty.mapping.inj certificate.view
    obtain ⟨rfl, rfl⟩ := shape
    cases tail
    rfl

private theorem actualPath {route : Route} {prepared : Prepared}
    (described : describe context checked.signatures source site assignment = .ok route)
    (preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) = .ok prepared) :
    PreparedPath checked source site rootType projections 0 prepared.steps prepared.keys .word ∧
    checked.catalog.project rootType = .ok prepared.route.rootType ∧
    checked.catalog.project .word = .ok prepared.route.leafType ∧
    VirtualRoot.Generated context prepared.route .bool .word := by
  obtain ⟨actualBinder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
  have binding : rootBinder source assignment.target.root = .ok binder := by cbv
  have same := Except.ok.inj (description.binding.symm.trans binding)
  subst actualBinder
  obtain ⟨sameRoute, _, path⟩ := description.prepared preparedBy
  have selectedEq := leaf_word path
  subst selected
  exact ⟨path, sameRoute ▸ description.rootProjected, sameRoute ▸ description.leafProjected,
    sameRoute ▸ description.virtual .bool .word rfl⟩

private theorem arguments {registry : SourceCoreRawMetadata.Registry} {prepared : Prepared}
    {steps : List PreparedStep} {sites : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site rootType projections 0 steps sites .word) :
    Arguments checked registry (noFunctions checked.catalog) [1] (world prepared) source site keys path resolved ∧
      steps ≠ [] ∧ sites.length = keys.length := by
  cases path with
  | index certificate generated tail =>
    have shape := TypeSystem.Ty.mapping.inj certificate.view
    obtain ⟨rfl, rfl⟩ := shape
    have nativeKey := Except.ok.inj certificate.keyProjection
    cases tail
    refine ⟨?_, (by simp), rfl⟩
    apply Arguments.index (certificate := certificate) (generated := generated) rfl
    · rw [← nativeKey]; exact .bool true
    · exact .nil

private theorem store_typed {prepared : Prepared} {optional : Value}
    (typed : RuntimeValueHasType (world prepared) optional (OptionalCell.cellType prepared.route.rootType) checked.catalog.definitions) :
    RuntimeStoreHasTypes (world prepared) [.integer (-123), optional] checked.catalog.definitions := by
  refine ⟨rfl, ?_⟩
  intro index type found
  cases index with
  | zero => cases found; exact ⟨_, rfl, .integer⟩
  | succ index => cases index with
    | zero => cases found; exact ⟨_, rfl, typed⟩
    | succ index => simp [world] at found
private theorem environment_typed (prepared : Prepared) :
    RuntimeEnvironmentHasTypes (world prepared) (environment prepared) (coreContext prepared) checked.catalog.definitions :=
  .cons (.cellRef rfl) (.cons .bool .nil)

private theorem snapshot {prepared : Prepared} {registry : SourceCoreRawMetadata.Registry}
    {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot selected : Dynamic.Value}
    (root : RootRead checked registry (noFunctions checked.catalog) [1] (world prepared) prepared
      ⟨[cell]⟩ [.integer (-123), optional] ⟨0⟩ 1 cell optional sourceRoot rootValue)
    (path : PreparedPath checked source site rootType projections 0 prepared.steps prepared.keys .word)
    (cellType : cell.type = rootType) (leaf : checked.catalog.project .word = .ok prepared.route.leafType)
    (read : Dynamic.ProjectionsRead (some sourceRoot) resolved (some selected))
    (optionalTyped : RuntimeValueHasType (world prepared) optional (OptionalCell.cellType prepared.route.rootType) checked.catalog.definitions)
    (typed : HasType (coreContext prepared) (code prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions) :
    ∃ native after,
      FiniteRun (environment prepared) [.integer (-123), optional] (code prepared) (.inRight .word (.inRight .unit native)) after ∧
      after.read? 1 = some optional ∧ after.read? 0 = some (.integer (-123)) := by
  obtain ⟨keysRelated, nonempty, keyLength⟩ := arguments (registry := registry) (prepared := prepared) path
  have keyLength : prepared.keyTypes.length = keys.length := by simpa [Prepared.keyTypes] using keyLength
  have root' : RootRead checked registry (noFunctions checked.catalog) [1] (world prepared) prepared
      ⟨[cell]⟩ [.integer (-123), optional] ⟨0⟩ 1 cell optional sourceRoot rootValue := root
  have path' : PreparedPath checked source site cell.type projections 0 prepared.steps prepared.keys .word := cellType.symm ▸ path
  have keysRelated' : Arguments checked registry (noFunctions checked.catalog) [1] (world prepared) source site keys path' resolved := by
    simpa only [cellType] using keysRelated
  obtain ⟨native, after, suffix, future, _, _, ran, _, _, _, finalRoot, _, appended, _⟩ := read_at root' keysRelated' leaf read
    nonempty faithful noFunctionObservations keyLength (store_typed optionalTyped) (environment_typed prepared) typed (.var rfl) (.var rfl)
  refine ⟨native, after, ran, finalRoot.nativeRead, ?_⟩
  rw [appended]
  rfl

private def w (n : Nat) : Word := Word.ofNatModulo n
private def carrier : SourceCoreDataValues.Value := .mapping .bool .word [(.bool true, .word (w 7)), (.bool true, .word (w 9))]
private def sourceRoot : Dynamic.Value := .mapping .bool .word [(.bool true, .word (w 7)), (.bool true, .word (w 9))]
private theorem meaning : CompatibleEncoding.Means carrier sourceRoot :=
  .mapping (.prepend (.bool _) (.word _) (.prepend (.bool _) (.word _) .empty))

private theorem initialized_snapshot {route : Route} {prepared : Prepared}
    (described : describe context checked.signatures source site assignment = .ok route)
    (preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded)
    (typed : HasType (coreContext prepared) (code prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions) :
    ∃ native after,
      FiniteRun (environment prepared) [.integer (-123), .inRight .unit encoded.value] (code prepared) (.inRight .word (.inRight .unit native)) after ∧
      after.read? 1 = some (.inRight .unit encoded.value) ∧ after.read? 0 = some (.integer (-123)) := by
  obtain ⟨path, projected, leaf, _⟩ := actualPath described preparedBy
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted meaning [1] (world prepared)
  have same := Except.ok.inj (represented.projection.symm.trans projected)
  rw [same] at represented
  have root := RootRead.initialized (prepared := prepared) (heap := ⟨[⟨rootType, some sourceRoot, none⟩]⟩)
    (store := [.integer (-123), .inRight .unit encoded.value]) (location := ⟨0⟩) (target := 1) (.intro .head) ⟨rfl, rfl⟩ rfl represented
  exact snapshot root path rfl leaf (.indexFound (.head ⟨rfl, .bool _⟩) .nil) (.inRight represented.runtime_hasType) typed

private theorem virtual_snapshot {route : Route} {prepared : Prepared}
    (described : describe context checked.signatures source site assignment = .ok route)
    (preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) = .ok prepared)
    (typed : HasType (coreContext prepared) (code prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions) :
    ∃ native after,
      FiniteRun (environment prepared) [.integer (-123), .inLeft prepared.route.rootType .unit] (code prepared) (.inRight .word (.inRight .unit native)) after ∧
      after.read? 1 = some (.inLeft prepared.route.rootType .unit) ∧ after.read? 0 = some (.integer (-123)) := by
  obtain ⟨path, projected, leaf, generated⟩ := actualPath described preparedBy
  obtain ⟨value, root⟩ := RootRead.virtual (functions := noFunctions checked.catalog) (mapping := [1]) (world := world prepared)
    (heap := ⟨[⟨rootType, none, none⟩]⟩) (store := [.integer (-123), .inLeft prepared.route.rootType .unit])
    (location := ⟨0⟩) (target := 1) generated (.refl _) projected (.intro .head) ⟨rfl, rfl⟩ rfl
  exact snapshot root path rfl leaf (.indexDefault .nil .word .nil) (.inLeft .unit) typed

private def completed (prepared : Prepared) (optional : Value) (expected : Word) : IO Unit := do
  let before := [.integer (-123), optional]
  let initial := State.initial (code prepared) (environment prepared) before
  match runStateful 100000 initial with
  | .done value after =>
    unless value == .inRight .word (.inRight .unit (.word expected)) do throw (IO.userError "live snapshot value changed")
    unless after.take 2 == before do throw (IO.userError "snapshot changed root or prior admin cell")
    unless after.length == 2 + checked.catalog.entries.length + 1 do throw (IO.userError "snapshot helper allocation count changed")
    match runStateful 1 initial with
    | .outOfFuel checkpoint =>
      unless runStateful 100000 checkpoint == .done value after do throw (IO.userError "live snapshot resumption changed observation")
    | _ => throw (IO.userError "live snapshot expected a checkpoint")
  | other => throw (IO.userError s!"live snapshot did not finish: {reprStr other}")

def run : IO Unit := do
  match described : describe context checked.signatures source site assignment with
  | .error error => throw (IO.userError s!"live describe failed: {reprStr error}")
  | .ok route => match preparedBy : prepare context 100 route Word.zero (fun _ => Word.zero) with
    | .error error => throw (IO.userError s!"live prepare failed: {reprStr error}")
    | .ok prepared =>
      if inferred : infer? (coreContext prepared) (code prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.optionalLeaf) then
        have typed := infer_sound inferred
        have _virtual := virtual_snapshot described preparedBy typed
        completed prepared (.inLeft prepared.route.rootType .unit) Word.zero
        match accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier with
        | .error error => throw (IO.userError s!"live encode failed: {reprStr error}")
        | .ok encoded =>
          have _initialized := initialized_snapshot described preparedBy accepted typed
          completed prepared (.inRight .unit encoded.value) (w 7)
      else throw (IO.userError "live generated helper was rejected by Core checker")
  IO.println "compatible live-root snapshot proofs GREEN"

end Tests.SourceCoreCompatiblePlaceSnapshot
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleStructuralFault
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreCompatibleStructuralFault
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_structural", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_structural.solc"⟩, 0, 1⟩
private def boxType : TypeSystem.Ty := .nominal owner []
private def rootType : TypeSystem.Ty := .mapping .bool boxType
private def signature : ProgramDataSignature := {
  id := owner, name := "Box", parameters := []
  constructors := [⟨⟨owner, 0⟩, "Box", [], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def metadata : DataConstructorInstantiation := ⟨⟨owner, 0⟩, [], [], boxType⟩
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def catalog : SourceCoreCompatibleCatalog.Catalog := { entries := [
  { sourceType := rootType, definition := some (OrderedMapping.Layout.definition ⟨.bool, .namedData ⟨1⟩, ⟨0⟩⟩) },
  { sourceType := boxType, constructors := [⟨owner, 0⟩], definition := some ⟨[.product .word .unit]⟩ }] }
private theorem registryExists : (SourceCoreRawMetadata.prepare signatures [.mapping .bool boxType]).toOption.isSome = true := by decide
private def registry := (SourceCoreRawMetadata.prepare signatures [.mapping .bool boxType]).toOption.get registryExists
private def checked : SourceCoreCompatibleCatalog.Checked :=
  ⟨catalog, DataEnvironment.isWellFormed_sound (by decide), signatures, registry,
    SourceCoreRawMetadata.prepare_signatures (except_get _ registryExists)⟩
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.index key], boxType⟩, []⟩
private def missing : Word := Word.ofNatModulo 100
private def carrier : SourceCoreDataValues.Value := .mapping .bool (.comptime boxType) []
private def sourceRoot : Dynamic.Value := .mapping .bool (.comptime boxType) []
private theorem carrierMeaning : CompatibleEncoding.Means carrier sourceRoot := .mapping .empty
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem observations : FunctionObservations checked.catalog (noFunctions checked.catalog) (fun _ _ => False) := by
  intro _ _ _ _ _ _ _ impossible; exact impossible.elim
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by constructor <;> intros <;> contradiction
private theorem unavailable : ¬ Dynamic.Defaultable (.comptime boxType) := by
  intro impossible; cases impossible with | comptime inner => cases inner
private theorem fault : Dynamic.ProjectionsFaults (some sourceRoot) [.index (.bool true)] (.missingMappingDefault (.comptime boxType)) :=
  .indexDefaultUnavailable (.bool true) .nil unavailable

private def coreContext (prepared : Prepared) : Core.Context :=
  [OptionalCell.referenceType prepared.route.rootType, .bool, prepared.route.leafType]
private def code (prepared : Prepared) : Expr :=
  .apply (setter prepared .bool) (.pair (.loadCell (.var 0)) (.pair (.var 1) (.var 2)))
private def environment (prepared : Prepared) (replacement : Value) : Environment :=
  [.cellRef (OptionalCell.cellType prepared.route.rootType) 1, .bool true, replacement]
private def world (prepared : Prepared) : StoreTyping := [.integer, OptionalCell.cellType prepared.route.rootType]

private theorem pathArguments {registry : SourceCoreRawMetadata.Registry} {prepared : Prepared}
    {steps : List PreparedStep} {sites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
    (path : PreparedPath checked source site rootType assignment.target.projections 0 steps sites leaf) :
    Arguments checked registry (noFunctions checked.catalog) [1] (world prepared) source site [.bool true] path [.index (.bool true)] ∧
      steps ≠ [] ∧ sites.length = 1 := by
  cases path with
  | index certificate generated tail =>
    have shape := TypeSystem.Ty.mapping.inj certificate.view
    obtain ⟨rfl, rfl⟩ := shape
    have nativeKey := Except.ok.inj certificate.keyProjection
    cases tail
    refine ⟨?_, (by simp), rfl⟩
    apply Arguments.index (certificate := certificate) (generated := generated) rfl
    · rw [← nativeKey]; exact .bool true
    · exact .nil

/-- The actual route and encoder suffice to construct a live setter fault.
The raw staged nominal default is unavailable, even though its native carrier
uses the same type as the unstaged declaration. -/
theorem certified {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => missing) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded)
    {replacement : Value}
    (replacementTyped : RuntimeValueHasType (world prepared) replacement prepared.route.leafType checked.catalog.definitions)
    (setterTyped : HasType (coreContext prepared) (code prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions) :
    ∃ token count finalStore futureWorld,
      FaultToken checked encoded.context.registry sourceRoot prepared.steps [.index (.bool true)]
        (.missingMappingDefault (.comptime boxType)) token count ∧
      Evaluates (environment prepared replacement) [.integer (-123), .inRight .unit encoded.value] (code prepared)
        (.inLeft prepared.route.rootType (.word token)) finalStore ∧
      HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [1] futureWorld
        ⟨[⟨rootType, some sourceRoot, none⟩]⟩ finalStore ∧
      finalStore.read? 0 = some (.integer (-123)) ∧ finalStore.read? 1 = some (.inRight .unit encoded.value) := by
  obtain ⟨actualBinder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (description.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
  have projected : checked.catalog.project rootType = .ok prepared.route.rootType := routeEq ▸ description.rootProjected
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted carrierMeaning [1] (world prepared)
  have same := Except.ok.inj (represented.projection.symm.trans projected)
  rw [same] at represented
  have empty : HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  have before := empty.allocate_administrative (RuntimeValueHasType.integer (value := -123))
  have firstRep := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted carrierMeaning [] [.integer]
  rw [same] at firstRep
  obtain ⟨heaps, reference⟩ := before.allocate (.initialized firstRep) Dynamic.Heap.Allocates.append
  have heaps : HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [1] (world prepared)
      ⟨[⟨rootType, some sourceRoot, none⟩]⟩ [.integer (-123), .inRight .unit encoded.value] := heaps
  have root : RootRead checked encoded.context.registry (noFunctions checked.catalog) [1] (world prepared) prepared
      ⟨[⟨rootType, some sourceRoot, none⟩]⟩ [.integer (-123), .inRight .unit encoded.value] ⟨0⟩ 1
      ⟨rootType, some sourceRoot, none⟩ (.inRight .unit encoded.value) sourceRoot encoded.value :=
    .initialized (.intro .head) ⟨rfl, rfl⟩ rfl represented
  obtain ⟨arguments, nonempty, length⟩ := pathArguments (registry := encoded.context.registry) (prepared := prepared) path
  have keyLength : prepared.keyTypes.length = ([Value.bool true] : List Value).length := by
    simpa [Prepared.keyTypes] using length
  have typed : RuntimeEnvironmentHasTypes (world prepared) (environment prepared replacement) (coreContext prepared) checked.catalog.definitions :=
    .cons (.cellRef rfl) (.cons .bool (.cons replacementTyped .nil))
  obtain ⟨token, count, after, administrative, futureWorld, receipt, evaluated, finalHeaps, _, _, finalRoot, appended, _⟩ :=
    CompatiblePlaceSetterFault.preserves root heaps arguments fault nonempty faithful observations keyLength typed setterTyped
      (.var rfl) (.var rfl) (.var rfl)
  exact ⟨token, count, after, futureWorld, receipt, evaluated, finalHeaps, by rw [appended]; rfl, finalRoot.nativeRead⟩

private def executeAfterRhs (prepared : Prepared) : Expr :=
  execute prepared (.var 0) ⟨.bool, LanguageResult.success (.bool true)⟩
    (.letE (.storeCell (.var 0) (.inRight .unit (.var 4))) (LanguageResult.success (.var 3)))
    (LanguageResult.failure .bool (.word (Word.ofNatModulo 777))) .bool none false Word.zero

private def exercise {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => missing) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded) : IO Unit := do
  let replacement ← match SourceCoreCompatibleValues.encode 100 encoded.context boxType (.constructed metadata []) with
    | .ok result => pure result
    | .error error => throw (IO.userError s!"structural-fault replacement encoding failed: {reprStr error}")
  if same : replacement.type = prepared.route.leafType then
    if typed : infer? (coreContext prepared) (code prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.route.rootType) then
      have replacementTyped : RuntimeValueHasType (world prepared) replacement.value prepared.route.leafType checked.catalog.definitions :=
        same ▸ replacement.typed (world prepared)
      have receipt := certified described preparedBy accepted replacementTyped (infer_sound typed)
      have _finite : ∃ fuel token after,
          runStateful fuel (.initial (code prepared) (environment prepared replacement.value) [.integer (-123), .inRight .unit encoded.value]) =
            .done (.inLeft prepared.route.rootType (.word token)) after := by
        obtain ⟨token, _, after, _, _, evaluated, _⟩ := receipt
        obtain ⟨fuel, completed⟩ := evaluation_runStateful_complete evaluated
        exact ⟨fuel, token, after, completed⟩
      let header ← match encoded.value with
        | .pair (.word header) _ => pure header
        | _ => throw (IO.userError "structural-fault raw header missing")
      unless encoded.context.registry.lookup header == some (.mapping .bool (.comptime boxType)) do
        throw (IO.userError "structural-fault raw staged metadata erased")
      let before := [Value.integer (-123), Value.inRight .unit encoded.value]
      match runStateful 200000 (.initial (code prepared) (environment prepared replacement.value) before) with
      | .done (.inLeft _ (.word token)) after =>
        unless token == missing.add header && after.take 2 == before &&
            after.length == 2 + checked.catalog.entries.length + 1 do
          throw (IO.userError "structural-fault setter changed token, root or allocation order")
      | other => throw (IO.userError s!"structural-fault setter failed: {reprStr other}")
      let initialRoot ← match SourceCoreCompatibleValues.encode 100 replacement.context rootType
          (.mapping .bool (.comptime boxType) [(.bool true, .constructed metadata [])]) with
        | .ok value => pure value
        | .error error => throw (IO.userError s!"structural-fault initial root failed: {reprStr error}")
      let fullContext := [OptionalCell.referenceType prepared.route.rootType, Ty.bool, prepared.route.leafType,
        prepared.route.rootType, prepared.route.rootType]
      let fullEnvironment := [Value.cellRef (OptionalCell.cellType prepared.route.rootType) 1, .bool true,
        replacement.value, initialRoot.value, encoded.value]
      unless infer? fullContext (executeAfterRhs prepared) checked.catalog.definitions == some (LanguageResult.resultType .bool) do
        throw (IO.userError "structural-fault whole execute checker failed")
      let initial := Core.State.initial (executeAfterRhs prepared) fullEnvironment [.integer (-123), .inRight .unit initialRoot.value]
      match runStateful 200000 initial with
      | .done (.inLeft .bool (.word token)) after =>
        unless token == missing.add header && after.take 2 == before && after.length == 2 + 2 * (checked.catalog.entries.length + 1) do
          throw (IO.userError "RHS/latest-root fault did not preserve prefix effects or suppress writeback")
        match runStateful 19 initial with
        | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done (.inLeft .bool (.word token)) after do
            throw (IO.userError "structural-fault resume changed observation")
        | _ => throw (IO.userError "structural-fault expected a checkpoint")
      | other => throw (IO.userError s!"RHS/latest-root structural fault failed: {reprStr other}")
    else throw (IO.userError "structural-fault setter checker failed")
  else throw (IO.userError "structural-fault replacement type changed")

def run : IO Unit := do
  match described : describe compilation checked.signatures source site assignment with
  | .error error => throw (IO.userError s!"structural-fault describe failed: {reprStr error}")
  | .ok route =>
    match preparedBy : prepare compilation 100 route Word.zero (fun _ => missing) with
    | .error error => throw (IO.userError s!"structural-fault prepare failed: {reprStr error}")
    | .ok _ =>
      match accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier with
      | .error error => throw (IO.userError s!"structural-fault carrier encode failed: {reprStr error}")
      | .ok _ => exercise described preparedBy accepted
  IO.println "compatible latest-root structural fault and raw default token GREEN"

end Tests.SourceCoreCompatibleStructuralFault
end

section
-- leanmerge: from Solcore.Test.SourceCoreCompatibleTargetFaults
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleTargetFaults
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_target_fault", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_target_fault.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def valueType : TypeSystem.Ty := .function .bool .bool
private def rootType : TypeSystem.Ty := .comptime (.mapping .bool valueType)
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.index key], valueType⟩, []⟩
private def context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem observations : FunctionObservations checked.catalog (noFunctions checked.catalog) (fun _ _ => False) := by
  intro _ _ _ _ _ _ _ impossible; exact impossible.elim
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem unique : NodeOccurrencesUnique source := by simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]
private theorem contains : ContainsExpression source key node := lookupExpression?_sound (by cbv)
private theorem selected {other : ExpressionNode} (member : ContainsExpression source key other) : other = node :=
  Option.some.inj ((lookupExpression?_complete unique member).symm.trans (show source.lookupExpression? key = some node by cbv))
private def lowered : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def Child : GenericExpressionMeaning.Certificate := fun _ id code => id = key ∧ code = lowered

/-- The small child IH is independently proved for all heaps, environments
and renamings. It does not retain an execution as a certificate field. -/
private theorem childMeaning (registry : SourceCoreRawMetadata.Registry) : GenericExpressionMeaning.Preserves
    (payloadModel checked registry (noFunctions checked.catalog)) program context [] source Child (fun _ _ => False) := by
  intro scope id code certificate n found mapping world administrative environment canonical actual before store ξ outcome after
    environments heaps locals agrees trace
  obtain ⟨rfl, rfl⟩ := certificate
  have nodeEq : n = node := Option.some.inj (found.symm.trans (show source.lookupExpression? key = some node by cbv))
  subst n
  have outcomeEq : outcome = .value (.bool true) ∧ after = before := by
    cases trace with
    | value evaluated =>
      cases evaluated with
      | intro member form coercions =>
        have eq := selected member; subst_vars
        cases form
        cases coercions
        exact ⟨rfl, rfl⟩
      | generalizedLocal member form => have eq := selected member; subst_vars; cases form
    | fault fault =>
      cases fault with
      | missing absent => exact (Dynamic.ExpressionAbsentIn.excludes_contains (source := source) absent contains).elim
      | form member failed => have eq := selected member; subst_vars; cases failed
      | coercion member _ failed => have eq := selected member; subst_vars; cases failed
      | generalizedLocalRequirement member form => have eq := selected member; subst_vars; cases form
      | generalizedLocalCoercion member form => have eq := selected member; subst_vars; cases form
  obtain ⟨rfl, rfl⟩ := outcomeEq
  exact ⟨_, store, mapping, world, .inRight .bool, .value (.bool true), heaps, .refl _, .refl _, .refl _ _, .refl _⟩

private theorem keyEvaluates (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context [] source environment heap key (.bool true) heap :=
  .intro contains (.builtinBoolean rfl) .nil


private def scope (prepared : Prepared) : SourceCoreLocalCell.Scope := [(binder.id, prepared.route.rootType)]
private def getCode (prepared : Prepared) : Expr :=
  .apply (getter prepared .bool) (.pair (.loadCell (.var 1)) (.var 0))
private def putCode (prepared : Prepared) : Expr :=
  .apply (setter prepared .bool) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))
private def getContext (prepared : Prepared) : Core.Context :=
  [.bool, OptionalCell.referenceType prepared.route.rootType, OptionalCell.referenceType prepared.route.rootType]
private def putContext (prepared : Prepared) : Core.Context :=
  [prepared.route.leafType, prepared.route.leafType, prepared.optionalLeaf, .bool,
    OptionalCell.referenceType prepared.route.rootType, OptionalCell.referenceType prepared.route.rootType]

private theorem pathViews {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
    (path : PreparedPath checked source site rootType assignment.target.projections 0 steps keySites leaf) : KeyViews path [.bool] := by
  cases path with
  | index certificate generated tail =>
    have same := TypeSystem.Ty.mapping.inj certificate.view
    obtain ⟨rfl, rfl⟩ := same
    cases tail
    exact .index (certificate := certificate) (generated := generated) rfl .nil

private theorem staticReceipt {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions) :
    prepared.route.rootSourceType = rootType ∧ checked.catalog.project valueType = .ok prepared.route.leafType ∧
    checked.catalog.project rootType = .ok prepared.route.rootType ∧
    ∃ leaf, SourceCoreRawMetadata.runtimeType leaf = valueType ∧
      CompatiblePlaceAssignmentSuccess.Layout compilation source Child (scope prepared) site assignment.target prepared [lowered] [.bool] leaf [] := by
  obtain ⟨actualBinder, leaf, receipt⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (receipt.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  obtain ⟨routeEq, _, path⟩ := receipt.prepared preparedBy
  have rootEq : prepared.route.rootSourceType = rootType := routeEq ▸ receipt.rootSource
  have leafEq : checked.catalog.project valueType = .ok prepared.route.leafType := by
    rw [routeEq]
    exact receipt.leafProjected
  have children : DataExpressionSequence.Tree source Child (scope prepared)
      (DataPlaceKeyOrder.sourceKeys assignment.target.projections) [.bool] [lowered] :=
    .single (node := node) (by cbv) ⟨rfl, rfl⟩
  have views := pathViews path
  have actualPath : PreparedPath checked source site prepared.route.rootSourceType assignment.target.projections 0 prepared.steps prepared.keys leaf := by
    simpa only [rootEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using path
  refine ⟨rootEq, leafEq, by simpa only [routeEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using receipt.rootProjected, leaf, receipt.selectedType, ?_⟩
  refine ⟨actualPath, by simpa only [rootEq, compilation, SourceCoreCompatibleValues.Context.initial, binder, TypeSystem.Scheme.mono] using views, children, keyTypes, ?_, ?_, nonempty, getterTyped, setterTyped⟩
  · change checked.catalog.project leaf = .ok prepared.route.leafType
    rw [← checked.catalog.project_runtimeType leaf, receipt.selectedType]; exact leafEq
  · intro key value declared
    rw [routeEq]
    apply receipt.virtual key value
    exact rootEq.symm.trans declared

private def carrier : SourceCoreDataValues.Value := .mapping .bool (.comptime valueType) []
private def sourceRoot : Dynamic.Value := .mapping .bool (.comptime valueType) []
private theorem carrierMeaning : CompatibleEncoding.Means carrier sourceRoot := .mapping .empty
private theorem unavailable : ¬ Dynamic.Defaultable (.comptime valueType) := by
  intro impossible; cases impossible with | comptime inner => cases inner
private theorem fault : Dynamic.ProjectionsFaults (some sourceRoot) [.index (.bool true)] (.missingMappingDefault (.comptime valueType)) :=
  .indexDefaultUnavailable (.bool true) .nil unavailable
private def before : Dynamic.Heap := ⟨[⟨rootType, some sourceRoot, none⟩]⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def world (prepared : Prepared) : StoreTyping := [OptionalCell.cellType prepared.route.rootType]
private def nativeEnvironment (prepared : Prepared) : Environment := [.cellRef (OptionalCell.cellType prepared.route.rootType) 0]
private def body (prepared : Prepared) : Expr :=
  execute prepared (.var 0) (SourceCoreCalls.packArguments [lowered])
    (LanguageResult.failure prepared.route.leafType (.word (Word.ofNatModulo 777)))
    (LanguageResult.failure .bool (.word (Word.ofNatModulo 888))) .bool none false Word.zero
private theorem localAgrees : Dynamic.EnvironmentAgrees before context.locals environment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal context binder.id rootType :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme,
    .comptime (.mapping (.builtin .bool) (.function (.builtin .bool) (.builtin .bool)))⟩

/-- The public target theorem consumes actual compiler and encoder receipts.
The proof uses a universal child theorem and authentic raw staged default. -/
theorem whole {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context [] source environment before assignment.target .equal key
        (.missingMappingDefault (.comptime valueType)) before ∧
      Evaluates (nativeEnvironment prepared) [.inRight .unit encoded.value] (body prepared) (.inLeft .bool (.word token)) finalStore ∧
      HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) finalMap finalWorld before finalStore := by
  obtain ⟨rootEq, _, rootProjection, leaf, _, layout⟩ := staticReceipt described preparedBy keyTypes nonempty getterTyped setterTyped
  have empty : HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted carrierMeaning [] []
  have same := Except.ok.inj (represented.projection.symm.trans rootProjection)
  rw [same] at represented
  obtain ⟨heaps, reference⟩ := empty.allocate (.initialized represented) Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] (world prepared) [] (scope prepared) environment (nativeEnvironment prepared) :=
    .cons reference (.nil .nil)
  have writable : WritableLocal context binder.id prepared.route.rootSourceType := rootEq ▸ rootWritable
  obtain ⟨token, _, _, finalStore, finalMap, finalWorld, failed, _, _, evaluated, heaps, _⟩ :=
    CompatiblePlaceTargetFaults.projection (compilation := compilation) (ambient := .original checked.catalog.definitions) (functions := noFunctions checked.catalog) (index := 0) layout (childMeaning encoded.context.registry) environments heaps localAgrees
      (by simp [scope, SourceCoreLocalCell.lookup?, assignment]) writable
      (Dynamic.Environment.LooksUp.head) (Dynamic.Heap.Reads.intro .head)
      (Dynamic.SourceProjectionsEvaluate.index (keyEvaluates environment before) .nil) (Dynamic.Heap.Reads.intro .head)
      encoded.preserves faithful observations Dynamic.RootInitialValue.initialized fault .equal key
      (LanguageResult.failure prepared.route.leafType (.word (Word.ofNatModulo 777)))
      (LanguageResult.failure .bool (.word (Word.ofNatModulo 888))) .bool Word.zero
  exact ⟨token, finalStore, finalMap, finalWorld, failed, evaluated, heaps⟩

private def absent : Dynamic.Heap := ⟨[⟨rootType, none, none⟩]⟩
private theorem absentAgrees : Dynamic.EnvironmentAgrees absent context.locals environment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil

/-- An outer staged declaration remains a nonmapping raw root for the
independent uninitialized rule, although its structural route contains an
index. Actual describe supplies the absence of a virtual-empty initializer. -/
theorem uninitialized {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    (keyTypes : prepared.keyTypes = [.bool]) (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType (getContext prepared) (getCode prepared) (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (setterTyped : HasType (putContext prepared) (putCode prepared) (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context [] source environment absent assignment.target .equal key
        (.uninitializedLocation ⟨0⟩) absent ∧
      Evaluates (nativeEnvironment prepared) [.inLeft prepared.route.rootType .unit] (body prepared)
        (.inLeft .bool (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents checked compilation.registry (noFunctions checked.catalog) finalMap finalWorld absent finalStore := by
  obtain ⟨rootEq, _, rootProjection, leaf, _, layout⟩ := staticReceipt described preparedBy keyTypes nonempty getterTyped setterTyped
  obtain ⟨actualBinder, _, description⟩ := CompatiblePlaceDescription.of_describe described
  have same := Except.ok.inj (description.binding.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  subst actualBinder
  have routeEq := (description.prepared preparedBy).1
  have ordinary : (∀ k v, prepared.route.rootSourceType ≠ .mapping k v) → prepared.route.rootMapping = none := by
    intro _
    rw [routeEq]
    exact description.ordinary (by intros; intro impossible; cases impossible)
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate (.uninitialized rootProjection) Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] (world prepared) [] (scope prepared) environment (nativeEnvironment prepared) :=
    .cons reference (.nil .nil)
  have writable : WritableLocal context binder.id prepared.route.rootSourceType := rootEq ▸ rootWritable
  obtain ⟨finalStore, finalMap, finalWorld, failed, evaluated, heaps, _⟩ :=
    CompatiblePlaceTargetFaults.uninitialized (compilation := compilation) (ambient := .original checked.catalog.definitions) (functions := noFunctions checked.catalog) (index := 0) layout (childMeaning compilation.registry) environments heaps absentAgrees
      (by simp [scope, SourceCoreLocalCell.lookup?, assignment]) writable
      (Dynamic.Environment.LooksUp.head) (Dynamic.Heap.Reads.intro .head)
      (Dynamic.SourceProjectionsEvaluate.index (keyEvaluates environment absent) .nil) (Dynamic.Heap.Reads.intro .head)
      ordinary rfl (by rintro ⟨k, v, impossible⟩; cases impossible) (by simp) .equal key
      (LanguageResult.failure prepared.route.leafType (.word (Word.ofNatModulo 777)))
      (LanguageResult.failure .bool (.word (Word.ofNatModulo 888))) .bool Word.zero
  exact ⟨finalStore, finalMap, finalWorld, failed, evaluated, heaps⟩

private def exercise {route : Route} {prepared : Prepared}
    (described : describe compilation checked.signatures source site assignment = .ok route)
    (preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) = .ok prepared)
    {encoded : SourceCoreCompatibleValues.Encoded 100 compilation rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier = .ok encoded) : IO Unit := do
  if keyTypes : prepared.keyTypes = [.bool] then
    match stepsEq : prepared.steps with
    | [] => throw (IO.userError "target fault omitted index")
    | _ :: _ =>
      have nonempty : prepared.steps ≠ [] := by rw [stepsEq]; simp
      if getTyped : infer? (getContext prepared) (getCode prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.optionalLeaf) then
        if putTyped : infer? (putContext prepared) (putCode prepared) checked.catalog.definitions = some (LanguageResult.resultType prepared.route.rootType) then
          have receipt := whole described preparedBy keyTypes nonempty (infer_sound getTyped) (infer_sound putTyped) accepted
          have _finite : ∃ fuel token after, runStateful fuel (.initial (body prepared) (nativeEnvironment prepared) [.inRight .unit encoded.value]) = .done (.inLeft .bool (.word token)) after := by
            obtain ⟨token, after, _, _, _, evaluated, _⟩ := receipt
            obtain ⟨fuel, completed⟩ := evaluation_runStateful_complete evaluated
            exact ⟨fuel, token, after, completed⟩
          have _absent := uninitialized described preparedBy keyTypes nonempty (infer_sound getTyped) (infer_sound putTyped)
          let absentStore := [Value.inLeft prepared.route.rootType .unit]
          unless runStateful 200000 (.initial (body prepared) (nativeEnvironment prepared) absentStore) ==
              .done (.inLeft .bool (.word prepared.invalidProjection)) absentStore do
            throw (IO.userError "ordinary absent root allocated helpers or ran RHS")
          let keyEffect := Expr.letE (.storeCell (.var 1) (.inRight .unit (.bool true))) (LanguageResult.success (.bool true))
          let effectBody := execute prepared (.var 0) ⟨.bool, keyEffect⟩
            (LanguageResult.failure prepared.route.leafType (.word (Word.ofNatModulo 777)))
            (LanguageResult.failure .bool (.word (Word.ofNatModulo 888))) .bool none false Word.zero
          let effectEnvironment := nativeEnvironment prepared ++ [.cellRef (OptionalCell.cellType .bool) 1]
          let effectStore := absentStore ++ [.inRight .unit (.bool false)]
          unless infer? [OptionalCell.referenceType prepared.route.rootType, OptionalCell.referenceType .bool]
              effectBody checked.catalog.definitions == some (LanguageResult.resultType .bool) do
            throw (IO.userError "target key effect body rejected")
          unless runStateful 200000 (.initial effectBody effectEnvironment effectStore) ==
              .done (.inLeft .bool (.word prepared.invalidProjection)) (absentStore ++ [.inRight .unit (.bool true)]) do
            throw (IO.userError "target fault lost successful key effects or ran RHS")
          let header ← match encoded.value with
            | .pair (.word word) _ => pure word
            | _ => throw (IO.userError "target fault missing raw mapping header")
          unless encoded.context.registry.lookup header == some (.mapping .bool (.comptime valueType)) do
            throw (IO.userError "target fault lost raw default metadata")
          unless infer? [OptionalCell.referenceType prepared.route.rootType] (body prepared) checked.catalog.definitions == some (LanguageResult.resultType .bool) do
            throw (IO.userError "target fault emitted body rejected")
          let initial := Core.State.initial (body prepared) (nativeEnvironment prepared) [.inRight .unit encoded.value]
          match runStateful 200000 initial with
          | .done (.inLeft .bool (.word token)) after =>
            unless token == (Word.ofNatModulo 100).add header && after.take 1 == [.inRight .unit encoded.value] &&
                after.length == 1 + checked.catalog.entries.length + 1 do
              throw (IO.userError "target fault lost root or evaluated RHS/continuation")
            match runStateful 11 initial with
            | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done (.inLeft .bool (.word token)) after do
                throw (IO.userError "target fault resumption changed observation")
            | _ => throw (IO.userError "target fault expected checkpoint")
          | other => throw (IO.userError s!"target fault unexpected result {reprStr other}")
        else throw (IO.userError "target fault setter checker failed")
      else throw (IO.userError "target fault getter checker failed")
  else throw (IO.userError "target fault key types changed")

def run : IO Unit := do
  match described : describe compilation checked.signatures source site assignment with
  | .error error => throw (IO.userError s!"target fault describe failed {reprStr error}")
  | .ok route =>
    match preparedBy : prepare compilation 100 route Word.zero (fun _ => Word.ofNatModulo 100) with
    | .error error => throw (IO.userError s!"target fault prepare failed {reprStr error}")
    | .ok _ =>
      match accepted : SourceCoreCompatibleValues.encode 100 compilation rootType carrier with
      | .error error => throw (IO.userError s!"target fault encoding failed {reprStr error}")
      | .ok _ => exercise described preparedBy accepted
  IO.println "compatible target failure before RHS and exact raw default token GREEN"

end Tests.SourceCoreCompatibleTargetFaults
end

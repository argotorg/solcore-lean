import Solcore.SourceSemantics.CoreLowering.ProtectedStagedBareAssignment
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBareAssignmentAdmission
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementHead

/-! Actual bare assignment Heads use the same admitted staged RHS and preserve
its exact reached caller. Source assignment typing establishes admission after
the write; failures keep the precise staged tag and the RHS endpoint. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Rhs
variable {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
  {faults : RecursiveStageMeaning.FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate}
  (snapshot : CompatibleBareAssignment.Snapshot values.checked registry functions prepared place environment actual heap store mapping world (ξ index))

private theorem rhs_preserves_at (size : Nat)
    (meaning : PreservesAt bridge context (payloadModel values.checked registry functions) stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents values.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (admitted : Admission bridge context initial)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      ProtectedStagedBareAssignment.RhsResult (compilation := values) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        snapshot size outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial admitted trace
  refine ⟨value, finalStore, finalMap, finalWorld,
    ⟨trace, ?_, represented, finalHeaps, maps, worlds, frame, metadata, ?_⟩, reached, related⟩
  · simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
    DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated
  · intro right same
    cases same
    exact ⟨post.at_value.1, post.at_value.2.heap⟩

private theorem rhs_reflects_at (size : Nat)
    (meaning : ReflectsAt bridge context (payloadModel values.checked registry functions) stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents values.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (admitted : Admission bridge context initial)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size
      (DataPlaceExecution.snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      ProtectedStagedBareAssignment.RhsResult (compilation := values) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        snapshot sourceSize outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial admitted
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
        DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld,
    ⟨trace, evaluated.sound, represented, finalHeaps, maps, worlds, frame, metadata, by
      intro right same
      cases same
      exact ⟨post.at_value.1, post.at_value.2.heap⟩⟩, reached, related⟩
end Rhs

inductive ResultAt (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (context : SourceSemantics.Context) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (faults : RecursiveStageMeaning.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | operands {sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {right : Dynamic.Value} {after : Dynamic.Heap} {current : Dynamic.Cell}
      {initialValue selected : Option Dynamic.Value} {token : Word}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) after)
      (currentRead : Dynamic.Heap.Reads after target.location current)
      (rootType : current.type = target.rootType)
      (initialized : Dynamic.RootInitialValue current initialValue)
      (path : Dynamic.ProjectionsRead initialValue target.projections selected)
      (invalid : Dynamic.AssignmentOperandsInvalid operator target.selected right)
      (same : value = .inLeft output (.word token))
      (matched : faults (.semantic (.invalidAssignmentOperands operator)) token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | success {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace}
      {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
        middle target updated after)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size checked registry functions context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore

section Heads
variable {values : SourceCoreCompatibleValues.Context}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values invocation.source context certificate scope administrative ambient.definitions assignment operator rhs)
  (bare : assignment.target.projections = [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)

include extension environments heaps locals agrees bare head in
/-- The accepted writable root and actual represented heap determine the
pre-RHS snapshot; no Source assignment execution is assumed. -/
theorem target_snapshot :
    ∃ target, Staging.Recursive.BareTarget environment before assignment.target target := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    obtain ⟨snapshot⟩ := CompatibleBareAssignment.snapshot_of_heap layout extension environments heaps locals agrees slot writable
    exact ⟨snapshot.resolved, .intro empty snapshot.lookup snapshot.read snapshot.root⟩

include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare in
theorem reflects_bounded (budget : Nat)
    (boundedReflection : ReflectsBelow bridge context (payloadModel values.checked registry functions) stages invocation certificate faults budget)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator head.invalid)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt bridge size values.checked registry functions context stages invocation faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    have result := ProtectedStagedBareAssignment.reflects_with_rhs callerProtocol transport budget initial layout empty extension
      (fun snapshot child smaller {_ _} evaluated => rhs_reflects_at bridge snapshot child (boundedReflection child smaller)
        right found sourceTyped environments heaps locals agrees actualTyped initial admitted evaluated)
      rightView rightType (CallableIndexedOwnedBareAssignmentAdmission.source_profile unique found assignmentTyped rightView)
      environments heaps locals agrees actualTyped slot writable invalidToken completed bounded
    cases result with
    | fault snapshot trace same matched finalHeaps maps worlds preservation metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .fault snapshot trace same matched finalHeaps maps worlds preservation metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation)
    | operands snapshot trace currentRead rootType initialized path invalidOperands same matched finalHeaps maps worlds preservation metadata post =>
      obtain ⟨reached, related⟩ := post
      exact .operands snapshot trace currentRead rootType initialized path invalidOperands same matched finalHeaps maps worlds preservation metadata reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation)
    | success snapshot trace rightTyped middleTyped write finalHeaps maps worlds preservation metadata count typed strict remaining post =>
      obtain ⟨reached, related⟩ := post
      exact .success snapshot trace write finalHeaps maps worlds preservation metadata count
        (by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
          Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed)
        reached related ⟨CallableIndexedOwnedBareAssignmentAdmission.heap_after_assignment unique found assignmentTyped
          locals snapshot middleTyped rightTyped write,
          StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation⟩ strict remaining
include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare in
theorem preserves_value {sourceSize : Nat}
    (meaning : PreservesAt bridge context (payloadModel values.checked registry functions) stages invocation certificate faults sourceSize)
    {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
    (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
    (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) middle)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨finalStore, finalMap, finalWorld, slots, rightTyped, middleTyped, finalHeaps, maps, worlds, frame, metadata, count, typed, post, agreement⟩ :=
      ProtectedStagedBareAssignment.preserves_value_with_rhs callerProtocol transport initial layout empty extension snapshot trace write
        (fun snapshot => rhs_preserves_at bridge snapshot sourceSize meaning generated found sourceTyped
          environments heaps locals agrees actualTyped initial admitted trace)
        rightView rightType (CallableIndexedOwnedBareAssignmentAdmission.source_profile unique found assignmentTyped rightView)
        environments heaps locals agrees actualTyped slot writable invalid
    obtain ⟨reached, related⟩ := post
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count,
      by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
        Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed,
      ⟨reached, related, CallableIndexedOwnedBareAssignmentAdmission.heap_after_assignment unique found assignmentTyped
        locals snapshot middleTyped rightTyped write,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩,
      agreement⟩

include extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare in
theorem preserves_fault {sourceSize : Nat}
    (meaning : PreservesAt bridge context (payloadModel values.checked registry functions) stages invocation certificate faults sourceSize)
    {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.fault failure) after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
      ProtectedStagedBareAssignment.preserves_fault_with_rhs callerProtocol initial layout extension
        (fun snapshot => rhs_preserves_at bridge snapshot sourceSize meaning generated found sourceTyped
          environments heaps locals agrees actualTyped initial admitted trace)
        environments heaps locals agrees slot writable next output invalid
    obtain ⟨reached, related⟩ := post
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata,
      reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

include extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare in
theorem preserves_operands {sourceSize : Nat}
    (meaning : PreservesAt bridge context (payloadModel values.checked registry functions) stages invocation certificate faults sourceSize)
    {right : Dynamic.Value} {after : Dynamic.Heap} {target : Dynamic.ResolvedPlace}
    (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
    (invalidOperands : Dynamic.AssignmentOperandsInvalid operator target.selected right)
    (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) after)
    (next : Expr) (output : Ty)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator head.invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults (.semantic (.invalidAssignmentOperands operator)) token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
      ProtectedStagedBareAssignment.preserves_operands_with_rhs callerProtocol initial layout empty extension snapshot invalidOperands
        (fun snapshot => rhs_preserves_at bridge snapshot sourceSize meaning generated found sourceTyped
          environments heaps locals agrees actualTyped initial admitted trace)
        rightView rightType (CallableIndexedOwnedBareAssignmentAdmission.source_profile unique found assignmentTyped rightView)
        environments heaps locals agrees slot writable next output invalid invalidToken
    obtain ⟨reached, related⟩ := post
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata,
      reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

end Heads
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareAssignmentHeads

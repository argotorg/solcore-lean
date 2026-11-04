import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualReads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallTree
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductCertificates
import Solcore.SourceSemantics.CoreLowering.DataExpressionSequence
import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionInstantiationLaws
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.RecursiveMethodPreparedStageScopes
import Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.RecursiveMethodSelectionIdentity
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.RecursiveMethodDictionaryIdentity
import Solcore.SourceSemantics.CoreLowering.CallableMethodOriginSource
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualProducts

/-!
# Staged bounds: expressions

Staged bounds of reads, literals, groups, pairs, products, tuples, constructors and operators, with operator method authority and issuance.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadBounds
/-! Actual compatible local reads discharge the staged leaf contracts. The
compiler receipt keeps the original declaration and occurrence type. The
visible heap cell excludes generalized local evaluation, and empty output
coercions allow only the original atomic Source rule. The fault policy is requested only for a certified read. Lazy mapping reads keep
their real write and every ordered caller record at the reached state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CompatibleExpressionReads
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

private theorem no_stage
    {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {size : Nat}
    {name : String} {binder : Resolved.LocalId} {failedScope call reason}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (coercions : node.coercions = [])
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      before id (.fault (.stage failedScope call reason)) after) : False := by
  have reference : ∀ {shape requirements}, Staging.Recursive.Occurrence invocation id shape requirements →
      shape = .reference name (.local binder) := by
    intro shape requirements occurrence
    obtain ⟨other, contains, sameForm, _, _⟩ := occurrence
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    exact sameForm.symm.trans form
  cases trace with
  | generalizedLocal contains _ _ _ _ _ _ _ path =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [coercions] at path
      cases path
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found coercions contains))
  | group occurrence _
  | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _
  | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
      cases reference occurrence

/-- Reconstruct only an ordinary readable local, using its actual cell. The
generalized-local alternatives are excluded by that same cell's descriptor. -/
private theorem staged_of_read
    {fuel : Nat} {values : ValuesContext} {invocation : Staging.Recursive.Scope}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel values invocation.source scope id reason code)
    {program : Program} {registry : Staging.Recursive.Registry} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    (read : Dynamic.Heap.Reads before location cell)
    (ordinary : cell.generalized = none)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
      environment before id outcome after) :
    Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [])
      invocation context environment before id
      (match outcome with | .value value => .value value | .fault fault => .fault (.semantic fault)) after := by
  have same_node : ∀ {other}, ContainsExpression invocation.source id other → other = certificate.node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans certificate.metadata.found)
  have same_cell : ∀ {otherLocation otherCell},
      Dynamic.Environment.LooksUp environment certificate.binder otherLocation →
      Dynamic.Heap.Reads before otherLocation otherCell → otherCell = cell := by
    intro otherLocation otherCell otherLookup otherRead
    have sameLocation := otherLookup.functional lookup
    subst otherLocation
    exact otherRead.functional read
  have contains := lookupExpression?_sound certificate.metadata.found
  have atomic : Staging.Recursive.AtomicForm certificate.node.form := by
    rw [certificate.form]
    exact .reference _ _
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro otherContains raw coercions =>
      cases same_node otherContains
      rw [certificate.metadata.coercions] at coercions
      cases coercions
      exact .atomicValue contains atomic certificate.metadata.coercions
        (by simpa only [certificate.metadata.coercions] using raw)
    | generalizedLocal otherContains otherForm _ otherLookup otherRead descriptor _ _ _ =>
      cases same_node otherContains
      rw [certificate.form] at otherForm
      cases otherForm
      cases same_cell otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
    | form otherContains raw =>
      cases same_node otherContains
      exact .atomicFault contains atomic certificate.metadata.coercions
        (by simpa only [certificate.metadata.coercions] using raw)
    | coercion otherContains _ failed =>
      cases same_node otherContains
      rw [certificate.metadata.coercions] at failed
      cases failed
    | generalizedLocalRequirement otherContains otherForm _ otherLookup otherRead descriptor _ _ _
    | generalizedLocalCoercion otherContains otherForm _ otherLookup otherRead descriptor _ _ _ =>
      cases same_node otherContains
      rw [certificate.form] at otherForm
      cases otherForm
      cases same_cell otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {fuel : Nat} {reasonAt : ExpressionId → Word}
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ scope id lowered,
    LoweredRead fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "reads" => LoweredRead fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) invocation.source context reasonAt

include extension semantic unique wellFormed runtime covers in
/-- The accepted local-read compiler discharges preservation internally. A
stage failure at this atomic occurrence is impossible; semantic failures keep
their original token, heap and actual caller state. -/
theorem preserves_local (size : Nat) :
    PreservesAt bridge context model registry invocation
      (fun scope id lowered => reads scope id lowered ∧
        ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) faults size := by
  intro scope id lowered ⟨receipt, readFault⟩ node found sourceTyped
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  have plain : ∃ plainOutcome : Dynamic.ExpressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
        environment before id plainOutcome after ∧
      outcome = (match plainOutcome with | .value value => .value value | .fault reason => .fault (.semantic reason)) := by
    cases outcome with
    | value value => exact ⟨.value value, .value trace.sound.value_plain, rfl⟩
    | fault failure => cases failure with
      | semantic reason => exact ⟨.fault reason, .fault trace.sound.semanticFault_plain, rfl⟩
      | stage failedScope call reason =>
        exact False.elim (no_stage unique found (nodeEq ▸ certificate.form) (nodeEq ▸ certificate.metadata.coercions) trace)
  obtain ⟨plainOutcome, plainTrace, outcomeEq⟩ := plain
  obtain ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata⟩ :=
    certificate.preserves functions extension program context invocation.evidence binding
      environments heaps locals agrees readFault unique plainTrace
  simp only [SourceCoreCompatibleValues.Context.initial, nodeEq, typeEq] at represented finalHeaps
  let transport := administrativeTransport headers keys
  let reachedPool := transport.extend (bridge.pool initial) (.refl _) (.refl _) frame metadata
  obtain ⟨reached, _poolEq, related⟩ := bridge.restore initial reachedPool (.refl _) (.refl _)
    frame metadata (transport.related (bridge.pool initial) (.refl _) (.refl _) frame metadata)
  refine ⟨value, finalStore, mapping, world, ?_, ?_, finalHeaps, .refl _, .refl _,
    frame, metadata, reached, related, ?_⟩
  · simpa only [← typeEq] using evaluated
  · cases represented with
    | value payload =>
      rw [outcomeEq]
      exact .value payload
    | fault matched =>
      rw [outcomeEq]
      exact .fault (semantic _ _ matched)
  · exact after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame

include extension semantic unique wellFormed runtime covers in
/-- A completed native read reconstructs the original atomic Source outcome
at grade one. Lazy mapping initialization retains its exact written cell and
every caller row at the same final store. -/
theorem reflects_local (size : Nat) :
    ReflectsAt bridge context model registry invocation
      (fun scope id lowered => reads scope id lowered ∧
        ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) faults size := by
  intro scope id lowered ⟨receipt, readFault⟩ node found sourceTyped
    mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  obtain ⟨_, selected, _, _, _, selectedRead, _, cellRep⟩ :=
    GenericHeap.lookup_visible environments heaps lookup certificate.slot
  have sameCell := read.functional selectedRead
  subst selected
  obtain ⟨outcome, after, sourceTrace, represented, finalHeaps, frame, metadata⟩ :=
    certificate.reflects functions extension program context invocation.evidence binding
      environments heaps locals agrees readFault (by simpa only [← typeEq] using completed.sound)
  simp only [SourceCoreCompatibleValues.Context.initial, nodeEq, typeEq] at represented finalHeaps
  have staged := staged_of_read (registry := registry) certificate unique lookup read cellRep.ordinary sourceTrace
  let transport := administrativeTransport headers keys
  let reachedPool := transport.extend (bridge.pool initial) (.refl _) (.refl _) frame metadata
  obtain ⟨reached, _poolEq, related⟩ := bridge.restore initial reachedPool (.refl _) (.refl _)
    frame metadata (transport.related (bridge.pool initial) (.refl _) (.refl _) frame metadata)
  refine ⟨Staging.Recursive.Size.stepSize [], _, after, mapping, world, staged, ?_, finalHeaps,
    .refl _, .refl _, frame, metadata, reached, related, ?_⟩
  · cases represented with
    | value payload => exact .value payload
    | fault matched => exact .fault (semantic _ _ matched)
  · exact after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped staged frame

include extension uninitialized semantic unique wellFormed runtime covers in
/-- The global diagnostic interface follows by restricting it to the actual read. -/
theorem preserves (size : Nat) :
    PreservesAt bridge context model registry invocation reads faults size := by
  intro scope id lowered receipt
  exact preserves_local bridge functions extension semantic unique wellFormed runtime covers size
    ⟨receipt, uninitialized scope id lowered receipt⟩

include extension uninitialized semantic unique wellFormed runtime covers in
/-- The global diagnostic interface follows by restricting it to the actual read. -/
theorem reflects (size : Nat) :
    ReflectsAt bridge context model registry invocation reads faults size := by
  intro scope id lowered receipt
  exact reflects_local bridge functions extension semantic unique wellFormed runtime covers size
    ⟨receipt, uninitialized scope id lowered receipt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds
/-! A compiler group keeps the literal child code. Preservation uses the
strict Source child grade. Reflection uses the finite LiteralSites child
hypothesis at the same native grade, keeping the exact staged failure and
reached caller state. Semantic hypotheses are theorem arguments, never fields
of the static compiler receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CompatibleExpressionPrimitives (Metadata)
universe u

/-- The existing compiler grouping fields, including the SAME child code. -/
inductive Group (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (children : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | actual {id node inner innerNode lowered}
      (metadata : Metadata checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : children scope inner lowered) : Group checked source children scope id lowered

/-- Select the genuine used child from the original finite LiteralSites.
The original group head, child list, fuel and literal receipts are retained.
Use the actual node fields exposed by LiteralSites induction; the proof
index itself is not an inverse to an arbitrary external child list. -/
theorem of_literal_sites
    {calls : CompatibleExpressionCalls.CallHeads} {fuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {literals : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {id inner : ExpressionId}
    {node innerNode : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    {entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)}
    (metadata : Metadata values.checked source id node lowered.type)
    (form : node.form = .group inner)
    (innerFound : source.lookupExpression? inner = some innerNode)
    (sourceType : node.type = innerNode.type)
    (member : (inner, lowered) ∈ entries)
    (children : ∀ child code, (child, code) ∈ entries →
      CompatibleExpressionCalls.Tree calls fuel values source sourceContext solved reasonAt scope child code)
    (childSites : ∀ child code (entry : (child, code) ∈ entries),
      (children child code entry).LiteralSites literals) :
    Group values.checked source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls) (fuel := fuel)
        (values := values) (source := source) (context := sourceContext)
        (solved := solved) (reasonAt := reasonAt) literals) scope id lowered := by
  exact .actual metadata form innerFound sourceType
    ⟨children inner lowered member, childSites inner lowered member⟩

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

private theorem source_group_inv
    {id inner : ExpressionId} {node : ExpressionNode}
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .group inner)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context
      environment before id outcome after) :
    ∃ childSize, size = Staging.Recursive.Size.stepSize [childSize] ∧
      Staging.Recursive.Size.Expression program registry childSize invocation context
        environment before inner outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm requirements},
      Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .group inner := by
    intro actualForm requirements occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | atomicFault contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | generalizedLocal contains localForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _ =>
      cases same_node contains
      rw [form] at localForm
      cases localForm
  | group occurrence child =>
      cases ExpressionForm.group.inj (occurrence_form occurrence)
      exact ⟨_, rfl, child⟩
  | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _
  | applied occurrence _ _ _ _ _ _ => cases occurrence_form occurrence

private theorem child_typed
    {id inner : ExpressionId} {node innerNode : ExpressionNode} {type : Ty}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .group inner)
    (innerFound : invocation.source.lookupExpression? inner = some innerNode)
    (unique : NodeOccurrencesUnique invocation.source)
    (typed : ExpressionHasType invocation.source context id node.type) :
    ExpressionHasType invocation.source context inner innerNode.type := by
  obtain ⟨actualNode, found, _sourceType, child⟩ :=
    CompatibleExpressionProducts.group_source_types unique metadata.found form metadata.coercions typed
  have same := Option.some.inj (found.symm.trans innerFound)
  cases same
  exact child

/-- The Source group rule adds one genuine step above its executed child.
The child theorem carries either fault tag and the exact reached state. -/
theorem group_preserves
    (unique : NodeOccurrencesUnique invocation.source) (budget : Nat)
    (childMeaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation children faults budget) :
    ∀ size, size ≤ budget → CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation (Group checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  cases certified with
  | actual metadata form innerFound sourceType child =>
      have same := Option.some.inj (found.symm.trans metadata.found)
      cases same
      obtain ⟨childSize, sizeEq, childTrace⟩ := source_group_inv unique metadata.found form trace
      have smaller : childSize < budget := by
        rw [sizeEq] at within
        exact Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
        childMeaning childSize smaller child innerFound
          (child_typed metadata form innerFound unique typed)
          environments heaps locals agrees actualTyped initial admitted childTrace
      refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, ?_⟩
      · simpa only [sourceType] using represented
      · simpa only [sourceType] using post

/-- The native group is literally the child code. Its structural child IH
uses the SAME grade; this theorem requests no strict native inequality. -/
theorem group_reflects
    (unique : NodeOccurrencesUnique invocation.source) (size : Nat)
    (childMeaning : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsAt
      bridge context model registry invocation children faults size) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsAt
      bridge context model registry invocation (Group checked invocation.source children) faults size := by
  intro scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  cases certified with
  | actual metadata form innerFound sourceType child =>
      have same := Option.some.inj (found.symm.trans metadata.found)
      cases same
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
        childMeaning child innerFound (child_typed metadata form innerFound unique typed)
          environments heaps locals agrees actualTyped initial admitted completed
      have occurrence : Staging.Recursive.Occurrence invocation id (.group _) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome, after, finalMap, finalWorld,
        .group occurrence trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
        reached, related, ?_⟩
      · simpa only [sourceType] using represented
      · simpa only [sourceType] using post

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLiteralGroupBounds
/-! The finite literal/group compiler fragment has concrete staged meaning.
Selected numeric rows construct both values internally. Groups retain the
same child code. Source preservation follows strict executed Source grades;
native reflection follows the finite tree at the same native grade. Every
literal returns the identical caller state. No completed child/body law is a
field or an input to the closed fragment theorem. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLiteralGroupBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CompatibleExpressionLiterals
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

/-- Only actual selected literal receipts and exact compiler group fields. -/
inductive Tree (checked : SourceCoreCompatibleCatalog.Checked) (solved : List SolvedRequirement)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | literal {id lowered}
      (receipt : CompatibleExpressionLiteralRuntime.Certificate solved source id lowered) :
      Tree checked solved source scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : CompatibleExpressionReads.Metadata checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Tree checked solved source scope inner lowered) :
      Tree checked solved source scope id lowered

/-- The same real compiler fields construct the canonical finite literal
support. This is a forward producer from the retained child, not an inverse
from equality between proof indices. -/
theorem Tree.literal_sites
    {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree values.checked solved source scope id lowered) :
    CompatibleExpressionProducts.Tree.WithLiterals (fuel := fuel) (values := values)
      (source := source) (context := sourceContext) (solved := solved) (reasonAt := reasonAt)
      (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved source id lowered)
      scope id lowered := by
  induction tree with
  | literal receipt => exact ⟨.literal receipt.forget, .literal receipt.forget receipt⟩
  | group metadata form innerFound sourceType child ih =>
      obtain ⟨actualChild, sites⟩ := ih
      exact ⟨.group metadata form innerFound sourceType actualChild,
        .group metadata form innerFound sourceType actualChild sites⟩

/-- Actual accepted atomic lowering produces the selected literal leaf.
The compiler policy/read/leaf facts are static; no value or execution is given. -/
theorem Tree.of_functions_literal
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilerContext : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (atomic : Atomic node.form) (unitType : node.form = .tuple [] → node.type = .unit)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilerContext child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilerContext
      source scope id reasonAt = .ok lowered) :
    Tree values.checked compilerContext.solvedRequirements source scope id lowered := by
  exact .literal (CompatibleExpressionLiteralRuntime.of_functions found atomic unitType
    special readPolicy leafPolicy accepted)

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

private theorem atomic_not_local {form : ExpressionForm} (atomic : Atomic form) :
    ∀ name binder, form ≠ .reference name (.local binder) := by
  cases atomic <;> intros <;> intro impossible <;> cases impossible

private theorem literal_atomic {solved node type code} (literal : Literal solved node type code) : Atomic node.form := by
  cases literal with
  | unit form _ _ _ => rw [form]; exact .unit
  | bool value form _ _ _ => rw [form]; exact .bool _ _
  | word value form _ _ _ _ => rw [form]; exact .word _
  | resolvedWord form _ | resolvedInteger form _ => rw [form]; exact .integer _ _

private theorem literal_coercions {solved node type code} (literal : Literal solved node type code) : node.coercions = [] := by
  cases literal with
  | unit _ _ _ empty | bool _ _ _ _ empty | word _ _ _ _ empty _ => exact empty
  | resolvedWord _ metadata | resolvedInteger _ metadata => exact metadata.coercions

private theorem evaluation_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (atomic : Atomic node.form) (empty : node.coercions = [])
    (evaluation : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment before node.form node.requirements node.coercions value after := by
  cases evaluation with
  | intro found raw coercions =>
    have same := contains_unique unique found contains
    subst same
    rw [empty] at coercions
    cases coercions
    exact raw
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := contains_unique unique found contains
    subst same
    exact False.elim (atomic_not_local atomic _ _ form)

private theorem fault_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (atomic : Atomic node.form) (empty : node.coercions = [])
    (fault : Dynamic.ExpressionFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFormFaults program context evidence source environment before node.form node.requirements node.coercions reason after := by
  cases fault with
  | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
  | form found raw => exact contains_unique unique found contains ▸ raw
  | coercion found _ failed =>
    have same := contains_unique unique found contains
    subst same
    rw [empty] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := contains_unique unique found contains
    subst same
    exact False.elim (atomic_not_local atomic _ _ form)

private theorem literal_form_unique {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap firstHeap secondHeap : Dynamic.Heap}
    {left right : Dynamic.Value}
    (first : Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form node.requirements node.coercions left firstHeap)
    (second : Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form node.requirements node.coercions right secondHeap) :
    left = right ∧ firstHeap = secondHeap := by
  cases literal with
  | unit form _ _ _ =>
    rw [form] at first second
    cases first with | tuple _ elements pack =>
      cases elements
      cases pack
      cases second with | tuple _ elements pack => cases elements; cases pack; exact ⟨rfl, rfl⟩
  | bool value form _ _ _ => rw [form] at first second; cases first; cases second; exact ⟨rfl, rfl⟩
  | word value form _ _ _ _ =>
    rw [form] at first second
    cases first with | literal _ first =>
      cases second with | literal _ second => exact ⟨first.functional second, rfl⟩
  | resolvedWord form _ | resolvedInteger form _ =>
    rw [form] at first second
    cases first with | integerLiteral _ first =>
      cases second with | integerLiteral _ second => exact ⟨first.functional second, rfl⟩

private theorem literal_excludes_fault_with_evidence {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : NumericEvidence context evidence node)
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (fault : Dynamic.ExpressionFormFaults program context evidence source environment before node.form node.requirements node.coercions reason after) : False := by
  cases literal with
  | unit form _ _ _ =>
    rw [form] at fault
    cases fault with | tuple _ failed => cases failed
  | bool value form _ _ _ | word value form _ _ _ _ => rw [form] at fault; cases fault
  | resolvedWord form metadata | resolvedInteger form metadata =>
    rw [form] at fault
    cases fault with | integerRequirement _ unavailable =>
      exact (valid _ _ form).2 unavailable


private theorem literal_atomic_staged {solved node type code}
    (literal : Literal solved node type code) : Staging.Recursive.AtomicForm node.form := by
  cases literal with
  | unit form _ _ _ => rw [form]; exact .unit
  | bool value form _ _ _ => rw [form]; exact .reference _ _
  | word value form _ _ _ _ => rw [form]; exact .literal _
  | resolvedWord form _ | resolvedInteger form _ => rw [form]; exact .integerLiteral _ _

/-- The actual atomic compiler forms cannot acquire a nested stage failure. -/
private theorem no_stage
    {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {size : Nat}
    {solved : List SolvedRequirement} {type code} {failedScope call reason}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (literal : Literal solved node type code)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      before id (.fault (.stage failedScope call reason)) after) : False := by
  have occurrence_atomic : ∀ {form requirements}, Staging.Recursive.Occurrence invocation id form requirements → Atomic form := by
    intro form requirements occurrence
    obtain ⟨actualNode, contains, sameForm, _requirements, _coercions⟩ := occurrence
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    rw [← sameForm]
    exact (literal_atomic literal)
  cases trace with
  | generalizedLocal contains localForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact False.elim (atomic_not_local (literal_atomic literal) _ _ localForm)
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found (literal_coercions literal) contains))
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ =>
      have atomic := occurrence_atomic occurrence
      cases atomic
  | tupleFault occurrence failed =>
      have atomic := occurrence_atomic occurrence
      cases atomic
      cases failed
  | group occurrence _
  | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _
  | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
      cases occurrence_atomic occurrence

variable {checked : SourceCoreCompatibleCatalog.Checked} {rawRegistry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)
  (faults : RecursiveStageMeaning.FaultRep)

private abbrev literalCertificate : GenericExpressionMeaning.Certificate :=
  fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved invocation.source id lowered

include sameLedger runtimeLedger unique wellFormed runtime covers in
/-- A genuine static numeric receipt constructs the actual Source and native
values. The Source grade is independent of native evaluation size. -/
theorem literal_preserves (size : Nat) :
    PreservesAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (literalCertificate (solved := solved) (invocation := invocation)) faults size := by
  intro scope id lowered receipt node found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨other, otherFound, literal, selected⟩ := receipt
  have same := Option.some.inj (otherFound.symm.trans found)
  cases same
  have valid := selected.evidence sameLedger runtimeLedger invocation.evidence
  obtain ⟨sourceValue, coreValue, raw, represented, evaluated⟩ :=
    literal.evaluates_with_evidence functions program context invocation.evidence valid invocation.source
      environment before mapping world actual store ξ
  have unchanged : outcome = .value sourceValue ∧ after = before := by
    cases outcome with
    | value value =>
        have actualRaw := evaluation_raw unique (lookupExpression?_sound found)
          (literal_atomic literal) (literal_coercions literal) trace.sound.value_plain
        obtain ⟨rfl, rfl⟩ := literal_form_unique literal actualRaw raw
        exact ⟨rfl, rfl⟩
    | fault failure =>
        cases failure with
        | semantic reason =>
            exact False.elim (literal_excludes_fault_with_evidence literal valid
              (fault_raw unique (lookupExpression?_sound found) (literal_atomic literal) (literal_coercions literal)
                trace.sound.semanticFault_plain))
        | stage failedScope call reason => exact False.elim (no_stage unique found literal trace)
  obtain ⟨rfl, rfl⟩ := unchanged
  refine ⟨.inRight .word coreValue, store, mapping, world, evaluated, .value represented,
    heaps, .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, ?_⟩
  exact after_expression_sized initial initial admitted wellFormed runtime covers locals typed trace (.refl _ _)

include sameLedger runtimeLedger wellFormed runtime covers in
/-- Reflection constructs an atomic Source rule of grade one and keeps the
literal input caller itself as the reached dependent witness. -/
theorem literal_reflects (size : Nat) :
    ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (literalCertificate (solved := solved) (invocation := invocation)) faults size := by
  intro scope id lowered receipt node found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨other, otherFound, literal, selected⟩ := receipt
  have same := Option.some.inj (otherFound.symm.trans found)
  cases same
  have valid := selected.evidence sameLedger runtimeLedger invocation.evidence
  obtain ⟨sourceValue, coreValue, raw, represented, evaluated⟩ :=
    literal.evaluates_with_evidence functions program context invocation.evidence valid invocation.source
      environment before mapping world actual store ξ
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed.sound
  have sourceTrace : Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [])
      invocation context environment before id (.value sourceValue) before :=
    .atomicValue (lookupExpression?_sound found) (literal_atomic_staged literal) (literal_coercions literal)
      (by simpa only [(literal_coercions literal)] using raw)
  refine ⟨Staging.Recursive.Size.stepSize [], .value sourceValue, before, mapping, world,
    sourceTrace, .value represented, heaps, .refl _, .refl _, .refl _ _, .refl _,
    initial, callerProtocol.refl initial, ?_⟩
  exact after_expression_sized initial initial admitted wellFormed runtime covers locals typed sourceTrace (.refl _ _)

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

include sameLedger runtimeLedger unique wellFormed runtime covers in
/-- Finite structural descent closes every supported node. There is no
universal E law or literal execution supplied by the caller. -/
theorem preserves (size : Nat) :
    PreservesAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (Tree checked solved invocation.source) faults size := by
  intro scope id lowered tree
  induction tree generalizing size with
  | literal receipt =>
      exact literal_preserves functions bridge sameLedger runtimeLedger unique wellFormed runtime covers faults size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
      have children : PreservesBelow bridge context
          (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) registry invocation
          (Point scope inner lowered) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih childSize
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size children
        size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)

include sameLedger runtimeLedger unique wellFormed runtime covers in
/-- Group reflection invokes only its finite child at the SAME native size.
The reconstructed Source grade grows through the independent group rule. -/
theorem reflects (size : Nat) :
    ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (Tree checked solved invocation.source) faults size := by
  intro scope id lowered tree
  induction tree with
  | literal receipt =>
      exact literal_reflects functions bridge sameLedger runtimeLedger wellFormed runtime covers faults size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
      have children : ReflectsAt bridge context
          (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) registry invocation
          (Point scope inner lowered) faults size := by
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size children
        (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLiteralGroupBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPairBounds
/-! The actual binary tuple head executes two children in their original order.
Source preservation descends at the actual Source child grades. Native
reflection descends at the actual bind child grades. Both keep the reached
caller state and both staged failure tags. No pair execution or body law is
part of the static compiler certificate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPairBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CompatibleExpressionProducts (Metadata)
universe u

inductive Pair (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (children : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | actual {id node left right leftNode rightNode first second}
      (metadata : Metadata checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (firstChild : children scope left first) (secondChild : children scope right second) :
      Pair checked source children scope id
        ⟨.product first.type second.type,
          LocalSequence.pair first.type second.type first.expression second.expression⟩

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- A payload model may combine two represented values at the same reached
heap/world. This is a representation constructor, with no execution input. -/
def ProductValues : Prop :=
  ∀ {mapping world leftType rightType left right first second firstType secondType},
    model.Represents mapping world leftType left first firstType →
    model.Represents mapping world rightType right second secondType →
    model.Represents mapping world (.product leftType rightType) (.product left right)
      (.pair first second) (.product firstType secondType)

private inductive SourceChildren (size : Nat) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (left right : ExpressionId) :
    Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | leftFault {childSize after failure}
      (smaller : childSize < size)
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context
        environment before left (.fault failure) after) :
      SourceChildren size environment before left right (.fault failure) after
  | rightFault {firstSize secondSize middle after value failure}
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size)
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context
        environment before left (.value value) middle)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context
        environment middle right (.fault failure) after) :
      SourceChildren size environment before left right (.fault failure) after
  | values {firstSize secondSize middle after leftValue rightValue}
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size)
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context
        environment before left (.value leftValue) middle)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context
        environment middle right (.value rightValue) after) :
      SourceChildren size environment before left right (.value (.product leftValue rightValue)) after

private theorem source_children
    {id left right : ExpressionId} {node : ExpressionNode}
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .tuple [left, right])
    (trace : Staging.Recursive.Size.Expression program registry size invocation context
      environment before id outcome after) :
    SourceChildren (program := program) (registry := registry) (invocation := invocation)
      (context := context) size environment before left right outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm requirements},
      Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .tuple [left, right] := by
    intro actualForm requirements occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | generalizedLocal contains localForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _ =>
      cases same_node contains
      rw [form] at localForm
      cases localForm
  | pair occurrence first second =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .values (Staging.Recursive.Size.child_lt_stepSize (by simp))
          (Staging.Recursive.Size.child_lt_stepSize (by simp)) first second
  | pairLeftFault occurrence child =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .leftFault (Staging.Recursive.Size.child_lt_stepSize (by simp)) child
  | pairRightFault occurrence first second =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .rightFault (Staging.Recursive.Size.child_lt_stepSize (by simp))
          (Staging.Recursive.Size.child_lt_stepSize (by simp)) first second
  | tupleValue occurrence sequence packed =>
      cases ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases sequence with
      | cons first rest =>
          cases rest with
          | cons second tail =>
              cases tail
              cases packed with
              | cons last =>
                  cases last
                  exact .values (by simp [Staging.Recursive.Size.stepSize]; omega)
                    (by simp [Staging.Recursive.Size.stepSize]; omega) first second
  | tupleFault occurrence sequence =>
      cases ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases sequence with
      | headFault first =>
          exact .leftFault (by simp [Staging.Recursive.Size.stepSize]; omega) first
      | tailFault first rest =>
          cases rest with
          | headFault second =>
              exact .rightFault (by simp [Staging.Recursive.Size.stepSize]; omega)
                (by simp [Staging.Recursive.Size.stepSize]; omega) first second
          | tailFault _ rest => cases rest
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _
  | group occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _
  | applied occurrence _ _ _ _ _ _ => cases occurrence_form occurrence

private theorem child_typing
    {id left right : ExpressionId} {node leftNode rightNode : ExpressionNode} {type : Ty}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .tuple [left, right])
    (leftFound : invocation.source.lookupExpression? left = some leftNode)
    (rightFound : invocation.source.lookupExpression? right = some rightNode)
    (unique : NodeOccurrencesUnique invocation.source)
    (typed : ExpressionHasType invocation.source context id node.type) :
    ExpressionHasType invocation.source context left leftNode.type ∧
      ExpressionHasType invocation.source context right rightNode.type := by
  obtain ⟨first, second, firstFound, secondFound, _sourceType, firstTyped, secondTyped⟩ :=
    CompatibleExpressionProducts.pair_source_types unique metadata.found form metadata.coercions typed
  cases Option.some.inj (firstFound.symm.trans leftFound)
  cases Option.some.inj (secondFound.symm.trans rightFound)
  exact ⟨firstTyped, secondTyped⟩

/-- Two genuine Source children are executed in their actual successive heaps.
Either failure keeps its original scoped representation and exact endpoint. -/
theorem pair_preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context) (products : ProductValues (model := model)) (budget : Nat)
    (childMeaning : PreservesBelow bridge context model registry invocation children faults budget) :
    ∀ size, size ≤ budget → PreservesAt bridge context model registry invocation
      (Pair checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  cases certified with
  | actual metadata form leftFound rightFound sourceType firstChild secondChild =>
      cases Option.some.inj (found.symm.trans metadata.found)
      obtain ⟨firstTyped, secondTyped⟩ := child_typing metadata form leftFound rightFound unique typed
      have parts := source_children unique metadata.found form trace
      cases parts with
      | leftFault smaller first =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le smaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | fault matched =>
              refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
                maps, worlds, frame, heapMetadata, reached, related, post.at_fault_type⟩
              rw [DataExpressionSequence.pair_rename]
              exact LocalSequence.pair_left_failure _ _ evaluated
      | rightFault firstSmaller secondSmaller first second =>
          obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le firstSmaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps,
                  maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
                childMeaning _ (Nat.lt_of_lt_of_le secondSmaller within) secondChild rightFound secondTyped
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix agrees _) (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 second
              cases represented with
              | fault matched =>
                  refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
                    firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                    firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related,
                    post.at_fault_type⟩
                  rw [DataExpressionSequence.pair_rename]
                  rw [rename_prefix] at secondEval
                  exact LocalSequence.pair_right_failure _ _ firstEval secondEval
      | values firstSmaller secondSmaller first second =>
          obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le firstSmaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps,
                  maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
                childMeaning _ (Nat.lt_of_lt_of_le secondSmaller within) secondChild rightFound secondTyped
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix agrees _) (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 second
              cases represented with
              | @value lastSource lastCoreValue lastPayload =>
                  refine ⟨.inRight .word (.pair coreValue lastCoreValue), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
                    firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                    firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related, ?_⟩
                  · rw [DataExpressionSequence.pair_rename]
                    rw [rename_prefix] at secondEval
                    exact LocalSequence.pair_success _ _ firstEval secondEval
                  · exact .value (sourceType ▸ products (model.extend payload maps worlds) lastPayload)
                  · exact after_expression_sized initial reached admitted wellFormed runtime covers
                      locals typed trace (firstFrame.trans frame)

/-- Actual native bind inversion supplies strictly smaller executed children;
the Source pair grade is constructed independently from their Source traces. -/
theorem pair_reflects
    (unique : NodeOccurrencesUnique invocation.source)
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context) (products : ProductValues (model := model)) (budget : Nat)
    (childMeaning : ReflectsBelow bridge context model registry invocation children faults budget) :
    ∀ size, size ≤ budget → ReflectsAt bridge context model registry invocation
      (Pair checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  cases certified with
  | actual metadata form leftFound rightFound sourceType firstChild secondChild =>
      cases Option.some.inj (found.symm.trans metadata.found)
      obtain ⟨firstTyped, secondTyped⟩ := child_typing metadata form leftFound rightFound unique typed
      have occurrence : Staging.Recursive.Occurrence invocation id (.tuple [_, _]) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      change EvaluationSize size actual store ((LocalSequence.pair _ _ _ _).rename ξ) value finalStore at completed
      rw [DataExpressionSequence.pair_rename] at completed
      have complete := completed
      cases completed with
      | caseLeft first _ =>
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
            childMeaning _ (by omega) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                (LocalSequence.pair_left_failure _ _ first.sound)
              exact ⟨_, .fault _, after, finalMap, finalWorld, .pairLeftFault occurrence trace,
                .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related,
                post.at_fault_type⟩
      | caseRight first continuation =>
          obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (by omega) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | @value sourceValue coreValue payload =>
              cases continuation with
              | caseLeft second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps,
                      maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
                    childMeaning _ (by omega) secondChild rightFound secondTyped
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                      (agree_prefix agrees _)
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 shifted
                  cases represented with
                  | fault matched =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_right_failure _ _ first.sound second.sound)
                      exact ⟨_, .fault _, after, finalMap, finalWorld,
                        .pairRightFault occurrence firstTrace secondTrace, .fault matched,
                        finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                        firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related,
                        post.at_fault_type⟩
              | caseRight second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps,
                      maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
                    childMeaning _ (by omega) secondChild rightFound secondTyped
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                      (agree_prefix agrees _)
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 shifted
                  cases represented with
                  | @value lastSource lastCoreValue lastPayload =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_success _ _ first.sound second.sound)
                      have trace := Staging.Recursive.Size.Expression.pair occurrence firstTrace secondTrace
                      refine ⟨_, .value _, after, finalMap, finalWorld, trace, ?_, finalHeaps,
                        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                        firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related, ?_⟩
                      · exact .value (sourceType ▸ products (model.extend payload maps worlds) lastPayload)
                      · exact after_expression_sized initial reached admitted wellFormed runtime covers
                          locals typed trace (firstFrame.trans frame)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPairBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedProductTreeBounds
/-! The actual accepted compiler extracts the finite pure product fragment.
The selected literal sites and exact grouped/product children are retained
through one canonical extraction. Structural recursion constructs the staged
meaning of every child. Native grouping keeps the same size; executed pair
children descend strictly. Source and native sizes remain independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedProductTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

/-- A finite syntax restriction, with actual lookup and form fields only. -/
inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | literal {id node} (found : source.lookupExpression? id = some node)
      (atomic : CompatibleExpressionLiterals.Atomic node.form) : Syntax source id
  | group {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .group inner) (child : Syntax source inner) : Syntax source id
  | pair {id node left right} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple [left, right])
      (first : Syntax source left) (second : Syntax source right) : Syntax source id

theorem Syntax.to_canonical {source : TypedSource} {id : ExpressionId}
    (syntaxTree : Syntax source id) : CompatibleExpressionProducts.Syntax source id := by
  induction syntaxTree with
  | literal found atomic => exact .literal found atomic
  | group found form child ih => exact .group found form ih
  | pair found form first second firstIH secondIH => exact .pair found form firstIH secondIH

/-- Every retained child is the literal native child from the same compiler
extraction. Source product types are independent raw typing identities. -/
inductive Tree (checked : SourceCoreCompatibleCatalog.Checked) (solved : List SolvedRequirement)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | literal {id lowered}
      (receipt : CompatibleExpressionLiteralRuntime.Certificate solved source id lowered) :
      Tree checked solved source scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : CompatibleExpressionReads.Metadata checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Tree checked solved source scope inner lowered) :
      Tree checked solved source scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : CompatibleExpressionReads.Metadata checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (leftTree : Tree checked solved source scope left first)
      (rightTree : Tree checked solved source scope right second) :
      Tree checked solved source scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩

/-- Translation follows actual LiteralSites, including their authentic
compound fields. The pure syntax rules rule out a local-read leaf. -/
theorem Tree.of_literal_sites
    {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered}
    (sites : tree.LiteralSites
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate solved source id code))
    (syntaxTree : Syntax source id) : Tree values.checked solved source scope id lowered := by
  induction sites with
  | literal _ receipt => exact .literal receipt
  | read receipt =>
      obtain ⟨actual, _type, _binding⟩ := receipt
      cases syntaxTree with
      | literal found atomic =>
          cases Option.some.inj (found.symm.trans actual.metadata.found)
          rw [actual.form] at atomic
          cases atomic
      | group found form child =>
          cases Option.some.inj (found.symm.trans actual.metadata.found)
          simp [actual.form] at form
      | pair found form first second =>
          cases Option.some.inj (found.symm.trans actual.metadata.found)
          simp [actual.form] at form
  | group metadata form innerFound sourceType child childSites ih =>
      cases syntaxTree with
      | literal found atomic =>
          cases Option.some.inj (found.symm.trans metadata.found)
          rw [form] at atomic
          cases atomic
      | group found actualForm childSyntax =>
          cases Option.some.inj (found.symm.trans metadata.found)
          cases ExpressionForm.group.inj (actualForm.symm.trans form)
          exact .group metadata form innerFound sourceType (ih childSyntax)
      | pair found actualForm first second =>
          cases Option.some.inj (found.symm.trans metadata.found)
          simp [form] at actualForm
  | pair metadata form leftFound rightFound sourceType first second firstSites secondSites firstIH secondIH =>
      cases syntaxTree with
      | literal found atomic =>
          cases Option.some.inj (found.symm.trans metadata.found)
          rw [form] at atomic
          cases atomic
      | group found actualForm child =>
          cases Option.some.inj (found.symm.trans metadata.found)
          simp [form] at actualForm
      | pair found actualForm leftSyntax rightSyntax =>
          cases Option.some.inj (found.symm.trans metadata.found)
          have ids := ExpressionForm.tuple.inj (actualForm.symm.trans form)
          cases (List.cons.inj ids).1
          cases (List.cons.inj (List.cons.inj ids).2).1
          exact .pair metadata form leftFound rightFound sourceType
            (firstIH leftSyntax) (secondIH rightSyntax)

/-- The selected numeric literal producer runs at the exact accepted leaf
action. It supplies both canonical membership and the stronger runtime leaf. -/
private theorem selected_literals {policy body context values source scope reasonAt} :
    CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt
      (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate context.solvedRequirements source id lowered) := by
  intro id node fuel lowered found atomic unitType special readPolicy leafPolicy accepted
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType
    special readPolicy leafPolicy accepted
  exact ⟨receipt.forget, receipt⟩

/-- One canonical static extraction constructs the finite runtime tree.
Only authentic syntax, raw typing and policy/compiler facts are inputs. -/
theorem Tree.of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (policyFor : CompatibleExpressionProducts.PolicyFor policy compilation readFuel values source scope reasonAt)
    (coercions : ∀ id node, CompatibleExpressionProducts.Syntax source id →
      source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Tree values.checked compilation.solvedRequirements source scope id lowered := by
  obtain ⟨tree, sites⟩ := CompatibleExpressionProducts.tree_of_functions_with_literals
    (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate compilation.solvedRequirements source id code)
    selected_literals unique declarations policyFor coercions syntaxTree.to_canonical found typed accepted
  exact Tree.of_literal_sites sites syntaxTree

variable {checked : SourceCoreCompatibleCatalog.Checked} {rawRegistry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)
  (faults : RecursiveStageMeaning.FaultRep)

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues
      (model := CompatibleAmbientHeap.payloadModel checked rawRegistry functions) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include sameLedger runtimeLedger unique wellFormed runtime covers in
/-- Finite structural recursion constructs all child preservation proofs.
Each actual Source child has its own strictly smaller Source grade. -/
theorem preserves (size : Nat) :
    PreservesAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (Tree checked solved invocation.source) faults size := by
  intro scope id lowered tree
  induction tree generalizing size with
  | literal receipt =>
      exact CallableIndexedOwnedPreparedStagedLiteralGroupBounds.literal_preserves
        functions bridge sameLedger runtimeLedger unique wellFormed runtime covers faults size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
      have children : PreservesBelow bridge context
          (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) registry invocation
          (Point scope inner lowered) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih childSize
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size children
        size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
      have children : PreservesBelow bridge context
          (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) registry invocation
          (Two scope left right first second) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, alternative⟩ := point
        cases alternative with
        | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize
        | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedPairBounds.pair_preserves bridge unique wellFormed
        runtime covers (product_values functions) size children size (Nat.le_refl _)
        (.actual metadata form leftFound rightFound sourceType
          ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

include sameLedger runtimeLedger unique wellFormed runtime covers in
/-- LiteralSites structural recursion permits group reflection at the SAME
native size. Only actual pair bind children use strict native descent. -/
theorem reflects (size : Nat) :
    ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (Tree checked solved invocation.source) faults size := by
  intro scope id lowered tree
  induction tree generalizing size with
  | literal receipt =>
      exact CallableIndexedOwnedPreparedStagedLiteralGroupBounds.literal_reflects
        functions bridge sameLedger runtimeLedger wellFormed runtime covers faults size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
      have children : ReflectsAt bridge context
          (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) registry invocation
          (Point scope inner lowered) faults size := by
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih size
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size children
        (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
      have children : ReflectsBelow bridge context
          (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) registry invocation
          (Two scope left right first second) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, alternative⟩ := point
        cases alternative with
        | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize
        | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedPairBounds.pair_reflects bridge unique wellFormed
        runtime covers (product_values functions) size children size (Nat.le_refl _)
        (.actual metadata form leftFound rightFound sourceType
          ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedProductTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds
/-! One accepted compiler extraction retains the actual finite literal/read/
group/pair tree and its selected literal sites. Structural recursion constructs
every staged child meaning internally, including ordinary local reads and lazy
mapping initialization at the actual reached state. Source and native grades
remain independent: transparent group reflection uses the same native grade,
while evaluated pair binds use their real strict child grades. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u
open CallableLambdaBodyReachability

/-- The original compiler tree and LiteralSites are paired at the same code,
Source context and read fuel. Only static receipts are retained. -/
abbrev Certificate (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate :=
  CompatibleExpressionProducts.Tree.WithLiterals (fuel := readFuel) (values := values)
    (source := source) (context := context) (solved := solved) (reasonAt := reasonAt)
    (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved source id lowered)

private theorem selected_literals {policy body context values source scope reasonAt} :
    CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt
      (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate context.solvedRequirements source id lowered) := by
  intro id node fuel lowered found atomic unitType special readPolicy leafPolicy accepted
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType
    special readPolicy leafPolicy accepted
  exact ⟨receipt.forget, receipt⟩

/-- The genuine accepted action extracts this exact supported tree once. Raw
Source typing and compiler policy facts are independent static inputs. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (policyFor : CompatibleExpressionProducts.PolicyFor policy compilation readFuel values source scope reasonAt)
    (coercions : ∀ id node, CompatibleExpressionProducts.Syntax source id →
      source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : CompatibleExpressionProducts.Syntax source id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Certificate readFuel values source context compilation.solvedRequirements reasonAt scope id lowered := by
  exact CompatibleExpressionProducts.tree_of_functions_with_literals
    (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate compilation.solvedRequirements source id code)
    selected_literals unique declarations policyFor coercions syntaxTree found typed accepted

/-- Accepted extraction needs compiler facts only along the admitted source paths. -/
theorem of_functions_on
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {allowed : ExpressionId → Prop}
    (policyFor : CompatibleExpressionProducts.PolicyOn policy compilation readFuel values source scope reasonAt allowed)
    (closed : ∀ {parent node child}, allowed parent →
      source.lookupExpression? parent = some node →
      (.expression child : NodeId) ∈ node.form.references → allowed child)
    (coercions : ∀ id node, allowed id → CompatibleExpressionProducts.Syntax source id →
      source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : CompatibleExpressionProducts.Syntax source id)
    (admitted : allowed id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Certificate readFuel values source context compilation.solvedRequirements reasonAt scope id lowered := by
  exact CompatibleExpressionProducts.tree_of_functions_with_literals_on
    (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate compilation.solvedRequirements source id code)
    selected_literals unique declarations policyFor closed coercions syntaxTree admitted found typed accepted

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  {semanticFaults : FunctionCalls.FaultRep}
  (faults : RecursiveStageMeaning.FaultRep)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  {faultRoot : ExpressionId}
  (uninitializedOn : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    Reaches invocation.source [.expression faultRoot] (.expression id) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "trees" => Certificate readFuel
  (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
  invocation.source context solved reasonAt

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues
      (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include extension sameLedger runtimeLedger uninitializedOn semantic unique wellFormed runtime covers in
/-- LiteralSites recursion proves each actual Source child internally. A read
uses its genuine local certificate; no read or whole-child meaning is supplied. -/
theorem preserves_reached (size : Nat) :
    PreservesAt bridge context valueModel registry invocation
      (fun scope id lowered => trees scope id lowered ∧
        Reaches invocation.source [.expression faultRoot] (.expression id)) faults size := by
  intro scope id lowered ⟨⟨tree, sites⟩, reached⟩
  revert reached
  induction sites generalizing size with
  | literal _ receipt =>
      intro _reached actualNode
      exact CallableIndexedOwnedPreparedStagedLiteralGroupBounds.literal_preserves
        functions bridge sameLedger runtimeLedger unique wellFormed runtime covers faults size receipt
  | read receipt =>
      intro reached actualNode
      exact CallableIndexedOwnedPreparedStagedReadBounds.preserves_local bridge functions extension
        semantic unique wellFormed runtime covers size ⟨receipt, uninitializedOn scope _ _ receipt reached⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
      intro reached
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : PreservesBelow bridge context valueModel registry invocation
          (Point scope inner lowered) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih childSize innerReached
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size children
        size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
      intro reached
      have leftReached : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have rightReached : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : PreservesBelow bridge context valueModel registry invocation
          (Two scope left right first second) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, alternative⟩ := point
        cases alternative with
        | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize leftReached
        | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize rightReached
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedPairBounds.pair_preserves bridge unique wellFormed
        runtime covers (product_values functions) size children size (Nat.le_refl _)
        (.actual metadata form leftFound rightFound sourceType
          ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

include extension sameLedger runtimeLedger uninitializedOn semantic unique wellFormed runtime covers in
/-- Reflection follows the same finite sites at independent native grades.
Grouping recurses at the same grade; actual pair binds supply strict children. -/
theorem reflects_reached (size : Nat) :
    ReflectsAt bridge context valueModel registry invocation
      (fun scope id lowered => trees scope id lowered ∧
        Reaches invocation.source [.expression faultRoot] (.expression id)) faults size := by
  intro scope id lowered ⟨⟨tree, sites⟩, reached⟩
  revert reached
  induction sites generalizing size with
  | literal _ receipt =>
      intro _reached actualNode
      exact CallableIndexedOwnedPreparedStagedLiteralGroupBounds.literal_reflects
        functions bridge sameLedger runtimeLedger wellFormed runtime covers faults size receipt
  | read receipt =>
      intro reached actualNode
      exact CallableIndexedOwnedPreparedStagedReadBounds.reflects_local bridge functions extension
        semantic unique wellFormed runtime covers size ⟨receipt, uninitializedOn scope _ _ receipt reached⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
      intro reached
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : ReflectsAt bridge context valueModel registry invocation
          (Point scope inner lowered) faults size := by
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih size innerReached
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size children
        (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
      intro reached
      have leftReached : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have rightReached : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : ReflectsBelow bridge context valueModel registry invocation
          (Two scope left right first second) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, alternative⟩ := point
        cases alternative with
        | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize leftReached
        | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize rightReached
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedPairBounds.pair_reflects bridge unique wellFormed
        runtime covers (product_values functions) size children size (Nat.le_refl _)
        (.actual metadata form leftFound rightFound sourceType
          ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

include extension sameLedger runtimeLedger uninitialized semantic unique wellFormed runtime covers in
/-- Global diagnostic facts restrict to each authentic expression root. -/
theorem preserves (size : Nat) :
    PreservesAt bridge context valueModel registry invocation trees faults size := by
  intro scope id lowered tree
  exact preserves_reached (faultRoot := id) bridge functions extension sameLedger runtimeLedger faults
    (fun current child code receipt _reached => uninitialized current child code receipt)
    semantic unique wellFormed runtime covers size ⟨tree, .root (by simp)⟩

include extension sameLedger runtimeLedger uninitialized semantic unique wellFormed runtime covers in
/-- Global diagnostic facts restrict to each authentic expression root. -/
theorem reflects (size : Nat) :
    ReflectsAt bridge context valueModel registry invocation trees faults size := by
  intro scope id lowered tree
  exact reflects_reached (faultRoot := id) bridge functions extension sameLedger runtimeLedger faults
    (fun current child code receipt _reached => uninitialized current child code receipt)
    semantic unique wellFormed runtime covers size ⟨tree, .root (by simp)⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodCertificates
/-! Selected operator methods retain the real evidence hook, complete method
record and ordered recursive children. Their physical slot is independent of
ordinary declaration headers. This receipt contains no execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodCertificates
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child Metadata)

structure Receipt (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (compilation : SourceCoreFunctions.Context)
    (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  program : CheckedProgram
  project : SourceCoreEvidence.Projector
  caller : SourceSpecialization.SpecializedFunction
  node : ExpressionNode
  metadata : Metadata values.checked source id node lowered.type
  operator : CallablePreparedMethodSelection.Operator program project caller compilation
    (Child policy body fuel compilation) (fuel + 1) source scope id reasonAt policy.callables node lowered
  special : (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation (Child policy body fuel compilation) (fuel + 1)
        source scope id reasonAt) = .ok (some lowered)
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
    compilation source scope id reasonAt = .ok lowered

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

theorem call_index_eq {first second : SourceCoreCalls.Signature} {firstIndex secondIndex : Nat}
    {firstArguments secondArguments : Expr} {firstReason secondReason : Word}
    (same : SourceCoreCalls.call first firstIndex firstArguments firstReason =
      SourceCoreCalls.call second secondIndex secondArguments secondReason) : firstIndex = secondIndex := by
  simp only [SourceCoreCalls.call, LanguageResult.bind, OptionalCell.read] at same
  have tail := (Expr.caseE.inj same).2.2
  have read := (Expr.caseE.inj tail).1
  have reference := (Expr.caseE.inj read).1
  exact Nat.add_right_cancel (Expr.var.inj (Expr.loadCell.inj reference))

namespace Receipt
variable (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)

abbrev method := receipt.operator.selection.method
abbrev arguments := receipt.operator.arguments
abbrev codes := receipt.operator.loweredArguments
abbrev signature := receipt.operator.native.signature
abbrev index := receipt.operator.native.index

theorem generated : receipt.arguments.mapM (fun child =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope child reasonAt) =
      .ok receipt.codes := by
  simpa only [arguments, codes, Child, Nat.min_eq_right (Nat.le_succ fuel)] using receipt.operator.argumentsAccepted

theorem operand : receipt.operator.operand = lowered := by
  have suffix := receipt.operator.suffix.accepted
  simpa only [receipt.metadata.coercions, SourceCoreEvidence.applyCoercions, pure, Except.pure,
    Except.ok.injEq] using suffix

theorem parameter : receipt.signature.parameterType = (SourceCoreCalls.packArguments receipt.codes).type :=
  receipt.operator.native.inputType

theorem result : receipt.signature.resultType = lowered.type := by
  exact (congrArg SourceCoreBasic.LoweredExpr.type
    (receipt.operand.symm.trans receipt.operator.native.emitted)).symm

theorem emitted : lowered.expression = SourceCoreCalls.call receipt.signature
    (scope.length + compilation.administrativePrefix + receipt.index)
    (SourceCoreCalls.packArguments receipt.codes).expression compilation.internalReason :=
  congrArg SourceCoreBasic.LoweredExpr.expression
    (receipt.operand.symm.trans receipt.operator.native.emitted)

theorem global : compilation.globals[receipt.index]? = some receipt.signature := by
  have member : (receipt.signature, receipt.index) ∈ compilation.globals.zipIdx.filter
      (fun row => decide (row.1.key = receipt.operator.key)) := by
    rw [receipt.operator.native.global]
    exact List.mem_singleton.mpr rfl
  exact List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp member).1

theorem key : receipt.signature.key = receipt.operator.key := by
  have member : (receipt.signature, receipt.index) ∈ compilation.globals.zipIdx.filter
      (fun row => decide (row.1.key = receipt.operator.key)) := by
    rw [receipt.operator.native.global]
    exact List.mem_singleton.mpr rfl
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp member).2

theorem record : SourceCompilationPlan.exactSpecialization compilation.plan receipt.signature.key =
    .ok receipt.operator.target.specialized := by
  rw [receipt.key]
  exact receipt.operator.target.selected

theorem argument_references {child : ExpressionId} (member : child ∈ receipt.arguments) :
    (.expression child : NodeId) ∈ receipt.node.form.references := by
  rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ |
    ⟨operator, left, right, form, arguments⟩
  · simp only [Receipt.arguments, arguments, List.mem_singleton] at member
    subst child
    simp [form, ExpressionForm.references]
  · simp only [Receipt.arguments, arguments, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [form, ExpressionForm.references]

theorem unary_arguments {operator : Syntax.UnaryOp} {operand : ExpressionId}
    (form : receipt.node.form = .unary operator operand) : receipt.arguments = [operand] := by
  rcases receipt.operator.form with ⟨actual, child, actualForm, arguments⟩ |
    ⟨actual, left, right, actualForm, _⟩
  · obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (form.symm.trans actualForm)
    exact arguments
  · simp [form] at actualForm

theorem binary_arguments {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (form : receipt.node.form = .binary left operator right) : receipt.arguments = [left, right] := by
  rcases receipt.operator.form with ⟨actual, child, actualForm, _⟩ |
    ⟨actual, first, second, actualForm, arguments⟩
  · simp [form] at actualForm
  · obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (form.symm.trans actualForm)
    exact arguments

theorem node_eq (other : Receipt policy body fuel compilation values source scope id reasonAt lowered) :
    receipt.node = other.node :=
  Option.some.inj (receipt.metadata.found.symm.trans other.metadata.found)

theorem arguments_eq (other : Receipt policy body fuel compilation values source scope id reasonAt lowered) :
    receipt.arguments = other.arguments := by
  rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
  · have otherForm := receipt.node_eq other ▸ form
    exact arguments.trans (other.unary_arguments otherForm).symm
  · have otherForm := receipt.node_eq other ▸ form
    exact arguments.trans (other.binary_arguments otherForm).symm

theorem codes_eq (other : Receipt policy body fuel compilation values source scope id reasonAt lowered) :
    receipt.codes = other.codes := by
  have generated := receipt.generated
  rw [receipt.arguments_eq other] at generated
  exact Except.ok.inj (generated.symm.trans other.generated)

theorem index_eq (other : Receipt policy body fuel compilation values source scope id reasonAt lowered) :
    receipt.index = other.index := by
  have same := call_index_eq (receipt.emitted.symm.trans other.emitted)
  omega

theorem signature_eq (other : Receipt policy body fuel compilation values source scope id reasonAt lowered) :
    receipt.signature = other.signature := by
  have first := receipt.global
  rw [receipt.index_eq other] at first
  exact Option.some.inj (first.symm.trans other.global)

theorem arguments_typed {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type) :
    ∃ types, ExpressionsHaveTypes source context receipt.arguments types := by
  generalize typeEq : receipt.node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.metadata.found)
    subst actualNode
    rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ |
      ⟨operator, left, right, form, arguments⟩
    · rw [form] at raw
      cases raw with
      | @unary _ _ _ operandType _ _ child _ =>
          refine ⟨[operandType], ?_⟩
          change ExpressionsHaveTypes source context receipt.operator.arguments _
          rw [arguments]
          exact .cons child (.nil context)
    · rw [form] at raw
      cases raw with
      | @binary _ _ _ _ operandType _ _ first second _ =>
          refine ⟨[operandType, operandType], ?_⟩
          change ExpressionsHaveTypes source context receipt.operator.arguments _
          rw [arguments]
          exact .cons first (.cons second (.nil context))

end Receipt

/-- The real special branch fixes the same recursive budget and parent output.
Method Source selection and body support are supplied at the authority layer. -/
theorem of_evidence {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {caller : SourceSpecialization.SpecializedFunction} {node : ExpressionNode}
    (coercions : node.coercions = [])
    (projected : values.checked.catalog.project node.type = .ok lowered.type)
    (operator : CallablePreparedMethodSelection.Operator program project caller compilation
      (Child policy body fuel compilation) (fuel + 1) source scope id reasonAt policy.callables node lowered)
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation (Child policy body fuel compilation) (fuel + 1)
          source scope id reasonAt) = .ok (some lowered))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt policy body fuel compilation values source scope id reasonAt lowered) := by
  have owner : id.occurrence.owner = source.owner := by
    apply Classical.byContradiction
    intro mismatch
    simp [SourceCoreFunctions.lowerExpressionWithPolicy, mismatch, bind, Except.bind] at accepted
  exact ⟨⟨program, project, caller, node, ⟨operator.found, owner, coercions, projected⟩, operator, special, accepted⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorSourceInversion
/-! Original constructor traces retain the ordered argument sequence, its exact
heap, and the wrapper grade. Staging and semantic faults stay distinct. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorSourceInversion
open Frontend SourceInference Staging.Recursive

variable {program : Program} {registry : Registry} {invocation : Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Outcome}
  {instantiation : DataConstructorInstantiation} {arguments : List ExpressionId}

private theorem occurrence_form {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Occurrence invocation id actualForm requirements) : actualForm = node.form := by
  obtain ⟨actualNode, contains, actualFormEq, _, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact actualFormEq.symm.trans (congrArg ExpressionNode.form same)

theorem children
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .constructor instantiation arguments)
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    (∃ sequenceSize values, size = Size.stepSize [sequenceSize] ∧
      outcome = .value (.constructed instantiation values) ∧
      Size.Expressions program registry sequenceSize invocation context environment before arguments (.values values) after) ∨
    (∃ sequenceSize failure, size = Size.stepSize [sequenceSize] ∧
      outcome = .fault failure ∧
      Size.Expressions program registry sequenceSize invocation context environment before arguments (.fault failure) after) := by
  have actual : ∀ {actualForm requirements}, Occurrence invocation id actualForm requirements → actualForm = .constructor instantiation arguments :=
    fun occurrence => (occurrence_form unique found occurrence).trans form
  cases trace with
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [same, form] at atomic
      cases atomic
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | constructorValue occurrence _valid children =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.constructor.inj (actual occurrence)
      exact .inl ⟨_, _, rfl, rfl, children⟩
  | constructorFault occurrence children =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.constructor.inj (actual occurrence)
      exact .inr ⟨_, _, rfl, rfl, children⟩
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | tupleValue occurrence _ _ | tupleFault occurrence _ | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _
  | unaryInvalid occurrence _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _
  | binaryInvalid occurrence _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _
  | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorHeadBounds
/-! Nominal construction uses the actual metadata header and ordered recursive
children. A reached child failure keeps its original scope and heap; successful
construction retains the same caller state and the exact constructor payload. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CompatibleExpressionConstructors (construct_rename construct_success construct_failure)
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private theorem valuesRep {values : SourceCoreCompatibleValues.Context} {receiving : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
      mapping world types natives sources payloads) :
    ValuesRep values.checked receiving functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "valuesContext" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked

include bridge functions extension faults unique wellFormed runtime covers in
theorem constructor_preserves {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId} {tag : ConstructorId}
    {header : Word} {codes : List SourceCoreBasic.LoweredExpr} {children : GenericExpressionMeaning.Certificate}
    (size : Nat) (childMeaning : PreservesBelow bridge context model registry invocation children faults size)
    (receipt : CompatibleExpressionConstructors.Header valuesContext invocation.source id node instantiation tag header codes)
    (form : node.form = .constructor instantiation ids)
    (admissible : SourceSemantics.DataConstructorInstantiation.Admissible context instantiation)
    (ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution)
    (_count : ids.length = instantiation.payloadTypes.length)
    (_nodes : CompatibleExpressionConstructors.Nodes invocation.source ids instantiation.payloadTypes codes)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids instantiation.payloadTypes codes) :
    PreservesAt bridge context model registry invocation
      (Point scope id ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩)
      faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  have valid := CompatibleSourceInstantiationClosure.constructor_valid admissible runtime.variables_closed ranges
  obtain ⟨_admissible, typing, _sourceType⟩ := CompatibleExpressionConstructors.constructor_source_types
    unique receipt.metadata.found form receipt.metadata.coercions typed
  rcases CallableIndexedOwnedPreparedStagedConstructorSourceInversion.children unique receipt.metadata.found form trace with
    ⟨sequenceSize, sources, sameSize, outcomeEq, sourceTrace⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · subst outcome
    have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, payloads, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_values bridge size sequence unique typing
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace within
    refine ⟨.inRight .word (.constructed tag (.pair (.word header) (packValues values))), finalStore, finalMap, finalWorld,
      ?_, ?_, finalHeaps, maps, worlds, frame, metadata, reached, related, ?_⟩
    · rw [construct_rename]
      exact construct_success tag header evaluated
    · rw [receipt.sourceType]
      exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registryOwner)
        receipt.selected (receipt.sourceType ▸ receipt.metadata.projected) receipt.registered (valuesRep (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) payloads))
    · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame
  · subst outcome
    have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_fault bridge size sequence unique typing
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace within
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ?_⟩
    · rw [construct_rename]
      exact construct_failure tag header evaluated
    · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame

include bridge functions extension faults unique wellFormed runtime covers in
theorem constructor_reflects {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId} {tag : ConstructorId}
    {header : Word} {codes : List SourceCoreBasic.LoweredExpr} {children : GenericExpressionMeaning.Certificate}
    (size : Nat) (childMeaning : ReflectsBelow bridge context model registry invocation children faults size)
    (receipt : CompatibleExpressionConstructors.Header valuesContext invocation.source id node instantiation tag header codes)
    (form : node.form = .constructor instantiation ids)
    (admissible : SourceSemantics.DataConstructorInstantiation.Admissible context instantiation)
    (ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution)
    (_count : ids.length = instantiation.payloadTypes.length)
    (_nodes : CompatibleExpressionConstructors.Nodes invocation.source ids instantiation.payloadTypes codes)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids instantiation.payloadTypes codes) :
    ReflectsAt bridge context model registry invocation
      (Point scope id ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩)
      faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  have valid := CompatibleSourceInstantiationClosure.constructor_valid admissible runtime.variables_closed ranges
  obtain ⟨_admissible, typing, _sourceType⟩ := CompatibleExpressionConstructors.constructor_source_types
    unique receipt.metadata.found form receipt.metadata.coercions typed
  rw [construct_rename] at completed
  obtain ⟨sequenceSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
  obtain ⟨sourceSize, sourceOutcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    CallableIndexedOwnedAdmittedStagedExpressionSequence.reflects bridge size sequence unique typing childMeaning
      environments heaps locals agrees actualTyped initial admitted childEvaluation smaller
  have occurrence : Staging.Recursive.Occurrence invocation child (.constructor instantiation ids) :=
    ⟨node, lookupExpression?_sound receipt.metadata.found, form, receipt.metadata.requirements, receipt.metadata.coercions⟩
  cases represented with
  | @values sources values payloads =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (construct_success tag header childEvaluation.sound)
      have trace := Staging.Recursive.Size.Expression.constructorValue occurrence valid sourceTrace
      refine ⟨_, _, after, finalMap, finalWorld, trace, ?_, finalHeaps,
        maps, worlds, frame, metadata, reached, related, ?_⟩
      · rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registryOwner)
          receipt.selected (receipt.sourceType ▸ receipt.metadata.projected) receipt.registered (valuesRep (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) payloads))
      · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (construct_failure tag header childEvaluation.sound)
      have trace := Staging.Recursive.Size.Expression.constructorFault occurrence sourceTrace
      exact ⟨_, _, after, finalMap, finalWorld, trace, .fault matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related,
        after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleHeadBounds
/-! Generic admitted tuple heads retain the actual ordered child certificate
vector. The original Source inversion, legacy binary pair rules and reached
state proofs supply the head semantics. Child hypotheses are theorem arguments;
static compiler receipts carry no execution law. Singleton reflection permits
the same native grade and constructs its independent Source grade. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private theorem occurrence_form {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    {node : ExpressionNode} {form : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (owned : Staging.Recursive.Occurrence invocation id form requirements) : node.form = form := by
  obtain ⟨other, contains, formed, _, _⟩ := owned
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact formed

/-- Outside the two-element legacy rules, the actual list grade is bounded
by the original Source parent. The empty atomic tuple is childless. -/
private theorem source_sequence {program : Program} {registry : Staging.Recursive.Registry}
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {checked : SourceCoreCompatibleCatalog.Checked} {id : ExpressionId} {node : ExpressionNode}
    {type : Core.Ty} {ids : List ExpressionId} {size : Nat}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (metadata : CompatibleExpressionPrimitives.Metadata checked invocation.source id node type)
    (form : node.form = .tuple ids) (unique : NodeOccurrencesUnique invocation.source)
    (notPair : ids.length ≠ 2)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context
      environment before id outcome after) :
    ∃ childSize sequence, childSize ≤ size ∧
      Staging.Recursive.Size.Expressions program registry childSize invocation context
        environment before ids sequence after ∧
      RecursiveStageTupleMeaning.PacksOutcome sequence outcome := by
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique metadata.found metadata.coercions contains))
  | atomicValue contains atomic uncoerced raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      subst node
      rw [form] at atomic raw
      cases atomic
      cases raw with
      | tuple _ children pack =>
          cases children
          cases pack
          exact ⟨_, _, Nat.le_refl _, .nil, .values .nil⟩
  | atomicFault contains atomic uncoerced raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      subst node
      rw [form] at atomic raw
      cases atomic
      cases raw with | tuple _ children => cases children
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | pair owned first second =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      simp at notPair
  | pairLeftFault owned child =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      simp at notPair
  | pairRightFault owned first failed =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      simp at notPair
  | tupleValue owned children pack =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      exact ⟨_, _, Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp)), children, .values pack⟩
  | tupleFault owned children =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      exact ⟨_, _, Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp)), children, .fault _⟩
  | indexBaseFault owned _ | indexKeyFault owned _ _ | indexResult owned _ _ _ | builtinArgumentsFault owned _ | builtinApplied owned _ _ | directArgumentsFault owned _ _ | directApplied owned _ _ _ _ _
  | constructorValue owned _ _ | constructorFault owned _
  | group owned _
  | unaryMethod owned _ _ _ _ _ _ _ _ _ | binaryMethod owned _ _ _ _ _ _ _ _ _ _ _
  | unary owned _ _ | unaryOperandFault owned _ | unaryInvalid owned _ _
  | binaryLeftFault owned _ | binaryLeftInvalid owned _ _
  | binaryShortCircuit owned _ _ | binaryRightFault owned _ _ _
  | binary owned _ _ _ _ | binaryInvalid owned _ _ _ _
  | conditional owned _ _ | conditionalFault owned _
  | calleeFault owned _ | notCallable owned _ _ | rejected owned _ _
  | argumentsFault owned _ _ _ | sourceArity owned _ _ _ _
  | applied owned _ _ _ _ _ _ =>
      have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
      cases impossible

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "valuesContext" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues (model := valueModel) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include unique wellFormed runtime covers in
private theorem nonpair_preserves {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {children : GenericExpressionMeaning.Certificate}
    (header : CompatibleExpressionTuples.Header valuesContext invocation.source id node ids types codes)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids types codes)
    (notPair : ids.length ≠ 2) (size : Nat)
    (childMeaning : PreservesBelow bridge context valueModel registry invocation children faults size) :
    PreservesAt bridge context valueModel registry invocation
      (Point scope id (SourceCoreCalls.packArguments codes)) faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨originalTypes, typing, _sourceType⟩ := CompatibleExpressionTuples.source_types
    unique header.metadata.found header.form header.metadata.coercions typed
  obtain ⟨childSize, sourceOutcome, within, childTrace, packed⟩ :=
    source_sequence header.metadata header.form unique notPair trace
  cases packed with
  | @values sources sourceValue sourcePack =>
      obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, relatedValues, finalHeaps,
          maps, worlds, frame, metadata, reached, related, _post⟩ :=
        CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_values bridge size sequence unique typing
          childMeaning environments heaps locals agrees actualTyped initial admitted childTrace within
      have represented : RecursiveStageArguments.ResultFor valueModel finalMap finalWorld types codes faults
          (.values sources) (.inRight .word (packValues values)) := .values relatedValues
      obtain ⟨result, packed, payload⟩ := RecursiveStageTupleMeaning.sequence_result represented
      have same := (RecursiveStageTupleMeaning.PacksOutcome.values sourcePack).functional packed
      cases same
      refine ⟨_, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame,
        metadata, reached, related, ?_⟩
      · simpa only [header.sourceType] using payload
      · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame
  | fault failure =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
          maps, worlds, frame, metadata, reached, related, _post⟩ :=
        CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_fault bridge size sequence unique typing
          childMeaning environments heaps locals agrees actualTyped initial admitted childTrace within
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related,
        after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame⟩

include unique wellFormed runtime covers in
/-- Ordered tuple preservation consumes only the actual strict Source child
hypothesis. The binary legacy rules use the genuine pair producer. -/
theorem tuple_preserves {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (childMeaning : PreservesBelow bridge context valueModel registry invocation children faults size) :
    PreservesAt bridge context valueModel registry invocation
      (CompatibleExpressionTuples.Certificate valuesContext invocation.source children) faults size := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, header, sequence⟩ := certified
  subst lowered
  cases sequence with
  | nil =>
      intro actualNode
      exact nonpair_preserves bridge functions faults unique wellFormed runtime covers
        header .nil (by simp) size childMeaning ⟨rfl, rfl, rfl⟩
  | single childFound generated =>
      intro actualNode
      exact nonpair_preserves bridge functions faults unique wellFormed runtime covers
        header (.single childFound generated) (by simp) size childMeaning ⟨rfl, rfl, rfl⟩
  | cons firstFound firstChild tail =>
      cases tail with
      | single secondFound secondChild =>
          intro actualNode
          exact CallableIndexedOwnedPreparedStagedPairBounds.pair_preserves bridge unique wellFormed
            runtime covers (product_values functions) size childMeaning size (Nat.le_refl _)
            (.actual header.metadata header.form firstFound secondFound header.sourceType firstChild secondChild)
      | cons nextFound nextChild rest =>
          intro actualNode
          exact nonpair_preserves bridge functions faults unique wellFormed runtime covers
            header (.cons firstFound firstChild (.cons nextFound nextChild rest)) (by simp) size
            childMeaning ⟨rfl, rfl, rfl⟩

include unique wellFormed runtime covers in
/-- Singleton reflection permits the same native child grade. Every branch
retains the exact recursive failure and actual reached caller state. -/
theorem tuple_reflects {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (childMeaning : ReflectsBelow bridge context valueModel registry invocation children faults (size + 1)) :
    ReflectsAt bridge context valueModel registry invocation
      (CompatibleExpressionTuples.Certificate valuesContext invocation.source children) faults size := by
  intro scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨node, ids, types, codes, emitted, header, sequence⟩ := certified
  subst lowered
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨originalTypes, typing, _sourceType⟩ := CompatibleExpressionTuples.source_types
    unique header.metadata.found header.form header.metadata.coercions typed
  obtain ⟨sourceSize, sourceOutcome, after, finalMap, finalWorld, childTrace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    CallableIndexedOwnedAdmittedStagedExpressionSequence.reflects bridge (size + 1) sequence unique typing
      childMeaning environments heaps locals agrees actualTyped initial admitted completed (Nat.lt_succ_self _)
  obtain ⟨outcome, packed, payload⟩ := RecursiveStageTupleMeaning.sequence_result represented
  have occurrence : Staging.Recursive.Occurrence invocation id (.tuple ids) :=
    ⟨actualNode, lookupExpression?_sound header.metadata.found, header.form,
      header.metadata.requirements, header.metadata.coercions⟩
  have trace : Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [sourceSize])
      invocation context environment before id outcome after := by
    cases packed with
    | values pack => exact .tupleValue occurrence childTrace pack
    | fault failure => exact .tupleFault occurrence childTrace
  refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds, frame,
    metadata, reached, related, ?_⟩
  · simpa only [header.sourceType] using payload
  · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorSourceBounds
/-! Original staged operator children retain independent grades, both fault
kinds, and the exact heap reached before a second operand or chosen branch. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorSourceBounds
open Core Frontend SourceInference GeneralHeap CompatiblePayload CoreProof
open CompatibleExpressionPrimitives
inductive UnaryTrace (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (operand : ExpressionId) (operator : Syntax.UnaryOp) :
    Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | value {childSize input output after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before operand (.value input) after)
      (applies : Dynamic.UnaryPrimitiveApplies operator input output)
      (childSizeSmaller : childSize < size) : UnaryTrace program size context registry invocation environment before operand operator (.value output) after
  | fault {childSize reason after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before operand (.fault reason) after)
      (childSizeSmaller : childSize < size) :
      UnaryTrace program size context registry invocation environment before operand operator (.fault reason) after
  | invalid {childSize input after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before operand (.value input) after)
      (invalid : Dynamic.UnaryPrimitiveOperandInvalid operator input)
      (childSizeSmaller : childSize < size) :
      UnaryTrace program size context registry invocation environment before operand operator
        (.fault (.semantic (.invalidUnaryOperand operator))) after


inductive BinaryTrace (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (left right : ExpressionId) (operator : Syntax.BinaryOp) :
    Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | leftFault {childSize reason after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before left (.fault reason) after)
      (childSizeSmaller : childSize < size) :
      BinaryTrace program size context registry invocation environment before left right operator (.fault reason) after
  | leftInvalid {childSize input after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before left (.value input) after)
      (invalid : Dynamic.BinaryLeftOperandInvalid operator input)
      (childSizeSmaller : childSize < size) :
      BinaryTrace program size context registry invocation environment before left right operator (.fault (.semantic (.invalidBinaryOperands operator))) after
  | short {childSize input output after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before left (.value input) after)
      (circuit : Dynamic.ShortCircuits operator input output)
      (childSizeSmaller : childSize < size) :
      BinaryTrace program size context registry invocation environment before left right operator (.value output) after
  | rightFault {firstSize secondSize input reason middle after}
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context environment before left (.value input) middle)
      (continues : Dynamic.EvaluatesRightOperand operator input)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context environment middle right (.fault reason) after)
      (firstSizeSmaller : firstSize < size)
      (secondSizeSmaller : secondSize < size) :
      BinaryTrace program size context registry invocation environment before left right operator (.fault reason) after
  | value {firstSize secondSize a b output middle after}
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context environment before left (.value a) middle)
      (continues : Dynamic.EvaluatesRightOperand operator a)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context environment middle right (.value b) after)
      (applies : Dynamic.BinaryPrimitiveApplies operator a b output)
      (firstSizeSmaller : firstSize < size)
      (secondSizeSmaller : secondSize < size) :
      BinaryTrace program size context registry invocation environment before left right operator (.value output) after
  | invalid {firstSize secondSize a b middle after}
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context environment before left (.value a) middle)
      (continues : Dynamic.EvaluatesRightOperand operator a)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context environment middle right (.value b) after)
      (invalid : Dynamic.BinaryPrimitiveOperandsInvalid operator a b)
      (firstSizeSmaller : firstSize < size) (secondSizeSmaller : secondSize < size) :
      BinaryTrace program size context registry invocation environment before left right operator
        (.fault (.semantic (.invalidBinaryOperands operator))) after


inductive ConditionalTrace (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition thenId elseId : ExpressionId) :
    Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | fault {childSize reason after}
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment before condition (.fault reason) after)
      (childSizeSmaller : childSize < size) :
      ConditionalTrace program size context registry invocation environment before condition thenId elseId (.fault reason) after
  | branch {childSize branchSize flag middle outcome after}
      (conditionTrace : Staging.Recursive.Size.Expression program registry childSize invocation context environment before condition (.value (.bool flag)) middle)
      (branchTrace : Staging.Recursive.Size.Expression program registry branchSize invocation context environment middle
        (if flag then thenId else elseId) outcome after)
      (childSizeSmaller : childSize < size)
      (branchSizeSmaller : branchSize < size) :
      ConditionalTrace program size context registry invocation environment before condition thenId elseId outcome after

variable {checked : SourceCoreCompatibleCatalog.Checked} {program : Program}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {id : ExpressionId} {node : ExpressionNode}
  {type : Ty} {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Staging.Recursive.Outcome}

private theorem occurrence_form {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Staging.Recursive.Occurrence invocation id actualForm requirements) : actualForm = node.form := by
  obtain ⟨actualNode, contains, actualFormEq, _, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact actualFormEq.symm.trans (congrArg ExpressionNode.form same)

private theorem occurrence_requirements {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Staging.Recursive.Occurrence invocation id actualForm requirements) : node.requirements = requirements := by
  obtain ⟨actualNode, contains, _, actualRequirements, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact (congrArg ExpressionNode.requirements same).symm.trans actualRequirements

theorem unary_inv {operator : Syntax.UnaryOp} {operand : ExpressionId}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .unary operator operand) (unique : NodeOccurrencesUnique invocation.source)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment before id outcome after) :
    UnaryTrace program size context registry invocation environment before operand operator outcome after := by
  have actual : ∀ {actualForm requirements}, Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .unary operator operand :=
    fun occurrence => (occurrence_form unique metadata.found occurrence).trans form
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique metadata.found metadata.coercions contains))
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      rw [same, form] at atomic
      cases atomic
  | unaryMethod occurrence _ selected _ _ _ _ _ _ _ =>
      have empty := (occurrence_requirements unique metadata.found occurrence).symm.trans metadata.requirements
      rw [empty] at selected
      cases selected
  | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _ => cases actual occurrence
  | unary occurrence child applied =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (actual occurrence)
      refine .value child applied ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | unaryOperandFault occurrence child =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (actual occurrence)
      refine .fault child ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | unaryInvalid occurrence child invalid =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (actual occurrence)
      refine .invalid child invalid ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _ | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _ | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _ | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

theorem binary_inv {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .binary left operator right) (unique : NodeOccurrencesUnique invocation.source)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment before id outcome after) :
    BinaryTrace program size context registry invocation environment before left right operator outcome after := by
  have actual : ∀ {actualForm requirements}, Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .binary left operator right :=
    fun occurrence => (occurrence_form unique metadata.found occurrence).trans form
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique metadata.found metadata.coercions contains))
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      rw [same, form] at atomic
      cases atomic
  | binaryMethod occurrence _ selected _ _ _ _ _ _ _ _ _ =>
      have empty := (occurrence_requirements unique metadata.found occurrence).symm.trans metadata.requirements
      rw [empty] at selected
      cases selected
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ => cases actual occurrence
  | binaryLeftFault occurrence child =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      refine .leftFault child ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | binaryLeftInvalid occurrence child invalid =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      refine .leftInvalid child invalid ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | binaryShortCircuit occurrence child circuit =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      refine .short child circuit ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | binaryRightFault occurrence first continues second =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      refine .rightFault first continues second ?_ ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | binary occurrence first continues second applied =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      refine .value first continues second applied ?_ ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | binaryInvalid occurrence first continues second invalid =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      refine .invalid first continues second invalid ?_ ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _ | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _ | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _ | conditional occurrence _ _ | conditionalFault occurrence _ | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

theorem conditional_inv {condition thenId elseId : ExpressionId}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .conditional condition thenId elseId) (unique : NodeOccurrencesUnique invocation.source)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment before id outcome after) :
    ConditionalTrace program size context registry invocation environment before condition thenId elseId outcome after := by
  have actual : ∀ {actualForm requirements}, Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .conditional condition thenId elseId :=
    fun occurrence => (occurrence_form unique metadata.found occurrence).trans form
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique metadata.found metadata.coercions contains))
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      rw [same, form] at atomic
      cases atomic
  | conditional occurrence first second =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.conditional.inj (actual occurrence)
      refine .branch first second ?_ ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | conditionalFault occurrence child =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.conditional.inj (actual occurrence)
      refine .fault child ?_ <;> exact Staging.Recursive.Size.child_lt_stepSize (by simp)
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _ | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _ | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _ | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _ | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _ | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorSourceBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorBounds
/-! Recursive staged operators consume their actual child caller witnesses.
Pure operator steps keep that state; the right operand or selected branch starts
at the first successful child's exact heap and admission. Both fault kinds pass
through unchanged. Static heads contain only compiler fields and children. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CompatibleExpressionPrimitives CompatibleExpressionConditionals
open ProtectedStateExpressionOperandTyping
universe u
inductive Head (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : Metadata checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : UnaryProfile operator operandType resultType core)
      (child : certificate scope operand ⟨core.operandType, childCode⟩) :
      Head checked source certificate scope id
        ⟨core.resultType, LocalPrimitiveResults.unary core childCode⟩
  | binary {id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      (metadata : Metadata checked source id node (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = operandType)
      (outputType : node.type = resultType)
      (profile : BinaryProfile operator operandType resultType mode)
      (first : certificate scope left ⟨mode.operandType operator, leftCode⟩)
      (second : certificate scope right ⟨mode.operandType operator, rightCode⟩) :
      Head checked source certificate scope id
        ⟨mode.resultType operator, mode.binary operator leftCode rightCode⟩

  | conditional {id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      (metadata : Metadata checked source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (thenFound : source.lookupExpression? thenId = some thenNode)
      (elseFound : source.lookupExpression? elseId = some elseNode)
      (conditionType : conditionNode.type = .bool)
      (thenType : thenNode.type = node.type) (elseType : elseNode.type = node.type)
      (conditionTree : certificate scope condition ⟨.bool, conditionCode⟩)
      (thenTree : certificate scope thenId ⟨type, thenCode⟩)
      (elseTree : certificate scope elseId ⟨type, elseCode⟩) :
      Head checked source certificate scope id
        ⟨type, LocalControl.choose type conditionCode thenCode elseCode⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

/-- Strict Source children preserve the exact staged result and owned state. -/
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique invocation.source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source) (covers : invocation.evidence.Covers context)
    (meaning : PreservesBelow bridge context model stages invocation certificate faults budget) :
    PreservesAt bridge context model stages invocation (Head compiled.compatible.checked invocation.source certificate) faults size := by
  intro scope id lowered tree root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    cases tree with
    | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have ih := fun n (bound : n < budget) => @meaning n bound _ _ _ child _ childFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change operand ∈ [operand]; simp) childFound)
      have sourceStep := CallableIndexedOwnedPreparedStagedOperatorSourceBounds.unary_inv metadata form unique trace
      cases sourceStep with
      | value childTrace applied childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          ih _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | value payload =>
          rw [inputType] at payload
          obtain ⟨sourceResult, result, actualApplied, coreApplied, resultRep⟩ := profile.preserves payload
          have same := actualApplied.functional applied
          subst sourceResult
          refine ⟨.inRight .word result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, ⟨reached, related⟩⟩
          · rw [unary_rename]; exact LocalPrimitiveResults.unary_success evaluated coreApplied
          · exact .value (outputType ▸ resultRep)
      | fault childTrace childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          ih _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [unary_rename]; exact LocalPrimitiveResults.unary_failure evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
      | invalid childTrace failed childSmaller =>
        obtain ⟨_, _, _, _, _, represented, _⟩ := ih _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | value payload =>
          rw [inputType] at payload
          obtain ⟨_, _, applied, _, _⟩ := profile.preserves payload
          exact False.elim (failed.excludes_application ⟨_, applied⟩)
    | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have leftIH := fun n (bound : n < budget) => @meaning n bound _ _ _ leftTree _ leftFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change left ∈ [left, right]; simp) leftFound)
      have rightIH := fun n (bound : n < budget) => @meaning n bound _ _ _ rightTree _ rightFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change right ∈ [left, right]; simp) rightFound)
      have sourceStep := CallableIndexedOwnedPreparedStagedOperatorSourceBounds.binary_inv metadata form unique trace
      cases sourceStep with
      | leftFault childTrace childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact mode.left_failure operator evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
      | leftInvalid childTrace invalid childSmaller =>
        obtain ⟨_, _, _, _, _, represented, _⟩ := leftIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | value payload =>
          rw [leftType] at payload
          exact False.elim (profile.left_valid payload invalid)
      | short childTrace circuit childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | value payload =>
          rw [leftType] at payload
          obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit evaluated
          exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, ⟨reached, related⟩⟩
      | rightFault firstTrace continues secondTrace firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
          rw [GenericExpressionMeaning.rename_prefix] at second
          cases represented with
          | fault matched =>
            exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact profile.right_failure payload continues first second,
              .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
      | value firstTrace continues secondTrace applied firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
          rw [GenericExpressionMeaning.rename_prefix] at second
          cases represented with
          | value rightPayload =>
            rw [rightType] at rightPayload
            have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
            obtain ⟨sourceResult, result, actualApplied, resultRep, combined⟩ := profile.right_success leftPayload rightPayload continues first second
            have same := actualApplied.functional applied
            subst sourceResult
            exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
              .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
      | invalid firstTrace continues secondTrace failed firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, _, _, _, second, represented, _, maps, worlds, _⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
          rw [GenericExpressionMeaning.rename_prefix] at second
          cases represented with
          | value rightPayload =>
            rw [rightType] at rightPayload
            have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
            obtain ⟨_, _, applied, _, _⟩ := profile.right_success leftPayload rightPayload continues first second
            exact False.elim (failed.excludes_application ⟨_, applied⟩)

    | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have conditionIH := fun n (bound : n < budget) => @meaning n bound _ _ _ conditionTree _ conditionFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change condition ∈ [condition, thenId, elseId]; simp) conditionFound)
      have thenIH := fun n (bound : n < budget) => @meaning n bound _ _ _ thenTree _ thenFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change thenId ∈ [condition, thenId, elseId]; simp) thenFound)
      have elseIH := fun n (bound : n < budget) => @meaning n bound _ _ _ elseTree _ elseFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change elseId ∈ [condition, thenId, elseId]; simp) elseFound)
      have sourceStep := CallableIndexedOwnedPreparedStagedOperatorSourceBounds.conditional_inv metadata form unique trace
      cases sourceStep with
      | fault childTrace childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          conditionIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [choose_rename]; exact LocalControl.choose_failure type evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
      | @branch conditionSize branchSize flag middle outcome after conditionTrace branchTrace conditionSmaller branchSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          conditionIH _ (Nat.lt_of_lt_of_le conditionSmaller bounded) environments heaps locals agrees actualTyped initial admitted conditionTrace
        cases represented with
        | value payload =>
          obtain ⟨actualFlag, sourceEq, coreEq⟩ := bool_fields payload
          cases sourceEq
          subst coreEq
          cases flag with
          | false =>
            obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
              elseIH _ (Nat.lt_of_lt_of_le branchSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
                (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 branchTrace
            rw [GenericExpressionMeaning.rename_prefix] at branch
            refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            · rw [choose_rename]; exact LocalControl.choose_false type first branch
            · simpa only [elseType] using represented
          | true =>
            obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
              thenIH _ (Nat.lt_of_lt_of_le branchSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
                (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 branchTrace
            rw [GenericExpressionMeaning.rename_prefix] at branch
            refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            · rw [choose_rename]; exact LocalControl.choose_true type first branch
            · simpa only [thenType] using represented

  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    CallableIndexedOwnedAdmittedStagedExpressionBounds.after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

/-- Completed native children produce their own staged grades and exact state. -/
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique invocation.source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source) (covers : invocation.evidence.Covers context)
    (meaning : ReflectsBelow bridge context model stages invocation certificate faults budget) :
    ReflectsAt bridge context model stages invocation (Head compiled.compatible.checked invocation.source certificate) faults size := by
  intro scope id lowered tree root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted evaluated
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    cases tree with
    | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have ih := fun n (bound : n < budget) => @meaning n bound _ _ _ child _ childFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change operand ∈ [operand]; simp) childFound)
      have occurrence : Staging.Recursive.Occurrence invocation id (.unary operator operand) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      rw [unary_rename] at evaluated
      have complete := evaluated.sound
      cases evaluated with
      | caseLeft childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          ih _ (by omega) environments heaps locals agrees actualTyped initial admitted childEvaluation
        cases represented with
        | fault matched =>
          have failed := trace
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_failure (operator := core) childEvaluation.sound) complete
          exact ⟨_, _, after, finalMap, finalWorld, .unaryOperandFault occurrence failed, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
      | caseRight childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          ih _ (by omega) environments heaps locals agrees actualTyped initial admitted childEvaluation
        cases represented with
        | value payload =>
          rw [inputType] at payload
          obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_success childEvaluation.sound coreApplied) complete
          have childTrace := trace
          exact ⟨_, _, after, finalMap, finalWorld, .unary occurrence childTrace applied,
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, ⟨reached, related⟩⟩
    | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have leftIH := fun n (bound : n < budget) => @meaning n bound _ _ _ leftTree _ leftFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change left ∈ [left, right]; simp) leftFound)
      have rightIH := fun n (bound : n < budget) => @meaning n bound _ _ _ rightTree _ rightFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change right ∈ [left, right]; simp) rightFound)
      have occurrence : Staging.Recursive.Occurrence invocation id (.binary left operator right) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      rw [Mode.binary_rename] at evaluated
      have complete := evaluated.sound
      rw [Mode.binary_eq] at evaluated
      cases evaluated with
      | caseLeft leftEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          leftIH _ (by omega) environments heaps locals agrees actualTyped initial admitted leftEvaluation
        cases represented with
        | fault matched =>
          have failed := trace
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (mode.left_failure operator leftEvaluation.sound)
          exact ⟨_, _, after, finalMap, finalWorld, .binaryLeftFault occurrence failed, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
      | caseRight leftEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (by omega) environments heaps locals agrees actualTyped initial admitted leftEvaluation
        cases represented with
        | @value sourceValue coreValue payload =>
          rw [leftType] at payload
          have firstTrace := trace
          rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
          · obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit leftEvaluation.sound
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            exact ⟨_, _, middle, middleMap, middleWorld, .binaryShortCircuit occurrence firstTrace circuit,
              .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, ⟨middleState, firstRelated⟩⟩
          · obtain ⟨rightSize, rightValue, rightStore, rightEvaluation, rightSmaller⟩ := RecursiveNamedExpressionSourceBounds.right_evaluated profile payload continues branch
            have shifted := rightEvaluation
            rw [← GenericExpressionMeaning.rename_prefix] at shifted
            obtain ⟨rightSourceSize, rightOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
              rightIH rightSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 shifted
            cases represented with
            | fault matched =>
              have failed := trace
              have combined := profile.right_failure payload continues leftEvaluation.sound rightEvaluation.sound
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              exact ⟨_, _, after, finalMap, finalWorld, .binaryRightFault occurrence firstTrace continues failed,
                .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            | value rightPayload =>
              rw [rightType] at rightPayload
              have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
              obtain ⟨sourceResult, result, applied, resultRep, combined⟩ :=
                profile.right_success leftPayload rightPayload continues leftEvaluation.sound rightEvaluation.sound
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              have secondTrace := trace
              exact ⟨_, _, after, finalMap, finalWorld, .binary occurrence firstTrace continues secondTrace applied,
                .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩

    | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have conditionIH := fun n (bound : n < budget) => @meaning n bound _ _ _ conditionTree _ conditionFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change condition ∈ [condition, thenId, elseId]; simp) conditionFound)
      have thenIH := fun n (bound : n < budget) => @meaning n bound _ _ _ thenTree _ thenFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change thenId ∈ [condition, thenId, elseId]; simp) thenFound)
      have elseIH := fun n (bound : n < budget) => @meaning n bound _ _ _ elseTree _ elseFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change elseId ∈ [condition, thenId, elseId]; simp) elseFound)
      have occurrence : Staging.Recursive.Occurrence invocation id (.conditional condition thenId elseId) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      rw [choose_rename] at evaluated
      have complete := evaluated.sound
      cases evaluated with
      | caseLeft childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
          conditionIH _ (by omega) environments heaps locals agrees actualTyped initial admitted childEvaluation
        cases represented with
        | fault matched =>
          have failed := trace
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalControl.choose_failure type childEvaluation.sound)
          exact ⟨_, _, after, finalMap, finalWorld, .conditionalFault occurrence failed, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, reached, related⟩
      | caseRight childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          conditionIH _ (by omega) environments heaps locals agrees actualTyped initial admitted childEvaluation
        cases represented with
        | value payload =>
          obtain ⟨flag, sourceEq, coreEq⟩ := bool_fields payload
          subst sourceEq
          subst coreEq
          have conditionTrace := trace
          obtain ⟨selectedSize, selected, selectedSmaller⟩ := RecursiveNamedExpressionSourceBounds.choose_branch_evaluated branch
          cases flag with
          | false =>
            change EvaluationSize selectedSize _ _ ((elseCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
              elseIH selectedSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 selected
            refine ⟨_, outcome, after, finalMap, finalWorld, .conditional occurrence conditionTrace branchTrace,
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            simpa only [elseType] using represented
          | true =>
            change EvaluationSize selectedSize _ _ ((thenCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, _post⟩ :=
              thenIH selectedSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 selected
            refine ⟨_, outcome, after, finalMap, finalWorld, .conditional occurrence conditionTrace branchTrace,
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related⟩⟩
            simpa only [thenType] using represented

  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    CallableIndexedOwnedAdmittedStagedExpressionBounds.after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodAuthority
/-! A method port retains the genuine selected method, its full dictionary and
its actual cached slot. Runtime capture authority and body meaning are separate
inputs at the reached call state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodAuthority
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)

/-- The actual source operator fixes its trait method names. -/
def Dispatch (traitName methodName : String) : Prop :=
  (∃ operator operand, receipt.node.form = .unary operator operand ∧
    UnaryTraitDispatch operator traitName methodName) ∨
  (∃ operator left right, receipt.node.form = .binary left operator right ∧
    BinaryTraitDispatch operator traitName methodName)

/-- Static formation and complete source typing of the actual selected method. -/
structure SelectionCore
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator) : Prop where
  formed : CallableCoercionMethodInstantiation.Formation
    selected.certificate.selected.implementation selected.certificate.selected.declaration
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (SourceSemantics.Context.ofSignatures receipt.program.signatures)
    receipt.method.specialized.parameterSubstitution
  covered : CallableCoercionEvidenceOrigins.CallerCovered receipt.caller receipt.method
  unique : NodeOccurrencesUnique
    (CallableCoercionMethodInstantiation.bodyInstance receipt.program receipt.method).source

structure SelectionSupport
    (selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator) : Prop where
  formed : CallableCoercionMethodInstantiation.Formation
    selected.certificate.selected.implementation selected.certificate.selected.declaration
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (SourceSemantics.Context.ofSignatures receipt.program.signatures)
    receipt.method.specialized.parameterSubstitution
  covered : CallableCoercionEvidenceOrigins.CallerCovered receipt.caller receipt.method
  unique : NodeOccurrencesUnique
    (CallableCoercionMethodInstantiation.bodyInstance receipt.program receipt.method).source
  empty : (CallableCoercionMethodInstantiation.bodyInstance receipt.program receipt.method).context.assumptions = []

theorem SelectionSupport.core {selected : CallablePreparedMethodRuntimeMeaning.OperatorSource receipt.operator}
    (support : SelectionSupport receipt selected) : SelectionCore receipt selected :=
  ⟨support.formed, support.range, support.covered, support.unique⟩

structure Port (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment)
    (stages : Staging.Recursive.Registry) where
  actual : Receipt policy body fuel compilation values source scope id reasonAt lowered
  program : actual.program = compiled.sourceProgram
  principal : CallableIndexedOwnedMethodPrincipal.Principal compiled actual.method
  signature : principal.named.signature = receipt.signature
  slot : principal.cached.index = receipt.index
  dispatch : Dispatch receipt principal.traitName principal.methodName
  selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
    context caller principal.traitName principal.methodName receipt.node.requirements
    principal.sourceBody principal.dictionary
  agrees : ∀ sourceBody dictionary,
    Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
      context caller principal.traitName principal.methodName receipt.node.requirements
      sourceBody dictionary → sourceBody = principal.sourceBody ∧ dictionary = principal.dictionary
  child : Staging.Recursive.Scope
  staged : stages.Closure principal.sourceFunction child
  diagnostics : ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
    compiled.indexed.base.diagnostics = some diagnostics ∧
    principal.cached.diagnostics = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}
  resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
    compiled.sourceProgram principal.named.specialized principal.dictionary
  sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
    (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodAuthority
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodIssuance
/-! Authentic method issuance ties the actual compiler hook to the selected
Source method, full dictionary, real cache slot and staged method scope. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodIssuance
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port SelectionSupport SelectionCore)
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableNamedMetadata (environment)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  (actual : Operator compiled.sourceProgram project caller compilation
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation) (fuel+1)
    source scope id reasonAt policy.callables receipt.node lowered)
  (special : (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation
        (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation)
        (fuel+1) source scope id reasonAt) = .ok (some lowered))

def authentic : Receipt policy body fuel compilation values source scope id reasonAt lowered :=
  ⟨compiled.sourceProgram, project, caller, receipt.node, receipt.metadata, actual, special, receipt.accepted⟩

private theorem exact_key {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) : row.key = key := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected <;> try contradiction
  rename_i actual found
  cases selected
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [found]
    simp
  exact of_decide_eq_true (List.mem_filter.mp member).2

private theorem cached_key {method : ExecutableImplMethods.CheckedMethod}
    (cached : Cached compiled method.specialized) : cached.named.signature.key = method.specialized.key := by
  have record := CallableIndexedActualNamedSourceReceipts.cached_record compiled cached.selected cached.compilation.hook
  exact (exact_key record).symm.trans (congrArg (fun row : SourceSpecialization.SpecializedFunction => row.key) cached.same)

private theorem descriptor {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method) :
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named principal.named.signature.key)) := by
  obtain ⟨origin, selected, _, _⟩ := principal.hook_history
  cases made : SourceCoreCallableContracts.descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named principal.named.signature.key) with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at made
    split at made
    · next absent => rw [selected] at absent; cases absent
    · cases made
  | ok descriptor => exact ⟨descriptor⟩

include receipt actual special in
private theorem of_actual_with_identity
    (selected : OperatorSource actual)
    (support : SelectionCore (authentic receipt actual special) selected)
    (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
      actual.selection.method.specialized (environment actual.dictionary))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (_catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (_unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (identity : ∀ actualBody actualDictionary,
      Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
        selected.traitName selected.methodName receipt.node.requirements actualBody actualDictionary →
      actualBody = CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method ∧
        actualDictionary = environment actual.dictionary)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Port (compiled := compiled) receipt context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  let authentic := authentic receipt actual special
  obtain ⟨_, _, _, _, _, target⟩ := actual.prepared prepared callerMember nodeMember
  obtain ⟨initial⟩ := actual.cached prepared callerMember nodeMember compiled samePlan
  obtain ⟨diagnostics, code, diagnosticPresent, codeFound, codeAccepted⟩ := NamedCalls.compiled_at compiled.indexed initial.selected
  obtain ⟨generation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed codeAccepted
  let cached : Cached compiled actual.selection.method.specialized :=
    ⟨initial.index, initial.named, _, code, initial.selected, initial.same, codeFound, generation⟩
  have chosen := selected.toSourceReceipt.selects checked support.formed support.range signatures ledger assumptions support.covered
  have requirements : actual.requirements = receipt.node.requirements := by
    have layout := CallableCallRequirementLayouts.ordinary_owned actual.ordinary
    simpa only [receipt.metadata.coercions, coercionRequirementIds, List.flatMap_nil, List.append_nil] using layout.symm
  have chosen : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      selected.traitName selected.methodName receipt.node.requirements
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method)
      (environment actual.dictionary) := by
    simpa only [dictionary, requirements] using chosen
  let principal := CallableIndexedOwnedMethodPrincipal.of_selected cached chosen
  have key : cached.named.signature.key = actual.key :=
    (cached_key cached).trans ((congrArg (fun row : SourceSpecialization.SpecializedFunction => row.key) target).symm.trans
      (exact_key actual.target.selected))
  have member : (cached.named.signature, cached.index) ∈ compilation.globals.zipIdx.filter
      (fun row => decide (row.1.key = actual.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr ?_, ?_⟩
    · rw [globals]
      exact CallableIndexedPreparedInventories.cached_global_at compiled cached.selected
    · simp only [key, decide_true]
  rw [actual.native.global] at member
  have aligned := Prod.mk.inj (List.mem_singleton.mp member)
  have signature : principal.named.signature = receipt.signature :=
    aligned.1.trans (authentic.signature_eq receipt)
  have slot : principal.cached.index = receipt.index := aligned.2.trans (authentic.index_eq receipt)
  obtain ⟨descriptor⟩ := descriptor principal
  obtain ⟨sidecar, _, _, staged⟩ := RecursiveMethodPreparedStageScopes.selected_of_descriptor actualStages principal descriptor
  obtain ⟨retained⟩ := selected.toSourceReceipt.retained checked
  obtain ⟨sourceAt⟩ := CallablePreparedMethodRuntimeProfileFactory.source_at (values := .initial compiled.compatible.checked) cached rfl retained wellFormed
    chosen support.unique (CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm
  refine ⟨⟨authentic, rfl, principal, signature, slot, ?_, chosen, ?_, _, staged, ⟨diagnostics, diagnosticPresent, rfl⟩, ?_, sourceAt⟩⟩
  · rcases actual.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
    · exact .inl ⟨operator, operand, form, by simpa only [principal, CallableIndexedOwnedMethodPrincipal.of_selected, form] using selected.dispatch⟩
    · exact .inr ⟨operator, left, right, form, by simpa only [principal, CallableIndexedOwnedMethodPrincipal.of_selected, form] using selected.dispatch⟩
  · exact identity
  · change CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
      cached.named.specialized (environment actual.dictionary)
    rw [cached.same]
    exact resolved

include receipt actual special in
theorem of_actual_with_evidence
    (selected : OperatorSource actual)
    (support : SelectionCore (authentic receipt actual special) selected)
    (coherent : RecursiveMethodDictionaryIdentity.Coherent compiled.sourceProgram.signatures.resolutionRules
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method).context.assumptions)
    (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
      actual.selection.method.specialized (environment actual.dictionary))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Port (compiled := compiled) receipt context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  have chosen := selected.toSourceReceipt.selects checked support.formed support.range signatures ledger assumptions support.covered
  have requirements : actual.requirements = receipt.node.requirements := by
    have layout := CallableCallRequirementLayouts.ordinary_owned actual.ordinary
    simpa only [receipt.metadata.coercions, coercionRequirementIds, List.flatMap_nil, List.append_nil] using layout.symm
  have chosen : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      selected.traitName selected.methodName receipt.node.requirements
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method)
      (environment actual.dictionary) := by
    simpa only [dictionary, requirements] using chosen
  apply of_actual_with_identity receipt actual special selected support resolved checked wellFormed catalog
    prepared callerMember nodeMember samePlan globals signatures ledger assumptions unique dictionary ?_ actualStages
  intro actualBody actualDictionary selectedActual
  have req : receipt.node.requirements = actual.selection.primaryRequirement :: selected.methodIds :=
    requirements.symm.trans selected.requirements
  rw [req] at chosen selectedActual
  have callerValid : callerEvidence.Valid compiled.sourceProgram.signatures.resolutionRules := by
    rw [dictionary]
    exact (CallableEvidenceEnvironment.resolved_valid actual.resolved).1
  exact RecursiveMethodDictionaryIdentity.same_coherent catalog
    (fun _ _ first second => unique.contains_unique first second) signatures callerValid chosen selectedActual coherent


include receipt actual special in
theorem of_actual_with_origins
    (selected : OperatorSource actual)
    (support : SelectionCore (authentic receipt actual special) selected)
    (coherent : RecursiveMethodOriginIdentity.Coherent (environment actual.available)
      ((selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence).map CallableNamedMetadata.evidence)
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method).context.assumptions)
    (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
      actual.selection.method.specialized (environment actual.dictionary))
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Port (compiled := compiled) receipt context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  have chosen := selected.toSourceReceipt.selects checked support.formed support.range signatures ledger assumptions support.covered
  have requirements : actual.requirements = receipt.node.requirements := by
    have layout := CallableCallRequirementLayouts.ordinary_owned actual.ordinary
    simpa only [receipt.metadata.coercions, coercionRequirementIds, List.flatMap_nil, List.append_nil] using layout.symm
  have chosen : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      selected.traitName selected.methodName receipt.node.requirements
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method)
      (environment actual.dictionary) := by
    simpa only [dictionary, requirements] using chosen
  apply of_actual_with_identity receipt actual special selected support resolved checked wellFormed catalog
    prepared callerMember nodeMember samePlan globals signatures ledger assumptions unique dictionary ?_ actualStages
  intro actualBody actualDictionary selectedActual
  have req : receipt.node.requirements = actual.selection.primaryRequirement :: selected.methodIds :=
    requirements.symm.trans selected.requirements
  rw [req] at chosen selectedActual
  have produced := CallableMethodOriginSource.roots_produced selected.toSourceReceipt signatures ledger assumptions
  have produced := (congrArg (fun ids => RecursiveMethodOriginIdentity.RootsProduced context
    (environment actual.available) ids
    ((selected.certificate.roots.primary :: selected.certificate.roots.methodEvidence).map CallableNamedMetadata.evidence))
    selected.requirements).mp produced
  rw [← dictionary] at produced coherent
  exact RecursiveMethodOriginIdentity.same_from_origins catalog unique produced chosen selectedActual coherent



include receipt actual special in
/-- Existing empty-method issuers construct the strengthened receipt internally. -/
theorem of_actual
    (selected : OperatorSource actual)
    (support : SelectionSupport (authentic receipt actual special) selected)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Port (compiled := compiled) receipt context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  have chosen := selected.toSourceReceipt.selects checked support.formed support.range signatures ledger assumptions support.covered
  have emptyDictionary := RecursiveMethodSelectionIdentity.dictionary_empty chosen support.empty
  have empty : actual.selection.method.specialized.assumptions = [] := support.empty
  have resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
      actual.selection.method.specialized (environment actual.dictionary) :=
    ⟨[], by rw [empty]; rfl, emptyDictionary⟩
  apply of_actual_with_evidence receipt actual special selected (support.core (authentic receipt actual special))
    (support.empty ▸ RecursiveMethodDictionaryIdentity.Coherent.empty _) resolved
    checked wellFormed catalog prepared callerMember nodeMember samePlan globals
    signatures ledger assumptions unique dictionary actualStages

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodIssuance
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedContextualProductReceipts
/-! The production contextual traversal supplies the actual finite read and
product tree, retaining each selected runtime literal certificate. Ordinary
Source metadata authenticates the policy bypass at every child. The static
receipt contains no expression execution law or reconstructed child code. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedContextualProductReceipts
open Core Frontend SourceInference
open CompatibleExpressionProducts

private theorem contextualSource_fragment
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    (ordinary : Ordinary source locals owner) (syntaxTree : Syntax source id) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  cases syntaxTree with
  | @literal _ literalNode found atomic =>
    generalize form : literalNode.form = shape at atomic
    cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
  | read found form =>
    have localBinder := ordinary.localBinder _ _ _ _ (.read found form) found form
    simp only [SourceCoreGeneralFunctions.contextualSource, found, form, localBinder, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
  | group found form child => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
  | pair found form first second => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem evidence_fragment (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (requirements : node.requirements = CompatibleExpressionLiterals.owned node.form) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (CompatibleExpressionLiterals.owned node.form) := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    change (if (CompatibleExpressionLiterals.owned node.form).length < 0 then none else
      if CompatibleExpressionLiterals.owned node.form = (CompatibleExpressionLiterals.owned node.form).take
          ((CompatibleExpressionLiterals.owned node.form).length - 0) ++ [] then
        some ((CompatibleExpressionLiterals.owned node.form).take ((CompatibleExpressionLiterals.owned node.form).length - 0)) else none) = _
    simp
  cases syntaxTree with
  | @literal _ literalNode originalFound atomic =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    generalize form : literalNode.form = shape at atomic
    cases atomic <;> simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
      CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
  | read originalFound form | group originalFound form _ | pair originalFound form _ _ =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
      CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

private theorem fragment_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : Syntax source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases syntaxTree <;> exact ⟨_, by assumption⟩

private theorem context_bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem selected_literals {policy body context values source scope reasonAt} :
    CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt
      (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate context.solvedRequirements source id lowered) := by
  intro id node fuel lowered found atomic unitType special readPolicy leafPolicy accepted
  have receipt := CompatibleExpressionLiteralRuntime.of_functions found atomic unitType
    special readPolicy leafPolicy accepted
  exact ⟨receipt.forget, receipt⟩

/-- Complete ordinary product trees are extracted from the production
contextual traversal, at root or full specialized parent context. -/
theorem of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context}
    (ordinary : Ordinary source locals context.owner)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Tree.WithLiterals (fuel := readFuel) (values := values) (source := source)
      (context := sourceContext) (solved := context.solvedRequirements) (reasonAt := reasonAt)
      (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate context.solvedRequirements source id code)
      scope id lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine tree_of_functions_with_literals
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate context.solvedRequirements source id code)
        selected_literals unique declarations ?_ ordinary.coercions syntaxTree found typed accepted
      refine ⟨?_, ?_, lowerPolicy, leafPolicy⟩
      · intro childId childTree child budget
        obtain ⟨childNode, childFound⟩ := fragment_has_node childTree
        dsimp only
        rw [contextualSource_fragment program context.plan locals context.owner (some prepared) ordinary childTree]
        simp only [childFound, ordinary.notInitializer _ childTree, Option.filter]
        rw [evidence_fragment program _ prepared.caller context child budget scope reasonAt _ childTree childFound
          (ordinary.requirements _ _ childTree childFound) (ordinary.coercions _ _ childTree childFound)]
        cases childForm : childNode.form <;> simp only [childForm]
        case reference name resolution =>
          cases resolution <;> simp only
          case «local» binder =>
            rw [ordinary.localBinder _ _ _ _ childTree childFound childForm]
            rfl
      · intro childId childTree
        change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner (some prepared) source childId
          representation.expressions.readExpression viewed childId) = _
        rw [contextualSource_fragment program context.plan locals context.owner (some prepared) ordinary childTree]
        simp only [bind, Except.bind, readPolicy]
    | none =>
      dsimp only at accepted
      obtain ⟨caller, selected, generated⟩ := context_bind_accepted accepted
      refine tree_of_functions_with_literals
        (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate context.solvedRequirements source id code)
        selected_literals unique declarations ?_ ordinary.coercions syntaxTree found typed generated
      refine ⟨?_, ?_, lowerPolicy, leafPolicy⟩
      · intro childId childTree child budget
        obtain ⟨childNode, childFound⟩ := fragment_has_node childTree
        dsimp only
        rw [contextualSource_fragment program context.plan locals context.owner none ordinary childTree]
        simp only [bind, Except.bind, pure, Except.pure, childFound, ordinary.notInitializer _ childTree, Option.filter]
        rw [evidence_fragment program _ caller context child budget scope reasonAt _ childTree childFound
          (ordinary.requirements _ _ childTree childFound) (ordinary.coercions _ _ childTree childFound)]
        cases childForm : childNode.form <;> simp only [childForm]
        case reference name resolution =>
          cases resolution <;> simp only
          case «local» binder =>
            rw [ordinary.localBinder _ _ _ _ childTree childFound childForm]
            rfl
      · intro childId childTree
        change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner none source childId
          representation.expressions.readExpression viewed childId) = _
        rw [contextualSource_fragment program context.plan locals context.owner none ordinary childTree]
        simp only [bind, Except.bind, readPolicy]


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedContextualProductReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleTreeBounds
/-! Finite admitted tuples retain the actual ordered compiler vector. Leaves
are the accepted read/literal/group/pair trees with their literal sites.
Structural recursion constructs every child meaning at the reached caller
state. Singleton reflection may keep the native grade. Preservation retains
the actual Source list grade and uses the original binary-pair port for its
legacy rules. This grammar permits nested tuples over the finite leaves;
a group around a newly arbitrary tuple requires a separate static extension. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

abbrev Certificate (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source : TypedSource) (context : SourceSemantics.Context)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :
    GenericExpressionMeaning.Certificate :=
  RecursiveStageTupleMeaning.CertificateFor values source
    (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate
      readFuel values source context solved reasonAt)

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private theorem occurrence_form {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    {node : ExpressionNode} {form : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (owned : Staging.Recursive.Occurrence invocation id form requirements) : node.form = form := by
  obtain ⟨other, contains, formed, _, _⟩ := owned
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact formed

/-- Outside the two-element legacy rules, the actual list grade is bounded
by the original Source parent. The empty atomic tuple is childless. -/
private theorem source_sequence {program : Program} {registry : Staging.Recursive.Registry}
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {checked : SourceCoreCompatibleCatalog.Checked} {id : ExpressionId} {node : ExpressionNode}
    {type : Core.Ty} {ids : List ExpressionId} {size : Nat}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (metadata : CompatibleExpressionPrimitives.Metadata checked invocation.source id node type)
    (form : node.form = .tuple ids) (unique : NodeOccurrencesUnique invocation.source)
    (notPair : ids.length ≠ 2)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context
      environment before id outcome after) :
    ∃ childSize sequence, childSize ≤ size ∧
      Staging.Recursive.Size.Expressions program registry childSize invocation context
        environment before ids sequence after ∧
      RecursiveStageTupleMeaning.PacksOutcome sequence outcome := by
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique metadata.found metadata.coercions contains))
  | atomicValue contains atomic uncoerced raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      subst node
      rw [form] at atomic raw
      cases atomic
      cases raw with
      | tuple _ children pack =>
          cases children
          cases pack
          exact ⟨_, _, Nat.le_refl _, .nil, .values .nil⟩
  | atomicFault contains atomic uncoerced raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      subst node
      rw [form] at atomic raw
      cases atomic
      cases raw with | tuple _ children => cases children
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | pair owned first second =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      simp at notPair
  | pairLeftFault owned child =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      simp at notPair
  | pairRightFault owned first failed =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      simp at notPair
  | tupleValue owned children pack =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      exact ⟨_, _, Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp)), children, .values pack⟩
  | tupleFault owned children =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      exact ⟨_, _, Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp)), children, .fault _⟩
  | indexBaseFault owned _ | indexKeyFault owned _ _ | indexResult owned _ _ _ | builtinArgumentsFault owned _ | builtinApplied owned _ _ | directArgumentsFault owned _ _ | directApplied owned _ _ _ _ _
  | constructorValue owned _ _ | constructorFault owned _
  | group owned _
  | unaryMethod owned _ _ _ _ _ _ _ _ _ | binaryMethod owned _ _ _ _ _ _ _ _ _ _ _
  | unary owned _ _ | unaryOperandFault owned _ | unaryInvalid owned _ _
  | binaryLeftFault owned _ | binaryLeftInvalid owned _ _
  | binaryShortCircuit owned _ _ | binaryRightFault owned _ _ _
  | binary owned _ _ _ _ | binaryInvalid owned _ _ _ _
  | conditional owned _ _ | conditionalFault owned _
  | calleeFault owned _ | notCallable owned _ _ | rejected owned _ _
  | argumentsFault owned _ _ _ | sourceArity owned _ _ _ _
  | applied owned _ _ _ _ _ _ =>
      have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
      cases impossible

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  {semanticFaults : FunctionCalls.FaultRep} (faults : RecursiveStageMeaning.FaultRep)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "valuesContext" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
local notation "trees" => Certificate readFuel valuesContext invocation.source context solved reasonAt

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues (model := valueModel) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include unique wellFormed runtime covers in
private theorem nonpair_preserves {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {children : GenericExpressionMeaning.Certificate}
    (header : CompatibleExpressionTuples.Header valuesContext invocation.source id node ids types codes)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids types codes)
    (notPair : ids.length ≠ 2) (size : Nat)
    (childMeaning : PreservesBelow bridge context valueModel registry invocation children faults size) :
    PreservesAt bridge context valueModel registry invocation
      (Point scope id (SourceCoreCalls.packArguments codes)) faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨originalTypes, typing, _sourceType⟩ := CompatibleExpressionTuples.source_types
    unique header.metadata.found header.form header.metadata.coercions typed
  obtain ⟨childSize, sourceOutcome, within, childTrace, packed⟩ :=
    source_sequence header.metadata header.form unique notPair trace
  cases packed with
  | @values sources sourceValue sourcePack =>
      obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, relatedValues, finalHeaps,
          maps, worlds, frame, metadata, reached, related, _post⟩ :=
        CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_values bridge size sequence unique typing
          childMeaning environments heaps locals agrees actualTyped initial admitted childTrace within
      have represented : RecursiveStageArguments.ResultFor valueModel finalMap finalWorld types codes faults
          (.values sources) (.inRight .word (packValues values)) := .values relatedValues
      obtain ⟨result, packed, payload⟩ := RecursiveStageTupleMeaning.sequence_result represented
      have same := (RecursiveStageTupleMeaning.PacksOutcome.values sourcePack).functional packed
      cases same
      refine ⟨_, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame,
        metadata, reached, related, ?_⟩
      · simpa only [header.sourceType] using payload
      · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame
  | fault failure =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
          maps, worlds, frame, metadata, reached, related, _post⟩ :=
        CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_fault bridge size sequence unique typing
          childMeaning environments heaps locals agrees actualTyped initial admitted childTrace within
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related,
        after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame⟩

include unique wellFormed runtime covers in
private theorem tuple_preserves {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (childMeaning : PreservesBelow bridge context valueModel registry invocation children faults size) :
    PreservesAt bridge context valueModel registry invocation
      (CompatibleExpressionTuples.Certificate valuesContext invocation.source children) faults size := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, header, sequence⟩ := certified
  subst lowered
  cases sequence with
  | nil =>
      intro actualNode
      exact nonpair_preserves bridge functions faults unique wellFormed runtime covers
        header .nil (by simp) size childMeaning ⟨rfl, rfl, rfl⟩
  | single childFound generated =>
      intro actualNode
      exact nonpair_preserves bridge functions faults unique wellFormed runtime covers
        header (.single childFound generated) (by simp) size childMeaning ⟨rfl, rfl, rfl⟩
  | cons firstFound firstChild tail =>
      cases tail with
      | single secondFound secondChild =>
          intro actualNode
          exact CallableIndexedOwnedPreparedStagedPairBounds.pair_preserves bridge unique wellFormed
            runtime covers (product_values functions) size childMeaning size (Nat.le_refl _)
            (.actual header.metadata header.form firstFound secondFound header.sourceType firstChild secondChild)
      | cons nextFound nextChild rest =>
          intro actualNode
          exact nonpair_preserves bridge functions faults unique wellFormed runtime covers
            header (.cons firstFound firstChild (.cons nextFound nextChild rest)) (by simp) size
            childMeaning ⟨rfl, rfl, rfl⟩

include unique wellFormed runtime covers in
private theorem tuple_reflects {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (childMeaning : ReflectsBelow bridge context valueModel registry invocation children faults (size + 1)) :
    ReflectsAt bridge context valueModel registry invocation
      (CompatibleExpressionTuples.Certificate valuesContext invocation.source children) faults size := by
  intro scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨node, ids, types, codes, emitted, header, sequence⟩ := certified
  subst lowered
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨originalTypes, typing, _sourceType⟩ := CompatibleExpressionTuples.source_types
    unique header.metadata.found header.form header.metadata.coercions typed
  obtain ⟨sourceSize, sourceOutcome, after, finalMap, finalWorld, childTrace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    CallableIndexedOwnedAdmittedStagedExpressionSequence.reflects bridge (size + 1) sequence unique typing
      childMeaning environments heaps locals agrees actualTyped initial admitted completed (Nat.lt_succ_self _)
  obtain ⟨outcome, packed, payload⟩ := RecursiveStageTupleMeaning.sequence_result represented
  have occurrence : Staging.Recursive.Occurrence invocation id (.tuple ids) :=
    ⟨actualNode, lookupExpression?_sound header.metadata.found, header.form,
      header.metadata.requirements, header.metadata.coercions⟩
  have trace : Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [sourceSize])
      invocation context environment before id outcome after := by
    cases packed with
    | values pack => exact .tupleValue occurrence childTrace pack
    | fault failure => exact .tupleFault occurrence childTrace
  refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds, frame,
    metadata, reached, related, ?_⟩
  · simpa only [header.sourceType] using payload
  · exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame

include extension sameLedger runtimeLedger uninitialized semantic unique wellFormed runtime covers in
/-- The positive finite tree supplies every child law by structural descent;
legacy pair rules retain their own actual strictly smaller Source children. -/
theorem preserves (size : Nat) :
    PreservesAt bridge context valueModel registry invocation trees faults size := by
  intro scope id lowered tree
  induction tree generalizing size with
  | leaf receipt =>
      exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.preserves bridge functions extension
        sameLedger runtimeLedger faults uninitialized semantic unique wellFormed runtime covers size receipt
  | @tuple tupleId tupleNode tupleIds tupleTypes tupleCodes entries header sequence children ih =>
      have meaning : PreservesBelow bridge context valueModel registry invocation
          (RecursiveStageTupleMeaning.Entries scope entries) faults size := by
        intro childSize _smaller current child code certified
        obtain ⟨rfl, member⟩ := certified
        exact ih child code member childSize
      intro actualNode
      exact tuple_preserves bridge functions faults unique wellFormed runtime covers size meaning
        ⟨_, _, _, _, rfl, header, sequence⟩

include extension sameLedger runtimeLedger uninitialized semantic unique wellFormed runtime covers in
/-- The singleton helper can have the same native grade as its child. The
actual static child tree, not a false numeric decrease, supplies that result. -/
theorem reflects (size : Nat) :
    ReflectsAt bridge context valueModel registry invocation trees faults size := by
  intro scope id lowered tree
  induction tree generalizing size with
  | leaf receipt =>
      exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.reflects bridge functions extension
        sameLedger runtimeLedger faults uninitialized semantic unique wellFormed runtime covers size receipt
  | @tuple tupleId tupleNode tupleIds tupleTypes tupleCodes entries header sequence children ih =>
      have meaning : ReflectsBelow bridge context valueModel registry invocation
          (RecursiveStageTupleMeaning.Entries scope entries) faults (size + 1) := by
        intro childSize _smaller current child code certified
        obtain ⟨rfl, member⟩ := certified
        exact ih child code member childSize
      intro actualNode
      exact tuple_reflects bridge functions faults unique wellFormed runtime covers size meaning
        ⟨_, _, _, _, rfl, header, sequence⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleTreeBounds
end

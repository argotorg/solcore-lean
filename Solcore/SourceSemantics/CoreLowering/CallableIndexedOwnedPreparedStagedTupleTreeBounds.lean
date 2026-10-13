import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.RecursiveStageTupleMeaning

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

import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLiteralGroupBounds

/-! Actual literal and group receipts preserve Source admission without
requiring the bodies of unrelated program declarations to be well typed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLiteralBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CompatibleExpressionLiterals CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLiteralGroupBounds (Tree)
universe u

private theorem literal_value_typed {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {value : Dynamic.Value}
    (raw : Dynamic.ExpressionFormEvaluates program context evidence source environment before
      node.form node.requirements node.coercions value after) :
    Dynamic.ValueHasType context after value node.type := by
  cases literal with
  | unit form type _ _ =>
      rw [form] at raw
      rw [type]
      cases raw with
      | tuple _ elements pack => cases elements; cases pack; exact .unit
  | bool value form type _ _ =>
      rw [form] at raw
      rw [type]
      cases raw
      exact .bool value
  | word value form type _ _ _ =>
      rw [form] at raw
      rw [type]
      cases raw with
      | literal _ constructs => exact constructs.hasType
  | resolvedWord form metadata | resolvedInteger form metadata =>
      rw [form] at raw
      cases raw with
      | integerLiteral _ constructs =>
          simpa only [metadata.nodeType, metadata.targetType] using constructs.hasType

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
  (faults : RecursiveStageMeaning.FaultRep)

private abbrev literalCertificate : GenericExpressionMeaning.Certificate :=
  fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved invocation.source id lowered

include sameLedger runtimeLedger unique in
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
  exact ⟨admitted.rows, by
    intro value same
    cases same
    exact ⟨literal_value_typed literal raw, admitted.heap⟩⟩

include sameLedger runtimeLedger in
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
  exact ⟨admitted.rows, by
    intro value same
    cases same
    exact ⟨literal_value_typed literal raw, admitted.heap⟩⟩

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

include sameLedger runtimeLedger unique in
/-- Finite structural descent closes every supported node. There is no
universal E law or literal execution supplied by the caller. -/
theorem preserves (size : Nat) :
    PreservesAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (Tree checked solved invocation.source) faults size := by
  intro scope id lowered tree
  induction tree generalizing size with
  | literal receipt =>
      exact literal_preserves functions bridge sameLedger runtimeLedger unique faults size receipt
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

include sameLedger runtimeLedger unique in
/-- Group reflection invokes only its finite child at the SAME native size.
The reconstructed Source grade grows through the independent group rule. -/
theorem reflects (size : Nat) :
    ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (Tree checked solved invocation.source) faults size := by
  intro scope id lowered tree
  induction tree with
  | literal receipt =>
      exact literal_reflects functions bridge sameLedger runtimeLedger faults size receipt
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

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLiteralBounds

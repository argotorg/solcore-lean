import Solcore.Test.SourceCoreChosenOrdinaryAcceptedArgumentAdmission
import Solcore.Test.SourceCoreChosenOrdinaryAcceptedStaticInventory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedTupleHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralRuntime

/-! The actual accepted parent supplies its ordered tuple and numeric child
receipts at the original remaining compiler budgets. The original admitted
sequence and tuple proofs consume those children at their actual caller state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreChosenOrdinaryAcceptedPairArgumentBounds
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreChosenOrdinaryAcceptedFixture CallableIndexedNamedGeneration
open CallableIndexedOwnedLiteralReturnSiteShells CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

variable (fixture : AcceptedFixture)

def parentScope : SourceCoreLocalCell.Scope :=
  (fixture.graph.binder.id, fixture.calls.payload) :: initialScope fixture.packet

/-- Only the two retained numeric argument occurrences belong to this family. -/
def Child : GenericExpressionMeaning.Certificate := fun _ id code =>
  (id = expressionId fixture.packet 7 ∨ id = expressionId fixture.packet 8) ∧
    CompatibleExpressionLiteralRuntime.Certificate
      (context fixture.packet.compiled.indexed fixture.packet.named).solvedRequirements
      (source fixture.packet.named) id code

variable {compilation : Compilation fixture.packet.compiled.indexed fixture.packet.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode}
  (root : LiteralRootReceipt (compiled := fixture.packet.compiled) fixture.packet.named
    (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics) fixture.packet.namedCode compilation
    498 (source fixture.packet.named) (initialScope fixture.packet) (expressionId fixture.packet 1)
    ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
    fixture.calls.initializer)

/-- The parent-selected tuple and both ordered children keep their actual
acceptance equations. Neither Source nor native execution is a field. -/
structure PairReceipt where
  left : SourceCoreBasic.LoweredExpr
  right : SourceCoreBasic.LoweredExpr
  tuple : SourceCoreBasic.LoweredExpr
  tupleAccepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
    497 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
    (parentScope fixture) (expressionId fixture.packet 6)
    ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) = .ok tuple
  leftAccepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
    496 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
    (parentScope fixture) (expressionId fixture.packet 7)
    ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) = .ok left
  rightAccepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
    496 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
    (parentScope fixture) (expressionId fixture.packet 8)
    ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) = .ok right
  packed : tuple = SourceCoreCalls.packArguments [left, right]
  metadata : CompatibleExpressionPrimitives.Metadata fixture.packet.compiled.compatible.checked
    (source fixture.packet.named) (expressionId fixture.packet 6) fixture.graph.argument tuple.type
  leftCertified : Child fixture (parentScope fixture) (expressionId fixture.packet 7) left
  rightCertified : Child fixture (parentScope fixture) (expressionId fixture.packet 8) right

private theorem empty_owned (node : ExpressionNode) (requirements : node.requirements = [])
    (coercions : node.coercions = []) : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  rw [requirements, coercions]
  rfl

include root in
/-- One actual parent acceptance exposes tuple497 and literal496. The original
indirect and tuple compiler receipts retain their original Source order. -/
theorem compiler_receipt
    (parentAccepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      498 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      (parentScope fixture) (expressionId fixture.packet 5)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) = .ok fixture.calls.parent) :
    Nonempty (PairReceipt fixture root) := by
  have parentPolicy := indirect_policy root.root (scope := parentScope fixture)
    (reasonAt := (effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key)
    fixture.graph.parentFound fixture.graph.parentForm fixture.graph.parentRequirements
    fixture.graph.parentCoercions rfl fixture.calls.parentOrdinary
  obtain ⟨parent⟩ := CallableIndirectCallCertificates.of_functions fixture.graph.parentFound fixture.graph.parentForm
    parentPolicy.special (parentPolicy.read.trans fixture.parentRows.parentRead) fixture.graph.parentForm parentAccepted
  cases tupleAction : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      497 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      (parentScope fixture) (expressionId fixture.packet 6)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) with
  | error error =>
      have accepted := parent.argumentsAccepted
      simp [tupleAction, List.mapM_cons, bind, Except.bind] at accepted
  | ok tuple =>
    have tuplePolicy := SourceCoreChosenOrdinaryAcceptedStaticInventory.ordinary_policy root.root
      (childScope := parentScope fixture) fixture.graph.argumentFound (.inr (.inl ⟨_, fixture.graph.argumentForm⟩))
      (empty_owned fixture.graph.argument fixture.parentRows.argumentRequirements fixture.parentRows.argumentCoercions)
      fixture.parentRows.argumentCoercions (.inl fixture.parentRows.argumentRequirements) fixture.parentRows.argumentOrdinary
    obtain ⟨codes, children, packed, metadata⟩ := CompatibleExpressionTuples.of_functions
      (values := .initial fixture.packet.compiled.compatible.checked) fixture.graph.argumentFound fixture.graph.argumentForm
      tuplePolicy.special tuplePolicy.read root.leaf tupleAction
    cases leftAction : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      496 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      (parentScope fixture) (expressionId fixture.packet 7)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) with
    | error error => simp [List.mapM_cons, leftAction, bind, Except.bind] at children
    | ok left =>
      cases rightAction : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
        496 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
        (parentScope fixture) (expressionId fixture.packet 8)
        ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) with
      | error error => simp [List.mapM_cons, leftAction, rightAction, bind, Except.bind] at children
      | ok right =>
        simp only [List.mapM_cons, List.mapM_nil, leftAction, rightAction, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at children
        subst codes
        have leftPolicy := SourceCoreChosenOrdinaryAcceptedStaticInventory.ordinary_policy root.root
          (childScope := parentScope fixture) fixture.parentRows.leftFound (.inr (.inr ⟨_, _, fixture.parentRows.leftForm⟩))
          fixture.parentRows.leftOwned fixture.parentRows.leftCoercions (.inr ⟨_, _, fixture.parentRows.leftForm⟩) fixture.parentRows.leftOrdinary
        have rightPolicy := SourceCoreChosenOrdinaryAcceptedStaticInventory.ordinary_policy root.root
          (childScope := parentScope fixture) fixture.parentRows.rightFound (.inr (.inr ⟨_, _, fixture.parentRows.rightForm⟩))
          fixture.parentRows.rightOwned fixture.parentRows.rightCoercions (.inr ⟨_, _, fixture.parentRows.rightForm⟩) fixture.parentRows.rightOrdinary
        have leftCertified := CompatibleExpressionLiteralRuntime.of_functions (values := .initial fixture.packet.compiled.compatible.checked)
          fixture.parentRows.leftFound (by rw [fixture.parentRows.leftForm]; exact .integer _ _)
          (by intro form; rw [fixture.parentRows.leftForm] at form; cases form)
          leftPolicy.special leftPolicy.read root.leaf leftAction
        have rightCertified := CompatibleExpressionLiteralRuntime.of_functions (values := .initial fixture.packet.compiled.compatible.checked)
          fixture.parentRows.rightFound (by rw [fixture.parentRows.rightForm]; exact .integer _ _)
          (by intro form; rw [fixture.parentRows.rightForm] at form; cases form)
          rightPolicy.special rightPolicy.read root.leaf rightAction
        exact ⟨⟨left, right, tuple, tupleAction, leftAction, rightAction, packed,
          packed.symm ▸ metadata, ⟨.inl rfl, leftCertified⟩, ⟨.inr rfl, rightCertified⟩⟩⟩

private theorem child_fields (metadata : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
    {id : ExpressionId} {node : ExpressionNode}
    (allowed : id = expressionId fixture.packet 7 ∨ id = expressionId fixture.packet 8)
    (found : (source fixture.packet.named).lookupExpression? id = some node) :
    node.type = .word ∧ node.coercions = [] := by
  rcases allowed with rfl | rfl
  · have same := Option.some.inj (found.symm.trans fixture.parentRows.leftFound)
    subst node
    exact ⟨metadata.leftType, fixture.parentRows.leftCoercions⟩
  · have same := Option.some.inj (found.symm.trans fixture.parentRows.rightFound)
    subst node
    exact ⟨metadata.rightType, fixture.parentRows.rightCoercions⟩

private theorem child_outcome {id : ExpressionId}
    (allowed : id = expressionId fixture.packet 7 ∨ id = expressionId fixture.packet 8)
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {value : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (first : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      environment before id (.value value) before)
    (second : Dynamic.ExpressionEvaluatesOutcome (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      environment before id outcome after) : outcome = .value value ∧ after = before := by
  rcases allowed with rfl | rfl
  · have raw := SourceCoreChosenOrdinaryAcceptedArgumentAdmission.left_outcome fixture first
    have actual := SourceCoreChosenOrdinaryAcceptedArgumentAdmission.left_outcome fixture second
    exact ⟨actual.1.trans raw.1.symm, actual.2⟩
  · have raw := SourceCoreChosenOrdinaryAcceptedArgumentAdmission.right_outcome fixture first
    have actual := SourceCoreChosenOrdinaryAcceptedArgumentAdmission.right_outcome fixture second
    exact ⟨actual.1.trans raw.1.symm, actual.2⟩

private theorem literal_word_type {solved : List SolvedRequirement} {node : ExpressionNode} {type : Ty} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) (wordType : node.type = .word) : type = .word := by
  cases literal with
  | unit _ typed _ _ | bool _ _ typed _ _ => cases typed.symm.trans wordType
  | word => rfl
  | resolvedWord => rfl
  | resolvedInteger _ metadata => cases metadata.nodeType.symm.trans wordType

private theorem word_typed {solved : List SolvedRequirement} {node : ExpressionNode} {code : Expr}
    (literal : CompatibleExpressionLiterals.Literal solved node .word code)
    {program : SourceSemantics.Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap} {value : Dynamic.Value}
    (raw : Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions value heap) : Dynamic.ValueHasType context heap value .word := by
  cases literal with
  | word _ form _ _ _ _ =>
    rw [form] at raw
    cases raw with | literal _ constructed => cases constructed; exact .word _
  | resolvedWord form metadata =>
    rw [form] at raw
    cases raw with | integerLiteral _ constructed =>
      cases constructed with
      | word => exact .word _
      | integer => cases metadata.targetType

section Admitted
universe u
variable {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.packet.compiled
      (Program.ofChecked fixture.packet.compiled.sourceProgram))}
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (functions : FunctionModel fixture.packet.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions fixture.packet.compiled.indexed))
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (metadata : SourceCoreChosenOrdinaryAcceptedOuterTyping.Metadata fixture)
    (evidence : Dynamic.EvidenceEnvironment)

include metadata in
/-- The real numeric row produces its original pure tuple and current Word
admission. No expression meaning or induction hypothesis is supplied. -/
theorem literal_preserves (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      (Child fixture) faults size := by
  intro scope id code certified node found _sourceTyped mapping world administrative environment canonical native
    actualContext before store ξ outcome after _environments heaps _locals _agrees _typed initial admitted trace
  obtain ⟨allowed, other, otherFound, literal, selected⟩ := certified
  have same := Option.some.inj (otherFound.symm.trans found)
  subst other
  have fields := child_fields fixture metadata allowed found
  have nativeWord := literal_word_type literal fields.1
  rw [nativeWord] at literal
  have numeric := selected.evidence (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
    rfl (numeric_runtime_ledger fixture.runtime.rows) evidence
  obtain ⟨sourceValue, coreValue, raw, related, evaluated⟩ := literal.evaluates_with_evidence (registry := registry)
    functions (Program.ofChecked fixture.packet.compiled.sourceProgram)
    (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence numeric
    _ environment before mapping world native store ξ
  have sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      environment before id sourceValue before := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found) raw
    rw [fields.2]
    exact .nil
  obtain ⟨sameOutcome, sameHeap⟩ := child_outcome fixture allowed (.value sourceTrace) trace.sound
  subst outcome
  subst after
  refine ⟨.inRight .word coreValue, store, mapping, world, evaluated,
    .value (by simpa only [CompatibleAmbientHeap.payloadModel, nativeWord] using related), heaps,
    .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, admitted.rows, ?_⟩
  intro value same
  cases same
  rw [fields.1]
  exact ⟨word_typed literal raw, admitted.heap⟩

include metadata in
/-- Native determinism aligns the same pure literal output. Its reconstructed
Source grade is independent of the actual native child size. -/
theorem literal_reflects (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      (Child fixture) faults size := by
  intro scope id code certified node found _sourceTyped mapping world administrative environment canonical native
    actualContext before store ξ value finalStore _environments heaps _locals _agrees _typed initial admitted completed
  obtain ⟨allowed, other, otherFound, literal, selected⟩ := certified
  have same := Option.some.inj (otherFound.symm.trans found)
  subst other
  have fields := child_fields fixture metadata allowed found
  have nativeWord := literal_word_type literal fields.1
  rw [nativeWord] at literal
  have numeric := selected.evidence (context := SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
    rfl (numeric_runtime_ledger fixture.runtime.rows) evidence
  obtain ⟨sourceValue, coreValue, raw, related, evaluated⟩ := literal.evaluates_with_evidence (registry := registry)
    functions (Program.ofChecked fixture.packet.compiled.sourceProgram)
    (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence numeric
    _ environment before mapping world native store ξ
  obtain ⟨sameValue, sameStore⟩ := evaluation_deterministic evaluated completed.sound
  subst value
  subst finalStore
  have sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.packet.compiled.sourceProgram)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      environment before id sourceValue before := by
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found) raw
    rw [fields.2]
    exact .nil
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size (.value sourceTrace)
  refine ⟨sourceSize, .value sourceValue, before, mapping, world, sized,
    .value (by simpa only [CompatibleAmbientHeap.payloadModel, nativeWord] using related), heaps,
    .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, admitted.rows, ?_⟩
  intro value same
  cases same
  rw [fields.1]
  exact ⟨word_typed literal raw, admitted.heap⟩

variable (receipt : PairReceipt fixture root)

def Tuple : GenericExpressionMeaning.Certificate := fun scope id code =>
  scope = parentScope fixture ∧ id = expressionId fixture.packet 6 ∧ code = receipt.tuple

include metadata in
/-- The original physical tuple owns the two actual Source Word rows. -/
theorem PairReceipt.header : CompatibleExpressionTuples.Header
    (.initial fixture.packet.compiled.compatible.checked) (source fixture.packet.named)
    (expressionId fixture.packet 6) fixture.graph.argument
    [expressionId fixture.packet 7, expressionId fixture.packet 8] [wordType, wordType] [receipt.left, receipt.right] := by
  refine ⟨?_, fixture.graph.argumentForm, ?_⟩
  · simpa only [receipt.packed, SourceCoreCompatibleValues.Context.initial] using receipt.metadata
  · exact metadata.argumentType

include metadata in
/-- The finite static tree uses each retained child certificate once. -/
theorem PairReceipt.tree : DataExpressionSequence.Tree (source fixture.packet.named) (Child fixture)
    (parentScope fixture) [expressionId fixture.packet 7, expressionId fixture.packet 8]
    [wordType, wordType] [receipt.left, receipt.right] := by
  have tree := DataExpressionSequence.Tree.cons fixture.parentRows.leftFound receipt.leftCertified
    (DataExpressionSequence.Tree.single fixture.parentRows.rightFound receipt.rightCertified)
  simpa only [metadata.leftType, metadata.rightType] using tree

include metadata in
private theorem children_typed : ExpressionsHaveTypes (source fixture.packet.named)
    (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
    [expressionId fixture.packet 7, expressionId fixture.packet 8] [wordType, wordType] :=
  .cons (SourceCoreChosenOrdinaryAcceptedOuterTyping.left_typed metadata)
    (.cons (SourceCoreChosenOrdinaryAcceptedOuterTyping.right_typed metadata) (.nil _))

include metadata in
/-- Ordered argument meaning uses the original sequence producer once and
then the original tuple core once. Actual reached rows supply the whole post. -/
theorem preserves (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      (Tuple fixture root receipt) faults size := by
  intro scope id code certified node found _sourceTyped mapping world administrative environment canonical native
    actualContext before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := certified
  have same := Option.some.inj (found.symm.trans fixture.graph.argumentFound)
  subst node
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, transition⟩ :=
    RecursiveNamedTupleHeadBounds.Stateful.preserves_bounded_with_sequence functions
      (Program.ofChecked fixture.packet.compiled.sourceProgram) evidence callerProtocol size size (Nat.le_refl _)
      fixture.runtime.source_runtime.graph.nodeOccurrencesUnique (PairReceipt.header fixture root metadata receipt)
      initial (CallableIndexedOwnedAdmittedSequenceProducer.preserves bridge initial admitted
        (PairReceipt.tree fixture root metadata receipt)
        fixture.runtime.source_runtime.graph.nodeOccurrencesUnique (children_typed fixture metadata)
        environments heaps locals agrees typed (size + 1)
        (fun child _ => literal_preserves fixture bridge functions metadata evidence child)) trace
  obtain ⟨reached, related⟩ := transition
  refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
    reached, related, ?_⟩
  · simpa only [receipt.packed] using evaluated
  · simpa only [receipt.packed, SourceCoreCompatibleValues.Context.initial] using represented
  · simpa only [metadata.argumentType] using
      SourceCoreChosenOrdinaryAcceptedArgumentAdmission.post_admission fixture bridge initial reached admitted trace.sound frame

include metadata in
/-- Reflection reuses the original native tuple decomposition and constructs
its independent Source size and genuine admission at the same returned state. -/
theorem reflects (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
      (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
      (Tuple fixture root receipt) faults size := by
  intro scope id code certified node found _sourceTyped mapping world administrative environment canonical native
    actualContext before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := certified
  have same := Option.some.inj (found.symm.trans fixture.graph.argumentFound)
  subst node
  have packedCompleted : EvaluationSize size native store
      ((SourceCoreCalls.packArguments [receipt.left, receipt.right]).expression.rename ξ) value finalStore := by
    simpa only [receipt.packed] using completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata, transition⟩ :=
    RecursiveNamedTupleHeadBounds.Stateful.reflects_bounded_with_sequence functions
      (Program.ofChecked fixture.packet.compiled.sourceProgram) evidence callerProtocol size size (Nat.le_refl _)
      (PairReceipt.header fixture root metadata receipt)
      initial (CallableIndexedOwnedAdmittedSequenceProducer.reflects bridge initial admitted
        (PairReceipt.tree fixture root metadata receipt)
        fixture.runtime.source_runtime.graph.nodeOccurrencesUnique (children_typed fixture metadata)
        environments heaps locals agrees typed (size + 1)
        (fun child _ => literal_reflects fixture bridge functions metadata evidence child)) packedCompleted
  obtain ⟨reached, related⟩ := transition
  refine ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
    reached, related, ?_⟩
  · simpa only [receipt.packed, SourceCoreCompatibleValues.Context.initial] using represented
  · simpa only [metadata.argumentType] using
      SourceCoreChosenOrdinaryAcceptedArgumentAdmission.post_admission fixture bridge initial reached admitted trace.sound frame

include metadata in
/-- Successful pair admission transports the same reached Source heap back to
its real closure context through the authentic outer binder extension. -/
theorem before_typed {index : ProtectedStateTransition.Index}
    (reached : callerProtocol.State index) {value : Dynamic.Value}
    (post : PostAdmission bridge (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture)
      parameterType (.value value) reached) :
    Dynamic.HeapWellTyped (runtimeContext fixture.packet) index.heap := by
  exact (Dynamic.HeapWellTyped.iff_of_binderExtends metadata.extended).mpr post.at_value.2.heap

include metadata in
/-- The concrete endpoint derives the parent-selected static receipt internally
once. Both admitted meanings use that same tuple and original child family. -/
theorem at_parent
    (parentAccepted : SourceCoreFunctions.lowerExpressionWithPolicy root.root.selected.policy root.root.selected.lowerBody
      498 (context fixture.packet.compiled.indexed fixture.packet.named) (source fixture.packet.named)
      (parentScope fixture) (expressionId fixture.packet 5)
      ((effectiveDiagnostics fixture.packet.compiled fixture.packet.diagnostics).reasonAt fixture.packet.named.signature.key) = .ok fixture.calls.parent) :
    ∃ selected : PairReceipt fixture root,
      (∀ size, CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
        (Tuple fixture root selected) faults size) ∧
      (∀ size, CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel fixture.packet.compiled.compatible.checked registry functions)
        (SourceCoreChosenOrdinaryAcceptedOuterTyping.localContext fixture) evidence (source fixture.packet.named)
        (Tuple fixture root selected) faults size) := by
  obtain ⟨selected⟩ := compiler_receipt fixture root parentAccepted
  exact ⟨selected, fun size => preserves fixture root bridge functions metadata evidence selected size,
    fun size => reflects fixture root bridge functions metadata evidence selected size⟩

end Admitted
end Tests.SourceCoreChosenOrdinaryAcceptedPairArgumentBounds

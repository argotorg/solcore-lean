import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedBareAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperative
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionPrimitives
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionGeneralBuiltins
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceBitNot
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StagedProjectedBitNot
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.RenamedPlaces
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalWhile
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedCallExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BareAssignments

/-!
# Compatible profile: bit-not statements and calls

Bit-not statements in bare and projected form, and call expression trees.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementHead
/-! A bare unary assignment has no source RHS or key child. Its head retains
only actual place layout, lexical lookup, numeric source profile and token. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

structure Head (context : SourceSemantics.Context) (scope : Scope) (assignment : AssignmentResolution) where
  prepared : Prepared
  index : Nat
  invalid : Word
  bare : assignment.target.projections = []
  layout : CompatibleBareBitNotCertificates.Layout prepared
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType)
  writable : WritableLocal context assignment.target.root prepared.route.rootSourceType
  profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
    SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer

namespace Head
variable {context : SourceSemantics.Context} {scope : Scope} {assignment : AssignmentResolution}

def emit (head : Head context scope assignment) (next : Expr) (output : Ty) : Expr :=
  execute head.prepared (.var head.index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
    next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid

def writtenContext (head : Head context scope assignment) (actual : Core.Context) : Core.Context :=
  CompatibleRenamedBareBitNot.writtenContext head.prepared actual

def Errors (head : Head context scope assignment) (faults : FunctionCalls.FaultRep) : Prop :=
  faults (.invalidUnaryOperand .bitNot) head.invalid

theorem of_lower_with_token {values : ValuesContext} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {expression : ExpressionLowerer} {fuel : Nat} {next code : Expr} {output : Ty}
    {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (bare : assignment.target.projections = [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment .equal none
      output next reasonAt invalid invalidOperand missing = .ok code) :
    ∃ head : Head context scope assignment, code = head.emit next output ∧ head.invalid = invalidOperand := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  exact ⟨⟨prepared, index, invalidOperand, bare, layout, slot, rootEq ▸ writable binder binding,
    view ▸ profile⟩, lowering, rfl⟩

theorem of_lower {values : ValuesContext} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {expression : ExpressionLowerer} {fuel : Nat} {next code : Expr} {output : Ty}
    {reasonAt : ExpressionId → Word} {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (bare : assignment.target.projections = [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment .equal none
      output next reasonAt invalid invalidOperand missing = .ok code) :
    ∃ head : Head context scope assignment, code = head.emit next output := by
  obtain ⟨head, emitted, _⟩ := of_lower_with_token writable bare profile accepted
  exact ⟨head, emitted⟩
end Head
end Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementCertificates
/-! Authentication of the production absent-RHS callback. The original
binary policy is deliberately separate so existing extraction APIs are unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces

abbrev Policy (policy : SourceCoreLoops.Policy) (values : ValuesContext)
    (invalidProjection invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word) : Prop :=
  policy.assignBitNotWithExpression = some (fun expression fuel source scope site assignment output next reasonAt =>
    lower values values.checked.signatures expression fuel source scope site assignment .equal none output next reasonAt
      (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root)
      (missingDefault site assignment.target.root))
end Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTupleCertificates
/-! Static receipts for the actual ordered tuple packer. The independent source
judgment supplies raw element types. Compiler receipts retain exact child code,
including duplicate occurrences. Source and native sizes remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTuples
open Core Frontend SourceInference GeneralHeap CompatiblePayload CoreProof
open RecursiveNamedCallBounds CompatibleExpressionPrimitives RecursiveNamedExpressionSourceBounds

structure Header (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (id : ExpressionId) (node : ExpressionNode) (ids : List ExpressionId)
    (types : List TypeSystem.Ty) (codes : List SourceCoreBasic.LoweredExpr) : Prop where
  metadata : Metadata values.checked source id node (SourceCoreCalls.packArguments codes).type
  form : node.form = .tuple ids
  sourceType : node.type = TypeSystem.Ty.productMany types

/-- Source types are recovered from the retained source proof, separately from
native projections and the type check in the compiler. -/
theorem source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {ids : List ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .tuple ids) (empty : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ types, ExpressionsHaveTypes source context ids types ∧ node.type = TypeSystem.Ty.productMany types := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := Option.some.inj (found.symm.trans (lookupExpression?_complete unique contains))
    subst actualNode
    have path := requirements.outputPath
    rw [empty] at path
    cases path
    rw [form] at raw
    generalize rawTypeEq : node.type = rawType at raw
    cases raw with
    | tuple elements => exact ⟨_, elements, rfl⟩

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

private theorem evaluation_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder)) (empty : node.coercions = [])
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
    exact False.elim (notLocal _ _ form)

private theorem fault_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder)) (empty : node.coercions = [])
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
    exact False.elim (notLocal _ _ form)

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome}

theorem source_inv (metadata : Metadata checked source id node type) {ids : List ExpressionId}
    (form : node.form = .tuple ids) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ∃ sequence, DataExpressionSequence.Trace program context evidence source environment before ids sequence after ∧
      CompatibleExpressionProducts.PacksOutcome sequence outcome := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form] at raw
    cases raw with | tuple _ children pack => exact ⟨_, .values children, .values pack⟩
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form] at raw
    cases raw with | tuple _ children => exact ⟨_, .fault children, .fault _⟩

theorem source_intro (metadata : Metadata checked source id node type) {ids : List ExpressionId}
    (form : node.form = .tuple ids) {sequence : DataExpressionSequence.Outcome}
    (trace : DataExpressionSequence.Trace program context evidence source environment before ids sequence after)
    (packed : CompatibleExpressionProducts.PacksOutcome sequence outcome) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases packed with
  | values pack =>
    cases trace with
    | values evaluated =>
      apply Dynamic.ExpressionEvaluatesOutcome.value
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
      · rw [form, metadata.requirements, metadata.coercions]; exact .tuple rfl evaluated pack
      · rw [metadata.coercions]; exact .nil
  | fault reason =>
    cases trace with
    | fault failed =>
      apply Dynamic.ExpressionEvaluatesOutcome.fault
      apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
      rw [form, metadata.requirements, metadata.coercions]
      exact .tuple rfl failed


private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensure_type {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

private theorem leaf_receipt {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreBasic.Scope} {id : ExpressionId}
    {node : ExpressionNode} {type : Ty} {ids : List ExpressionId} {fuel : Nat}
    {reasonAt : ExpressionId → Word} {child : SourceCoreFunctions.ExpressionLowerer}
    {lowered : SourceCoreBasic.LoweredExpr}
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, type))
    (form : node.form = .tuple ids)
    (accepted : SourceCoreCompatibleDataExpressions.leafLowerer values child fuel source scope id reasonAt = .ok lowered) :
    ∃ codes, ids.mapM (fun element => child fuel source scope element reasonAt) = .ok codes ∧
      lowered = SourceCoreCalls.packArguments codes ∧
      Metadata values.checked source id node (SourceCoreCalls.packArguments codes).type := by
  unfold SourceCoreCompatibleDataExpressions.leafLowerer at accepted
  simp only [read, form, bind, Except.bind, pure, Except.pure] at accepted
  obtain ⟨codes, children, accepted⟩ := bind_ok accepted
  obtain ⟨output, checked, accepted⟩ := bind_ok accepted
  cases output
  have same := ensure_type checked
  subst type
  cases accepted
  exact ⟨codes, children, rfl, CompatibleExpressionReads.metadata_of_read read⟩

/-- Every tuple arity uses the actual production mapM, including the separate
binary branch. The returned vector is source ordered and keeps repeated IDs. -/
theorem of_functions {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreBasic.Scope} {id : ExpressionId} {node : ExpressionNode}
    {ids : List ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .tuple ids)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id reasonAt = .ok lowered) :
    ∃ codes, ids.mapM (fun element => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope element reasonAt) = .ok codes ∧
      lowered = SourceCoreCalls.packArguments codes ∧
      Metadata values.checked source id node (SourceCoreCalls.packArguments codes).type := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error => simp [readPolicy, read, form] at accepted
      | ok pair =>
        obtain ⟨other, type⟩ := pair
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        simp only [readPolicy, read, form] at accepted
        cases ids with
        | nil =>
          simp only [leaf] at accepted
          simpa only [Nat.min_eq_right (Nat.le_succ fuel)] using leaf_receipt read form accepted
        | cons first rest =>
          cases rest with
          | nil =>
            simp only [leaf] at accepted
            simpa only [Nat.min_eq_right (Nat.le_succ fuel)] using leaf_receipt read form accepted
          | cons second rest =>
            cases rest with
            | cons next rest =>
              simp only [leaf] at accepted
              simpa only [Nat.min_eq_right (Nat.le_succ fuel)] using leaf_receipt read form accepted
            | nil =>
              obtain ⟨firstCode, firstAccepted, accepted⟩ := bind_ok accepted
              obtain ⟨secondCode, secondAccepted, accepted⟩ := bind_ok accepted
              obtain ⟨output, checked, accepted⟩ := bind_ok accepted
              cases output
              have same := ensure_type checked
              subst type
              cases accepted
              refine ⟨[firstCode, secondCode], ?_, rfl, metadata⟩
              simp only [List.mapM_cons, List.mapM_nil, firstAccepted, secondAccepted, bind, Except.bind, pure, Except.pure]
  · simp [owner, bind, Except.bind] at accepted

/-- The actual sequence result determines both the source pack and its full
payload representation at the final heap. -/
theorem values_pack {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {types : List TypeSystem.Ty} {nativeTypes : List Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world types nativeTypes sources values) :
    ∃ packed, Dynamic.ValuesPack sources packed ∧
      ValueRep checked registry functions mapping world (TypeSystem.Ty.productMany types)
        packed (DataPatternValues.packValues values) (SourceCoreCompatibleCatalog.packTypes nativeTypes) := by
  induction represented with
  | nil => exact ⟨.unit, .nil, .unit⟩
  | cons head tail ih =>
    cases tail with
    | nil => exact ⟨_, .singleton _, head⟩
    | cons =>
      obtain ⟨packed, packedSource, represented⟩ := ih
      exact ⟨_, .cons packedSource, .product head represented⟩

theorem sequence_result {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {faults : FunctionCalls.FaultRep} {sequence : DataExpressionSequence.Outcome} {value : Value}
    (represented : DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world types codes faults sequence value) :
    ∃ outcome, CompatibleExpressionProducts.PacksOutcome sequence outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping world (TypeSystem.Ty.productMany types) (SourceCoreCalls.packArguments codes).type faults outcome value := by
  cases represented with
  | values related =>
    obtain ⟨packed, packedSource, payload⟩ := values_pack related
    exact ⟨_, .values packedSource, .value (by simpa only [CompatibleExpressionConstructorNativeTyping.packed_type, CompatibleAmbientHeap.payloadModel] using payload)⟩
  | fault matched => exact ⟨_, .fault _, .fault matched⟩


theorem source_inv_at {size : Nat} (metadata : Metadata checked source id node type) {ids : List ExpressionId}
    (form : node.form = .tuple ids) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ child sequence, ProtectedDataExpressionSequence.TraceAt program child context evidence source environment before
      ids sequence after ∧ CompatibleExpressionProducts.PacksOutcome sequence outcome ∧ child < size := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form] at raw
    cases raw with
    | tuple _ children pack => exact ⟨_, _, .values children, .values pack,
        Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form] at raw
    cases raw with
    | tuple _ children => exact ⟨_, _, .fault children, .fault _,
        Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩


def Certificate (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  ∃ node ids types codes, lowered = SourceCoreCalls.packArguments codes ∧
    Header values source id node ids types codes ∧ DataExpressionSequence.Tree source children scope ids types codes

variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {children : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include transport in
theorem preserves (unique : NodeOccurrencesUnique source)
    (meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source children faults entry) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source children) faults entry := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, receipt, sequence⟩ := certified
  subst lowered
  intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped installed trace
  have same := Option.some.inj (receipt.metadata.found.symm.trans found)
  subst root
  obtain ⟨sourceOutcome, sourceTrace, packed⟩ := source_inv receipt.metadata receipt.form unique trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    ProtectedDataExpressionSequence.preserves transport sequence meaning environments heaps locals agrees actualTyped installed sourceTrace
  obtain ⟨actualOutcome, actualPacked, payload⟩ := sequence_result represented
  have sameOutcome := actualPacked.functional packed
  subst outcome
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, by simpa only [receipt.sourceType] using payload,
    finalHeaps, maps, worlds, frame, metadata⟩

include transport in
theorem reflects
    (meaning : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source children faults entry) :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Certificate values source children) faults entry := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, receipt, sequence⟩ := certified
  subst lowered
  intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped installed evaluated
  have same := Option.some.inj (receipt.metadata.found.symm.trans found)
  subst root
  obtain ⟨sourceOutcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    ProtectedDataExpressionSequence.reflects transport sequence meaning environments heaps locals agrees actualTyped installed evaluated
  obtain ⟨outcome, packed, payload⟩ := sequence_result represented
  exact ⟨outcome, after, finalMap, finalWorld, source_intro receipt.metadata receipt.form sourceTrace packed,
    by simpa only [receipt.sourceType] using payload, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTuples
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallTree
/-! A recursive expression grammar with an open static call-head interface.
Each node retains a finite list of child compiler results. The children are
recursively certified at every ordinary data, control, index and argument
position; a call head contains static source/compiled receipts only.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls
open Core Frontend SourceInference CompatibleExpressionPrimitives
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev CallHeads := GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate

def Entries (scope : Scope) (entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)) :
    GenericExpressionMeaning.Certificate := fun current id code => current = scope ∧ (id, code) ∈ entries

inductive Head (calls : CallHeads) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (reasonAt : ExpressionId → Word)
    (children : GenericExpressionMeaning.Certificate) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | primitive {id code} (head : CompatibleExpressionTypedCompositions.Head values.checked source children scope id code) :
      Head calls values source context reasonAt children scope id code
  | constructor {id node instantiation ids tag header codes}
      (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
      (form : node.form = .constructor instantiation ids)
      (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
      (sequence : DataExpressionSequence.Tree source children scope ids instantiation.payloadTypes codes) :
      Head calls values source context reasonAt children scope id
        ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩
  | member {id node base baseNode name index identity branches result child}
      (metadata : Metadata values.checked source id node result)
      (baseMetadata : Metadata values.checked source base baseNode child.type)
      (form : node.form = .member base name index)
      (layout : CompatibleExpressionMembers.Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result)
      (certified : children scope base child) :
      Head calls values source context reasonAt children scope id
        ⟨result, SourceCoreDataExpressions.member identity result branches child.expression⟩
  | index {id node base key baseNode keyNode layout comparison first second}
      (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (baseCertified : children scope base first) (keyCertified : children scope key second) :
      Head calls values source context reasonAt children scope id
        ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)⟩
  | builtin {id code} (head : BuiltinCalls.Typed.Head values source children scope id code) :
      Head calls values source context reasonAt children scope id code
  | call {id code} (head : calls children scope id code) :
      Head calls values source context reasonAt children scope id code
  | tuple {id node ids types codes}
      (receipt : CompatibleExpressionTuples.Header values source id node ids types codes)
      (sequence : DataExpressionSequence.Tree source children scope ids types codes) :
      Head calls values source context reasonAt children scope id (SourceCoreCalls.packArguments codes)

inductive Tree (calls : CallHeads) (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | fragment {id lowered}
      (child : CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id lowered) :
      Tree calls fuel values source context solved reasonAt scope id lowered
  | node {id lowered entries}
      (head : Head calls values source context reasonAt (Entries scope entries) scope id lowered)
      (children : ∀ child code, (child, code) ∈ entries →
        Tree calls fuel values source context solved reasonAt scope child code) :
      Tree calls fuel values source context solved reasonAt scope id lowered

variable {calls : CallHeads} {fuel : Nat} {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : Scope}

/-- Support follows the exact builtin fragment or the exact ordered child list.
It contains no called-body or runtime law. -/
inductive Tree.LiteralSites (literals : GenericExpressionMeaning.Certificate) :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Tree calls fuel values source context solved reasonAt scope id lowered → Prop where
  | fragment {id lowered}
      (child : CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id lowered)
      (sites : child.LiteralSites literals) : LiteralSites literals (.fragment child)
  | node {id lowered entries}
      (head : Head calls values source context reasonAt (Entries scope entries) scope id lowered)
      (children : ∀ child code, (child, code) ∈ entries →
        Tree calls fuel values source context solved reasonAt scope child code)
      (sites : ∀ child code (member : (child, code) ∈ entries), LiteralSites literals (children child code member)) :
      LiteralSites literals (.node head children)

def Tree.WithLiterals (literals : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun current id lowered => ∃ tree : Tree calls fuel values source context solved reasonAt current id lowered,
    tree.LiteralSites literals

theorem Tree.literalSites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree calls fuel values source context solved reasonAt scope id lowered) :
    tree.LiteralSites (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code) := by
  induction tree with
  | fragment child => exact .fragment child child.literalSites
  | node head children ih => exact .node head children ih

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatementHead
/-! A projected unary head retains only the actual key children. The compiler's
Unit slot has no corresponding Source expression. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open SourceCoreCompatibleDataPlaces
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

structure Head (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (certificate : GenericExpressionMeaning.Certificate) (scope : Scope)
    (administrative : Core.Context) (definitions : DataEnvironment) (assignment : AssignmentResolution) where
  prepared : Prepared
  index : Nat
  codes : List SourceCoreBasic.LoweredExpr
  leaf : TypeSystem.Ty
  sourceTypes : List TypeSystem.Ty
  site : SourceCoreElaboration.ErrorSite
  invalid : Word
  layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source certificate scope site
    assignment.target prepared codes sourceTypes leaf administrative .unit
  ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType)
  writable : WritableLocal context assignment.target.root prepared.route.rootSourceType
  profile : SourceCoreRawMetadata.runtimeType leaf = .word ∨ SourceCoreRawMetadata.runtimeType leaf = .integer

namespace Head
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {definitions : DataEnvironment} {assignment : AssignmentResolution}

theorem projected (head : Head values source context certificate scope administrative definitions assignment) :
    assignment.target.projections ≠ [] := by
  intro empty
  have path := head.layout.path
  rw [empty] at path
  have noSteps {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
      {root leaf : TypeSystem.Ty} {position : Nat} {steps : List PreparedStep}
      {keys : List (ExpressionId × Ty)}
      (path : CompatibleMixedRoute.PreparedPath checked source site root [] position steps keys leaf) : steps = [] := by
    cases path
    rfl
  exact head.layout.nonempty (noSteps path)

def emit (head : Head values source context certificate scope administrative definitions assignment)
    (next : Expr) (output : Ty) : Expr :=
  execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) (LanguageResult.success .unit)
    next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid

def writtenContext (head : Head values source context certificate scope administrative definitions assignment)
    (actual : Core.Context) : Core.Context :=
  ProtectedStagedProjectedBitNotCommit.writtenContext head.prepared (SourceCoreCalls.packArguments head.codes).type actual

structure Errors (head : Head values source context certificate scope administrative definitions assignment)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop where
  missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token
  uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection

/-- Genuine lowering and Source typing determine every key and leaf view. -/
theorem of_lower {site : SourceCoreElaboration.ErrorSite} {expression : ExpressionLowerer}
    {fuel : Nat} {reasonAt : ExpressionId → Word} {next code : Expr} {output resultType : Ty}
    {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (writable : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (sourceTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (nonempty : assignment.target.projections ≠ [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (extract : ∀ id lowered, expression fuel source scope id reasonAt = .ok lowered → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id lowered)
    (accepted : lower values values.checked.signatures expression fuel source scope site assignment .equal none output
      next reasonAt invalid invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code resultType definitions) :
    ∃ head : Head values source context certificate scope administrative definitions assignment,
      code = head.emit next output ∧ head.invalid = invalidOperand := by
  obtain ⟨binder, leaf, prepared, codes, sourceTypes, index, _, binding, rootEq, view, slot, layout, ordinary, _, emitted⟩ :=
    CompatiblePlaceBitNotCertificates.of_lower unique signatures sourceTyped nonempty extract accepted typed
  exact ⟨⟨prepared, index, codes, leaf, sourceTypes, site, invalidOperand, layout, ordinary, slot,
    rootEq ▸ writable binder binding, view ▸ profile⟩, emitted, rfl⟩

end Head
end Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatementMeaning
/-! Shared assignment composition consumes a typed expression meaning contract.
Concrete clients discharge that contract with their own expression Tree theorem.
Seven actual temporary values retain post-write typing and closure captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPlaceExecution DataPatternValues

namespace Head
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel values.checked registry functions)
    program context evidence source certificate faults)
  (reflection : TypedGenericExpressionMeaning.Reflects (payloadModel values.checked registry functions)
    program context evidence source certificate faults)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)
  {assignment : AssignmentResolution}
  (head : Head values source context certificate scope administrative ambient.definitions assignment)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include extension meaning faithful observations environments heaps locals agrees actualTyped in
theorem preserves_prefix {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before assignment.target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  cases trace with
  | intro resolve write =>
    obtain ⟨resolution, coreLookup⟩ := CompatibleRenamedPlaceResolution.preserves
      head.layout.path head.layout.views head.layout.children head.layout.keyTypes head.layout.leafProjected
      head.layout.virtual extension head.layout.nonempty
      (getter_typed head.layout (virtual_closed head.layout head.ordinary)
        (environment_respects environments.runtime_hasTypes actualTyped agrees))
      meaning faithful observations environments heaps locals agrees actualTyped head.slot head.writable resolve
    obtain ⟨commit, typed⟩ := ProtectedStagedProjectedBitNotCommit.typed_of_write head.layout head.ordinary extension
      faithful observations head.profile environments agrees actualTyped resolution write
      (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
    refine ⟨commit.finalStore, resolution.mapping, commit.finalWorld,
      [.unit, commit.value, commit.replacement, .unit, .inRight .unit resolution.snapshot,
        packValues resolution.values, .cellRef (OptionalCell.cellType head.prepared.route.rootType) resolution.target],
      commit.heaps, resolution.maps, resolution.worlds.trans commit.worlds,
      resolution.frame.trans commit.frame, resolution.metadata.trans commit.metadata, rfl, typed, ?_⟩
    intro next output
    change ContinuationAgreement actual store
      ((execute head.prepared (.var head.index) (SourceCoreCalls.packArguments head.codes) (LanguageResult.success .unit)
        next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) true head.invalid).rename ξ) _ _ _
    rw [execute_rename head.layout.path (virtual_closed head.layout head.ordinary)]
    simpa only [renamed_packed, Expr.rename, LanguageResult.success, writtenEnvironment, modifiedEnvironment, rhsEnvironment, snapshotEnvironment, keysEnvironment, referenceEnvironment, List.cons_append, List.nil_append] using
      commit.prefix_agreement resolution coreLookup (CompatiblePlaceModifier.passes_of_total rfl _ _) (next.rename ξ) output

end Head
end Solcore.SourceSemantics.CoreLowering.CompatibleProjectedBitNotStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementMeaning
/-! Bare unary head semantics close the actual numeric update/fault and retain
all seven real administrative values. The RHS slot is Unit, not a source child. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning

namespace Head
variable   {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

  {assignment : AssignmentResolution}
  (head : Head context scope assignment)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : HeapRepresents values.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)

include environments heaps locals agrees actualTyped in
theorem preserves_prefix {updated : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before assignment.target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨_, finalStore, slots, _, finalHeaps, frame, metadata, count, typed, continuation⟩ :=
    CompatibleRenamedBareBitNot.preserves_prefix (compilation := values) head.layout head.bare head.profile
      environments heaps locals agrees actualTyped head.slot head.writable trace (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
      (CompatiblePlaceModifier.passes_of_total rfl _ _)
  exact ⟨finalStore, mapping, world, slots, finalHeaps, .refl _, .refl _, frame, metadata, count, typed, continuation⟩

include environments heaps locals agrees in
theorem preserves_fault (errors : head.Errors faults)
    {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨rfl, rfl, evaluated⟩ := CompatibleRenamedBareBitNot.preserves_fault (compilation := values)
    head.layout head.bare head.profile environments heaps locals agrees head.slot head.writable trace
      next output (binaryOperator (head.prepared.route.leafType = .integer) .equal) head.invalid
  exact ⟨head.invalid, store, mapping, world, evaluated, errors, heaps, .refl _, .refl _, .refl _ _, .refl _⟩

include environments heaps locals agrees actualTyped in
theorem reflects (errors : head.Errors faults)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    (completed : Evaluates actual store ((head.emit next output).rename ξ) value finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after ∧
      value = .inLeft output (.word token) ∧ faults reason token ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
        environment before assignment.target updated after ∧
      HeapRepresents values.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      Evaluates (slots ++ actual) written (shift 7 (next.rename ξ)) value finalStore) := by
  cases CompatibleRenamedBareBitNot.reflects (compilation := values) head.layout head.bare head.profile
    environments heaps locals agrees actualTyped head.slot head.writable errors completed with
  | fault trace same matched stores =>
    subst finalStore
    exact .inl ⟨_, _, before, mapping, world, trace, same, matched, heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | success trace _ finalHeaps frame metadata count typed continuation =>
    exact .inr ⟨_, _, _, mapping, world, _, trace, finalHeaps, .refl _, .refl _, frame, metadata, count, typed, continuation⟩

end Head
end Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementComposition
/-! Bare unary heads compose with transfer-aware continuations.
The continuation contracts are intermediate induction hypotheses; the public
recursive tree discharges them using its concrete children. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open TypedLexicalWhile (Preserves Reflects FlowRep)
open TypedScopedStatements (Executes source_view prepend head_fault)

private theorem statement_shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

section Views
variable {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome}
  (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
include unique contains

theorem bitNot_view {assignment : AssignmentResolution} (form : node.form = .assignBitNot assignment)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ ∃ updated,
      Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
        environment before assignment.target updated after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, by assumption⟩

theorem bitNot_fault {assignment : AssignmentResolution} {reason : Dynamic.SemanticFault}
    (form : node.form = .assignBitNot assignment)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after := by
  have shape := statement_shape unique contains form
  have present : ¬ Dynamic.StatementMissing source id := fun absent => Dynamic.StatementAbsentIn.excludes_contains absent contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
end Views

variable {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {solved : List SolvedRequirement}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

theorem assignment_preserves {mode : Bool} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {body : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (head : Head context scope assignment)
    (headErrors : head.Errors faults)
    (unique : NodeOccurrencesUnique source)
    (continuationMeaning : Preserves (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode rest expected type body) :
    Preserves (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext environments heaps locals agrees actualTyped reference read unmapped trace
  have go {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
      (first : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough next) middle)
      (tail : Executes mode program middleContext evidence source next middle rest resultContext outcome after) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
          context scope environment resultContext after := by
    obtain ⟨rfl, same, updated, assigned⟩ := bitNot_view unique (lookupStatement?_sound found) form first
    cases same
    obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩ :=
      head.preserves_prefix functions program evidence
        environments heaps locals agrees actualTyped assigned
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
      continuationMeaning valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
        ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 tail
    exact ⟨value, finalStore, finalMap, finalWorld,
      (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
      represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) executed with
      ⟨_, _, _, first, tail⟩ | ⟨first, terminal⟩
    · exact go first (by cases mode <;> exact .control tail)
    · obtain ⟨_, rfl, _⟩ := bitNot_view unique (lookupStatement?_sound found) form first
      cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) failed with
      ⟨rfl, first⟩ | ⟨_, _, _, first, tail⟩
    · have assigned := bitNot_fault unique (lookupStatement?_sound found) form first
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
        head.preserves_fault functions program evidence
          environments heaps locals agrees headErrors assigned body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · exact go first (by cases mode <;> exact .fault tail)

theorem assignment_reflects
    {mode : Bool} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {body : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (head : Head context scope assignment)
    (headErrors : head.Errors faults)
    (_unique : NodeOccurrencesUnique source)
    (continuationMeaning : Reflects (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode rest expected type body) :
    Reflects (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped evaluated
  rcases head.reflects functions program evidence
    environments heaps locals agrees actualTyped headErrors evaluated with
    ⟨reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, frame, metadata⟩ |
    ⟨updated, middle, written, middleMap, middleWorld, slots, trace, middleHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
  · exact ⟨context, .fault reason, after, finalMap, finalWorld,
      head_fault mode rest (.assignBitNot (lookupStatement?_sound found) form trace), .fault matched,
      finalHeaps, maps, worlds, frame, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  · obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
      continuationMeaning valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
        ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
    exact ⟨resultContext, outcome, after, finalMap, finalWorld,
      prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignBitNot (lookupStatement?_sound found) form trace) tailTrace,
      represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallMeaning
/-! Protected administrative entries compose with every ordinary recursive
expression head. Runtime child obligations are used only inside the generic
composition layer and discharged by the final concrete tree induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedBuiltinCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload DataPatternValues
open BuiltinCalls BuiltinCalls.Protocol
open BuiltinCalls.Typed (Head)
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CompatibleExpressionPrimitives (Metadata)
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
private theorem values_rep {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world types natives sources payloads) :
    ValuesRep values.checked registry functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

private theorem contracted_typed {definitions : DataEnvironment} {world : StoreTyping}
    {environment : Environment} {actualContext : Core.Context}
    (typed : RuntimeEnvironmentHasTypes world environment actualContext definitions)
    (function : BuiltinFunctionId) (identity contract : Word) :
    RuntimeValueHasType world (contractedValue function identity contract environment)
      (CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function))
      definitions := by
  have closureTyped := SourceCoreInteger.builtinClosure_hasType (scope := actualContext) (definitions := definitions) function
  cases closureTyped with
  | lambda _ _ body => exact .pair (.pair (.inRight .word) (.closure typed body)) .word

private theorem contracted_rename (function : BuiltinFunctionId) (identity contract : Word) (ξ : Renaming) :
    (Protocol.contracted function identity contract).rename ξ = Protocol.contracted function identity contract := by
  cases function <;> rfl

private theorem call_rename (function : BuiltinFunctionId) (identity contract unknown : Word)
    (arguments : Expr) (ξ : Renaming) :
    (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (Protocol.contracted function identity contract) arguments).rename ξ =
    CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
      (Protocol.contracted function identity contract) (arguments.rename ξ) := by
  simp [CallableContract.call, LanguageResult.bind, CallableContract.dispatch, CallableContract.guardResult,
    CallableContract.Gate.reason, LanguageResult.success, LanguageResult.failure,
    contracted_rename, Expr.rename, Renaming.lift]


variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

variable {certificate : GenericExpressionMeaning.Certificate}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
include transport

include functionLeaves unique in
theorem Head.preserves
    (argumentMeaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType children nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have prefixedLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        canonical (.unit :: contractedValue function identity contract actual :: actual) := agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
    have prefixedTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
      (.cons (contracted_typed actualTyped function identity contract) actualTyped)
    have sourceTrace := source_inv metadata form unique trace
    cases sourceTrace with
    | argumentsFault failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, argumentEval, matched, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ProtectedDataExpressionSequence.preserves_fault transport children argumentMeaning environments heaps locals prefixedLayout prefixedTyped installedEntry failed
      rw [rename_prefix, rename_prefix] at argumentEval
      refine ⟨.inLeft _ (.word token), finalStore, finalMap, finalWorld, ?_, .fault matched,
        finalHeaps, maps, worlds, frame, heapMetadata⟩
      rw [call_rename]
      exact CallableContract.call_argument_failure [⟨contract, none, none⟩] unknown
        (contracted_evaluates function identity contract actual store) (gates_accept contract unknown .beforeArguments) argumentEval
    | apply argumentsEvaluated application =>
      obtain ⟨payloads, argumentStore, finalMap, finalWorld, argumentEval, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ProtectedDataExpressionSequence.preserves_values transport children argumentMeaning environments heaps locals prefixedLayout prefixedTyped installedEntry argumentsEvaluated
      have related := values_rep represented
      rw [nativeTypes] at related
      have inputs := CompatibleBuiltinMeaning.input_of_values functionLeaves related
      rw [rename_prefix, rename_prefix] at argumentEval
      cases application with
      | value applied =>
        cases applied with
        | builtin applied =>
          obtain ⟨sourceResult, nativeResult, appliedAgain, resultRep, completed⟩ := contracted_preserves inputs argumentEval
          have same := appliedAgain.functional applied
          subst sourceResult
          refine ⟨.inRight .word nativeResult, argumentStore, finalMap, finalWorld, ?_, ?_,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
          · rw [call_rename]; exact completed
          · rw [sourceType]; exact .value (CompatibleBuiltinMeaning.result_represents inputs applied resultRep)
      | fault failed => exact False.elim (InputRep.excludes_callable_fault inputs failed)

include functionLeaves in
theorem Head.reflects
    (argumentMeaning : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry) :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head values source certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType children nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ result finalStore
      environments heaps locals agrees actualTyped installedEntry completed
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [call_rename] at completed
    obtain ⟨argumentValue, argumentStore, argumentEval⟩ := contracted_argument_completes completed
    have shifted := argumentEval
    rw [← rename_prefix, ← rename_prefix] at shifted
    have prefixedLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        canonical (.unit :: contractedValue function identity contract actual :: actual) := agree_prefix (agree_prefix agrees (contractedValue function identity contract actual)) .unit
    have prefixedTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (definitions := ambient.definitions))
      (.cons (contracted_typed actualTyped function identity contract) actualTyped)
    obtain ⟨argumentOutcome, middle, finalMap, finalWorld, argumentTrace, represented, finalHeaps,
      maps, worlds, frame, heapMetadata⟩ :=
      ProtectedDataExpressionSequence.reflects transport children argumentMeaning environments heaps locals prefixedLayout prefixedTyped installedEntry shifted
    cases represented with
    | values represented =>
      cases argumentTrace with
      | values sourceArgs =>
        have related := values_rep represented
        rw [nativeTypes] at related
        have inputs := CompatibleBuiltinMeaning.input_of_values functionLeaves related
        obtain ⟨sourceResult, nativeResult, applied, resultRep, resultEq, storesEq⟩ := contracted_reflects inputs argumentEval completed
        subst result
        subst finalStore
        refine ⟨.value sourceResult, middle, finalMap, finalWorld,
          source_intro metadata form (.apply sourceArgs (.value (.builtin applied))), ?_,
          finalHeaps, maps, worlds, frame, heapMetadata⟩
        rw [sourceType]; exact .value (CompatibleBuiltinMeaning.result_represents inputs applied resultRep)
    | fault matched =>
      cases argumentTrace with
      | fault sourceArgs =>
        have failed := CallableContract.call_argument_failure (result := SourceCoreInteger.builtinResult function)
          [⟨contract, none, none⟩] unknown (contracted_evaluates function identity contract actual store)
          (gates_accept contract unknown .beforeArguments) argumentEval
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed failed
        exact ⟨.fault _, middle, finalMap, finalWorld, source_intro metadata form (.argumentsFault sourceArgs),
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedBuiltinCalls

namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open CompatibleExpressionIndices CoreProof
open GenericExpressionMeaning (agree_prefix rename_prefix)
open DataPatternValues
private theorem valuesRep {values : ValuesContext} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world types natives sources payloads) :
    ValuesRep values.checked registry functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

private theorem missing_excludes {values : List Dynamic.Value} {index : Nat} {value : Dynamic.Value}
    (missing : Dynamic.ValueIndexMissing values index) (selected : Dynamic.ValueAt values index value) : False := by
  induction missing with
  | nil => cases selected
  | tail rest ih => cases selected with | tail child => exact ih child

private theorem at_functional {values : List Dynamic.Value} {index : Nat} {first second : Dynamic.Value}
    (left : Dynamic.ValueAt values index first) (right : Dynamic.ValueAt values index second) : first = second := by
  induction left with
  | head => cases right; rfl
  | tail _ ih => cases right with | tail rest => exact ih rest

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))


variable {calls : CallHeads} {certificate : GenericExpressionMeaning.Certificate}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include transport extension faithful functionLeaves functionTypes unique missing in
theorem Head.preserves
    [FunctionCalls.FaultTokens faults] (meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
    (callMeaning : ∀ {children},
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source children faults entry →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (calls children) faults entry) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head calls values source context reasonAt certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | primitive head => exact ProtectedExpressionCompositions.Head.preserves functions program evidence transport unique meaning head
  | builtin head => exact ProtectedBuiltinCalls.Head.preserves functions functionLeaves program evidence unique transport meaning head
  | call head => exact callMeaning meaning head
  | tuple receipt sequence =>
    exact CompatibleExpressionTuples.preserves functions program evidence transport unique meaning
      ⟨_, _, _, _, rfl, receipt, sequence⟩
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨sourceOutcome, sourceTrace, packed⟩ := constructor_inv receipt.metadata form unique valid trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      ProtectedDataExpressionSequence.preserves transport sequence meaning environments heaps locals agrees actualTyped installedEntry sourceTrace
    cases represented with
    | @values sources payloadValues payloads =>
      cases packed
      have projected := receipt.metadata.projected
      rw [receipt.sourceType] at projected
      refine ⟨.inRight .word (.constructed tag (.pair (.word header) (packValues payloadValues))), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
      · rw [CompatibleExpressionConstructors.construct_rename]; exact CompatibleExpressionConstructors.construct_success tag header evaluated
      · rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
          receipt.selected projected receipt.registered (valuesRep payloads))
    | fault matched =>
      cases packed
      exact ⟨_, finalStore, finalMap, finalWorld, by rw [CompatibleExpressionConstructors.construct_rename]; exact CompatibleExpressionConstructors.construct_failure tag header evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩

  | @member node base baseNode name index identity branches result child metadata baseMetadata form layout childTree =>
    have ih := @meaning _ _ _ childTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have raw := member_inv metadata form unique trace
    cases raw with
    | value childTrace selected =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, sourceChild, native, shape, sourceAt, related, completed⟩ := member_success layout payload evaluated
        cases shape
        have same := at_functional sourceAt selected
        subst sourceChild
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact completed,
          .value related, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | failure childTrace =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped installedEntry (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact LanguageResult.bind_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | shape childTrace invalid =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, _⟩ := member_success layout payload evaluated
        subst_vars
        exact False.elim (invalid .intro)
    | position childTrace missing =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped installedEntry (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, selected, _⟩ := member_success layout payload evaluated
        cases shape
        exact False.elim (missing_excludes missing selected)

  | @index node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree =>
    have firstIH := @meaning _ _ _ firstTree
    have secondIH := @meaning _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped installedEntry trace
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rcases (index_inv header.metadata form unique trace).split with ⟨reason, rfl, failed⟩ | ⟨baseSource, middle, baseTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
        rw [index_rename comparison header.registered header.comparisonType]
        exact LanguageResult.bind_failure _ evaluated
    · obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry (.value baseTrace)
      cases represented with
      | @value _ baseValue baseRep =>
        have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
        rcases tail with ⟨reason, rfl, failed⟩ | ⟨keySource, keyTrace, terminal⟩
        · obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.fault failed)
          cases represented with
          | fault matched =>
            refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            exact LanguageResult.bind_success _ firstEval (LanguageResult.bind_failure _ secondEval)
        · obtain ⟨value, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) (.value keyTrace)
          cases represented with
          | @value _ keyValue keyRep =>
            obtain ⟨actualOutcome, result, finalStore, finalWorld, terminal', related, lookup, finalHeaps, worlds, frame, uniqueResult⟩ :=
              CompatibleGeneralIndex.finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps (reasonAt id) (missing id)
            have same := uniqueResult outcome terminal
            subst actualOutcome
            refine ⟨result, finalStore, keyMap, finalWorld, ?_, related, finalHeaps,
              firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
              (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            apply SourceCoreCompatibleDataExpressions.index_completed layout (reasonAt id) firstEval secondEval
            simpa only [CompatibleMapping.Transport.expression_weaken] using lookup


include transport extension faithful functionLeaves functionTypes missing in
theorem Head.reflects
    [FunctionCalls.FaultTokens faults] (meaning : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source certificate faults entry)
    (callMeaning : ∀ {children},
      ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source children faults entry →
      ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (calls children) faults entry) :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Head calls values source context reasonAt certificate) faults entry := by
  intro scope id lowered tree
  cases tree with
  | primitive head => exact ProtectedExpressionCompositions.Head.reflects functions program evidence transport meaning head
  | builtin head => exact ProtectedBuiltinCalls.Head.reflects functions functionLeaves program evidence transport meaning head
  | call head => exact callMeaning meaning head
  | tuple receipt sequence =>
    exact CompatibleExpressionTuples.reflects functions program evidence transport meaning
      ⟨_, _, _, _, rfl, receipt, sequence⟩
  | @constructor node instantiation ids tag header codes receipt form valid sequence =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    rw [CompatibleExpressionConstructors.construct_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ProtectedDataExpressionSequence.reflects transport sequence meaning environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_failure tag header childEvaluation)
        exact ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace (.fault _),
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ProtectedDataExpressionSequence.reflects transport sequence meaning environments heaps locals agrees actualTyped installedEntry childEvaluation
      cases represented with
      | values payloads =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_success tag header childEvaluation)
        have projected := receipt.metadata.projected
        rw [receipt.sourceType] at projected
        refine ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace (.values _),
          ?_, finalHeaps, maps, worlds, frame, heapMetadata⟩
        rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
          receipt.selected projected receipt.registered (valuesRep payloads))

  | @member node base baseNode name index identity branches result child metadata baseMetadata form layout childTree =>
    have ih := @meaning _ _ _ childTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [member_rename layout] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped installedEntry baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure result baseEvaluation (body := .matchData identity (LanguageResult.resultType result) (.var 0) branches)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.failure failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped installedEntry baseEvaluation
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, selected, native, shape, sourceAt, related, expected⟩ := member_success layout payload baseEvaluation
        subst_vars
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.value childTrace sourceAt), .value related,
            finalHeaps, maps, worlds, frame, heapMetadata⟩

  | @index node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree =>
    have firstIH := @meaning _ _ _ firstTree
    have secondIH := @meaning _ _ _ secondTree
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped installedEntry evaluated
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure layout.valueType baseEvaluation (body :=
          LanguageResult.bind layout.valueType ((second.expression.rename ξ).weakenAt 0)
            (SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.baseFailure failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨outcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped installedEntry baseEvaluation
      cases represented with
      | @value baseSource baseValue baseRep =>
        cases trace with
        | value baseTrace =>
          have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
          cases branch with
          | caseLeft keyEvaluation ignored =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) keyEvaluation
            cases represented with
            | fault matched =>
              rw [rename_prefix] at keyEvaluation
              have expected := LanguageResult.bind_success layout.valueType baseEvaluation
                (LanguageResult.bind_failure layout.valueType keyEvaluation (body :=
                  SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              cases trace with
              | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.keyFailure baseTrace failed),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
          | caseRight keyEvaluation lookupEvaluation =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, keyMap, keyWorld, trace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment (transport.extend installedEntry firstMaps firstWorlds firstFrame firstMetadata) keyEvaluation
            cases represented with
            | @value keySource keyValue keyRep =>
              obtain ⟨outcome, result, endStore, finalWorld, terminal, related, lookup, finalHeaps, worlds, frame, uniqueResult⟩ :=
                CompatibleGeneralIndex.finish header sourceType faithful functionLeaves functionTypes (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                  (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps (reasonAt id) (missing id)
              rw [rename_prefix] at keyEvaluation
              have expected := SourceCoreCompatibleDataExpressions.index_completed (comparison := comparison.expression) layout (reasonAt id) baseEvaluation keyEvaluation
                (by simpa only [CompatibleMapping.Transport.expression_weaken] using lookup)
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              cases trace with
              | value keyTrace =>
                exact ⟨outcome, after, keyMap, finalWorld, index_intro header.metadata form (terminal.trace baseTrace keyTrace),
                  related, finalHeaps, firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
                  (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata⟩



end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls

namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {calls : CallHeads} {entry : ProtectedExpressionMeaning.Entry}
  (transport : ProtectedExpressionMeaning.Transport entry)

include extension faithful functionLeaves functionTypes valid uninitialized missing transport in
/-- The finite tree induction supplies every recursive child meaning. The
call-head interface is an inner composition law supplied by a concrete caller
adapter; it is not stored in an expression certificate. -/
theorem preserves [FunctionCalls.FaultTokens faults] (unique : NodeOccurrencesUnique source)
    (callMeaning : ∀ {children},
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source children faults entry →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (calls children) faults entry) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree calls fuel values source context solved reasonAt) faults entry := by
  intro scope id lowered tree
  induction tree with
  | fragment child =>
    exact ProtectedExpressionMeaning.preserves_of_typed entry
      (CompatibleExpressionBuiltins.preserves functions extension faithful functionLeaves functionTypes
        program evidence valid unique uninitialized missing) child
  | @node id lowered entries head children ih =>
    have meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope entries) faults entry := by
      intro current child code certified
      obtain ⟨rfl, member⟩ := certified
      exact ih child code member
    intro root found
    exact Head.preserves functions extension faithful functionLeaves functionTypes program evidence unique missing
      transport meaning callMeaning head found

include extension faithful functionLeaves functionTypes valid uninitialized missing transport in
/-- Native completion recursively builds all source child traces, including
skipped branches and first argument faults, with the actual protected entry. -/
theorem reflects [FunctionCalls.FaultTokens faults]
    (callMeaning : ∀ {children},
      ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source children faults entry →
      ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (calls children) faults entry) :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree calls fuel values source context solved reasonAt) faults entry := by
  intro scope id lowered tree
  induction tree with
  | fragment child =>
    exact ProtectedExpressionMeaning.reflects_of_typed entry
      (CompatibleExpressionBuiltins.reflects functions extension faithful functionLeaves functionTypes
        program evidence valid uninitialized missing) child
  | @node id lowered entries head children ih =>
    have meaning : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope entries) faults entry := by
      intro current child code certified
      obtain ⟨rfl, member⟩ := certified
      exact ih child code member
    intro root found
    exact Head.reflects functions extension faithful functionLeaves functionTypes program evidence missing
      transport meaning callMeaning head found

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls

namespace Solcore.SourceSemantics.CoreLowering.NamedCallExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

/-- Concrete recursive ordinary named expressions. The retained body inventory
contains static compiler/body receipts; its installed observations remain a
separate, protected dynamic entry. -/
abbrev Tree (bodies : Bodies prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) : GenericExpressionMeaning.Certificate :=
  CompatibleExpressionCalls.Tree (Head bodies compilation source context)
    fuel values source context solved reasonAt

variable (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {bodies : Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (caller : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context caller)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include extension faithful functionLeaves functionTypes valid uninitialized missing bodyUninitialized bodyMissing in
/-- All recursive child and named body meanings are discharged by the finite
Tree and concrete builtin-lexical body certificates. Actual global/frame
provenance, context/evidence validity and static source ownership stay explicit. -/
theorem Tree.preserves [FunctionCalls.FaultTokens faults] (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context caller source (Tree bodies compilation fuel source context solved reasonAt) faults
      (Entry functions registry bodies compilation.administrativePrefix) := by
  apply CompatibleExpressionCalls.preserves functions extension faithful functionLeaves functionTypes
    program caller valid uninitialized missing
    (entry_transport functions registry bodies compilation.administrativePrefix) unique
  intro children meaning
  exact Head.preserves functions extension caller bodyUninitialized bodyMissing faithful functionLeaves
    functionTypes unique owners meaning

include extension faithful functionLeaves functionTypes valid uninitialized missing bodyUninitialized bodyMissing in
/-- Native finite completion constructs the complete independent expression
outcome, including named calls at arbitrary child positions and first faults.
No external recursive child or body meaning is required. -/
theorem Tree.reflects [FunctionCalls.FaultTokens faults] :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context caller source (Tree bodies compilation fuel source context solved reasonAt) faults
      (Entry functions registry bodies compilation.administrativePrefix) := by
  apply CompatibleExpressionCalls.reflects functions extension faithful functionLeaves functionTypes
    program caller valid uninitialized missing
    (entry_transport functions registry bodies compilation.administrativePrefix)
  intro children meaning
  exact Head.reflects functions extension caller bodyUninitialized bodyMissing faithful functionLeaves
    functionTypes meaning

end Solcore.SourceSemantics.CoreLowering.NamedCallExpressions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotFaults
/-! Bare numeric faults are exactly absent unary operands. They bypass the
setter, mapped write and continuation, preserving both source and native heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

private theorem excludes_target_fault {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {heap after : Dynamic.Heap} {place : PlaceResolution} {location : Dynamic.Location} {cell : Dynamic.Cell}
    {reason : Dynamic.SemanticFault}
    (bare : place.projections = []) (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (read : Dynamic.Heap.Reads heap location cell)
    (fault : Dynamic.SourcePlaceFaults program context evidence source environment heap place reason after) : False := by
  cases fault with
  | unbound missing => exact missing.excludes_lookup lookup
  | dangling found missing => exact missing.excludes_read (found.functional lookup ▸ read)
  | projectionExpression found initialRead fault => rw [bare] at fault; cases fault
  | danglingAfterProjections found initialRead keys missing =>
    rw [bare] at keys
    cases keys
    exact missing.excludes_read initialRead
  | projectionRead found initialRead keys currentRead root fault =>
    rw [bare] at keys
    cases keys
    cases fault
  | uninitialized found initialRead keys currentRead empty notMapping nonempty =>
    rw [bare] at keys
    cases keys
    exact nonempty rfl

theorem preserves_fault {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {administrativeContext : Core.Context}
    {place : PlaceResolution} {prepared : Prepared} {mapping : LocationMap} {world : StoreTyping}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before after : Dynamic.Heap}
    {store : Store} {index : Nat} {reason : Dynamic.SemanticFault}
    (layout : Layout prepared) (bare : place.projections = [])

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before place reason after)
    (next : Expr) (outputType : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) :
    reason = .invalidUnaryOperand .bitNot ∧ after = before ∧
      Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
        (LanguageResult.success .unit) next outputType operator true invalid) (.inLeft outputType (.word invalid)) store := by
  obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨staticLocation, staticCell, staticLookup, staticRead, staticType, _⟩ := locals.lookup schemeLookup
  cases trace with
  | target fault => exact (excludes_target_fault bare staticLookup staticRead fault).elim
  | uninitialized resolve empty =>
    cases resolve with
    | intro lookup initialRead keys currentRead root selection =>
      rw [bare] at keys
      cases keys
      cases selection
      cases empty
      cases root with
      | uninitialized notMapping =>
        obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
        obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference currentRead
        cases represented with
        | uninitialized projected => exact ⟨rfl, rfl,
            CompatibleBareBitNotNative.absent_evaluates layout nativeLookup nativeRead next outputType operator invalid⟩
  | operand resolve selected invalidOperand =>
    cases resolve with
    | intro lookup initialRead keys currentRead root selection =>
      rw [bare] at keys
      cases keys
      cases selection
      cases selected
      have sameLocation := lookup.functional staticLookup
      subst staticLocation
      have sameCell := currentRead.functional staticRead
      subst staticCell
      have cellType := staticType.trans bodyEq
      cases root with
      | emptyMapping key value =>
        have impossible := cellType ▸ profile
        rcases impossible with impossible | impossible <;> cases impossible
      | initialized =>
        obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
        obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference currentRead
        cases represented with
        | initialized related =>
          have profile := cellType ▸ profile
          obtain ⟨_, _, _, _, _, valid⟩ := CompatiblePlaceNumericBitNotModifier.success profile related
            (environment := [_]) (rhs := .unit) (.var (index := 0) rfl) operator store invalid
          exact (valid invalidOperand).elim

end Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotLowering
/-! Actual compatible compiler success supplies the complete bare-root layout.
No child compiler/evaluation or helper typing premise remains in these bridges.
Writable-local/source numeric typing and authenticated heap/function leaves are
still independent semantic conditions; source checker admission is unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotLowering
open Core Frontend SourceInference GeneralHeap GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
  {faults : FaultRep} {assignment : AssignmentResolution} {administrativeContext : Core.Context}
  {expression : ExpressionLowerer} {fuel : Nat} {operator : Syntax.ValueAssignOp}
  {next lowered : Expr} {outputType : Ty} {reasonAt : ExpressionId → Word}
  {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
  {before after : Dynamic.Heap} {store finalStore : Store} {result : Value}
  (rootTyped : ∀ binder, rootBinder source assignment.target.root = .ok binder →
    WritableLocal context assignment.target.root binder.scheme.body)
  (bare : assignment.target.projections = [])
  (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
    SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)

  (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
  (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)

include rootTyped bare profile environments heaps locals

/-- Every completed actual compiler output has an independent unary failure
or snapshot-write trace. The real seven-slot continuation is recovered only
after the source write, and remains an output of reflection. -/
theorem reflects
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      outputType next reasonAt invalid invalidOperand missing = .ok lowered)
    (token : faults (.invalidUnaryOperand .bitNot) invalidOperand)
    (completed : Evaluates coreEnvironment store lowered result finalStore) :
    CompatiblePlaceBitNotMeaning.Result compilation.checked registry functions program context evidence source faults assignment.target
      environment coreEnvironment before store mapping world next outputType result finalStore := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  exact CompatibleBareBitNotMeaning.reflects layout bare (view ▸ profile) environments heaps locals slot
    (rootEq ▸ rootTyped binder binding) token (lowering ▸ completed)

/-- An independent successful snapshot trace executes to Unit and the related
written heap through the actual compiler output, at the same world and map. -/
theorem preserves
    (total : operator.mayPanic = false)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      .unit (LanguageResult.success .unit) reasonAt invalid invalidOperand missing = .ok lowered)
    {updated : Dynamic.Value}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before assignment.target updated after) :
    ∃ finalStore, Evaluates coreEnvironment store lowered (.inRight .word .unit) finalStore ∧
      HeapRepresents compilation.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  rw [lowering]
  exact CompatibleBareBitNotMeaning.preserves layout bare (view ▸ profile) environments heaps locals slot
    (rootEq ▸ rootTyped binder binding) trace _ _ (CompatiblePlaceModifier.passes_of_total total _ _)

/-- A source fault is exactly the absent unary operand; actual generated code
returns its token and preserves the entire native store. -/
theorem preserves_fault
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      outputType next reasonAt invalid invalidOperand missing = .ok lowered)
    {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after) :
    reason = .invalidUnaryOperand .bitNot ∧ after = before ∧
      Evaluates coreEnvironment store lowered (.inLeft outputType (.word invalidOperand)) store := by
  obtain ⟨binder, prepared, index, binding, rootEq, view, slot, layout, lowering⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare profile accepted
  rw [lowering]
  exact CompatibleBareBitNotMeaning.preserves_fault layout bare (view ▸ profile) environments heaps locals slot
    (rootEq ▸ rootTyped binder binding) trace _ _ _ _

end Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotLowering
end

import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorNativeTyping

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

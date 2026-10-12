import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTupleCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveStageTupleMeaning

/-! Successful compilation constructs a finite recursive caller certificate.
The callee and ordered argument vector retain the exact compiler occurrences,
including repetitions. Raw Source typing precedes recursive extraction. These
are static receipts: runtime states, execution laws and called-body meaning are
not certificate fields. Reachable call authority is indexed by the actual tree.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open Core Frontend SourceInference
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | leaf {id} (tree : CompatibleExpressionProducts.Syntax source id) : Syntax source id
  | group {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .group inner) (child : Syntax source inner) : Syntax source id
  | tuple {id node ids} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple ids)
      (children : ∀ child, child ∈ ids → Syntax source child) : Syntax source id
  | call {id node callee ids metadata} (found : source.lookupExpression? id = some node)
      (form : node.form = .call callee ids (.indirect metadata))
      (calleeSyntax : Syntax source callee)
      (children : ∀ child, child ∈ ids → Syntax source child) : Syntax source id

structure PolicyFor (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) : Prop where
  special : ∀ id, Syntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none
  read : ∀ id, Syntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

/-- Only occurrences admitted by the enclosing body need policy facts. -/
structure PolicyOn (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word)
    (allowed : ExpressionId → Prop) : Prop where
  special : ∀ id, allowed id → Syntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none
  read : ∀ id, allowed id → Syntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

theorem PolicyFor.on {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    (profile : PolicyFor policy compilation readFuel values source scope reasonAt)
    (allowed : ExpressionId → Prop) : PolicyOn policy compilation readFuel values source scope reasonAt allowed :=
  ⟨fun id _ tree => profile.special id tree, fun id _ tree => profile.read id tree, profile.lower, profile.leaf⟩

inductive Certificate (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (reasonAt : ExpressionId → Word)
    (scope : SourceCoreLocalCell.Scope) : ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | leaf {id code}
      (tree : CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate readFuel values
        source context compilation.solvedRequirements reasonAt scope id code) :
      Certificate policy body compilation readFuel values source context reasonAt scope id code
  | group {id node inner innerNode code}
      (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node code.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Certificate policy body compilation readFuel values source context reasonAt scope inner code) :
      Certificate policy body compilation readFuel values source context reasonAt scope id code
  | tuple {id node ids types codes}
      (header : CompatibleExpressionTuples.Header values source id node ids types codes)
      (sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (ids.zip codes)) scope ids types codes)
      (children : ∀ child code, (child, code) ∈ ids.zip codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child code) :
      Certificate policy body compilation readFuel values source context reasonAt scope id
        (SourceCoreCalls.packArguments codes)
  | call {id callee ids metadata fuel lowered types}
      (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
        id callee ids metadata reasonAt lowered)
      (sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) scope ids types compiler.codes)
      (children : ∀ child code, (child, code) ∈ compiler.entries →
        Certificate policy body compilation readFuel values source context reasonAt scope child code) :
      Certificate policy body compilation readFuel values source context reasonAt scope id lowered

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}

/-- A call is reachable only through this exact static certificate. Authority
for unrelated accepted receipts is not needed. The argument path retains the
literal membership proof, including the leading callee and repeated entries. -/
inductive Calls {fuel : Nat} {callScope : SourceCoreLocalCell.Scope}
    {callId callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source callScope
      callId callee ids metadata reasonAt lowered) :
    {scope : SourceCoreLocalCell.Scope} → {id : ExpressionId} → {code : SourceCoreBasic.LoweredExpr} →
      Certificate policy body compilation readFuel values source context reasonAt scope id code → Prop where
  | here {types}
      (sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries callScope compiler.entries) callScope ids types compiler.codes)
      (children : ∀ child code, (child, code) ∈ compiler.entries →
        Certificate policy body compilation readFuel values source context reasonAt callScope child code) :
      Calls compiler (.call compiler sequence children)
  | group {scope id node inner innerNode code}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node code.type}
      {form : node.form = .group inner} {found : source.lookupExpression? inner = some innerNode}
      {type : node.type = innerNode.type}
      {child : Certificate policy body compilation readFuel values source context reasonAt scope inner code}
      (inside : Calls compiler child) : Calls compiler (.group actual form found type child)
  | tuple_child {scope id node tupleIds types codes}
      {header : CompatibleExpressionTuples.Header values source id node tupleIds types codes}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (tupleIds.zip codes)) scope tupleIds types codes}
      {children : ∀ child code, (child, code) ∈ tupleIds.zip codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child code}
      {child childCode} (member : (child, childCode) ∈ tupleIds.zip codes)
      (inside : Calls compiler (children child childCode member)) :
      Calls compiler (.tuple header sequence children)
  | call_child {scope id otherCallee otherIds otherMetadata otherFuel code types}
      {outer : CallableIndirectCallCertificates.Receipt policy body otherFuel compilation source scope
        id otherCallee otherIds otherMetadata reasonAt code}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope outer.entries) scope otherIds types outer.codes}
      {children : ∀ child childCode, (child, childCode) ∈ outer.entries →
        Certificate policy body compilation readFuel values source context reasonAt scope child childCode}
      {child childCode} (member : (child, childCode) ∈ outer.entries)
      (inside : Calls compiler (children child childCode member)) :
      Calls compiler (.call outer sequence children)

private theorem product_policy_on {scope : SourceCoreLocalCell.Scope} {allowed : ExpressionId → Prop}
    (policyFor : PolicyOn policy compilation readFuel values source scope reasonAt allowed) :
    CompatibleExpressionProducts.PolicyOn policy compilation readFuel values source scope reasonAt allowed :=
  ⟨fun id admitted tree => policyFor.special id admitted (.leaf tree),
   fun id admitted tree => policyFor.read id admitted (.leaf tree), policyFor.lower, policyFor.leaf⟩

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

private theorem group_step {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id inner : ExpressionId}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation
      source scope id reasonAt = .ok lowered) :
    CompatibleExpressionPrimitives.Metadata values.checked source id node lowered.type ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
        source scope inner reasonAt = .ok lowered := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
      bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation
        childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form, readPolicy] at accepted
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error => simp [read] at accepted
      | ok pair =>
        obtain ⟨other, type⟩ := pair
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        simp only [read, form] at accepted
        obtain ⟨child, generated, rest⟩ := bind_ok accepted
        obtain ⟨checked, checkedType, output⟩ := bind_ok rest
        cases checked
        have same := ensure_type checkedType
        subst type
        simp only [Except.ok.injEq] at output
        subst lowered
        exact ⟨metadata, generated⟩
  · simp [owner, bind, Except.bind] at accepted

private theorem call_read {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {ids : List ExpressionId} {resolution : IndirectCallResolution}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect resolution))
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation
      source scope id reasonAt = .ok lowered) :
    ∃ type, policy.readExpression source id = .ok (node, type) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
      bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation
        childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form, readPolicy] at accepted
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error => simp [read] at accepted
      | ok pair =>
        obtain ⟨other, type⟩ := pair
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        exact ⟨type, readPolicy.trans read⟩
  · simp [owner, bind, Except.bind] at accepted

private theorem child_certificates {scope : SourceCoreLocalCell.Scope} {budget : Nat}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {certificate : ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ids.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body budget
      compilation source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt = .ok code →
      certificate id code) :
    ids.length = types.length ∧ CompatibleExpressionConstructors.Nodes source ids types codes ∧
      ∀ id code, (id, code) ∈ ids.zip codes → certificate id code := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at generated
    subst codes
    exact ⟨rfl, .nil, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at generated
      obtain ⟨code, first, generated⟩ := bind_ok generated
      obtain ⟨restCodes, rest, generated⟩ := bind_ok generated
      cases generated
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have child := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨count, nodes, children⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      refine ⟨congrArg Nat.succ count, .cons ⟨node, found, sourceType⟩ nodes, ?_⟩
      intro other otherCode member
      rcases List.mem_cons.mp member with same | remaining
      · cases same; exact child
      · exact children other otherCode remaining

/-- The actual successful action supplies every recursive compiler child.
Independent raw Source typing supplies child types before their extraction. -/
theorem of_functions_on {scope : SourceCoreLocalCell.Scope}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {allowed : ExpressionId → Prop}
    (policyFor : PolicyOn policy compilation readFuel values source scope reasonAt allowed)
    (closed : ∀ {parent node child}, allowed parent → source.lookupExpression? parent = some node →
      (.expression child : NodeId) ∈ node.form.references → allowed child)
    (coercions : ∀ id node, allowed id → Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) (admitted : allowed id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Certificate policy body compilation readFuel values source context reasonAt scope id lowered := by
  revert admitted
  induction syntaxTree generalizing node fuel lowered with
  | leaf tree =>
    intro admitted
    exact .leaf (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions_on
      unique declarations (product_policy_on policyFor) closed
      (fun id node allowed tree found => coercions id node allowed (.leaf tree) found) tree admitted found typed accepted)
  | group originalFound form child ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨metadata, generated⟩ := group_step originalFound form
        (policyFor.special _ admitted (.group originalFound form child))
        (policyFor.read _ admitted (.group originalFound form child)) accepted
      obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ :=
        CompatibleExpressionProducts.group_source_types unique originalFound form metadata.coercions typed
      exact .group metadata form innerFound sourceType (ih innerFound childTyped generated (closed admitted originalFound (by simp [form, ExpressionForm.references])))
  | tuple originalFound form children ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨codes, generated, rfl, metadata⟩ := CompatibleExpressionTuples.of_functions
        originalFound form (policyFor.special _ admitted (.tuple originalFound form children))
        (policyFor.read _ admitted (.tuple originalFound form children)) policyFor.leaf accepted
      obtain ⟨types, childTyped, sourceType⟩ := CompatibleExpressionTuples.source_types
        unique originalFound form metadata.coercions typed
      obtain ⟨count, nodes, certified⟩ := child_certificates unique childTyped generated
        (fun child member childNode code childFound childTyped childAccepted =>
          ih child member childFound childTyped childAccepted
            (closed admitted originalFound (by simp [form, ExpressionForm.references, member])))
      exact .tuple ⟨metadata, form, sourceType⟩
        (CompatibleExpressionConstructors.sequence_of_nodes count nodes
          (fun child code member => (⟨rfl, member⟩ : RecursiveStageTupleMeaning.Entries scope
            (_root_.List.zip _ _) scope child code))) certified
  | @call callId _original _callee _ids _metadata originalFound form calleeSyntax children calleeIH ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have special := policyFor.special _ admitted (.call originalFound form calleeSyntax children)
      have readPolicy := policyFor.read _ admitted (.call originalFound form calleeSyntax children)
      obtain ⟨type, read⟩ := call_read originalFound form special readPolicy accepted
      obtain ⟨compiler⟩ := CallableIndirectCallCertificates.of_functions originalFound form special read form accepted
      have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent compiler readPolicy
      have originalSame := Option.some.inj (compiler.found.symm.trans originalFound)
      have parentTyped : ExpressionHasType source context callId compiler.original.type := by
        simpa [originalSame] using typed
      obtain ⟨parameter, result, types, calleeTyped, argumentsTyped, _bundle, _result⟩ :=
        CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
          compiler parent unique parentTyped
      obtain ⟨calleeNode, contains, sourceType⟩ := calleeTyped.stored_type
      have calleeFound := lookupExpression?_complete unique contains
      have calleeCertified := calleeIH calleeFound (sourceType ▸ calleeTyped) compiler.calleeAccepted
        (closed admitted originalFound (by simp [form, ExpressionForm.references]))
      obtain ⟨count, nodes, certified⟩ := child_certificates unique argumentsTyped compiler.argumentsAccepted
        (fun child member childNode code childFound childTyped childAccepted =>
          ih child member childFound childTyped childAccepted
            (closed admitted originalFound (by simp [form, ExpressionForm.references, member])))
      refine .call compiler (CompatibleExpressionConstructors.sequence_of_nodes count nodes ?_) ?_
      · intro child code member
        exact ⟨rfl, List.mem_cons_of_mem _ member⟩
      · intro child code member
        rcases List.mem_cons.mp member with head | remaining
        · cases head; exact calleeCertified
        · exact certified child code remaining

theorem of_functions {scope : SourceCoreLocalCell.Scope}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Certificate policy body compilation readFuel values source context reasonAt scope id lowered := by
  exact of_functions_on unique declarations (policyFor.on (fun _ => True))
    (fun _ _ _ => trivial) (fun id node _ tree found => coercions id node tree found)
    syntaxTree trivial found typed accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates

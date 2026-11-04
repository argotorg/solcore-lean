import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRecursive
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionContextualConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.ScalarReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements

/-!
# Compatible expressions: typed forms

Certificates and meaning of typed and general expressions.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedCertificates
/-! Successful ordinary Functions lowering extracts the full recursive data
and control tree. Raw constructor/member types come from independent typing;
actual native operand checks select the admitted primitive operation. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTyped
open Core Frontend SourceInference CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open DataPatternValues

private theorem bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked


private def selectedUnary (operator : Syntax.UnaryOp) (operand : Ty) : UnaryOp :=
  if operator = .bitNot && operand = .integer then .integerNot else SourceCorePrimitive.unaryOperator operator
private def selectedMode (operand : Ty) : Mode := if operand = .integer then .integer else .word

private theorem unary_selected {catalog : SourceCoreCompatibleCatalog.Catalog}
    {operator : Syntax.UnaryOp} {operand result : TypeSystem.Ty} {core : UnaryOp} {type : Ty}
    (profile : UnaryProfile operator operand result core) (projected : catalog.project operand = .ok type) :
    selectedUnary operator type = core := by
  cases profile <;> cases projected <;> rfl
private theorem binary_selected {catalog : SourceCoreCompatibleCatalog.Catalog}
    {operator : Syntax.BinaryOp} {operand result : TypeSystem.Ty} {mode : Mode} {type : Ty}
    (profile : BinaryProfile operator operand result mode) (projected : catalog.project operand = .ok type) :
    selectedMode type = mode := by
  cases profile <;> cases projected <;> rfl

private inductive Compound : ExpressionForm → Prop where
  | unary (operator : Syntax.UnaryOp) (operand : ExpressionId) : Compound (.unary operator operand)
  | binary (operator : Syntax.BinaryOp) (left right : ExpressionId) : Compound (.binary left operator right)
  | group (inner : ExpressionId) : Compound (.group inner)
  | pair (left right : ExpressionId) : Compound (.tuple [left, right])
  | conditional (condition thenId elseId : ExpressionId) : Compound (.conditional condition thenId elseId)

private inductive Step (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (context : SourceCoreFunctions.Context) (values : ValuesContext)
    (source : TypedSource) (scope : Scope) (reasonAt : ExpressionId → Word)
    (id : ExpressionId) (node : ExpressionNode) : SourceCoreBasic.LoweredExpr → Prop where
  | unary {operator operand child}
      (form : node.form = .unary operator operand)
      (metadata : Metadata values.checked source id node (selectedUnary operator child.type).resultType)
      (generated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope operand reasonAt = .ok child)
      (operandType : (selectedUnary operator child.type).operandType = child.type) :
      Step policy body fuel context values source scope reasonAt id node
        ⟨(selectedUnary operator child.type).resultType, LocalPrimitiveResults.unary (selectedUnary operator child.type) child.expression⟩
  | binary {operator left right first second}
      (form : node.form = .binary left operator right)
      (metadata : Metadata values.checked source id node ((selectedMode first.type).resultType operator))
      (firstGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope left reasonAt = .ok first)
      (secondGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope right reasonAt = .ok second)
      (leftType : (selectedMode first.type).operandType operator = first.type)
      (rightType : (selectedMode first.type).operandType operator = second.type) :
      Step policy body fuel context values source scope reasonAt id node
        ⟨(selectedMode first.type).resultType operator, (selectedMode first.type).binary operator first.expression second.expression⟩
  | group {inner lowered}
      (form : node.form = .group inner) (metadata : Metadata values.checked source id node lowered.type)
      (generated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope inner reasonAt = .ok lowered) :
      Step policy body fuel context values source scope reasonAt id node lowered
  | pair {left right first second}
      (form : node.form = .tuple [left, right])
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (firstGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope left reasonAt = .ok first)
      (secondGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope right reasonAt = .ok second) :
      Step policy body fuel context values source scope reasonAt id node
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩

  | conditional {condition thenId elseId conditionCode thenCode elseCode type}
      (form : node.form = .conditional condition thenId elseId)
      (metadata : Metadata values.checked source id node type)
      (conditionGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope condition reasonAt = .ok ⟨.bool, conditionCode⟩)
      (thenGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope thenId reasonAt = .ok ⟨type, thenCode⟩)
      (elseGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope elseId reasonAt = .ok ⟨type, elseCode⟩) :
      Step policy body fuel context values source scope reasonAt id node
        ⟨type, LocalControl.choose type conditionCode thenCode elseCode⟩

private theorem step_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (compound : Compound node.form)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) context source scope id reasonAt = .ok lowered) :
    Step policy body fuel context values source scope reasonAt id node lowered := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
      bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) context childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      generalize form : node.form = shape at compound
      cases compound <;> simp only [form, readPolicy, bind, Except.bind, pure, Except.pure] at accepted
    all_goals
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error error => simp [read] at accepted
      | ok pair =>
        obtain ⟨other, type⟩ := pair
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        simp only [read, form] at accepted
        first
        | obtain ⟨child, generated, afterChild⟩ := bind_accepted accepted
          obtain ⟨output, operandChecked, afterOperand⟩ := bind_accepted afterChild
          cases output
          obtain ⟨output, resultChecked, outputEq⟩ := bind_accepted afterOperand
          cases output
          have operandType := ensureType_ok operandChecked
          have resultType := ensureType_ok resultChecked
          subst type
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .unary form metadata generated operandType
        | obtain ⟨first, generated, afterFirst⟩ := bind_accepted accepted
          obtain ⟨second, secondGenerated, afterSecond⟩ := bind_accepted afterFirst
          split at afterSecond <;>
            obtain ⟨output, firstChecked, afterChecked⟩ := bind_accepted afterSecond <;> cases output <;>
            obtain ⟨output, secondChecked, afterSecondChecked⟩ := bind_accepted afterChecked <;> cases output <;>
            obtain ⟨output, resultChecked, outputEq⟩ := bind_accepted afterSecondChecked <;> cases output
          all_goals
            rename_i branch
            have firstType := ensureType_ok firstChecked
            have secondType := ensureType_ok secondChecked
            have resultType := ensureType_ok resultChecked
            subst type
            simp only [pure, Except.pure, Except.ok.injEq] at outputEq
            subst lowered
            simpa only [selectedMode, branch, ↓reduceIte, Mode.binary, Mode.resultType] using (Step.binary form (by simpa only [selectedMode, branch, ↓reduceIte, Mode.resultType] using metadata)
              generated secondGenerated (by simpa only [selectedMode, branch, ↓reduceIte, Mode.operandType] using firstType)
              (by simpa only [selectedMode, branch, ↓reduceIte, Mode.operandType] using secondType))
        | obtain ⟨child, generated, afterChild⟩ := bind_accepted accepted
          obtain ⟨output, checked, outputEq⟩ := bind_accepted afterChild
          cases output
          have same := ensureType_ok checked
          subst type
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .group form metadata generated
        | obtain ⟨first, generated, afterFirst⟩ := bind_accepted accepted
          obtain ⟨second, secondGenerated, afterSecond⟩ := bind_accepted afterFirst
          obtain ⟨output, checked, outputEq⟩ := bind_accepted afterSecond
          cases output
          have same := ensureType_ok checked
          subst type
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .pair form metadata generated secondGenerated
        | obtain ⟨condition, conditionGenerated, afterCondition⟩ := bind_accepted accepted
          obtain ⟨output, conditionChecked, afterChecked⟩ := bind_accepted afterCondition
          cases output
          obtain ⟨thenCode, thenGenerated, afterThen⟩ := bind_accepted afterChecked
          obtain ⟨elseCode, elseGenerated, afterElse⟩ := bind_accepted afterThen
          obtain ⟨output, thenChecked, afterThenChecked⟩ := bind_accepted afterElse
          cases output
          obtain ⟨output, elseChecked, outputEq⟩ := bind_accepted afterThenChecked
          cases output
          have conditionType := ensureType_ok conditionChecked
          have thenType := ensureType_ok thenChecked
          have elseType := ensureType_ok elseChecked
          rcases condition with ⟨conditionType', conditionExpr⟩
          rcases thenCode with ⟨thenType', thenExpr⟩
          rcases elseCode with ⟨elseType', elseExpr⟩
          dsimp only at conditionType thenType elseType
          subst conditionType' thenType' elseType'
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .conditional form metadata conditionGenerated thenGenerated elseGenerated
  · simp [owner, bind, Except.bind] at accepted

structure PolicyFor (policy : SourceCoreFunctions.Policy) (context : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource) (scope : Scope)
    (reasonAt : ExpressionId → Word) : Prop where
  special : ∀ id, Syntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower context child budget source scope id reasonAt) = .ok none
  read : ∀ id, Syntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values



private theorem child_trees
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context} {readFuel : Nat}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source sourceContext ids types)
    (generated : ListRel (Argument values (fun budget source scope id reasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget context source scope id reasonAt)
      fuel source scope reasonAt) (ids.zip types) codes)
    (extract : ∀ id, id ∈ ids → ∀ node code,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok code →
      Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id code) :
    CompatibleExpressionConstructors.Nodes source ids types codes ∧ ∀ id code, (id, code) ∈ ids.zip codes →
      Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id code := by
  induction ids generalizing types codes with
  | nil => cases typed; cases generated; exact ⟨.nil, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      cases generated with
      | @cons _ _ code codes first rest =>
        obtain ⟨node, contains, sourceType⟩ := head.stored_type
        have found := lookupExpression?_complete unique contains
        have child := extract id (by simp) node code found (sourceType ▸ head) first.generated
        obtain ⟨nodes, children⟩ := ih tail rest (fun id member => extract id (by simp [member]))
        refine ⟨.cons ⟨node, found, sourceType⟩ nodes, ?_⟩
        intro other otherCode member
        rcases List.mem_cons.mp member with same | remaining
        · cases same; exact child
        · exact children other otherCode remaining


/-- Actual successful lowering and independent source typing supply every
child certificate. No semantic child assumption is part of this extraction. -/
theorem tree_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
    (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
  | proxy originalFound form =>
    exact .proxy (CompatibleExpressionProxies.certificate_of_functions originalFound form
      (policyFor.special _ (.proxy originalFound form)) (policyFor.read _ (.proxy originalFound form))
      policyFor.leaf accepted)
  | fragment syntaxTree =>
    refine .fragment (CompatibleExpressionRecursive.tree_of_functions unique declarations signatures closed residual ?_ ?_ syntaxTree found typed accepted)
    · exact ⟨fun id child => policyFor.special id (.fragment child),
        fun id child => policyFor.read id (.fragment child), policyFor.lower, policyFor.leaf⟩
    · exact fun id node child => coercions id node (.fragment child)
  | unary originalFound form child ih =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ (.unary originalFound form child)) (policyFor.read _ (.unary originalFound form child)) accepted
      cases step with
      | @unary operator operand compiled otherForm metadata generated inputChecked =>
        obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (form.symm.trans otherForm)
        obtain ⟨childNode, core, childFound, childTyped, profile⟩ :=
          unary_source_types unique originalFound form metadata.coercions metadata.requirements typed
        have childTree := ih childFound childTyped generated
        have chosen := unary_selected profile (childTree.projected childFound)
        rw [chosen] at metadata inputChecked ⊢
        obtain ⟨childType, childCode⟩ := compiled
        dsimp only at inputChecked childTree ⊢
        subst childType
        exact .unary metadata form childFound rfl rfl profile childTree
      | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ => simp [form] at otherForm
  | binary originalFound form leftSyntax rightSyntax leftIH rightIH =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ (.binary originalFound form leftSyntax rightSyntax))
        (policyFor.read _ (.binary originalFound form leftSyntax rightSyntax)) accepted
      cases step with
      | @binary operator left right first second otherForm metadata firstGenerated secondGenerated leftChecked rightChecked =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, mode, leftFound, rightFound, sameType, leftTyped, rightTyped, profile⟩ :=
          binary_source_types unique originalFound form metadata.coercions metadata.requirements typed
        have firstTree := leftIH leftFound leftTyped firstGenerated
        have secondTree := rightIH rightFound rightTyped secondGenerated
        have chosen := binary_selected profile (firstTree.projected leftFound)
        rw [chosen] at metadata leftChecked rightChecked ⊢
        obtain ⟨firstType, leftCode⟩ := first
        obtain ⟨secondType, rightCode⟩ := second
        dsimp only at leftChecked rightChecked firstTree secondTree ⊢
        subst firstType secondType
        exact .binary metadata form leftFound rightFound rfl sameType.symm rfl profile firstTree secondTree
      | unary otherForm _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ => simp [form] at otherForm
  | group originalFound form child ih =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ (.group originalFound form child)) (policyFor.read _ (.group originalFound form child)) accepted
      cases step with
      | group otherForm metadata generated =>
        have same := ExpressionForm.group.inj (form.symm.trans otherForm)
        subst_vars
        obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ :=
          CompatibleExpressionProducts.group_source_types unique originalFound form metadata.coercions typed
        exact .group metadata form innerFound sourceType (ih innerFound childTyped generated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ => simp [form] at otherForm
  | pair originalFound form leftSyntax rightSyntax leftIH rightIH =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ (.pair originalFound form leftSyntax rightSyntax))
        (policyFor.read _ (.pair originalFound form leftSyntax rightSyntax)) accepted
      cases step with
      | pair otherForm metadata firstGenerated secondGenerated =>
        have same := ExpressionForm.tuple.inj (form.symm.trans otherForm)
        simp only [List.cons.injEq, and_true] at same
        obtain ⟨rfl, rfl⟩ := same
        obtain ⟨leftNode, rightNode, leftFound, rightFound, sourceType, leftTyped, rightTyped⟩ :=
          CompatibleExpressionProducts.pair_source_types unique originalFound form metadata.coercions typed
        exact .pair metadata form leftFound rightFound sourceType
          (leftIH leftFound leftTyped firstGenerated) (rightIH rightFound rightTyped secondGenerated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | conditional otherForm _ _ _ _ => simp [form] at otherForm

  | conditional originalFound form conditionSyntax thenSyntax elseSyntax conditionIH thenIH elseIH =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ (.conditional originalFound form conditionSyntax thenSyntax elseSyntax))
        (policyFor.read _ (.conditional originalFound form conditionSyntax thenSyntax elseSyntax)) accepted
      cases step with
      | @conditional condition thenId elseId conditionCode thenCode elseCode type otherForm metadata conditionGenerated thenGenerated elseGenerated =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.conditional.inj (form.symm.trans otherForm)
        obtain ⟨conditionNode, thenNode, elseNode, conditionFound, thenFound, elseFound, conditionType, thenType, elseType,
          conditionTyped, thenTyped, elseTyped⟩ := conditional_source_types unique originalFound form metadata.coercions typed
        exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType
          (conditionIH conditionFound conditionTyped conditionGenerated)
          (thenIH thenFound thenTyped thenGenerated) (elseIH elseFound elseTyped elseGenerated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ => simp [form] at otherForm

  | @constructor id original instantiation ids originalFound form children ih =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨tag, header, codes, rfl, receipt, count, arguments⟩ := constructor_of_functions originalFound form
        (policyFor.special _ (.constructor originalFound form children))
        (policyFor.read _ (.constructor originalFound form children)) policyFor.leaf accepted
      obtain ⟨admissible, argumentsTyped, sourceType⟩ := constructor_source_types unique originalFound form receipt.metadata.coercions typed
      obtain ⟨nodes, childTrees⟩ := child_trees unique argumentsTyped arguments
        (fun id member node code found typed generated => ih id member found typed generated)
      exact .constructor receipt form (admissible.toValid closed residual) count nodes childTrees

  | @member id original base name index originalFound form child ih =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨baseType, baseTyped, projection⟩ := member_source_types unique originalFound form
        (coercions _ _ (.member originalFound form child) originalFound) typed
      obtain ⟨baseNode, contains, sourceType⟩ := baseTyped.stored_type
      have baseFound := lookupExpression?_complete unique contains
      rw [← sourceType] at baseTyped projection
      obtain ⟨identity, branches, result, code, rfl, metadata, baseMetadata, layout, generated⟩ :=
        member_of_functions signatures originalFound baseFound form projection
          (policyFor.special _ (.member originalFound form child))
          (policyFor.read _ (.member originalFound form child)) policyFor.leaf accepted
      exact .member metadata baseMetadata form layout (ih baseFound baseTyped generated)
  | @index id original base key keyNode originalFound form keyFound scalar firstSyntax secondSyntax firstIH secondIH =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have syntaxTree : Syntax source id := .index originalFound form keyFound scalar firstSyntax secondSyntax
      obtain ⟨keyType, baseTyped, keyTyped⟩ := CompatibleExpressionIndices.index_source_types unique originalFound form
        (coercions _ _ syntaxTree originalFound) typed
      obtain ⟨baseNode, baseContains, baseType⟩ := baseTyped.stored_type
      obtain ⟨actualKeyNode, keyContains, actualKeyType⟩ := keyTyped.stored_type
      have keySame := Option.some.inj ((lookupExpression?_complete unique keyContains).symm.trans keyFound)
      subst actualKeyNode
      have baseFound := lookupExpression?_complete unique baseContains
      rw [← actualKeyType] at keyTyped baseType baseTyped
      rw [← baseType] at baseTyped
      obtain ⟨layout, comparison, first, second, rfl, header, firstGenerated, secondGenerated⟩ :=
        CompatibleExpressionIndices.index_of_functions originalFound baseFound form
          (policyFor.special _ syntaxTree) (policyFor.read _ syntaxTree) policyFor.leaf accepted
      exact .index header keyFound form baseType scalar (firstIH baseFound baseTyped firstGenerated)
        (secondIH keyFound keyTyped secondGenerated)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTyped
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualTyped
/-! The actual contextual dispatcher supplies the ordinary recursive data/control policy.
Static occurrence metadata excludes local specialization and output coercions.
The final receipt contains no child lowering or runtime execution hypothesis. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTyped
open Core Frontend SourceInference

/-- Metadata for the ordinary fragment in this source view. Conditions apply
only to occurrences admitting the finite grammar, not arbitrary source forms. -/
structure Ordinary (source : TypedSource) (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceSpecialization.SpecializationKey) : Prop where
  requirements : ∀ id node, Syntax source id → source.lookupExpression? id = some node →
    node.requirements = CompatibleExpressionLiterals.owned node.form
  coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = []
  notInitializer : ∀ id, Syntax source id → locals.bindings.find?
    (fun binding => decide (binding.caller = owner ∧ binding.initializer = id)) = none
  localBinder : ∀ id node name binder, Syntax source id → source.lookupExpression? id = some node →
    node.form = .reference name (.local binder) →
    locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false

private theorem contextualSource_fragment
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    (ordinary : Ordinary source locals owner) (syntaxTree : Syntax source id) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  cases syntaxTree with
  | fragment oldRecursive =>
    cases oldRecursive with
    | fragment oldMember =>
      cases oldMember with
        | fragment old =>
          cases old with
            | fragment child =>
              cases child with
              | primitive syntaxTree =>
                cases syntaxTree with
                | product syntaxTree =>
                  cases syntaxTree with
                  | @literal _ literalNode found atomic =>
                    generalize form : literalNode.form = shape at atomic
                    cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
                  | read found form =>
                    have localBinder := ordinary.localBinder _ _ _ _ (.fragment (.fragment (.fragment (.fragment (.primitive (.product (.read found form))))))) found form
                    simp only [SourceCoreGeneralFunctions.contextualSource, found, form, localBinder, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]
                  | group found form child => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
                  | pair found form first second => simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
                | unary found form child | binary found form first second | group found form child | pair found form first second =>
                  simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
              | unary found form child | binary found form first second | group found form child | pair found form first second | conditional found form _ _ _ =>
                simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

            | constructor found form _ =>
              simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
        | member found form _ =>
          simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
    | unary found form _ | binary found form _ _ | group found form _ | pair found form _ _ | conditional found form _ _ _ | constructor found form _ | member found form _ =>
        simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]
  | proxy found form | unary found form _ | binary found form _ _ | group found form _ | pair found form _ _ | conditional found form _ _ _ | constructor found form _ | member found form _ | index found form _ _ _ _ =>
      simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

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
  | fragment oldRecursive =>
    cases oldRecursive with
    | fragment oldMember =>
      cases oldMember with
        | fragment old =>
          cases old with
            | fragment child =>
              cases child with
              | primitive syntaxTree =>
                cases syntaxTree with
                | product syntaxTree =>
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
                | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ =>
                  have same := Option.some.inj (originalFound.symm.trans found)
                  subst node
                  simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
                    CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
              | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ | conditional originalFound form _ _ _ =>
                have same := Option.some.inj (originalFound.symm.trans found)
                subst node
                simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
                  CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

            | constructor originalFound form _ =>
              have same := Option.some.inj (originalFound.symm.trans found)
              subst node
              simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
                CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
        | member originalFound form _ =>
          have same := Option.some.inj (originalFound.symm.trans found)
          subst node
          simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
            CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
    | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ | conditional originalFound form _ _ _ | constructor originalFound form _ | member originalFound form _ =>
        have same := Option.some.inj (originalFound.symm.trans found)
        subst node
        simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
          CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
  | proxy originalFound form | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ | conditional originalFound form _ _ _ | constructor originalFound form _ | member originalFound form _ | index originalFound form _ _ _ _ =>
      have same := Option.some.inj (originalFound.symm.trans found)
      subst node
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
        CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

private theorem fragment_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : Syntax source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases syntaxTree with
  | fragment oldRecursive =>
    cases oldRecursive with
    | fragment oldMember =>
      cases oldMember with
        | fragment old =>
          cases old with
            | fragment child =>
              cases child with
              | primitive syntaxTree =>
                cases syntaxTree with
                | product child => cases child <;> exact ⟨_, by assumption⟩
                | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ => exact ⟨_, found⟩
              | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ | conditional found _ _ _ _ => exact ⟨_, found⟩

            | constructor found _ _ => exact ⟨_, found⟩
        | member found _ _ => exact ⟨_, found⟩
    | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ | conditional found _ _ _ _ | constructor found _ _ | member found _ _ => exact ⟨_, found⟩
  | proxy found _ | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ | conditional found _ _ _ _ | constructor found _ _ | member found _ _ | index found _ _ _ _ _ => exact ⟨_, found⟩

private theorem context_bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Recursive data/control trees are extracted from the production
contextual traversal, at root or full specialized parent context. -/
theorem tree_of_contextual
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
    (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (sourceSignatures : sourceContext.signatures = values.checked.signatures)
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine tree_of_functions unique declarations sourceSignatures closed residual ?_ ordinary.coercions syntaxTree found typed accepted
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
      refine tree_of_functions unique declarations sourceSignatures closed residual ?_ ordinary.coercions syntaxTree found typed generated
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

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTyped
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedMeaning
/-! Arbitrarily nested data/control/scalar-key index expressions use actual
runtime typing for every generated comparator capture. Recursive induction
closes all child meanings against the common ambient heap relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTyped
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open CompatibleExpressionIndices CoreProof
open GenericExpressionMeaning (agree_prefix rename_prefix)
open DataPatternValues

private def Entries (scope : Scope) (entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)) :
    GenericExpressionMeaning.Certificate := fun current id code => current = scope ∧ (id, code) ∈ entries

private def Children (scope : Scope) (ids : List ExpressionId) (codes : List SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate := fun current id code => current = scope ∧ (id, code) ∈ ids.zip codes

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
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension valid unique uninitialized missing in
theorem preserves :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  induction tree with
  | proxy receipt => exact CompatibleExpressionProxies.preserves functions extension program context evidence unique faults receipt
  | fragment child =>
    exact TypedGenericExpressionMeaning.preserves_of_unrestricted
      (CompatibleExpressionRecursive.preserves functions extension program evidence valid unique uninitialized) child
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    have meaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(inner, lowered)]) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩
      · exact ih
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves functions program evidence unique meaning (.group metadata form innerFound sourceType (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree leftIH rightIH =>
    have meaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(left, first), (right, second)]) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves functions program evidence unique meaning (.pair metadata form leftFound rightFound sourceType (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @unary id node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child ih =>
    have meaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(operand, ⟨core.operandType, childCode⟩)]) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩
      · exact ih
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves functions program evidence unique meaning (.unary (childCode := childCode) metadata form childFound inputType outputType profile (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile firstTree secondTree leftIH rightIH =>
    have meaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(left, ⟨mode.operandType operator, leftCode⟩), (right, ⟨mode.operandType operator, rightCode⟩)]) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves functions program evidence unique meaning (.binary (leftCode := leftCode) (rightCode := rightCode) metadata form leftFound rightFound leftType rightType outputType profile (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionIH thenIH elseIH =>
    have meaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact conditionIH
      · exact thenIH
      · exact elseIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves functions program evidence unique meaning (.conditional (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) metadata form conditionFound thenFound elseFound conditionType thenType elseType (⟨rfl, by simp⟩) (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children ih =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have meaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Children scope ids codes) faults := by
      intro current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member
    have sequence := sequence_of_nodes (scope := scope) (certificate := Children scope ids codes) count nodes (fun id code member => (⟨rfl, member⟩ : Children scope ids codes scope id code))
    obtain ⟨sourceOutcome, sourceTrace, packed⟩ := constructor_inv receipt.metadata form unique valid trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
      TypedDataExpressionSequence.preserves sequence meaning environments heaps locals agrees actualTyped sourceTrace
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

  | @member id node base baseNode name index identity branches result child metadata baseMetadata form layout childTree ih =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have raw := member_inv metadata form unique trace
    cases raw with
    | value childTrace selected =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped (.value childTrace)
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
        ih baseMetadata.found environments heaps locals agrees actualTyped (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact LanguageResult.bind_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | shape childTrace invalid =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, _⟩ := member_success layout payload evaluated
        subst_vars
        exact False.elim (invalid .intro)
    | position childTrace missing =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, selected, _⟩ := member_success layout payload evaluated
        cases shape
        exact False.elim (missing_excludes missing selected)

  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType scalar firstTree secondTree firstIH secondIH =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rcases (index_inv header.metadata form unique trace).split with ⟨reason, rfl, failed⟩ | ⟨baseSource, middle, baseTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
        rw [index_rename comparison header.registered header.comparisonType]
        exact LanguageResult.bind_failure _ evaluated
    · obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped (.value baseTrace)
      cases represented with
      | @value _ baseValue baseRep =>
        have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
        rcases tail with ⟨reason, rfl, failed⟩ | ⟨keySource, keyTrace, terminal⟩
        · obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (.fault failed)
          cases represented with
          | fault matched =>
            refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            exact LanguageResult.bind_success _ firstEval (LanguageResult.bind_failure _ secondEval)
        · obtain ⟨value, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (.value keyTrace)
          cases represented with
          | @value _ keyValue keyRep =>
            obtain ⟨actualOutcome, result, finalStore, finalWorld, terminal', related, lookup, finalHeaps, worlds, frame, uniqueResult⟩ :=
              header.finish sourceType scalar (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
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


include extension valid uninitialized missing in
theorem reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  induction tree with
  | proxy receipt => exact CompatibleExpressionProxies.reflects functions extension program context evidence faults receipt
  | fragment child =>
    exact TypedGenericExpressionMeaning.reflects_of_unrestricted
      (CompatibleExpressionRecursive.reflects functions extension program evidence valid uninitialized) child
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    have meaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(inner, lowered)]) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩
      · exact ih
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects functions program evidence meaning (.group metadata form innerFound sourceType (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree leftIH rightIH =>
    have meaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(left, first), (right, second)]) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects functions program evidence meaning (.pair metadata form leftFound rightFound sourceType (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @unary id node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child ih =>
    have meaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(operand, ⟨core.operandType, childCode⟩)]) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩
      · exact ih
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects functions program evidence meaning (.unary (childCode := childCode) metadata form childFound inputType outputType profile (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile firstTree secondTree leftIH rightIH =>
    have meaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(left, ⟨mode.operandType operator, leftCode⟩), (right, ⟨mode.operandType operator, rightCode⟩)]) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects functions program evidence meaning (.binary (leftCode := leftCode) (rightCode := rightCode) metadata form leftFound rightFound leftType rightType outputType profile (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionIH thenIH elseIH =>
    have meaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) faults := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact conditionIH
      · exact thenIH
      · exact elseIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects functions program evidence meaning (.conditional (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) metadata form conditionFound thenFound elseFound conditionType thenType elseType (⟨rfl, by simp⟩) (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children ih =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have meaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Children scope ids codes) faults := by
      intro current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member
    have sequence := sequence_of_nodes (scope := scope) (certificate := Children scope ids codes) count nodes (fun id code member => (⟨rfl, member⟩ : Children scope ids codes scope id code))
    rw [CompatibleExpressionConstructors.construct_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        TypedDataExpressionSequence.reflects sequence meaning environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_failure tag header childEvaluation)
        exact ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace (.fault _),
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        TypedDataExpressionSequence.reflects sequence meaning environments heaps locals agrees actualTyped childEvaluation
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

  | @member id node base baseNode name index identity branches result child metadata baseMetadata form layout childTree ih =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [member_rename layout] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
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
        ih baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, selected, native, shape, sourceAt, related, expected⟩ := member_success layout payload baseEvaluation
        subst_vars
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.value childTrace sourceAt), .value related,
            finalHeaps, maps, worlds, frame, heapMetadata⟩

  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType scalar firstTree secondTree firstIH secondIH =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
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
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
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
                (agree_prefix agrees _) keyEnvironment keyEvaluation
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
                (agree_prefix agrees _) keyEnvironment keyEvaluation
            cases represented with
            | @value keySource keyValue keyRep =>
              obtain ⟨outcome, result, endStore, finalWorld, terminal, related, lookup, finalHeaps, worlds, frame, uniqueResult⟩ :=
                header.finish sourceType scalar (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
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


end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTyped
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralMeaning
/-! Arbitrarily nested data/control/general-key index expressions use actual
runtime typing for every generated comparator capture. Recursive induction
closes all child meanings against the common ambient heap relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneral
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open CompatibleExpressionIndices CoreProof
open GenericExpressionMeaning (agree_prefix rename_prefix)
open DataPatternValues

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : Scope}

/-- Static leaf support indexes the existing tree and its exact children.
It contains only leaf membership, with no execution or heap law. -/
inductive Tree.LiteralSites (literals : GenericExpressionMeaning.Certificate) :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Tree fuel values source context solved reasonAt scope id lowered → Prop where
  | proxy {id lowered} (receipt : CompatibleExpressionProxies.Certificate values source scope id lowered)
      :
      LiteralSites literals (Tree.proxy (scope := scope) receipt)
  | fragment {id lowered}
      (child : CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope id lowered)
      (childSites : CompatibleExpressionRecursive.Tree.LiteralSites literals child) :
      LiteralSites literals (Tree.fragment (scope := scope) child)
  | group {id node inner innerNode lowered}
      (metadata : Metadata values.checked source id node lowered.type)
      (form : node.form = .group inner) (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Tree fuel values source context solved reasonAt scope inner lowered)
      (childSites : Tree.LiteralSites literals child) :
      LiteralSites literals (Tree.group (scope := scope) metadata form innerFound sourceType child)
  | pair {id node left right leftNode rightNode first second}
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode) (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (firstTree : Tree fuel values source context solved reasonAt scope left first)
      (secondTree : Tree fuel values source context solved reasonAt scope right second)
      (firstTreeSites : Tree.LiteralSites literals firstTree) (secondTreeSites : Tree.LiteralSites literals secondTree) :
      LiteralSites literals (Tree.pair (scope := scope) metadata form leftFound rightFound sourceType firstTree secondTree)
  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : Metadata values.checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : UnaryProfile operator operandType resultType core)
      (child : Tree fuel values source context solved reasonAt scope operand ⟨core.operandType, childCode⟩)
      (childSites : Tree.LiteralSites literals child) :
      LiteralSites literals (Tree.unary (scope := scope) metadata form found inputType outputType profile child)
  | binary {id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      (metadata : Metadata values.checked source id node (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = operandType)
      (outputType : node.type = resultType)
      (profile : BinaryProfile operator operandType resultType mode)
      (first : Tree fuel values source context solved reasonAt scope left ⟨mode.operandType operator, leftCode⟩)
      (second : Tree fuel values source context solved reasonAt scope right ⟨mode.operandType operator, rightCode⟩)
      (firstSites : Tree.LiteralSites literals first) (secondSites : Tree.LiteralSites literals second) :
      LiteralSites literals (Tree.binary (scope := scope) metadata form leftFound rightFound leftType rightType outputType profile first second)
  | conditional {id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      (metadata : Metadata values.checked source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (thenFound : source.lookupExpression? thenId = some thenNode)
      (elseFound : source.lookupExpression? elseId = some elseNode)
      (conditionType : conditionNode.type = .bool)
      (thenType : thenNode.type = node.type) (elseType : elseNode.type = node.type)
      (conditionTree : Tree fuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree fuel values source context solved reasonAt scope thenId ⟨type, thenCode⟩)
      (elseTree : Tree fuel values source context solved reasonAt scope elseId ⟨type, elseCode⟩)
      (conditionTreeSites : Tree.LiteralSites literals conditionTree) (thenTreeSites : Tree.LiteralSites literals thenTree) (elseTreeSites : Tree.LiteralSites literals elseTree) :
      LiteralSites literals (Tree.conditional (scope := scope) metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree)
  | constructor {id node instantiation ids tag header codes}
      (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
      (form : node.form = .constructor instantiation ids)
      (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
      (count : ids.length = instantiation.payloadTypes.length)
      (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
      (children : ∀ child code, (child, code) ∈ ids.zip codes →
        Tree fuel values source context solved reasonAt scope child code)
      (childrenSites : ∀ child code (member : (child, code) ∈ ids.zip codes),
        Tree.LiteralSites literals (children child code member)) :
      LiteralSites literals (Tree.constructor (scope := scope) receipt form valid count nodes children)
  | member {id node base baseNode name index identity branches result child}
      (metadata : Metadata values.checked source id node result)
      (baseMetadata : Metadata values.checked source base baseNode child.type)
      (form : node.form = .member base name index)
      (layout : CompatibleExpressionMembers.Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result)
      (childTree : Tree fuel values source context solved reasonAt scope base child)
      (childTreeSites : Tree.LiteralSites literals childTree) :
      LiteralSites literals (Tree.member (scope := scope) metadata baseMetadata form layout childTree)
  | index {id node base key baseNode keyNode layout comparison first second}
      (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (firstTree : Tree fuel values source context solved reasonAt scope base first)
      (secondTree : Tree fuel values source context solved reasonAt scope key second)
      (firstTreeSites : Tree.LiteralSites literals firstTree) (secondTreeSites : Tree.LiteralSites literals secondTree) :
      LiteralSites literals (Tree.index (scope := scope) header keyFound form sourceType firstTree secondTree)

/-- The exact old tree restricted to the supplied static leaf certificates. -/
def Tree.WithLiterals (literals : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun current id lowered => ∃ tree : Tree fuel values source context solved reasonAt current id lowered,
    tree.LiteralSites literals

/-- Ordinary literal membership supplies support for every original tree. -/
theorem Tree.literalSites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree fuel values source context solved reasonAt scope id lowered) :
    tree.LiteralSites (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code) := by
  induction tree with
  | proxy receipt => exact .proxy receipt
  | fragment child => exact .fragment child child.literalSites
  | group metadata form innerFound sourceType child childIH => exact .group metadata form innerFound sourceType child childIH
  | pair metadata form leftFound rightFound sourceType firstTree secondTree firstTreeIH secondTreeIH => exact .pair metadata form leftFound rightFound sourceType firstTree secondTree firstTreeIH secondTreeIH
  | unary metadata form found inputType outputType profile child childIH => exact .unary metadata form found inputType outputType profile child childIH
  | binary metadata form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH => exact .binary metadata form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH
  | conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeIH thenTreeIH elseTreeIH => exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeIH thenTreeIH elseTreeIH
  | constructor receipt form valid count nodes children childrenIH => exact .constructor receipt form valid count nodes children childrenIH
  | member metadata baseMetadata form layout childTree childTreeIH => exact .member metadata baseMetadata form layout childTree childTreeIH
  | index header keyFound form sourceType firstTree secondTree firstTreeIH secondTreeIH => exact .index header keyFound form sourceType firstTree secondTree firstTreeIH secondTreeIH

private def Entries (scope : Scope) (entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)) :
    GenericExpressionMeaning.Certificate := fun current id code => current = scope ∧ (id, code) ∈ entries

private def Children (scope : Scope) (ids : List ExpressionId) (codes : List SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate := fun current id code => current = scope ∧ (id, code) ∈ ids.zip codes

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
  {literals : GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension unique in
theorem preserves_with_literals_and_post
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (constructorJoins : ScalarConstructorFaultPostContracts.Joins post listPost values program context evidence source)
    (memberJoins : ScalarMemberFaultPostContracts.Joins post values program context evidence source)
    (indexJoins : IndexFaultPostContracts.IndexJoins post values program context evidence source)
    (literalMeaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults post)
    (readMeaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults post)
    (proxyMeaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionProxies.Certificate values source) faults post)
    (terminalProvider : IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt (fun _ => True) faults post) :
    ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults post := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | proxy receipt => exact proxyMeaning receipt
  | fragment child childSites =>
    exact ReachedLoweredReadOutcomePorts.typed_preserves_of_unrestricted
      (CompatibleExpressionRecursive.preserves_with_literals_and_post functions extension program evidence unique sequenceJoins ordinaryJoins constructorJoins memberJoins literalMeaning readMeaning) ⟨child, childSites⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(inner, lowered)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩
      · exact ih
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves_with_post functions program evidence unique sequenceJoins ordinaryJoins meaning (.group metadata form innerFound sourceType (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree firstTreeSites secondTreeSites leftIH rightIH =>
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(left, first), (right, second)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves_with_post functions program evidence unique sequenceJoins ordinaryJoins meaning (.pair metadata form leftFound rightFound sourceType (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @unary id node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child childSites ih =>
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(operand, ⟨core.operandType, childCode⟩)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩
      · exact ih
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves_with_post functions program evidence unique sequenceJoins ordinaryJoins meaning (.unary (childCode := childCode) metadata form childFound inputType outputType profile (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile firstTree secondTree firstSites secondSites leftIH rightIH =>
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(left, ⟨mode.operandType operator, leftCode⟩), (right, ⟨mode.operandType operator, rightCode⟩)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves_with_post functions program evidence unique sequenceJoins ordinaryJoins meaning (.binary (leftCode := leftCode) (rightCode := rightCode) metadata form leftFound rightFound leftType rightType outputType profile (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeSites thenTreeSites elseTreeSites conditionIH thenIH elseIH =>
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact conditionIH
      · exact thenIH
      · exact elseIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    exact CompatibleExpressionTypedCompositions.Head.preserves_with_post functions program evidence unique sequenceJoins ordinaryJoins meaning (.conditional (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) metadata form conditionFound thenFound elseFound conditionType thenType elseType (⟨rfl, by simp⟩) (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped trace
  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children childrenSites ih =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Children scope ids codes) faults post := by
      intro current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member
    have sequence := sequence_of_nodes (scope := scope) (certificate := Children scope ids codes) count nodes (fun id code member => (⟨rfl, member⟩ : Children scope ids codes scope id code))
    obtain ⟨sourceOutcome, sourceTrace, packed⟩ := constructor_inv receipt.metadata form unique valid trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      TypedDataExpressionSequence.preserves_with_post sequence sequenceJoins meaning environments heaps locals agrees actualTyped sourceTrace
    cases represented with
    | @values sources payloadValues payloads =>
      cases packed
      have projected := receipt.metadata.projected
      rw [receipt.sourceType] at projected
      refine ⟨.inRight .word (.constructed tag (.pair (.word header) (packValues payloadValues))), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
      · rw [CompatibleExpressionConstructors.construct_rename]; exact CompatibleExpressionConstructors.construct_success tag header evaluated
      · rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
          receipt.selected projected receipt.registered (valuesRep payloads))
    | fault matched =>
      cases packed
      cases sourceTrace with
      | fault failed =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [CompatibleExpressionConstructors.construct_rename]; exact CompatibleExpressionConstructors.construct_failure tag header evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          ScalarConstructorFaultPostContracts.arguments_fault_outcome constructorJoins
            receipt form valid count nodes failed retained⟩

  | @member id node base baseNode name index identity branches result child metadata baseMetadata form layout childTree childTreeSites ih =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have raw := member_inv metadata form unique trace
    cases raw with
    | value childTrace selected =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, sourceChild, native, shape, sourceAt, related, completed⟩ := member_success layout payload evaluated
        cases shape
        have same := at_functional sourceAt selected
        subst sourceChild
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact completed,
          .value related, finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
    | failure childTrace =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact LanguageResult.bind_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          ScalarMemberFaultPostContracts.base_fault_outcome memberJoins metadata baseMetadata form layout childTrace retained⟩
    | shape childTrace invalid =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, _⟩ := member_success layout payload evaluated
        subst_vars
        exact False.elim (invalid .intro)
    | position childTrace missing =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, selected, _⟩ := member_success layout payload evaluated
        cases shape
        exact False.elim (missing_excludes missing selected)

  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree firstTreeSites secondTreeSites firstIH secondIH =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rcases (index_inv header.metadata form unique trace).split with ⟨reason, rfl, failed⟩ | ⟨baseSource, middle, baseTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, metadata,
          indexJoins.base_outcome header keyFound form sourceType failed retained⟩
        rw [index_rename comparison header.registered header.comparisonType]
        exact LanguageResult.bind_failure _ evaluated
    · obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped (.value baseTrace)
      cases represented with
      | @value _ baseValue baseRep =>
        have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
        rcases tail with ⟨reason, rfl, failed⟩ | ⟨keySource, keyTrace, terminal⟩
        · obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (.fault failed)
          cases represented with
          | fault matched =>
            refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
              indexJoins.key_outcome header keyFound form sourceType baseTrace failed retained⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            exact LanguageResult.bind_success _ firstEval (LanguageResult.bind_failure _ secondEval)
        · obtain ⟨value, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, _keyPost⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (.value keyTrace)
          cases represented with
          | @value _ keyValue keyRep =>
            obtain ⟨actualOutcome, result, finalStore, finalWorld, terminal', related, lookup, finalHeaps, worlds, frame, uniqueResult, _parentTrace, terminalPost⟩ :=
              terminalProvider header sourceType trivial (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace keyTrace
            have same := uniqueResult outcome terminal
            subst actualOutcome
            refine ⟨result, finalStore, keyMap, finalWorld, ?_, related, finalHeaps,
              firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
              (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, terminalPost⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            apply SourceCoreCompatibleDataExpressions.index_completed layout (reasonAt id) firstEval secondEval
            simpa only [CompatibleMapping.Transport.expression_weaken] using lookup


include extension faithful functionLeaves functionTypes unique uninitialized missing in
theorem preserves_with_literals
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.TypedPreserves.forget
    (preserves_with_literals_and_post (functions := functions) (extension := extension) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence) (unique := unique)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source)
      (ExpressionFailurePostContracts.Preserves.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Preserves.of_trivial
        (certificate := CompatibleExpressionReads.LoweredRead fuel values source context reasonAt)
        (by
          intro scope id lowered receipt
          exact CompatibleExpressionReads.loweredRead_preserves functions extension program context evidence reasonAt uninitialized unique receipt))
      (ExpressionFailurePostContracts.TypedPreserves.of_trivial
        (CompatibleExpressionProxies.preserves functions extension program context evidence unique faults))
      (IndexFaultPostContracts.trivial_general_terminal functions registry program context evidence reasonAt
        faithful functionLeaves functionTypes missing))

include extension faithful functionLeaves functionTypes valid unique uninitialized missing in
theorem preserves :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact preserves_with_literals functions extension faithful functionLeaves functionTypes program evidence unique uninitialized missing
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults) ⟨tree, tree.literalSites⟩

include extension in
theorem reflects_with_literals_and_post
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (constructorJoins : ScalarConstructorFaultPostContracts.Joins post listPost values program context evidence source)
    (memberJoins : ScalarMemberFaultPostContracts.Joins post values program context evidence source)
    (indexJoins : IndexFaultPostContracts.IndexJoins post values program context evidence source)
    (literalMeaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults post)
    (readMeaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults post)
    (proxyMeaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionProxies.Certificate values source) faults post)
    (terminalProvider : IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt (fun _ => True) faults post) :
    ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults post := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | proxy receipt => exact proxyMeaning receipt
  | fragment child childSites =>
    exact ReachedLoweredReadOutcomePorts.typed_reflects_of_unrestricted
      (CompatibleExpressionRecursive.reflects_with_literals_and_post functions extension program evidence sequenceJoins ordinaryJoins constructorJoins memberJoins literalMeaning readMeaning) ⟨child, childSites⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(inner, lowered)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩
      · exact ih
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects_with_post functions program evidence sequenceJoins ordinaryJoins meaning (.group metadata form innerFound sourceType (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree firstTreeSites secondTreeSites leftIH rightIH =>
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(left, first), (right, second)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects_with_post functions program evidence sequenceJoins ordinaryJoins meaning (.pair metadata form leftFound rightFound sourceType (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @unary id node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child childSites ih =>
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(operand, ⟨core.operandType, childCode⟩)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩
      · exact ih
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects_with_post functions program evidence sequenceJoins ordinaryJoins meaning (.unary (childCode := childCode) metadata form childFound inputType outputType profile (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile firstTree secondTree firstSites secondSites leftIH rightIH =>
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(left, ⟨mode.operandType operator, leftCode⟩), (right, ⟨mode.operandType operator, rightCode⟩)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects_with_post functions program evidence sequenceJoins ordinaryJoins meaning (.binary (leftCode := leftCode) (rightCode := rightCode) metadata form leftFound rightFound leftType rightType outputType profile (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeSites thenTreeSites elseTreeSites conditionIH thenIH elseIH =>
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Entries scope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at alternatives
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact conditionIH
      · exact thenIH
      · exact elseIH
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    exact CompatibleExpressionTypedCompositions.Head.reflects_with_post functions program evidence sequenceJoins ordinaryJoins meaning (.conditional (conditionCode := conditionCode) (thenCode := thenCode) (elseCode := elseCode) metadata form conditionFound thenFound elseFound conditionType thenType elseType (⟨rfl, by simp⟩) (⟨rfl, by simp⟩) (⟨rfl, by simp⟩)) found environments heaps locals agrees actualTyped evaluated
  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children childrenSites ih =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Children scope ids codes) faults post := by
      intro current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member
    have sequence := sequence_of_nodes (scope := scope) (certificate := Children scope ids codes) count nodes (fun id code member => (⟨rfl, member⟩ : Children scope ids codes scope id code))
    rw [CompatibleExpressionConstructors.construct_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        TypedDataExpressionSequence.reflects_with_post sequence sequenceJoins meaning environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_failure tag header childEvaluation)
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid (.fault failed) (.fault _),
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
            ScalarConstructorFaultPostContracts.arguments_fault_outcome constructorJoins
              receipt form valid count nodes failed retained⟩
    | caseRight childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        TypedDataExpressionSequence.reflects_with_post sequence sequenceJoins meaning environments heaps locals agrees actualTyped childEvaluation
      cases represented with
      | values payloads =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (CompatibleExpressionConstructors.construct_success tag header childEvaluation)
        have projected := receipt.metadata.projected
        rw [receipt.sourceType] at projected
        refine ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace (.values _),
          ?_, finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
        rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
          receipt.selected projected receipt.registered (valuesRep payloads))

  | @member id node base baseNode name index identity branches result child metadata baseMetadata form layout childTree childTreeSites ih =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [member_rename layout] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure result baseEvaluation (body := .matchData identity (LanguageResult.resultType result) (.var 0) branches)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.failure failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata,
            ScalarMemberFaultPostContracts.base_fault_outcome memberJoins metadata baseMetadata form layout failed retained⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, selected, native, shape, sourceAt, related, expected⟩ := member_success layout payload baseEvaluation
        subst_vars
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.value childTrace sourceAt), .value related,
            finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩

  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree firstTreeSites secondTreeSites firstIH secondIH =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | fault matched =>
        have expected := LanguageResult.bind_failure layout.valueType baseEvaluation (body :=
          LanguageResult.bind layout.valueType ((second.expression.rename ξ).weakenAt 0)
            (SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.baseFailure failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
            indexJoins.base_outcome header keyFound form sourceType failed retained⟩
    | caseRight baseEvaluation branch =>
      obtain ⟨outcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped baseEvaluation
      cases represented with
      | @value baseSource baseValue baseRep =>
        cases trace with
        | value baseTrace =>
          have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
          cases branch with
          | caseLeft keyEvaluation ignored =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, retained⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment keyEvaluation
            cases represented with
            | fault matched =>
              rw [rename_prefix] at keyEvaluation
              have expected := LanguageResult.bind_success layout.valueType baseEvaluation
                (LanguageResult.bind_failure layout.valueType keyEvaluation (body :=
                  SourceCoreMappingWithDefault.lookup layout (reasonAt id) (comparison.expression.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
              cases trace with
              | fault failed => exact ⟨_, after, finalMap, finalWorld, index_intro header.metadata form (.keyFailure baseTrace failed),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                  indexJoins.key_outcome header keyFound form sourceType baseTrace failed retained⟩
          | caseRight keyEvaluation lookupEvaluation =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, keyMap, keyWorld, trace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, _keyPost⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment keyEvaluation
            cases represented with
            | @value keySource keyValue keyRep =>
              cases trace with
              | value keyTrace =>
                obtain ⟨outcome, result, endStore, finalWorld, terminal, related, lookup, finalHeaps, worlds, frame, uniqueResult, _parentTrace, terminalPost⟩ :=
                  terminalProvider header sourceType trivial (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                    (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace keyTrace
                rw [rename_prefix] at keyEvaluation
                have expected := SourceCoreCompatibleDataExpressions.index_completed (comparison := comparison.expression) layout (reasonAt id) baseEvaluation keyEvaluation
                  (by simpa only [CompatibleMapping.Transport.expression_weaken] using lookup)
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
                exact ⟨outcome, after, keyMap, finalWorld, index_intro header.metadata form (terminal.trace baseTrace keyTrace),
                  related, finalHeaps, firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
                  (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, terminalPost⟩


include extension faithful functionLeaves functionTypes uninitialized missing in
theorem reflects_with_literals
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.TypedReflects.forget
    (reflects_with_literals_and_post (functions := functions) (extension := extension) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source)
      (ExpressionFailurePostContracts.Reflects.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Reflects.of_trivial
        (certificate := CompatibleExpressionReads.LoweredRead fuel values source context reasonAt)
        (by
          intro scope id lowered receipt
          exact CompatibleExpressionReads.loweredRead_reflects functions extension program context evidence reasonAt uninitialized receipt))
      (ExpressionFailurePostContracts.TypedReflects.of_trivial
        (CompatibleExpressionProxies.reflects functions extension program context evidence faults))
      (IndexFaultPostContracts.trivial_general_terminal functions registry program context evidence reasonAt
        faithful functionLeaves functionTypes missing))

include extension faithful functionLeaves functionTypes valid uninitialized missing in
theorem reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact reflects_with_literals functions extension faithful functionLeaves functionTypes program evidence uninitialized missing
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults) ⟨tree, tree.literalSites⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneral
end

import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionTyped
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRecursive
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionContextualConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Statements
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionIndices
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Encoding
import Solcore.Core.Internal.Renaming

/-!
# Compatible expressions: general forms and builtins

Certificates and native typing of general expressions and builtins.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralCertificates
/-! Successful ordinary Functions lowering extracts the full recursive data
and control tree. Raw constructor/member types come from independent typing;
actual native operand checks select the admitted primitive operation. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneral
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



private theorem child_certificates
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {certificate : ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source sourceContext ids types)
    (generated : ListRel (Argument values (fun budget source scope id reasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget context source scope id reasonAt)
      fuel source scope reasonAt) (ids.zip types) codes)
    (extract : ∀ id, id ∈ ids → ∀ node code,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok code →
      certificate id code) :
    CompatibleExpressionConstructors.Nodes source ids types codes ∧ ∀ id code, (id, code) ∈ ids.zip codes →
      certificate id code := by
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
  exact child_certificates unique typed generated extract

/-- Actual successful lowering and independent source typing supply every
child certificate. No semantic child assumption is part of this extraction. -/
theorem tree_of_functions_with_literals
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (literals : GenericExpressionMeaning.Certificate)
    (literalFactory : CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt literals)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree.WithLiterals (fuel := readFuel) (values := values) (source := source)
      (context := sourceContext) (solved := context.solvedRequirements) (reasonAt := reasonAt) literals scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
  | proxy originalFound form =>
    exact ⟨_, .proxy (CompatibleExpressionProxies.certificate_of_functions originalFound form
      (policyFor.special _ (.proxy originalFound form)) (policyFor.read _ (.proxy originalFound form))
      policyFor.leaf accepted)⟩
  | fragment syntaxTree =>
    refine (fun ⟨tree, sites⟩ => ⟨_, Tree.LiteralSites.fragment tree sites⟩) (CompatibleExpressionRecursive.tree_of_functions_with_literals literals literalFactory unique declarations signatures (constructorValid.restrict (fun _ child => .fragment child)) ?_ ?_ syntaxTree found typed accepted)
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
        obtain ⟨childTree, childTreeSites⟩ := ih childFound childTyped generated
        have chosen := unary_selected profile (childTree.projected childFound)
        rw [chosen] at metadata inputChecked ⊢
        obtain ⟨childType, childCode⟩ := compiled
        dsimp only at inputChecked childTree ⊢
        subst childType
        exact ⟨_, .unary metadata form childFound rfl rfl profile childTree childTreeSites⟩
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
        obtain ⟨firstTree, firstTreeSites⟩ := leftIH leftFound leftTyped firstGenerated
        obtain ⟨secondTree, secondTreeSites⟩ := rightIH rightFound rightTyped secondGenerated
        have chosen := binary_selected profile (firstTree.projected leftFound)
        rw [chosen] at metadata leftChecked rightChecked ⊢
        obtain ⟨firstType, leftCode⟩ := first
        obtain ⟨secondType, rightCode⟩ := second
        dsimp only at leftChecked rightChecked firstTree secondTree ⊢
        subst firstType secondType
        exact ⟨_, .binary metadata form leftFound rightFound rfl sameType.symm rfl profile firstTree secondTree firstTreeSites secondTreeSites⟩
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
        obtain ⟨acceptedChild1, acceptedChild1Sites⟩ := ih innerFound childTyped generated
        exact ⟨_, .group metadata form innerFound sourceType acceptedChild1 acceptedChild1Sites⟩
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
        obtain ⟨acceptedChild2, acceptedChild2Sites⟩ := leftIH leftFound leftTyped firstGenerated
        obtain ⟨acceptedChild3, acceptedChild3Sites⟩ := rightIH rightFound rightTyped secondGenerated
        exact ⟨_, .pair metadata form leftFound rightFound sourceType
          acceptedChild2 acceptedChild3 acceptedChild2Sites acceptedChild3Sites⟩
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
        obtain ⟨acceptedChild4, acceptedChild4Sites⟩ := conditionIH conditionFound conditionTyped conditionGenerated
        obtain ⟨acceptedChild5, acceptedChild5Sites⟩ := thenIH thenFound thenTyped thenGenerated
        obtain ⟨acceptedChild6, acceptedChild6Sites⟩ := elseIH elseFound elseTyped elseGenerated
        exact ⟨_, .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType
          acceptedChild4
          acceptedChild5 acceptedChild6 acceptedChild4Sites acceptedChild5Sites acceptedChild6Sites⟩
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
      obtain ⟨nodes, childReceipts⟩ := child_certificates unique argumentsTyped arguments
        (fun id member node code found typed generated => ih id member found typed generated)
      let childTrees := fun id code (member : (id, code) ∈ ids.zip codes) => (childReceipts id code member).choose
      exact ⟨_, .constructor receipt form (constructorValid _ _ _ _ (.constructor originalFound form children) originalFound form admissible) count nodes childTrees (fun id code member => (childReceipts id code member).choose_spec)⟩

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
      obtain ⟨acceptedChild7, acceptedChild7Sites⟩ := ih baseFound baseTyped generated
      exact ⟨_, .member metadata baseMetadata form layout acceptedChild7 acceptedChild7Sites⟩
  | @index id original base key keyNode originalFound form keyFound firstSyntax secondSyntax firstIH secondIH =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have syntaxTree : Syntax source id := .index originalFound form keyFound firstSyntax secondSyntax
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
      obtain ⟨acceptedChild8, acceptedChild8Sites⟩ := firstIH baseFound baseTyped firstGenerated
      obtain ⟨acceptedChild9, acceptedChild9Sites⟩ := secondIH keyFound keyTyped secondGenerated
      exact ⟨_, .index header keyFound form baseType acceptedChild8
        acceptedChild9 acceptedChild8Sites acceptedChild9Sites⟩

/-- Original tree-only API, projected from the single supported extraction. -/
theorem tree_of_functions_with_validity
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  exact (tree_of_functions_with_literals
    (fun _ id lowered => CompatibleExpressionLiterals.Certificate context.solvedRequirements source id lowered)
    CompatibleExpressionProducts.LiteralFactory.ordinary unique declarations signatures constructorValid policyFor coercions syntaxTree found typed accepted).choose

/-- Compatibility with the former false residual scope. -/
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
  exact tree_of_functions_with_validity (policy := policy) (body := body) (readFuel := readFuel)
    (context := context) (values := values) (source := source) (scope := scope) (reasonAt := reasonAt)
    (sourceContext := sourceContext) (unique := unique) (declarations := declarations) (signatures := signatures)
    (constructorValid := CompatibleExpressionInstantiationLaws.ConstructorLaw.of_closed closed residual)
    (policyFor := policyFor) (coercions := coercions) (id := id) (syntaxTree := syntaxTree) (node := node)
    (found := found) (typed := typed) (fuel := fuel) (lowered := lowered) (accepted := accepted)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneral
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinTree
/-! Builtins and ordinary data/control/index expressions share every child
position. Static receipts retain raw argument types and the actual contracted
callee. Meaning is closed by the same recursive grammar. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltins
open Core Frontend SourceInference CompatibleExpressionPrimitives
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | proxy {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .proxy inner) : Syntax source id
  | fragment {id} (child : CompatibleExpressionGeneral.Syntax source id) : Syntax source id
  | group {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .group inner) (child : Syntax source inner) : Syntax source id
  | pair {id node left right} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple [left, right]) (first : Syntax source left) (second : Syntax source right) : Syntax source id
  | unary {id node operand operator} (found : source.lookupExpression? id = some node)
      (form : node.form = .unary operator operand) (child : Syntax source operand) : Syntax source id
  | binary {id node left right operator} (found : source.lookupExpression? id = some node)
      (form : node.form = .binary left operator right)
      (first : Syntax source left) (second : Syntax source right) : Syntax source id

  | conditional {id node condition thenId elseId} (found : source.lookupExpression? id = some node)
      (form : node.form = .conditional condition thenId elseId)
      (conditionSyntax : Syntax source condition) (thenSyntax : Syntax source thenId)
      (elseSyntax : Syntax source elseId) : Syntax source id

  | constructor {id node instantiation ids} (found : source.lookupExpression? id = some node)
      (form : node.form = .constructor instantiation ids)
      (children : ∀ child, child ∈ ids → Syntax source child) : Syntax source id
  | member {id node base name index} (found : source.lookupExpression? id = some node)
      (form : node.form = .member base name index) (child : Syntax source base) : Syntax source id
  | index {id node base key keyNode} (found : source.lookupExpression? id = some node)
      (form : node.form = .index base key) (keyFound : source.lookupExpression? key = some keyNode)
      (first : Syntax source base) (second : Syntax source key) : Syntax source id

  | builtin {id node callee arguments function}
      (found : source.lookupExpression? id = some node)
      (form : node.form = .call callee arguments (.builtinFunction function))
      (children : ∀ child, child ∈ arguments → Syntax source child) : Syntax source id

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | proxy {id lowered} (receipt : CompatibleExpressionProxies.Certificate values source scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | fragment {id lowered}
      (child : CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : Metadata values.checked source id node lowered.type)
      (form : node.form = .group inner) (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Tree fuel values source context solved reasonAt scope inner lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode) (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (firstTree : Tree fuel values source context solved reasonAt scope left first)
      (secondTree : Tree fuel values source context solved reasonAt scope right second) :
      Tree fuel values source context solved reasonAt scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩
  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : Metadata values.checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : UnaryProfile operator operandType resultType core)
      (child : Tree fuel values source context solved reasonAt scope operand ⟨core.operandType, childCode⟩) :
      Tree fuel values source context solved reasonAt scope id
        ⟨core.resultType, LocalPrimitiveResults.unary core childCode⟩
  | binary {id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      (metadata : Metadata values.checked source id node (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = operandType)
      (outputType : node.type = resultType)
      (profile : BinaryProfile operator operandType resultType mode)
      (first : Tree fuel values source context solved reasonAt scope left ⟨mode.operandType operator, leftCode⟩)
      (second : Tree fuel values source context solved reasonAt scope right ⟨mode.operandType operator, rightCode⟩) :
      Tree fuel values source context solved reasonAt scope id
        ⟨mode.resultType operator, mode.binary operator leftCode rightCode⟩

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
      (elseTree : Tree fuel values source context solved reasonAt scope elseId ⟨type, elseCode⟩) :
      Tree fuel values source context solved reasonAt scope id
        ⟨type, LocalControl.choose type conditionCode thenCode elseCode⟩
  | constructor {id node instantiation ids tag header codes}
      (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
      (form : node.form = .constructor instantiation ids)
      (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
      (count : ids.length = instantiation.payloadTypes.length)
      (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
      (children : ∀ child code, (child, code) ∈ ids.zip codes →
        Tree fuel values source context solved reasonAt scope child code) :
      Tree fuel values source context solved reasonAt scope id
        ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩

  | member {id node base baseNode name index identity branches result child}
      (metadata : Metadata values.checked source id node result)
      (baseMetadata : Metadata values.checked source base baseNode child.type)
      (form : node.form = .member base name index)
      (layout : CompatibleExpressionMembers.Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result)
      (childTree : Tree fuel values source context solved reasonAt scope base child) :
      Tree fuel values source context solved reasonAt scope id
        ⟨result, SourceCoreDataExpressions.member identity result branches child.expression⟩


  | index {id node base key baseNode keyNode layout comparison first second}
      (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (firstTree : Tree fuel values source context solved reasonAt scope base first)
      (secondTree : Tree fuel values source context solved reasonAt scope key second) :
      Tree fuel values source context solved reasonAt scope id
        ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)⟩

  | builtin {id callee arguments function node codes identity contract unknown}
      (metadata : Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
      (form : node.form = .call callee arguments (.builtinFunction function))
      (sourceType : node.type = function.returnType)
      (count : arguments.length = function.parameterTypes.length)
      (nodes : CompatibleExpressionConstructors.Nodes source arguments function.parameterTypes codes)
      (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
      (children : ∀ child code, (child, code) ∈ arguments.zip codes →
        Tree fuel values source context solved reasonAt scope child code) :
      Tree fuel values source context solved reasonAt scope id
        ⟨SourceCoreInteger.builtinResult function,
          CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
            (BuiltinCalls.Protocol.contracted function identity contract) (SourceCoreCalls.packArguments codes).expression⟩

theorem Tree.projected {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree fuel values source context solved reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | proxy certificate =>
      cases certificate with
      | proxy receipt =>
          have same := Option.some.inj (receipt.metadata.found.symm.trans found)
          exact same ▸ receipt.metadata.projected
  | fragment child => exact child.projected found
  | builtin metadata _ _ _ _ _ _ =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      exact same ▸ metadata.projected
  | constructor receipt _ _ _ _ _ =>
      have same := Option.some.inj (receipt.metadata.found.symm.trans found)
      exact same ▸ receipt.metadata.projected
  | index header _ _ _ _ _ =>
      have same := Option.some.inj (header.metadata.found.symm.trans found)
      exact same ▸ header.metadata.projected
  | group metadata _ _ _ _ | pair metadata _ _ _ _ _ _ | unary metadata _ _ _ _ _ _ | binary metadata _ _ _ _ _ _ _ _ _ | conditional metadata _ _ _ _ _ _ _ _ _ _ | member metadata _ _ _ _ =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      exact same ▸ metadata.projected

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinMeaning
/-! Recursive builtin and data/control/index expressions preserve and reflect
finite source execution at every child position. Builtin heads compose child
meanings supplied here by induction on the complete concrete tree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open CompatibleExpressionIndices CoreProof
open GenericExpressionMeaning (agree_prefix rename_prefix)
open DataPatternValues

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : Scope}

/-- Static support for exactly the literal children of this existing tree. -/
inductive Tree.LiteralSites (literals : GenericExpressionMeaning.Certificate) :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Tree fuel values source context solved reasonAt scope id lowered → Prop where
  | proxy {id lowered} (receipt : CompatibleExpressionProxies.Certificate values source scope id lowered)
      :
      LiteralSites literals (Tree.proxy (scope := scope) receipt)
  | fragment {id lowered}
      (child : CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt scope id lowered)
      (childSites : CompatibleExpressionGeneral.Tree.LiteralSites literals child) :
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
  | builtin {id callee arguments function node codes identity contract unknown}
      (metadata : Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
      (form : node.form = .call callee arguments (.builtinFunction function))
      (sourceType : node.type = function.returnType)
      (count : arguments.length = function.parameterTypes.length)
      (nodes : CompatibleExpressionConstructors.Nodes source arguments function.parameterTypes codes)
      (nativeTypes : codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
      (children : ∀ child code, (child, code) ∈ arguments.zip codes →
        Tree fuel values source context solved reasonAt scope child code)
      (childrenSites : ∀ child code (member : (child, code) ∈ arguments.zip codes),
        Tree.LiteralSites literals (children child code member)) :
      LiteralSites literals (Tree.builtin (scope := scope) (identity := identity) (contract := contract) (unknown := unknown) metadata form sourceType count nodes nativeTypes children)

def Tree.WithLiterals (literals : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun current id lowered => ∃ tree : Tree fuel values source context solved reasonAt current id lowered,
    tree.LiteralSites literals

/-- The original ordinary tree supplies its own leaf membership. -/
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
  | builtin metadata form sourceType count nodes nativeTypes children childrenIH => exact .builtin metadata form sourceType count nodes nativeTypes children childrenIH

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

include extension functionLeaves unique in
theorem preserves_with_literals_and_post [FunctionCalls.FaultTokens faults]
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (constructorJoins : ScalarConstructorFaultPostContracts.Joins post listPost values program context evidence source)
    (memberJoins : ScalarMemberFaultPostContracts.Joins post values program context evidence source)
    (indexJoins : IndexFaultPostContracts.IndexJoins post values program context evidence source)
    (builtinJoins : BuiltinFaultPostContracts.Joins post listPost values program context evidence source)
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
    exact CompatibleExpressionGeneral.preserves_with_literals_and_post functions extension program evidence unique sequenceJoins ordinaryJoins constructorJoins memberJoins indexJoins literalMeaning readMeaning proxyMeaning terminalProvider ⟨child, childSites⟩
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

  | @builtin id callee arguments function node codes identity contract unknown metadata form sourceType count nodes nativeTypes children childrenSites ih =>
    have meaning : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Children scope arguments codes) faults post := by
      intro current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member
    have sequence := sequence_of_nodes (scope := scope) (certificate := Children scope arguments codes) count nodes
      (fun child code member => (⟨rfl, member⟩ : Children scope arguments codes scope child code))
    intro root found
    exact BuiltinCalls.Typed.Head.preserves_with_post functions functionLeaves program evidence unique sequenceJoins builtinJoins meaning
      (.contracted (identity := identity) (contract := contract) (unknown := unknown) metadata form sourceType sequence nativeTypes) found



include extension faithful functionLeaves functionTypes unique uninitialized missing in
theorem preserves_with_literals [FunctionCalls.FaultTokens faults]
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.TypedPreserves.forget
    (preserves_with_literals_and_post (functions := functions) (extension := extension) (functionLeaves := functionLeaves) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence) (unique := unique)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source)
      (BuiltinFaultPostContracts.trivial_joins values program context evidence source)
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
theorem preserves [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact preserves_with_literals functions extension faithful functionLeaves functionTypes program evidence unique uninitialized missing
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults) ⟨tree, tree.literalSites⟩

include extension functionLeaves in
theorem reflects_with_literals_and_post [FunctionCalls.FaultTokens faults]
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (constructorJoins : ScalarConstructorFaultPostContracts.Joins post listPost values program context evidence source)
    (memberJoins : ScalarMemberFaultPostContracts.Joins post values program context evidence source)
    (indexJoins : IndexFaultPostContracts.IndexJoins post values program context evidence source)
    (builtinJoins : BuiltinFaultPostContracts.Joins post listPost values program context evidence source)
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
    exact CompatibleExpressionGeneral.reflects_with_literals_and_post functions extension program evidence sequenceJoins ordinaryJoins constructorJoins memberJoins indexJoins literalMeaning readMeaning proxyMeaning terminalProvider ⟨child, childSites⟩
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

  | @builtin id callee arguments function node codes identity contract unknown metadata form sourceType count nodes nativeTypes children childrenSites ih =>
    have meaning : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Children scope arguments codes) faults post := by
      intro current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member
    have sequence := sequence_of_nodes (scope := scope) (certificate := Children scope arguments codes) count nodes
      (fun child code member => (⟨rfl, member⟩ : Children scope arguments codes scope child code))
    intro root found
    exact BuiltinCalls.Typed.Head.reflects_with_post functions functionLeaves program evidence sequenceJoins builtinJoins meaning
      (.contracted (identity := identity) (contract := contract) (unknown := unknown) metadata form sourceType sequence nativeTypes) found


include extension faithful functionLeaves functionTypes uninitialized missing in
theorem reflects_with_literals [FunctionCalls.FaultTokens faults]
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.TypedReflects.forget
    (reflects_with_literals_and_post (functions := functions) (extension := extension) (functionLeaves := functionLeaves) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source)
      (BuiltinFaultPostContracts.trivial_joins values program context evidence source)
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
theorem reflects [FunctionCalls.FaultTokens faults] :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact reflects_with_literals functions extension faithful functionLeaves functionTypes program evidence uninitialized missing
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults) ⟨tree, tree.literalSites⟩



end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinCertificates
/-! Actual Functions lowering and independent source typing extract one
recursive builtin/data/control/index tree. Every child compilation is exposed
and authenticated statically; no child execution premise is admitted. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltins
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



private theorem child_certificates
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {certificate : ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionsHaveTypes source sourceContext ids types)
    (generated : ListRel (Argument values (fun budget source scope id reasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget context source scope id reasonAt)
      fuel source scope reasonAt) (ids.zip types) codes)
    (extract : ∀ id, id ∈ ids → ∀ node code,
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok code →
      certificate id code) :
    CompatibleExpressionConstructors.Nodes source ids types codes ∧ ∀ id code, (id, code) ∈ ids.zip codes →
      certificate id code := by
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
  exact child_certificates unique typed generated extract


private theorem builtin_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id callee : ExpressionId} {arguments : List ExpressionId} {function : BuiltinFunctionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.builtinFunction function)) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ExpressionsHaveTypes source context arguments function.parameterTypes ∧ node.type = function.returnType := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | builtinCall _ argumentsTyped => exact ⟨argumentsTyped, rfl⟩

private theorem builtin_child_certificates
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {compilation : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context} {ids : List ExpressionId}
    {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {certificate : ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    (projectChild : ∀ {id code}, certificate id code → ∀ {node}, source.lookupExpression? id = some node →
      values.checked.catalog.project node.type = .ok code.type)
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ids.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok code →
      certificate id code) :
    ids.length = types.length ∧ CompatibleExpressionConstructors.Nodes source ids types codes ∧
      types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) ∧
      ∀ id code, (id, code) ∈ ids.zip codes →
        certificate id code := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at generated
    subst codes
    exact ⟨rfl, .nil, rfl, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at generated
      obtain ⟨code, first, generated⟩ := bind_accepted generated
      obtain ⟨restCodes, rest, generated⟩ := bind_accepted generated
      cases generated
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have child := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨count, nodes, projected, children⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      refine ⟨congrArg Nat.succ count, .cons ⟨node, found, sourceType⟩ nodes, ?_, ?_⟩
      · simp [List.mapM_cons, ← sourceType, projectChild child found, projected, Functor.map, Except.map, bind, Except.bind]
      · intro other otherCode member
        rcases List.mem_cons.mp member with same | remaining
        · cases same; exact child
        · exact children other otherCode remaining

private theorem builtin_children
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel readFuel : Nat}
    {compilation : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context} {ids : List ExpressionId}
    {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ids.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok code →
      Tree readFuel values source context compilation.solvedRequirements reasonAt scope id code) :
    ids.length = types.length ∧ CompatibleExpressionConstructors.Nodes source ids types codes ∧
      types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) ∧
      ∀ id code, (id, code) ∈ ids.zip codes →
        Tree readFuel values source context compilation.solvedRequirements reasonAt scope id code := by
  exact builtin_child_certificates (fun {_ _} child {_} found => child.projected found) unique typed generated extract


/-- Actual successful lowering and independent source typing supply every
child certificate. No semantic child assumption is part of this extraction. -/
theorem tree_of_functions_with_literals
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (literals : GenericExpressionMeaning.Certificate)
    (literalFactory : CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt literals)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree.WithLiterals (fuel := readFuel) (values := values) (source := source)
      (context := sourceContext) (solved := context.solvedRequirements) (reasonAt := reasonAt) literals scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
  | proxy originalFound form =>
    exact ⟨_, .proxy (CompatibleExpressionProxies.certificate_of_functions originalFound form
      (policyFor.special _ (.proxy originalFound form)) (policyFor.read _ (.proxy originalFound form))
      policyFor.leaf accepted)⟩
  | fragment syntaxTree =>
    refine (fun ⟨tree, sites⟩ => ⟨_, Tree.LiteralSites.fragment tree sites⟩) (CompatibleExpressionGeneral.tree_of_functions_with_literals literals literalFactory unique declarations signatures (constructorValid.restrict (fun _ child => .fragment child)) ?_ ?_ syntaxTree found typed accepted)
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
        obtain ⟨childTree, childTreeSites⟩ := ih childFound childTyped generated
        have chosen := unary_selected profile (childTree.projected childFound)
        rw [chosen] at metadata inputChecked ⊢
        obtain ⟨childType, childCode⟩ := compiled
        dsimp only at inputChecked childTree ⊢
        subst childType
        exact ⟨_, .unary metadata form childFound rfl rfl profile childTree childTreeSites⟩
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
        obtain ⟨firstTree, firstTreeSites⟩ := leftIH leftFound leftTyped firstGenerated
        obtain ⟨secondTree, secondTreeSites⟩ := rightIH rightFound rightTyped secondGenerated
        have chosen := binary_selected profile (firstTree.projected leftFound)
        rw [chosen] at metadata leftChecked rightChecked ⊢
        obtain ⟨firstType, leftCode⟩ := first
        obtain ⟨secondType, rightCode⟩ := second
        dsimp only at leftChecked rightChecked firstTree secondTree ⊢
        subst firstType secondType
        exact ⟨_, .binary metadata form leftFound rightFound rfl sameType.symm rfl profile firstTree secondTree firstTreeSites secondTreeSites⟩
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
        obtain ⟨acceptedChild1, acceptedChild1Sites⟩ := ih innerFound childTyped generated
        exact ⟨_, .group metadata form innerFound sourceType acceptedChild1 acceptedChild1Sites⟩
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
        obtain ⟨acceptedChild2, acceptedChild2Sites⟩ := leftIH leftFound leftTyped firstGenerated
        obtain ⟨acceptedChild3, acceptedChild3Sites⟩ := rightIH rightFound rightTyped secondGenerated
        exact ⟨_, .pair metadata form leftFound rightFound sourceType
          acceptedChild2 acceptedChild3 acceptedChild2Sites acceptedChild3Sites⟩
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
        obtain ⟨acceptedChild4, acceptedChild4Sites⟩ := conditionIH conditionFound conditionTyped conditionGenerated
        obtain ⟨acceptedChild5, acceptedChild5Sites⟩ := thenIH thenFound thenTyped thenGenerated
        obtain ⟨acceptedChild6, acceptedChild6Sites⟩ := elseIH elseFound elseTyped elseGenerated
        exact ⟨_, .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType
          acceptedChild4
          acceptedChild5 acceptedChild6 acceptedChild4Sites acceptedChild5Sites acceptedChild6Sites⟩
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
      obtain ⟨nodes, childReceipts⟩ := child_certificates unique argumentsTyped arguments
        (fun id member node code found typed generated => ih id member found typed generated)
      let childTrees := fun id code (member : (id, code) ∈ ids.zip codes) => (childReceipts id code member).choose
      exact ⟨_, .constructor receipt form (constructorValid _ _ _ _ (.constructor originalFound form children) originalFound form admissible) count nodes childTrees (fun id code member => (childReceipts id code member).choose_spec)⟩

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
      obtain ⟨acceptedChild7, acceptedChild7Sites⟩ := ih baseFound baseTyped generated
      exact ⟨_, .member metadata baseMetadata form layout acceptedChild7 acceptedChild7Sites⟩
  | @index id original base key keyNode originalFound form keyFound firstSyntax secondSyntax firstIH secondIH =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have syntaxTree : Syntax source id := .index originalFound form keyFound firstSyntax secondSyntax
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
      obtain ⟨acceptedChild8, acceptedChild8Sites⟩ := firstIH baseFound baseTyped firstGenerated
      obtain ⟨acceptedChild9, acceptedChild9Sites⟩ := secondIH keyFound keyTyped secondGenerated
      exact ⟨_, .index header keyFound form baseType acceptedChild8
        acceptedChild9 acceptedChild8Sites acceptedChild9Sites⟩

  | @builtin id original callee arguments function originalFound form children ih =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have syntaxTree : Syntax source id := .builtin originalFound form children
      have bypass := policyFor.special id syntaxTree
        (fun budget childSource childScope childId childReasonAt =>
          SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
            context childSource childScope childId childReasonAt) (fuel + 1)
      by_cases owner : id.occurrence.owner = source.owner
      · cases read : policy.readExpression source id with
        | error error =>
          cases hook : policy.lowerSpecial? <;> simp only [hook] at bypass
          all_goals simp [SourceCoreFunctions.lowerExpressionWithPolicy, owner, originalFound, form, hook, bypass, read,
            bind, Except.bind, pure, Except.pure] at accepted
        | ok pair =>
          obtain ⟨actualNode, nativeType⟩ := pair
          have compatibleRead := read
          rw [policyFor.read id syntaxTree] at compatibleRead
          have metadata := CompatibleExpressionReads.metadata_of_read compatibleRead
          have same := Option.some.inj (metadata.found.symm.trans originalFound)
          subst actualNode
          obtain ⟨calleeNode, calleeType, calleeCode, codes, expression, _, _, reference,
            argumentsAccepted, _, resultType, emitted, rfl⟩ :=
            BuiltinCalls.call_of_accepted owner originalFound read form bypass accepted
          have sourceTypes := builtin_source_types unique originalFound form metadata.coercions typed
          obtain ⟨count, nodes, projected, argumentReceipts⟩ := builtin_child_certificates
            (fun {_ _} receipt {_} found => receipt.choose.projected found) unique sourceTypes.1 argumentsAccepted
            (fun id member node code found typed generated => ih id member found typed generated)
          cases reference with
          | @intro index identity calleeExpression _ _ _ _ decorated =>
            cases selected : SourceCoreCallableContracts.descriptor native.table (.builtin function) with
            | error error =>
              simp [profile, SourceCoreGeneralFunctions.callablePolicy, selected,
                Except.mapError, bind, Except.bind] at decorated
            | ok descriptor =>
              rw [profile, ActualCallablePolicy.builtin_decoration native active context source calleeNode function
                (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) _ descriptor] at decorated
              cases decorated
              rw [profile, BuiltinCalls.Typed.builtin_call native active context source original callee arguments function
                nativeType _ _ descriptor form] at emitted
              cases emitted
              subst nativeType
              rw [CompatibleBuiltinMeaning.argumentTypes_project function] at projected
              let argumentTrees := fun id code (member : (id, code) ∈ arguments.zip codes) => (argumentReceipts id code member).choose
              exact ⟨_, .builtin metadata form sourceTypes.2 count nodes (Except.ok.inj projected).symm argumentTrees (fun id code member => (argumentReceipts id code member).choose_spec)⟩
      · rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
        simp only [owner, ne_eq, not_false_eq_true, ↓reduceIte] at accepted
        cases accepted

/-- Original tree-only API projected from the unique supported extraction. -/
theorem tree_of_functions_with_validity
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  exact (tree_of_functions_with_literals
    (fun _ id code => CompatibleExpressionLiterals.Certificate context.solvedRequirements source id code)
    CompatibleExpressionProducts.LiteralFactory.ordinary unique declarations signatures constructorValid
    policyFor native active profile coercions syntaxTree found typed accepted).choose

/-- Compatibility with the former false residual scope. -/
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
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_functions_with_validity (policy := policy) (body := body) (readFuel := readFuel)
    (context := context) (values := values) (source := source) (scope := scope) (reasonAt := reasonAt)
    (sourceContext := sourceContext) (unique := unique) (declarations := declarations) (signatures := signatures)
    (constructorValid := CompatibleExpressionInstantiationLaws.ConstructorLaw.of_closed closed residual)
    (policyFor := policyFor) (native := native) (active := active) (profile := profile) (coercions := coercions)
    (id := id) (syntaxTree := syntaxTree) (node := node) (found := found) (typed := typed) (fuel := fuel)
    (lowered := lowered) (accepted := accepted)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualGeneral
/-! The actual contextual dispatcher supplies the ordinary recursive data/control policy.
Static occurrence metadata excludes local specialization and output coercions.
The final receipt contains no child lowering or runtime execution hypothesis. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneral
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

theorem contextualSource_fragment
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
  | proxy found form | unary found form _ | binary found form _ _ | group found form _ | pair found form _ _ | conditional found form _ _ _ | constructor found form _ | member found form _ | index found form _ _ _ =>
      simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

theorem evidence_fragment (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
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
  | proxy originalFound form | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ | conditional originalFound form _ _ _ | constructor originalFound form _ | member originalFound form _ | index originalFound form _ _ _ =>
      have same := Option.some.inj (originalFound.symm.trans found)
      subst node
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
        CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

theorem fragment_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : Syntax source id) :
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
  | proxy found _ | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ | conditional found _ _ _ _ | constructor found _ _ | member found _ _ | index found _ _ _ _ => exact ⟨_, found⟩

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

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneral
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualBuiltins
/-! Actual contextual lowering authenticates recursive builtin/data/control
receipts using the same ordinary metadata and full parent context. The final
extraction theorem contains no child lowering or runtime execution hypothesis. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltins
open Core Frontend SourceInference

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

private theorem ordinary_general {source : TypedSource} {locals : SourceCoreLocalPolymorphism.Catalog}
    {owner : SourceSpecialization.SpecializationKey} (ordinary : Ordinary source locals owner) :
    CompatibleExpressionGeneral.Ordinary source locals owner :=
  ⟨fun id node child => ordinary.requirements id node (.fragment child),
   fun id node child => ordinary.coercions id node (.fragment child),
   fun id child => ordinary.notInitializer id (.fragment child),
   fun id node name binder child => ordinary.localBinder id node name binder (.fragment child)⟩

private theorem contextualSource_fragment
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    (ordinary : Ordinary source locals owner) (syntaxTree : Syntax source id) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  cases syntaxTree with
  | fragment child => exact CompatibleExpressionGeneral.contextualSource_fragment program plan locals owner parent (ordinary_general ordinary) child
  | proxy found form | unary found form _ | binary found form _ _ | group found form _ | pair found form _ _ | conditional found form _ _ _ | constructor found form _ | member found form _ | index found form _ _ _ | builtin found form _ =>
      simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem evidence_fragment (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (requirements : node.requirements = CompatibleExpressionLiterals.owned node.form) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have ordinaryOwned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (CompatibleExpressionLiterals.owned node.form) := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    change (if (CompatibleExpressionLiterals.owned node.form).length < 0 then none else
      if CompatibleExpressionLiterals.owned node.form = (CompatibleExpressionLiterals.owned node.form).take
          ((CompatibleExpressionLiterals.owned node.form).length - 0) ++ [] then
        some ((CompatibleExpressionLiterals.owned node.form).take ((CompatibleExpressionLiterals.owned node.form).length - 0)) else none) = _
    simp
  cases syntaxTree with
  | fragment old => exact CompatibleExpressionGeneral.evidence_fragment program projector caller context child fuel scope reasonAt callables old found requirements coercions
  | proxy originalFound form | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ | conditional originalFound form _ _ _ | constructor originalFound form _ | member originalFound form _ | index originalFound form _ _ _ | builtin originalFound form _ =>
      have same := Option.some.inj (originalFound.symm.trans found)
      subst node
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinaryOwned, requirements, coercions,
        CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

private theorem fragment_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : Syntax source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases syntaxTree with
  | fragment child => exact CompatibleExpressionGeneral.fragment_has_node child
  | proxy found _ | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ | conditional found _ _ _ _ | constructor found _ _ | member found _ _ | index found _ _ _ _ | builtin found _ _ => exact ⟨_, found⟩

private theorem context_bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Recursive data/control trees are extracted from the production
contextual traversal, at root or full specialized parent context. -/
theorem tree_of_contextual_with_validity
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context}
    (ordinary : Ordinary source locals context.owner)
    (unique : NodeOccurrencesUnique source)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (sourceSignatures : sourceContext.signatures = values.checked.signatures)
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context (some native) parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine tree_of_functions_with_validity unique declarations sourceSignatures constructorValid ?_ native prepared.substitution rfl ordinary.coercions syntaxTree found typed accepted
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
      refine tree_of_functions_with_validity unique declarations sourceSignatures constructorValid ?_ native [] rfl ordinary.coercions syntaxTree found typed generated
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

/-- Compatibility wrapper for the former closed source context. -/
theorem tree_of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
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
      diagnostics context (some native) parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_contextual_with_validity ordinary unique
    (CompatibleExpressionInstantiationLaws.ConstructorLaw.of_closed closed residual)
    declarations sourceSignatures syntaxTree found typed readPolicy lowerPolicy leafPolicy accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity
/-! Runtime context conditions retain the complete solved ledger and its actual
covering dictionary. Lexical changes transport these fields without removing
unused assumptions or qualified template rows. Ordinary validity is a one-way
adapter; the runtime interface does not imply ordinary ledger validity. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity
open Frontend SourceInference

structure Valid (solved : List SolvedRequirement) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) : Prop where
  ledger : context.solvedRequirements = solved
  runtime : RuntimeRequirementLedgerValid context
  covers : evidence.Covers context

/-- The old full ordinary ledger implies the execution-facing condition for
the same entire row list. This adapter never runs in the opposite direction. -/
theorem of_ordinary {solved : List SolvedRequirement} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment}
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) :
    Valid solved context evidence :=
  ⟨valid.ledger, ⟨valid.valid.idsUnique, fun row _ member _ => valid.valid.entriesValid row member⟩,
    valid.covers⟩

/-- Only non-lexical fields are needed; full solved-row equality transports
the same ledger and dictionary into the actual target context. -/
theorem Valid.transport {solved : List SolvedRequirement} {source target : Context}
    {evidence : Dynamic.EvidenceEnvironment} (valid : Valid solved source evidence)
    (fields : Dynamic.RuntimeContextFields source target) : Valid solved target evidence :=
  ⟨fields.solvedRequirements.trans valid.ledger, fields.runtimeRequirementLedger valid.runtime,
    fields.covers valid.covers⟩

theorem Valid.extend {solved : List SolvedRequirement} {source target : Context}
    {evidence : Dynamic.EvidenceEnvironment} {owner : Resolved.DeclarationId} {binder : TypedBinder}
    (valid : Valid solved source evidence) (extended : BinderExtends owner source binder target) :
    Valid solved target evidence :=
  valid.transport (Dynamic.RuntimeContextFields.ofBinderExtends extended)

theorem Valid.mono {solved : List SolvedRequirement} {source target : Context}
    {evidence : Dynamic.EvidenceEnvironment} {owner : Resolved.DeclarationId}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (valid : Valid solved source evidence) (extended : MonoBindersExtend owner source parameters types target) :
    Valid solved target evidence :=
  valid.transport (RecursiveNamedInitialContextValidity.mono_fields extended)

/-- Independent program validity supplies runtime rows and the actual source
frame supplies coverage. No Header.valid or template-empty test is an input. -/
theorem of_frame {program : Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : Context}
    {types : List TypeSystem.Ty} {solved : List SolvedRequirement}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved) :
    Valid solved context function.evidence :=
  ⟨(RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements.trans sameLedger,
    RecursiveNamedInitialContextValidity.runtime frame extended programTyped,
    RecursiveNamedInitialContextValidity.covers frame extended⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralNativeTyping
/-! The existing recursive grammars type their own child code at every position.
Constructor packing, member rows and general mapping comparators retain the
actual factory receipts. Source-static trees contain no native typing callbacks. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralNativeTyping
open Core Frontend SourceInference CompatibleExpressionPrimitives
open CompatibleExpressionScalarNativeTyping CompatibleExpressionMemberNativeTyping
open CompatibleExpressionConstructorNativeTyping CompatibleExpressionDataLeafNativeTyping
open CompatibleCatalogNominalCoverage

private theorem binary_native {definitions : DataEnvironment} {context : Core.Context}
    {mode : Mode} {operator : Syntax.BinaryOp} {left right : Expr}
    (first : HasType context left (LanguageResult.resultType (mode.operandType operator)) definitions)
    (second : HasType context right (LanguageResult.resultType (mode.operandType operator)) definitions) :
    NativeTyping definitions context ⟨mode.resultType operator, mode.binary operator left right⟩ := by
  constructor
  · cases mode <;> cases operator <;> constructor
  · cases mode with
    | word => exact SourceCorePrimitive.binary_hasType first second
    | integer => exact SourceCoreInteger.binary_hasType first second

private theorem constructor_native {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr} {context : Core.Context}
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
    (count : ids.length = instantiation.payloadTypes.length)
    (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
    (children : ∀ child code, (child, code) ∈ ids.zip codes →
      NativeTyping values.checked.catalog.definitions context code) :
    NativeTyping values.checked.catalog.definitions context
      ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩ := by
  have sequence := CompatibleExpressionConstructors.sequence_of_nodes
    (scope := scope) (certificate := fun _ _ code => NativeTyping values.checked.catalog.definitions context code)
    count nodes children
  obtain ⟨_, packedTyped⟩ := packed_native sequence (fun _ _ typed => typed)
  have registered := receipt.registered
  rw [← packed_type codes] at registered
  obtain ⟨_, ownerRegistered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner registered
  exact ⟨.namedData ownerRegistered, SourceCoreCompatibleDataExpressions.construct_hasType header registered packedTyped⟩

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (shaped : Shapes values.checked.signatures values.checked.catalog) (complete : Complete values.checked.catalog)
  (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope) (administrative : Core.Context)

include shaped complete visibleTypes in
theorem recursive_native
    (tree : CompatibleExpressionRecursive.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact members_native shaped complete visibleTypes administrative child
  | group _ _ _ _ _ child => exact child
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩
  | constructor receipt _ _ count nodes _ children => exact constructor_native (scope := scope) receipt count nodes children
  | member _ baseMetadata _ layout _ child =>
    have same := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← same]; exact child.2)⟩

include shaped complete visibleTypes in
theorem general_native
    (tree : CompatibleExpressionGeneral.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | proxy receipt => exact proxy_native receipt _
  | fragment child => exact recursive_native shaped complete visibleTypes administrative child
  | group _ _ _ _ _ child => exact child
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩
  | constructor receipt _ _ count nodes _ children => exact constructor_native (scope := scope) receipt count nodes children
  | member _ baseMetadata _ layout _ child =>
    have same := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← same]; exact child.2)⟩
  | index header _ _ _ _ _ first second => exact index_native header first second (reasonAt _)

include shaped complete visibleTypes in
theorem recursive_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionRecursive.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := recursive_native shaped complete visibleTypes administrative tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

include shaped complete visibleTypes in
theorem general_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionGeneral.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := general_native shaped complete visibleTypes administrative tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

include visibleTypes in
theorem contextual_native
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment}
    (ordinary : CompatibleExpressionGeneral.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionGeneral.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation native parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  have shaped := prepare_shapes registered
  rw [← SourceCoreCompatibleCatalog.prepare_signatures registered] at shaped
  exact general_native_at shaped (prepare_complete registered) visibleTypes administrative extension
    (CompatibleExpressionGeneral.tree_of_contextual ordinary unique closed residual declarations sourceSignatures syntaxTree found sourceTyped
      readPolicy lowerPolicy leafPolicy accepted)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralNativeTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinNativeTyping
/-! Contracted builtins share the existing recursive data/control grammar at
all child positions. Native child derivations follow its static Tree induction,
including ordered argument packing and the actual mapping/member layouts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinNativeTyping
open Core Frontend SourceInference CompatibleExpressionPrimitives
open CompatibleExpressionScalarNativeTyping CompatibleExpressionMemberNativeTyping
open CompatibleExpressionConstructorNativeTyping CompatibleExpressionDataLeafNativeTyping
open CompatibleCatalogNominalCoverage

private theorem binary_native {definitions : DataEnvironment} {context : Core.Context}
    {mode : Mode} {operator : Syntax.BinaryOp} {left right : Expr}
    (first : HasType context left (LanguageResult.resultType (mode.operandType operator)) definitions)
    (second : HasType context right (LanguageResult.resultType (mode.operandType operator)) definitions) :
    NativeTyping definitions context ⟨mode.resultType operator, mode.binary operator left right⟩ := by
  constructor
  · cases mode <;> cases operator <;> constructor
  · cases mode with
    | word => exact SourceCorePrimitive.binary_hasType first second
    | integer => exact SourceCoreInteger.binary_hasType first second

private theorem constructor_native {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr} {context : Core.Context}
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
    (count : ids.length = instantiation.payloadTypes.length)
    (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
    (children : ∀ child code, (child, code) ∈ ids.zip codes →
      NativeTyping values.checked.catalog.definitions context code) :
    NativeTyping values.checked.catalog.definitions context
      ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩ := by
  have sequence := CompatibleExpressionConstructors.sequence_of_nodes
    (scope := scope) (certificate := fun _ _ code => NativeTyping values.checked.catalog.definitions context code)
    count nodes children
  obtain ⟨_, packedTyped⟩ := packed_native sequence (fun _ _ typed => typed)
  have registered := receipt.registered
  rw [← packed_type codes] at registered
  obtain ⟨_, ownerRegistered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner registered
  exact ⟨.namedData ownerRegistered, SourceCoreCompatibleDataExpressions.construct_hasType header registered packedTyped⟩

variable {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (shaped : Shapes values.checked.signatures values.checked.catalog) (complete : Complete values.checked.catalog)
  (visibleTypes : ScopeWellFormed values.checked.catalog.definitions scope) (administrative : Core.Context)

include shaped complete visibleTypes in
theorem builtins_native
    (tree : CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | proxy receipt => exact proxy_native receipt _
  | fragment child => exact CompatibleExpressionGeneralNativeTyping.general_native shaped complete visibleTypes administrative child
  | group _ _ _ _ _ child => exact child
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩
  | constructor receipt _ _ count nodes _ children => exact constructor_native (scope := scope) receipt count nodes children
  | member _ baseMetadata _ layout _ child =>
    have same := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← same]; exact child.2)⟩
  | index header _ _ _ _ _ first second => exact index_native header first second (reasonAt _)

  | @builtin id callee arguments function node codes identity contract unknown _ _ _ count nodes nativeTypes _ children =>
    have sequence := CompatibleExpressionConstructors.sequence_of_nodes
      (scope := scope) (certificate := fun _ _ code => NativeTyping values.checked.catalog.definitions
        (SourceCoreLocalCell.coreContext scope ++ administrative) code) count nodes children
    apply BuiltinCallNativeTyping.call_native function identity contract unknown
      (packed_native sequence (fun _ _ typed => typed))
    rw [packed_type, nativeTypes, CompatibleBuiltinMeaning.argumentTypes_pack]

include shaped complete visibleTypes in
theorem builtins_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := builtins_native shaped complete visibleTypes administrative tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

include visibleTypes in
theorem contextual_native
    {catalogSignatures : ProgramSignatures} {catalogFuel : Nat} {catalogTypes : List TypeSystem.Ty}
    {metadata : List SourceCoreCompatibleCatalog.Metadata} {limits : SourceCoreCompatibleCatalog.Limits} {contracts : Bool}
    (registered : SourceCoreCompatibleCatalog.prepare catalogSignatures catalogFuel catalogTypes metadata limits contracts = .ok values.checked)
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {compileFuel : Nat} {node : ExpressionNode}
    {definitions : DataEnvironment}
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (syntaxTree : CompatibleExpressionBuiltins.Syntax source id)
    (found : source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType source context id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics compilation (some native) parent skipInitializer compileFuel source scope id reasonAt = .ok lowered)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  have shaped := prepare_shapes registered
  rw [← SourceCoreCompatibleCatalog.prepare_signatures registered] at shaped
  exact builtins_native_at shaped (prepare_complete registered) visibleTypes administrative extension
    (CompatibleExpressionBuiltins.tree_of_contextual ordinary unique closed residual declarations sourceSignatures syntaxTree found sourceTyped
      readPolicy lowerPolicy leafPolicy accepted)


end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinNativeTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCertificateNativeTyping
/-! Native expression typing follows the actual projection and read receipts.
Only referenced cells need valid annotations. Unused local scope entries are
unconstrained. Nominal identities are authenticated by the catalog lookup;
constructor payload typing continues to use its registered definitions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCertificateNativeTyping
open Core Frontend SourceInference CompatibleExpressionPrimitives
open CompatibleExpressionScalarNativeTyping CompatibleExpressionConstructorNativeTyping
open CompatibleExpressionMemberNativeTyping CompatibleExpressionDataLeafNativeTyping
open CompatibleCatalogNominalCoverage

private theorem identity_wellFormed {catalog : SourceCoreCompatibleCatalog.Catalog}
    {sourceType : TypeSystem.Ty} {identity : DataTypeId}
    (found : catalog.identity? sourceType = some identity) :
    Ty.WellFormed catalog.definitions (.namedData identity) := by
  obtain ⟨entry, stored, _⟩ := identity_entry found
  apply Ty.WellFormed.namedData (definition := entry.definition.getD ⟨[]⟩)
  simp [SourceCoreCompatibleCatalog.Catalog.definitions, List.getElem?_map, stored]

/-- The output IDs of this projection come from actual catalog entries.
This proves the native annotation, not source authority or payload semantics. -/
theorem project_wellFormed {catalog : SourceCoreCompatibleCatalog.Catalog}
    {sourceType : TypeSystem.Ty} {type : Ty}
    (projected : catalog.project sourceType = .ok type) : type.WellFormed catalog.definitions := by
  induction sourceType generalizing type with
  | product left right first second =>
    simp only [SourceCoreCompatibleCatalog.Catalog.project] at projected
    obtain ⟨a, leftEq, rest⟩ := CompatibleEncoding.bind_ok projected
    obtain ⟨b, rightEq, result⟩ := CompatibleEncoding.bind_ok rest
    cases result
    exact .product (first leftEq) (second rightEq)
  | function parameter result first second =>
    simp only [SourceCoreCompatibleCatalog.Catalog.project] at projected
    obtain ⟨a, firstEq, rest⟩ := CompatibleEncoding.bind_ok projected
    obtain ⟨b, secondEq, result⟩ := CompatibleEncoding.bind_ok rest
    cases result
    unfold SourceCoreCompatibleCatalog.Catalog.functionType
    split
    · exact CallableContract.functionType_wellFormed (first firstEq) (second secondEq)
    · exact TaggedFunction.functionType_wellFormed (first firstEq) (second secondEq)
  | mapping key value first second =>
    simp only [SourceCoreCompatibleCatalog.Catalog.project] at projected
    cases found : catalog.identity? (.mapping key value) with
    | none => simp [found, bind, Except.bind] at projected
    | some identity =>
      simp only [found, bind, Except.bind, pure, Except.pure] at projected
      obtain ⟨a, firstEq, rest⟩ := CompatibleEncoding.bind_ok projected
      obtain ⟨b, secondEq, result⟩ := CompatibleEncoding.bind_ok rest
      cases result
      exact .product .word (.product (.sum .unit (second secondEq)) (identity_wellFormed found))
  | comptime inner ih => exact ih projected
  | constructor constructor =>
    cases constructor with
    | builtin builtin => cases builtin <;> cases projected <;> constructor
    | declaration declaration =>
      simp only [SourceCoreCompatibleCatalog.Catalog.project] at projected
      cases found : catalog.identity? (.constructor (.declaration declaration)) <;> simp [found] at projected
      cases projected
      exact identity_wellFormed found
  | «variable» variableId | «parameter» parameterId | application left right _ _ | proxy inner _ | error =>
    simp only [SourceCoreCompatibleCatalog.Catalog.project] at projected
    split at projected
    · cases projected; exact identity_wellFormed (by assumption)
    · cases projected

theorem read_native {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (read : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id lowered)
    (administrative : Core.Context) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨certificate, same, binding⟩ := read
  have wellFormed := project_wellFormed certificate.metadata.projected
  exact ⟨same ▸ wellFormed, by rw [← same]; exact certificate.native_hasType binding wellFormed administrative⟩

theorem binary_native {definitions : DataEnvironment} {context : Core.Context}
    {mode : Mode} {operator : Syntax.BinaryOp} {left right : Expr}
    (first : HasType context left (LanguageResult.resultType (mode.operandType operator)) definitions)
    (second : HasType context right (LanguageResult.resultType (mode.operandType operator)) definitions) :
    NativeTyping definitions context ⟨mode.resultType operator, mode.binary operator left right⟩ := by
  constructor
  · cases mode <;> cases operator <;> constructor
  · cases mode with
    | word => exact SourceCorePrimitive.binary_hasType first second
    | integer => exact SourceCoreInteger.binary_hasType first second

theorem constructor_native {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr} {context : Core.Context}
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
    (count : ids.length = instantiation.payloadTypes.length)
    (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
    (children : ∀ child code, (child, code) ∈ ids.zip codes →
      NativeTyping values.checked.catalog.definitions context code) :
    NativeTyping values.checked.catalog.definitions context
      ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩ := by
  have sequence := CompatibleExpressionConstructors.sequence_of_nodes
    (scope := scope) (certificate := fun _ _ code => NativeTyping values.checked.catalog.definitions context code)
    count nodes children
  obtain ⟨_, packedTyped⟩ := packed_native sequence (fun _ _ typed => typed)
  have registered := receipt.registered
  rw [← packed_type codes] at registered
  obtain ⟨_, ownerRegistered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner registered
  exact ⟨.namedData ownerRegistered, SourceCoreCompatibleDataExpressions.construct_hasType header registered packedTyped⟩

variable {fuel readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (administrative : Core.Context)

theorem products_native
    (tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | literal receipt =>
    obtain ⟨_, _, literal⟩ := receipt
    exact literal_native literal _ _
  | read receipt => exact read_native receipt administrative
  | group _ _ _ _ _ ih => exact ih
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩

theorem primitives_native
    (tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | product child => exact products_native administrative child
  | group _ _ _ _ _ ih => exact ih
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2

theorem conditionals_native
    (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | primitive child => exact primitives_native administrative child
  | group _ _ _ _ _ ih => exact ih
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩

theorem constructors_native
    (tree : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact conditionals_native administrative child
  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children ih =>
    have sequence := CompatibleExpressionConstructors.sequence_of_nodes
      (scope := scope)
      (certificate := fun _ _ code => NativeTyping values.checked.catalog.definitions
        (SourceCoreLocalCell.coreContext scope ++ administrative) code) count nodes ih
    obtain ⟨packedWF, packedTyped⟩ := packed_native sequence (fun _ _ typed => typed)
    have registered := receipt.registered
    rw [← packed_type codes] at registered
    obtain ⟨_, ownerRegistered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner registered
    exact ⟨.namedData ownerRegistered, SourceCoreCompatibleDataExpressions.construct_hasType header registered packedTyped⟩

variable (shaped : Shapes values.checked.signatures values.checked.catalog) (complete : Complete values.checked.catalog)
include shaped complete in
theorem members_native
    (tree : CompatibleExpressionMembers.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact constructors_native administrative child
  | member metadata baseMetadata form layout childTree ih =>
    have childType := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← childType]; exact ih.2)⟩

include shaped complete in
theorem recursive_native
    (tree : CompatibleExpressionRecursive.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact members_native administrative shaped complete child
  | group _ _ _ _ _ child => exact child
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩
  | constructor receipt _ _ count nodes _ children => exact constructor_native (scope := scope) receipt count nodes children
  | member _ baseMetadata _ layout _ child =>
    have same := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← same]; exact child.2)⟩

include shaped complete in
theorem general_native
    (tree : CompatibleExpressionGeneral.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | proxy receipt => exact proxy_native receipt _
  | fragment child => exact recursive_native administrative shaped complete child
  | group _ _ _ _ _ child => exact child
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩
  | constructor receipt _ _ count nodes _ children => exact constructor_native (scope := scope) receipt count nodes children
  | member _ baseMetadata _ layout _ child =>
    have same := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← same]; exact child.2)⟩
  | index header _ _ _ _ _ first second => exact index_native header first second (reasonAt _)

include shaped complete in
theorem builtins_native
    (tree : CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | proxy receipt => exact proxy_native receipt _
  | fragment child => exact general_native administrative shaped complete child
  | group _ _ _ _ _ child => exact child
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩
  | constructor receipt _ _ count nodes _ children => exact constructor_native (scope := scope) receipt count nodes children
  | member _ baseMetadata _ layout _ child =>
    have same := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← same]; exact child.2)⟩
  | index header _ _ _ _ _ first second => exact index_native header first second (reasonAt _)

  | @builtin id callee arguments function node codes identity contract unknown _ _ _ count nodes nativeTypes _ children =>
    have sequence := CompatibleExpressionConstructors.sequence_of_nodes
      (scope := scope) (certificate := fun _ _ code => NativeTyping values.checked.catalog.definitions
        (SourceCoreLocalCell.coreContext scope ++ administrative) code) count nodes children
    apply BuiltinCallNativeTyping.call_native function identity contract unknown
      (packed_native sequence (fun _ _ typed => typed))
    rw [packed_type, nativeTypes, CompatibleBuiltinMeaning.argumentTypes_pack]

include shaped complete in
theorem builtins_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := builtins_native administrative shaped complete tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCertificateNativeTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEncodedDataTyping
/-! Successful compatible data encoding contains only structural data. Its
native typing can therefore be restricted from appended administrative
definitions to the actual catalog prefix. Catalog projection certifies the
type annotation independently; runtime type tags do not supply that fact.
Closures and references require a separate representation boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEncodedDataTyping
open Core Frontend
open SourceCoreCompatibleValues (encodeRaw encodePayloadsRaw encodeEntriesRaw encodeDefaultRaw)
open CompatibleEncoding (bind_ok mapError_ok)

/-- Structural data excludes executable closures and store references. Sum
annotations and constructor identities remain exactly those in the value. -/
inductive DataOnly : Value → Prop where
  | unit : DataOnly .unit
  | bool {value : Bool} : DataOnly (.bool value)
  | word {value : Word} : DataOnly (.word value)
  | integer {value : Int} : DataOnly (.integer value)
  | pair {left right : Value} : DataOnly left → DataOnly right → DataOnly (.pair left right)
  | inLeft {type : Ty} {payload : Value} : DataOnly payload → DataOnly (.inLeft type payload)
  | inRight {type : Ty} {payload : Value} : DataOnly payload → DataOnly (.inRight type payload)
  | constructed {constructor : ConstructorId} {payload : Value} :
      DataOnly payload → DataOnly (.constructed constructor payload)

/-- The existing projection proof follows actual catalog entry IDs and their
ordered definition lookup, including callable and mapping wrappers. -/
theorem project_wellFormed {catalog : SourceCoreCompatibleCatalog.Catalog}
    {sourceType : TypeSystem.Ty} {type : Ty}
    (projected : catalog.project sourceType = .ok type) : type.WellFormed catalog.definitions :=
  CompatibleExpressionCertificateNativeTyping.project_wellFormed projected

/-- Named payloads are selected from the original well formed definition,
then identified with the actual lookup in its appended environment. -/
theorem DataOnly.restrict_definitions {value : Value} (data : DataOnly value)
    {base future : DataEnvironment} (wellFormed : base.WellFormed)
    (extension : base.Extends future) {world : StoreTyping} {type : Ty}
    (annotation : type.WellFormed base)
    (typed : RuntimeValueHasType world value type future) : RuntimeValueHasType world value type base := by
  induction data generalizing type with
  | unit => cases typed; exact .unit
  | bool => cases typed; exact .bool
  | word => cases typed; exact .word
  | integer => cases typed; exact .integer
  | pair _ _ first second =>
    cases typed with
    | pair left right => cases annotation with
      | product firstType secondType => exact .pair (first firstType left) (second secondType right)
  | inLeft _ child =>
    cases typed with
    | inLeft payload => cases annotation with
      | sum payloadType _ => exact .inLeft (child payloadType payload)
  | inRight _ child =>
    cases typed with
    | inRight payload => cases annotation with
      | sum _ payloadType => exact .inRight (child payloadType payload)
  | @constructed constructor payload _ child =>
    cases typed with
    | constructed selected payloadTyped => cases annotation with
      | namedData owner =>
        obtain ⟨definition, selectedOwner, selectedPayload⟩ :=
          DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mp selected
        have same := Option.some.inj ((extension.lookup owner).symm.trans selectedOwner)
        subst definition
        have original := DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mpr
          ⟨_, owner, selectedPayload⟩
        exact .constructed original
          (child (wellFormed.constructorPayloadType_wellFormed original) payloadTyped)

private def RawData (fuel : Nat) : Prop :=
  ∀ (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    (expected : TypeSystem.Ty) (carrier : SourceCoreDataValues.Value)
    (encoded : SourceCoreCompatibleValues.Extended registry Value),
    encodeRaw fuel checked registry expected carrier = .ok encoded → DataOnly encoded.value

private def PayloadData (fuel : Nat) : Prop :=
  ∀ (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    (types : List TypeSystem.Ty) (carriers : List SourceCoreDataValues.Value) (index : Nat)
    (encoded : SourceCoreCompatibleValues.Extended registry Value),
    encodePayloadsRaw fuel checked registry types carriers index = .ok encoded → DataOnly encoded.value

private def EntriesData (fuel : Nat) : Prop :=
  ∀ (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    (key value : TypeSystem.Ty) (layout : OrderedMapping.Layout)
    (carriers : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value)) (index : Nat)
    (encoded : SourceCoreCompatibleValues.Extended registry Value),
    encodeEntriesRaw fuel checked registry key value layout carriers index = .ok encoded → DataOnly encoded.value

private theorem default_data {fuel : Nat} (raw : RawData fuel)
    {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {sourceType : TypeSystem.Ty} {type : Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : encodeDefaultRaw fuel checked registry sourceType type = .ok encoded) : DataOnly encoded.value := by
  cases found : SourceCoreCompatibleValues.defaultValue? (sourceType.size + 1) sourceType with
  | none =>
    simp only [encodeDefaultRaw, found, pure, Except.pure] at accepted
    cases accepted
    exact .inLeft .unit
  | some carrier =>
    simp only [encodeDefaultRaw, found] at accepted
    obtain ⟨inner, generated, accepted⟩ := bind_ok accepted
    cases accepted
    exact .inRight (raw checked registry sourceType carrier inner generated)

private theorem raw_data_succ {fuel : Nat} (raw : RawData fuel)
    (payload : PayloadData fuel) (entries : EntriesData fuel) : RawData (fuel + 1) := by
  intro checked registry expected carrier encoded accepted
  cases carrier with
  | unit | bool value | word value | integer value =>
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    all_goals try (solve | cases accepted)
    case constructor id =>
      cases id with
      | declaration => cases accepted
      | builtin builtin => cases builtin <;> try (solve | cases accepted)
                           all_goals cases accepted; constructor
  | product left right =>
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    case product leftType rightType =>
      obtain ⟨a, first, accepted⟩ := bind_ok accepted
      obtain ⟨b, second, accepted⟩ := bind_ok accepted
      cases accepted
      exact .pair (raw checked registry leftType left a (mapError_ok first))
        (raw checked a.registry rightType right b (mapError_ok second))
    all_goals try (solve | cases accepted)
    case constructor id => cases id <;> try (solve | cases accepted)
                           rename_i builtin; cases builtin <;> cases accepted
  | proxy inner =>
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    case proxy expectedInner =>
      obtain ⟨inserted, _, accepted⟩ := bind_ok accepted
      obtain ⟨identity, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact .constructed .word
    all_goals try (solve | cases accepted)
    case constructor id => cases id <;> try (solve | cases accepted)
                           rename_i builtin; cases builtin <;> cases accepted
  | mapping key value carriers =>
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    case mapping keyType valueType =>
      obtain ⟨inserted, _, accepted⟩ := bind_ok accepted
      obtain ⟨layout, _, accepted⟩ := bind_ok accepted
      obtain ⟨encodedEntries, entryEq, accepted⟩ := bind_ok accepted
      obtain ⟨fallback, fallbackEq, accepted⟩ := bind_ok accepted
      cases accepted
      exact .pair .word (.pair (default_data raw fallbackEq)
        (entries checked inserted.registry key value layout carriers 0 encodedEntries entryEq))
    all_goals try (solve | cases accepted)
    case constructor id => cases id <;> try (solve | cases accepted)
                           rename_i builtin; cases builtin <;> cases accepted
  | constructed metadata carriers =>
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    case function => cases accepted
    case constructor id =>
      cases id <;> try (rename_i builtin; cases builtin)
      all_goals
        obtain ⟨inserted, _, accepted⟩ := bind_ok accepted
        obtain ⟨tag, _, accepted⟩ := bind_ok accepted
        obtain ⟨fields, fieldEq, accepted⟩ := bind_ok accepted
        cases accepted
        exact .constructed (.pair .word (payload checked inserted.registry metadata.payloadTypes carriers 0 fields fieldEq))
    all_goals
      obtain ⟨inserted, _, accepted⟩ := bind_ok accepted
      obtain ⟨tag, _, accepted⟩ := bind_ok accepted
      obtain ⟨fields, fieldEq, accepted⟩ := bind_ok accepted
      cases accepted
      exact .constructed (.pair .word (payload checked inserted.registry metadata.payloadTypes carriers 0 fields fieldEq))

private theorem payload_data_succ {fuel : Nat} (raw : RawData fuel)
    (payload : PayloadData fuel) : PayloadData (fuel + 1) := by
  intro checked registry types carriers index encoded accepted
  by_cases length : types.length = carriers.length
  · cases types with
    | nil => cases carriers with
      | nil => simp [encodePayloadsRaw] at accepted; subst encoded; exact .unit
      | cons => simp at length
    | cons type types => cases carriers with
      | nil => simp at length
      | cons carrier carriers => cases types with
        | nil =>
          have empty : carriers = [] := by simpa using length.symm
          subst carriers
          simp only [encodePayloadsRaw, length, ↓reduceIte] at accepted
          exact raw checked registry type carrier encoded (mapError_ok accepted)
        | cons next types =>
          simp only [encodePayloadsRaw, length, ↓reduceIte] at accepted
          obtain ⟨first, firstEq, accepted⟩ := bind_ok accepted
          obtain ⟨rest, restEq, accepted⟩ := bind_ok accepted
          cases accepted
          exact .pair (raw checked registry type carrier first (mapError_ok firstEq))
            (payload checked first.registry (next :: types) carriers (index + 1) rest restEq)
  · unfold encodePayloadsRaw at accepted
    simp [length, bind, Except.bind, throw, throwThe] at accepted

private theorem entries_data_succ {fuel : Nat} (raw : RawData fuel)
    (entries : EntriesData fuel) : EntriesData (fuel + 1) := by
  intro checked registry keyType valueType layout carriers index encoded accepted
  cases carriers with
  | nil =>
    simp only [encodeEntriesRaw, pure, Except.pure] at accepted
    cases accepted
    exact .constructed .unit
  | cons pair rest =>
    obtain ⟨key, value⟩ := pair
    simp only [encodeEntriesRaw] at accepted
    obtain ⟨a, first, accepted⟩ := bind_ok accepted
    obtain ⟨b, second, accepted⟩ := bind_ok accepted
    obtain ⟨tail, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    exact .constructed (.pair (.pair (raw checked registry keyType key a (mapError_ok first))
      (raw checked a.registry valueType value b (mapError_ok second)))
      (entries checked b.registry keyType valueType layout rest (index + 1) tail remaining))

/-- One fuel induction closes the actual raw, payload and ordered-entry
encoders. The mapping default consumes the raw child at that same fuel. -/
private theorem data_only (fuel : Nat) : RawData fuel ∧ PayloadData fuel ∧ EntriesData fuel := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro checked registry expected carrier encoded accepted
      unfold encodeRaw at accepted
      cases accepted
    · intro checked registry types carriers index encoded accepted
      cases types with
      | nil => cases carriers with
        | nil => simp [encodePayloadsRaw] at accepted; subst encoded; exact .unit
        | cons => simp [encodePayloadsRaw, bind, Except.bind, throw, throwThe] at accepted
      | cons head tail =>
        simp only [encodePayloadsRaw] at accepted
        split at accepted <;> simp_all [bind, Except.bind, throw, throwThe]
    · intro checked registry key value layout carriers index encoded accepted
      cases carriers with
      | nil =>
        simp only [encodeEntriesRaw, pure, Except.pure] at accepted
        cases accepted
        exact .constructed .unit
      | cons => simp [encodeEntriesRaw, throw, throwThe] at accepted
  | succ fuel ih => exact ⟨raw_data_succ ih.1 ih.2.1 ih.2.2,
      payload_data_succ ih.1 ih.2.1, entries_data_succ ih.1 ih.2.2⟩

theorem encodeRaw_dataOnly {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {expected : TypeSystem.Ty} {carrier : SourceCoreDataValues.Value}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : encodeRaw fuel checked registry expected carrier = .ok encoded) : DataOnly encoded.value :=
  (data_only fuel).1 checked registry expected carrier encoded accepted

theorem encodePayloadsRaw_dataOnly {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {types : List TypeSystem.Ty}
    {carriers : List SourceCoreDataValues.Value} {index : Nat}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : encodePayloadsRaw fuel checked registry types carriers index = .ok encoded) : DataOnly encoded.value :=
  (data_only fuel).2.1 checked registry types carriers index encoded accepted

theorem encodeEntriesRaw_dataOnly {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {key value : TypeSystem.Ty} {layout : OrderedMapping.Layout}
    {carriers : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value)} {index : Nat}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : encodeEntriesRaw fuel checked registry key value layout carriers index = .ok encoded) :
    DataOnly encoded.value :=
  (data_only fuel).2.2 checked registry key value layout carriers index encoded accepted

theorem encodeDefaultRaw_dataOnly {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {sourceType : TypeSystem.Ty} {type : Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : encodeDefaultRaw fuel checked registry sourceType type = .ok encoded) : DataOnly encoded.value :=
  default_data (data_only fuel).1 accepted

/-- The actual codec and catalog projection remove the extended-definition
typing premise needed by the existing compatible raw soundness theorem. -/
theorem encodeRaw_restrict_typing {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {expected : TypeSystem.Ty} {carrier : SourceCoreDataValues.Value}
    {encoded : SourceCoreCompatibleValues.Extended registry Value} {world : StoreTyping}
    {type : Ty} {future : DataEnvironment}
    (accepted : encodeRaw fuel checked registry expected carrier = .ok encoded)
    (projected : checked.catalog.project expected = .ok type)
    (extension : checked.catalog.definitions.Extends future)
    (typed : RuntimeValueHasType world encoded.value type future) :
    RuntimeValueHasType world encoded.value type checked.catalog.definitions :=
  (encodeRaw_dataOnly accepted).restrict_definitions checked.definitionsTyped extension
    (project_wellFormed projected) typed

end Solcore.SourceSemantics.CoreLowering.CompatibleEncodedDataTyping
end

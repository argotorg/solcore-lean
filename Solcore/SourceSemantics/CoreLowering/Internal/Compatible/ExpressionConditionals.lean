import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionPrimitives
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.PrimitiveExpressions
import Solcore.Frontend.SourceCoreInteger
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FunctionCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.Core.CallableContract

/-!
# Compatible expressions: conditionals and builtin calls

Conditional expressions, and the meaning, Source and protocol of builtin calls.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalSource
/-! Independent source conditional traces retain the type-error alternative
until the compatible Bool representation excludes it. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
open Core Frontend SourceInference CompatibleExpressionPrimitives

inductive ConditionalTrace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition thenId elseId : ExpressionId) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | fault {reason after}
      (child : Dynamic.ExpressionFaults program context evidence source environment before condition reason after) :
      ConditionalTrace program context evidence source environment before condition thenId elseId (.fault reason) after
  | branch {flag middle outcome after}
      (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool flag) middle)
      (branchTrace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment middle
        (if flag then thenId else elseId) outcome after) :
      ConditionalTrace program context evidence source environment before condition thenId elseId outcome after
  | invalid {value actual after}
      (child : Dynamic.ExpressionEvaluates program context evidence source environment before condition value after)
      (invalid : ¬ Dynamic.BooleanValue value) (runtimeType : Dynamic.ValueRuntimeType value actual) :
      ConditionalTrace program context evidence source environment before condition thenId elseId (.fault (.typeMismatch .bool actual)) after

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome} {condition thenId elseId : ExpressionId}

theorem conditional_inv (metadata : Metadata checked source id node type)
    (form : node.form = .conditional condition thenId elseId) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ConditionalTrace program context evidence source environment before condition thenId elseId outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | conditionalTrue _ first second => exact .branch first (.value second)
    | conditionalFalse _ first second => exact .branch first (.value second)
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | conditionalCondition _ child => exact .fault child
    | conditionalTrueBranch _ first second => exact .branch first (.fault second)
    | conditionalFalseBranch _ first second => exact .branch first (.fault second)
    | conditionalType _ child invalid runtimeType => exact .invalid child invalid runtimeType

theorem conditional_intro (metadata : Metadata checked source id node type)
    (form : node.form = .conditional condition thenId elseId)
    (trace : ConditionalTrace program context evidence source environment before condition thenId elseId outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | fault child =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .conditionalCondition rfl child
  | @branch flag middle outcome after conditionTrace branchTrace =>
    cases flag
    all_goals cases branchTrace with
      | value branch =>
        apply Dynamic.ExpressionEvaluatesOutcome.value
        apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
        · rw [form, metadata.requirements, metadata.coercions]
          first | exact .conditionalTrue rfl conditionTrace branch | exact .conditionalFalse rfl conditionTrace branch
        · rw [metadata.coercions]; exact .nil
      | fault branch =>
        apply Dynamic.ExpressionEvaluatesOutcome.fault
        apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
        rw [form, metadata.requirements, metadata.coercions]
        first | exact .conditionalTrueBranch rfl conditionTrace branch | exact .conditionalFalseBranch rfl conditionTrace branch
  | invalid child invalid runtimeType =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .conditionalType rfl child invalid runtimeType

theorem conditional_source_types
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .conditional condition thenId elseId) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ conditionNode thenNode elseNode,
      source.lookupExpression? condition = some conditionNode ∧ source.lookupExpression? thenId = some thenNode ∧
      source.lookupExpression? elseId = some elseNode ∧ conditionNode.type = .bool ∧
      thenNode.type = node.type ∧ elseNode.type = node.type ∧
      ExpressionHasType source context condition conditionNode.type ∧
      ExpressionHasType source context thenId thenNode.type ∧ ExpressionHasType source context elseId elseNode.type := by
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
    | conditional conditionTyped thenTyped elseTyped =>
      obtain ⟨conditionNode, conditionContains, conditionType⟩ := conditionTyped.stored_type
      obtain ⟨thenNode, thenContains, thenType⟩ := thenTyped.stored_type
      obtain ⟨elseNode, elseContains, elseType⟩ := elseTyped.stored_type
      exact ⟨conditionNode, thenNode, elseNode, lookupExpression?_complete unique conditionContains,
        lookupExpression?_complete unique thenContains, lookupExpression?_complete unique elseContains,
        conditionType, thenType, elseType,
        conditionType ▸ conditionTyped, thenType ▸ thenTyped, elseType ▸ elseTyped⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalTree
/-! Conditional trees reuse certified primitive fragments. Recursive compound
constructors allow conditionals inside operands and selected branches. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
open Core Frontend SourceInference CompatibleExpressionPrimitives
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | primitive {id} (child : CompatibleExpressionPrimitives.Syntax source id) : Syntax source id
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

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | primitive {id lowered}
      (child : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id lowered) :
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

theorem Tree.projected {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree fuel values source context solved reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | primitive child => exact child.projected found
  | group metadata _ _ _ _ | pair metadata _ _ _ _ _ _ | unary metadata _ _ _ _ _ _ | binary metadata _ _ _ _ _ _ _ _ _ | conditional metadata _ _ _ _ _ _ _ _ _ _ =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    exact same ▸ metadata.projected

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalExecution
/-! Conditional helpers preserve the actual inserted Bool slot. They require
no store restriction and never evaluate the unselected branch. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
open Core

theorem choose_rename (type : Ty) (condition thenCode elseCode : Expr) (ξ : Renaming) :
    (LocalControl.choose type condition thenCode elseCode).rename ξ =
      LocalControl.choose type (condition.rename ξ) (thenCode.rename ξ) (elseCode.rename ξ) := by
  simp [LocalControl.choose, LanguageResult.bind, Expr.rename,
    Renaming.lift]

theorem choose_branch_evaluated {environment : Environment} {store finalStore : Store}
    {flag : Bool} {thenCode elseCode : Expr} {value : Value}
    (evaluated : Evaluates (.bool flag :: environment) store
      (.ifE (.var 0) (thenCode.weakenAt 0) (elseCode.weakenAt 0)) value finalStore) :
    Evaluates (.bool flag :: environment) store ((if flag then thenCode else elseCode).weakenAt 0) value finalStore := by
  cases evaluated with
  | ifTrue condition branch =>
    cases condition with
    | var selected => cases selected; exact branch
  | ifFalse condition branch =>
    cases condition with
    | var selected => cases selected; exact branch

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalMeaning
/-! Conditional and primitive composition over compatible heaps. Each child
semantic obligation is discharged by the tree induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : Scope}

/-- Static leaf support indexes the existing tree and its exact children.
It contains only leaf membership, with no execution or heap law. -/
inductive Tree.LiteralSites (literals : GenericExpressionMeaning.Certificate) :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Tree fuel values source context solved reasonAt scope id lowered → Prop where
  | primitive {id lowered}
      (child : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id lowered)
      (childSites : CompatibleExpressionPrimitives.Tree.LiteralSites literals child) :
      LiteralSites literals (Tree.primitive (scope := scope) child)
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

/-- The exact old tree restricted to the supplied static leaf certificates. -/
def Tree.WithLiterals (literals : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun current id lowered => ∃ tree : Tree fuel values source context solved reasonAt current id lowered,
    tree.LiteralSites literals

/-- Ordinary literal membership supplies support for every original tree. -/
theorem Tree.literalSites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree fuel values source context solved reasonAt scope id lowered) :
    tree.LiteralSites (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code) := by
  induction tree with
  | primitive child => exact .primitive child child.literalSites
  | group metadata form innerFound sourceType child childIH => exact .group metadata form innerFound sourceType child childIH
  | pair metadata form leftFound rightFound sourceType firstTree secondTree firstTreeIH secondTreeIH => exact .pair metadata form leftFound rightFound sourceType firstTree secondTree firstTreeIH secondTreeIH
  | unary metadata form found inputType outputType profile child childIH => exact .unary metadata form found inputType outputType profile child childIH
  | binary metadata form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH => exact .binary metadata form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH
  | conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeIH thenTreeIH elseTreeIH => exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeIH thenTreeIH elseTreeIH

private def Two (scope : Scope) (left right : ExpressionId) (first second : SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate := fun current id code =>
  current = scope ∧ ((id = left ∧ code = first) ∨ (id = right ∧ code = second))

private theorem two_tree {source : TypedSource} {scope : Scope} {left right : ExpressionId}
    {leftNode rightNode : ExpressionNode} {first second : SourceCoreBasic.LoweredExpr}
    (leftFound : source.lookupExpression? left = some leftNode)
    (rightFound : source.lookupExpression? right = some rightNode) :
    DataExpressionSequence.Tree source (Two scope left right first second) scope
      [left, right] [leftNode.type, rightNode.type] [first, second] :=
  .cons leftFound ⟨rfl, .inl ⟨rfl, rfl⟩⟩ (.single rightFound ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

private theorem pair_result {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {leftType rightType : TypeSystem.Ty}
    {first second : SourceCoreBasic.LoweredExpr} {faults : FunctionCalls.FaultRep}
    {sequence : DataExpressionSequence.Outcome} {value : Value}
    (result : DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel checked registry functions)
      mapping world [leftType, rightType] [first, second] faults sequence value) :
    ∃ outcome, CompatibleExpressionProducts.PacksOutcome sequence outcome ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping world (.product leftType rightType) (.product first.type second.type) faults outcome value := by
  cases result with
  | values represented =>
    change DataExpressionSequence.Values _ _ _ [leftType, rightType] [first.type, second.type] _ _ at represented
    cases represented with
    | cons left tail =>
      cases tail with
      | cons right tail =>
        cases tail
        exact ⟨_, .values (.cons (.singleton _)), .value (.product left right)⟩
  | fault matched => exact ⟨_, .fault _, .fault matched⟩


variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  {literals : GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include unique in
theorem preserves_with_literals_and_post
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (literalMeaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults post)
    (readMeaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults post) :
    ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults post := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | primitive child childSites =>
    exact CompatibleExpressionPrimitives.preserves_with_literals_and_post (fuel := fuel) (reasonAt := reasonAt) functions program evidence unique sequenceJoins ordinaryJoins literalMeaning readMeaning ⟨child, childSites⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after
      environments heaps locals agrees trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      ih innerFound environments heaps locals agrees (CompatibleExpressionProducts.group_inv metadata form unique trace)
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
      ExpressionFailurePostContracts.OutcomePost.expression ordinaryJoins
        (.group (lookupExpression?_sound metadata.found) form
          (ScalarExpressionFaultPostContracts.ordinary_layout metadata)) (CompatibleExpressionProducts.group_inv metadata form unique trace) retained⟩
    simpa only [sourceType] using represented
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree firstTreeSites secondTreeSites leftIH rightIH =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after
      environments heaps locals agrees trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have children : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Two scope left right first second) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    obtain ⟨sequence, sourceTrace, packed⟩ := CompatibleExpressionProducts.pair_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      (two_tree (first := first) (second := second) leftFound rightFound).preserves_with_post sequenceJoins children environments heaps locals agrees sourceTrace
    obtain ⟨actualOutcome, actualPack, payload⟩ := pair_result represented
    have sameOutcome := actualPack.functional packed
    subst actualOutcome
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
      ScalarExpressionFaultPostContracts.tuple_outcome ordinaryJoins metadata form sourceTrace packed retained⟩
    simpa only [sourceType] using payload

  | @unary id node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child childSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after environments heaps locals agrees trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := unary_inv metadata form unique trace
    cases sourceStep with
    | value childTrace applied =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih childFound environments heaps locals agrees (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, actualApplied, coreApplied, resultRep⟩ := profile.preserves payload
        have same := actualApplied.functional applied
        subst sourceResult
        refine ⟨.inRight .word result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
        · rw [unary_rename]; exact LocalPrimitiveResults.unary_success evaluated coreApplied
        · exact .value (outputType ▸ resultRep)
    | fault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih childFound environments heaps locals agrees (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [unary_rename]; exact LocalPrimitiveResults.unary_failure evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          ScalarExpressionFaultPostContracts.expression_fault_outcome ordinaryJoins
            (.unary (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata)) childTrace retained⟩
    | invalid childTrace failed =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := ih childFound environments heaps locals agrees (.value childTrace)
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨_, _, applied, _, _⟩ := profile.preserves payload
        exact False.elim (unary_fault_excluded applied failed)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree firstSites secondSites leftIH rightIH =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after environments heaps locals agrees trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := binary_inv metadata form unique trace
    cases sourceStep with
    | leftFault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        leftIH leftFound environments heaps locals agrees (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact mode.left_failure operator evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          ScalarExpressionFaultPostContracts.expression_fault_outcome ordinaryJoins
            (.binaryLeft (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata)) childTrace retained⟩
    | leftInvalid childTrace invalid =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := leftIH leftFound environments heaps locals agrees (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        exact False.elim (profile.left_valid payload invalid)
    | short childTrace circuit =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        leftIH leftFound environments heaps locals agrees (.value childTrace)
      cases represented with
      | value payload =>
        rw [leftType] at payload
        obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit evaluated
        exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
          .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
    | rightFault firstTrace continues secondTrace =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstRetained⟩ :=
        leftIH leftFound environments heaps locals agrees (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue) (.fault secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact profile.right_failure payload continues first second,
            .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata,
            ScalarExpressionFaultPostContracts.expression_fault_outcome ordinaryJoins
              (.binaryRight (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata) firstTrace continues) secondTrace retained⟩
    | value firstTrace continues secondTrace applied =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstRetained⟩ :=
        leftIH leftFound environments heaps locals agrees (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue) (.value secondTrace)
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
            firstFrame.trans frame, firstMetadata.trans heapMetadata, trivial⟩
    | invalid firstTrace continues secondTrace failed =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, _, firstMetadata, _⟩ :=
        leftIH leftFound environments heaps locals agrees (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, _, _, _, second, represented, _, maps, worlds, _⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          obtain ⟨_, _, applied, _, _⟩ := profile.right_success leftPayload rightPayload continues first second
          exact False.elim (binary_fault_excluded applied failed)

  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeSites thenTreeSites elseTreeSites conditionIH thenIH elseIH =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after environments heaps locals agrees trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have sourceStep := conditional_inv metadata form unique trace
    cases sourceStep with
    | fault childTrace =>
      obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        conditionIH conditionFound environments heaps locals agrees (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [choose_rename]; exact LocalControl.choose_failure type evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          ScalarExpressionFaultPostContracts.expression_fault_outcome ordinaryJoins
            (.conditionalCondition (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata)) childTrace retained⟩
    | @branch flag middle outcome after conditionTrace branchTrace =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstRetained⟩ :=
        conditionIH conditionFound environments heaps locals agrees (.value conditionTrace)
      cases represented with
      | value payload =>
        obtain ⟨actualFlag, sourceEq, coreEq⟩ := bool_fields payload
        cases sourceEq
        subst coreEq
        cases flag with
        | false =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
            elseIH elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool false)) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata,
            ExpressionFailurePostContracts.OutcomePost.expression ordinaryJoins
              (.conditionalFalse (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata) conditionTrace) branchTrace retained⟩
          · rw [choose_rename]; exact LocalControl.choose_false type first branch
          · simpa only [elseType] using represented
        | true =>
          obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
            thenIH thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool true)) branchTrace
          rw [GenericExpressionMeaning.rename_prefix] at branch
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata,
            ExpressionFailurePostContracts.OutcomePost.expression ordinaryJoins
              (.conditionalTrue (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata) conditionTrace) branchTrace retained⟩
          · rw [choose_rename]; exact LocalControl.choose_true type first branch
          · simpa only [thenType] using represented
    | invalid childTrace invalid runtimeType =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := conditionIH conditionFound environments heaps locals agrees (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨flag, rfl, _⟩ := bool_fields payload
        exact False.elim (invalid trivial)


theorem reflects_with_literals_and_post
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (literalMeaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults post)
    (readMeaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults post) :
    ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults post := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | primitive child childSites =>
    exact CompatibleExpressionPrimitives.reflects_with_literals_and_post (fuel := fuel) (reasonAt := reasonAt) functions program evidence sequenceJoins ordinaryJoins literalMeaning readMeaning ⟨child, childSites⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore
      environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      ih innerFound environments heaps locals agrees evaluated
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.group_intro metadata form trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
      ExpressionFailurePostContracts.OutcomePost.expression ordinaryJoins
        (.group (lookupExpression?_sound metadata.found) form
          (ScalarExpressionFaultPostContracts.ordinary_layout metadata)) trace retained⟩
    simpa only [sourceType] using represented
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType firstTree secondTree firstTreeSites secondTreeSites leftIH rightIH =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore
      environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have children : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Two scope left right first second) faults post := by
      intro childScope childId childCode entry
      obtain ⟨rfl, alternatives⟩ := entry
      rcases alternatives with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact leftIH
      · exact rightIH
    obtain ⟨sequence, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      (two_tree (first := first) (second := second) leftFound rightFound).reflects_with_post sequenceJoins children environments heaps locals agrees evaluated
    obtain ⟨outcome, packed, payload⟩ := pair_result represented
    refine ⟨outcome, after, finalMap, finalWorld, CompatibleExpressionProducts.pair_intro metadata form sourceTrace packed, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
      ScalarExpressionFaultPostContracts.tuple_outcome ordinaryJoins metadata form sourceTrace packed retained⟩
    simpa only [sourceType] using payload

  | @unary id node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child childSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [unary_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih childFound environments heaps locals agrees childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_failure (operator := core) childEvaluation) complete
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.fault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata,
            ScalarExpressionFaultPostContracts.expression_fault_outcome ordinaryJoins
              (.unary (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata)) failed retained⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih childFound environments heaps locals agrees childEvaluation
      cases represented with
      | value payload =>
        rw [inputType] at payload
        obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
        obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_success childEvaluation coreApplied) complete
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, unary_intro metadata form (.value childTrace applied),
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree firstSites secondSites leftIH rightIH =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [Mode.binary_rename] at evaluated
    have complete := evaluated
    rw [Mode.binary_eq] at evaluated
    cases evaluated with
    | caseLeft leftEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        leftIH leftFound environments heaps locals agrees leftEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (mode.left_failure operator leftEvaluation)
          exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.leftFault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata,
            ScalarExpressionFaultPostContracts.expression_fault_outcome ordinaryJoins
              (.binaryLeft (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata)) failed retained⟩
    | caseRight leftEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstRetained⟩ :=
        leftIH leftFound environments heaps locals agrees leftEvaluation
      cases represented with
      | @value sourceValue coreValue payload =>
        rw [leftType] at payload
        cases trace with
        | value firstTrace =>
          rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
          · obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit leftEvaluation
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            exact ⟨_, middle, middleMap, middleWorld, binary_intro metadata form (.short firstTrace circuit),
              .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, trivial⟩
          · obtain ⟨rightValue, rightStore, rightEvaluation⟩ := profile.right_evaluated payload continues branch
            have shifted := rightEvaluation
            rw [← GenericExpressionMeaning.rename_prefix] at shifted
            obtain ⟨rightOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
              rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees _) shifted
            cases represented with
            | fault matched =>
              cases trace with
              | fault failed =>
                have combined := profile.right_failure payload continues leftEvaluation rightEvaluation
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.rightFault firstTrace continues failed),
                  .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata,
                  ScalarExpressionFaultPostContracts.expression_fault_outcome ordinaryJoins
                    (.binaryRight (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata) firstTrace continues) failed retained⟩
            | value rightPayload =>
              rw [rightType] at rightPayload
              have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
              obtain ⟨sourceResult, result, applied, resultRep, combined⟩ :=
                profile.right_success leftPayload rightPayload continues leftEvaluation rightEvaluation
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              cases trace with
              | value secondTrace =>
                exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.value firstTrace continues secondTrace applied),
                  .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata, trivial⟩

  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeSites thenTreeSites elseTreeSites conditionIH thenIH elseIH =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [choose_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        conditionIH conditionFound environments heaps locals agrees childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalControl.choose_failure type childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, conditional_intro metadata form (.fault failed), .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata,
          ScalarExpressionFaultPostContracts.expression_fault_outcome ordinaryJoins
            (.conditionalCondition (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata)) failed retained⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstRetained⟩ :=
        conditionIH conditionFound environments heaps locals agrees childEvaluation
      cases represented with
      | value payload =>
        obtain ⟨flag, sourceEq, coreEq⟩ := bool_fields payload
        subst sourceEq
        subst coreEq
        cases trace with
        | value conditionTrace =>
          have selected := choose_branch_evaluated branch
          cases flag with
          | false =>
            change Evaluates _ _ ((elseCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
              elseIH elseFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false)) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace branchTrace),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
            ExpressionFailurePostContracts.OutcomePost.expression ordinaryJoins
              (.conditionalFalse (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata) conditionTrace) branchTrace retained⟩
            simpa only [elseType] using represented
          | true =>
            change Evaluates _ _ ((thenCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
              thenIH thenFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true)) selected
            refine ⟨outcome, after, finalMap, finalWorld, conditional_intro metadata form (.branch conditionTrace branchTrace),
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
            ExpressionFailurePostContracts.OutcomePost.expression ordinaryJoins
              (.conditionalTrue (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata) conditionTrace) branchTrace retained⟩
            simpa only [thenType] using represented


include extension unique uninitialized in
theorem preserves_with_literals
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.Preserves.forget
    (preserves_with_literals_and_post (functions := functions) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence) (unique := unique)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ExpressionFailurePostContracts.Preserves.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Preserves.of_trivial
        (certificate := CompatibleExpressionReads.LoweredRead fuel values source context reasonAt)
        (by
          intro scope id lowered receipt
          exact CompatibleExpressionReads.loweredRead_preserves functions extension program context evidence reasonAt uninitialized unique receipt)))

include extension valid unique uninitialized in
theorem preserves :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact preserves_with_literals functions extension program evidence unique uninitialized
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults) ⟨tree, tree.literalSites⟩


include extension uninitialized in
theorem reflects_with_literals
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.Reflects.forget
    (reflects_with_literals_and_post (functions := functions) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ExpressionFailurePostContracts.Reflects.of_trivial literalMeaning)
      (ExpressionFailurePostContracts.Reflects.of_trivial
        (certificate := CompatibleExpressionReads.LoweredRead fuel values source context reasonAt)
        (by
          intro scope id lowered receipt
          exact CompatibleExpressionReads.loweredRead_reflects functions extension program context evidence reasonAt uninitialized receipt)))

include extension valid uninitialized in
theorem reflects :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact reflects_with_literals functions extension program evidence uninitialized
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults) ⟨tree, tree.literalSites⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalCertificates
/-! Successful ordinary Functions lowering extracts the recursive conditional
syntax tree. Operator admission follows empty retained evidence and independent
source typing; actual native operand checks select Word versus Integer. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
open Core Frontend SourceInference CompatibleExpressionPrimitives

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


def selectedUnary (operator : Syntax.UnaryOp) (operand : Ty) : UnaryOp :=
  if operator = .bitNot && operand = .integer then .integerNot else SourceCorePrimitive.unaryOperator operator
def selectedMode (operand : Ty) : Mode := if operand = .integer then .integer else .word

theorem unary_selected {catalog : SourceCoreCompatibleCatalog.Catalog}
    {operator : Syntax.UnaryOp} {operand result : TypeSystem.Ty} {core : UnaryOp} {type : Ty}
    (profile : UnaryProfile operator operand result core) (projected : catalog.project operand = .ok type) :
    selectedUnary operator type = core := by
  cases profile <;> cases projected <;> rfl
theorem binary_selected {catalog : SourceCoreCompatibleCatalog.Catalog}
    {operator : Syntax.BinaryOp} {operand result : TypeSystem.Ty} {mode : Mode} {type : Ty}
    (profile : BinaryProfile operator operand result mode) (projected : catalog.project operand = .ok type) :
    selectedMode type = mode := by
  cases profile <;> cases projected <;> rfl

inductive Compound : ExpressionForm → Prop where
  | unary (operator : Syntax.UnaryOp) (operand : ExpressionId) : Compound (.unary operator operand)
  | binary (operator : Syntax.BinaryOp) (left right : ExpressionId) : Compound (.binary left operator right)
  | group (inner : ExpressionId) : Compound (.group inner)
  | pair (left right : ExpressionId) : Compound (.tuple [left, right])
  | conditional (condition thenId elseId : ExpressionId) : Compound (.conditional condition thenId elseId)

inductive Step (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
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

theorem step_of_functions
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
  | primitive syntaxTree =>
    refine (fun ⟨tree, sites⟩ => ⟨_, Tree.LiteralSites.primitive tree sites⟩) (CompatibleExpressionPrimitives.tree_of_functions_with_literals literals literalFactory unique declarations ?_ ?_ syntaxTree found typed accepted)
    · exact ⟨fun id child => policyFor.special id (.primitive child),
        fun id child => policyFor.read id (.primitive child), policyFor.lower, policyFor.leaf⟩
    · exact fun id node child => coercions id node (.primitive child)
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

/-- Original tree-only API, projected from the single supported extraction. -/
theorem tree_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
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
    CompatibleExpressionProducts.LiteralFactory.ordinary unique declarations policyFor coercions syntaxTree found typed accepted).choose

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinBodyMeaning
/-! Finite meaning of every actual compiler-provided builtin body. The argument
relation describes scalar source values and their real packed native input.
This is the body boundary: argument effects and callable decoration are handled
by expression and indexed-call adapters. Captures and stores are arbitrary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinBodyMeaning
open Core Frontend SourceInference

inductive InputRep : BuiltinFunctionId → List Dynamic.Value → Value → Prop where
  | integerSub (left right : Int) : InputRep .integerSub [.integer left, .integer right] (.pair (.integer left) (.integer right))
  | wordFromInteger (value : Int) : InputRep .wordFromInteger [.integer value] (.integer value)
  | integerAdd (left right : Int) : InputRep .integerAdd [.integer left, .integer right] (.pair (.integer left) (.integer right))
  | integerEq (left right : Int) : InputRep .integerEq [.integer left, .integer right] (.pair (.integer left) (.integer right))
  | integerLt (left right : Int) : InputRep .integerLt [.integer left, .integer right] (.pair (.integer left) (.integer right))
  | integerMul (left right : Int) : InputRep .integerMul [.integer left, .integer right] (.pair (.integer left) (.integer right))
  | wordToInteger (value : Word) : InputRep .wordToInteger [.word value] (.word value)

theorem InputRep.runtime_hasType {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (represented : InputRep function arguments input)
    (world : StoreTyping) (definitions : DataEnvironment) :
    RuntimeValueHasType world input (SourceCoreInteger.builtinParameter function) definitions := by
  cases represented <;> first | exact .pair .integer .integer | exact .integer | exact .word

/-- Source builtin application determines a concrete evaluation of the actual
body; no compiler or primitive implementation is placed in the source relation. -/
theorem InputRep.body_meaning {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (represented : InputRep function arguments input)
    (captured : Environment) (store : Store) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      Evaluates (input :: captured) store (LanguageResult.success (SourceCoreInteger.builtinBody function))
        (.inRight .word nativeResult) store := by
  cases represented with
  | integerSub left right =>
    exact ⟨_, _, .integerSub left right, .integer _, .inRight (.binary (.first (.var rfl)) (.second (.var rfl)) rfl)⟩
  | wordFromInteger value =>
    exact ⟨_, _, .wordFromInteger value, .word _, .inRight (.unary (.var rfl) rfl)⟩
  | integerAdd left right =>
    exact ⟨_, _, .integerAdd left right, .integer _, .inRight (.binary (.first (.var rfl)) (.second (.var rfl)) rfl)⟩
  | integerEq left right =>
    exact ⟨_, _, .integerEq left right, .bool _, .inRight (.binary (.first (.var rfl)) (.second (.var rfl)) rfl)⟩
  | integerLt left right =>
    exact ⟨_, _, .integerLt left right, .bool _, .inRight (.binary (.first (.var rfl)) (.second (.var rfl)) rfl)⟩
  | integerMul left right =>
    exact ⟨_, _, .integerMul left right, .integer _, .inRight (.binary (.first (.var rfl)) (.second (.var rfl)) rfl)⟩
  | wordToInteger value =>
    exact ⟨_, _, .wordToInteger value, .integer _, .inRight (.unary (.var rfl) rfl)⟩

/-- A completed actual builtin body reconstructs its independent source result
and leaves the entire native store unchanged. -/
theorem InputRep.body_reflects {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (represented : InputRep function arguments input)
    {captured : Environment} {store finalStore : Store} {result : Value}
    (completed : Evaluates (input :: captured) store (LanguageResult.success (SourceCoreInteger.builtinBody function)) result finalStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      result = .inRight .word nativeResult ∧ finalStore = store := by
  obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ := represented.body_meaning captured store
  obtain ⟨same, stores⟩ := evaluation_deterministic completed evaluated
  exact ⟨sourceResult, nativeResult, applied, related, same, stores⟩

/-- Invocation uses the exact compiler closure and an already selected packed
input. The selected argument may have produced the store seen by the body. -/
theorem InputRep.closure_preserves {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (represented : InputRep function arguments input)
    {environment : Environment} {before argumentStore : Store} {argument : Expr}
    (argumentEvaluated : Evaluates environment before argument input argumentStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      Evaluates environment before (.apply (SourceCoreInteger.builtinClosure function) argument)
        (.inRight .word nativeResult) argumentStore := by
  obtain ⟨sourceResult, nativeResult, applied, related, body⟩ := represented.body_meaning environment argumentStore
  exact ⟨sourceResult, nativeResult, applied, related, .apply .lambda argumentEvaluated body⟩

theorem InputRep.closure_reflects {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (represented : InputRep function arguments input)
    {environment : Environment} {before argumentStore finalStore : Store} {argument : Expr} {result : Value}
    (argumentEvaluated : Evaluates environment before argument input argumentStore)
    (completed : Evaluates environment before (.apply (SourceCoreInteger.builtinClosure function) argument) result finalStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      result = .inRight .word nativeResult ∧ finalStore = argumentStore := by
  obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ := represented.closure_preserves argumentEvaluated
  obtain ⟨same, stores⟩ := evaluation_deterministic completed evaluated
  exact ⟨sourceResult, nativeResult, applied, related, same, stores⟩
end Solcore.SourceSemantics.CoreLowering.BuiltinBodyMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinCallSource
/-! Direct builtin calls evaluate their arguments in source order. The callee
metadata is validated statically. Independent application and argument faults
remain explicit until the represented scalar inputs exclude invalid application.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinCalls
open Core Frontend SourceInference CompatibleExpressionPrimitives BuiltinBodyMeaning DataPatternValues

inductive SourceTrace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (arguments : List ExpressionId) (function : BuiltinFunctionId) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | argumentsFault {reason after}
      (failed : Dynamic.ExpressionsFault program context evidence source environment before arguments reason after) :
      SourceTrace program context evidence source environment before arguments function (.fault reason) after
  | apply {values middle outcome after}
      (argumentsEvaluated : Dynamic.ExpressionsEvaluate program context evidence source environment before arguments values middle)
      (applied : FunctionCallBody.Outcome program context evidence [] middle (.builtin ⟨function⟩) values outcome after) :
      SourceTrace program context evidence source environment before arguments function outcome after

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id callee : ExpressionId}
  {node : ExpressionNode} {type : Ty} {arguments : List ExpressionId} {function : BuiltinFunctionId}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}

theorem source_inv (metadata : Metadata checked source id node type)
    (form : node.form = .call callee arguments (.builtinFunction function)) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    SourceTrace program context evidence source environment before arguments function outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | builtinCall _ argumentsEvaluated applied => exact .apply argumentsEvaluated (.value applied)
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | builtinArguments _ argumentsFailed => exact .argumentsFault argumentsFailed
    | builtinApply _ argumentsEvaluated failed => exact .apply argumentsEvaluated (.fault failed)

theorem source_intro (metadata : Metadata checked source id node type)
    (form : node.form = .call callee arguments (.builtinFunction function))
    (trace : SourceTrace program context evidence source environment before arguments function outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | argumentsFault failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .builtinArguments rfl failed
  | apply argumentsEvaluated application =>
    cases application with
    | value applied =>
      apply Dynamic.ExpressionEvaluatesOutcome.value
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
      · rw [form, metadata.requirements, metadata.coercions]
        exact .builtinCall rfl argumentsEvaluated applied
      · rw [metadata.coercions]; exact .nil
    | fault failed =>
      apply Dynamic.ExpressionEvaluatesOutcome.fault
      apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
      rw [form, metadata.requirements, metadata.coercions]
      exact .builtinApply rfl argumentsEvaluated failed

private theorem types_exclude_mismatch {values : List Dynamic.Value} {types : List TypeSystem.Ty}
    (typed : ListRel Dynamic.ValueRuntimeType values types)
    {expected actual : TypeSystem.Ty} (mismatch : Dynamic.ValuesFirstTypeMismatch values types expected actual) : False := by
  induction typed with
  | nil => cases mismatch
  | cons head tail ih =>
    cases mismatch with
    | head actual different => exact different (head.functional actual).symm
    | tail _ fault => exact ih fault

theorem InputRep.source_argument_types {function : BuiltinFunctionId} {arguments : List Dynamic.Value} {input : Value}
    (inputs : InputRep function arguments input) :
    ListRel Dynamic.ValueRuntimeType arguments function.parameterTypes := by
  cases inputs <;> first
    | exact .cons (.integer _) (.cons (.integer _) .nil)
    | exact .cons (.integer _) .nil
    | exact .cons (.word _) .nil

theorem InputRep.excludes_callable_fault {function : BuiltinFunctionId} {arguments : List Dynamic.Value} {input : Value}
    (inputs : InputRep function arguments input)
    {program : Program} {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (fault : Dynamic.CallableFaults program context caller invocation before (.builtin ⟨function⟩) arguments reason after) : False := by
  cases fault with
  | notCallable invalid => exact invalid trivial
  | builtinArity mismatch =>
    cases inputs <;> exact mismatch rfl
  | builtinArgumentType _ mismatch => exact types_exclude_mismatch (InputRep.source_argument_types inputs) mismatch
end Solcore.SourceSemantics.CoreLowering.BuiltinCalls
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBuiltinMeaning
/-! The compatible argument payloads select the real packed input of every
builtin. Independent source primitive results enter the existing full payload
relation. Argument effects and callable gates remain the caller's boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBuiltinMeaning
open Core Frontend SourceInference GeneralHeap CompatiblePayload DataPatternValues
open BuiltinBodyMeaning

def argumentTypes : BuiltinFunctionId → List Ty
  | .wordToInteger => [.word]
  | .wordFromInteger => [.integer]
  | _ => [.integer, .integer]

theorem argumentTypes_project {checked : SourceCoreCompatibleCatalog.Checked}
    (function : BuiltinFunctionId) :
    function.parameterTypes.mapM checked.catalog.project = .ok (argumentTypes function) := by
  cases function <;> rfl

theorem argumentTypes_pack (function : BuiltinFunctionId) :
    SourceCoreCompatibleCatalog.packTypes (argumentTypes function) = SourceCoreInteger.builtinParameter function := by
  cases function <;> rfl

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping} {identities : Dynamic.Value → Word → Prop}

/-- Exact scalar values follow from the common compatible relation, including
its metadata compatibility constructor. No input codec or source evaluator is used. -/
theorem input_of_values
    (observations : CompatibleEquality.FunctionObservations checked.catalog functions identities)
    {function : BuiltinFunctionId} {arguments : List Dynamic.Value} {values : List Value}
    (represented : ValuesRep checked registry functions mapping world function.parameterTypes arguments values
      (argumentTypes function)) :
    InputRep function arguments (packValues values) := by
  cases function
  all_goals cases represented with
  | cons head tail =>
    first
    | obtain ⟨value, rfl, rfl⟩ := CompatiblePlaceModifier.word_fields observations head
      cases tail
      exact .wordToInteger value
    | obtain ⟨left, rfl, rfl⟩ := CompatiblePlaceModifier.integer_fields observations head
      cases tail with
      | nil => exact .wordFromInteger left
    | obtain ⟨left, rfl, rfl⟩ := CompatiblePlaceModifier.integer_fields observations head
      cases tail with
      | cons rightRep rest =>
        obtain ⟨right, rfl, rfl⟩ := CompatiblePlaceModifier.integer_fields observations rightRep
        cases rest
        first
        | exact .integerSub left right
        | exact .integerAdd left right
        | exact .integerEq left right
        | exact .integerLt left right
        | exact .integerMul left right

theorem result_represents {function : BuiltinFunctionId} {arguments : List Dynamic.Value}
    {input : Value} (inputs : InputRep function arguments input)
    {sourceResult : Dynamic.Value} {nativeResult : Value}
    (applied : Dynamic.BuiltinApplies function arguments sourceResult)
    (represented : IntegerPrimitives.ResultRepresents sourceResult nativeResult) :
    ValueRep checked registry functions mapping world function.returnType sourceResult nativeResult
      (SourceCoreInteger.builtinResult function) := by
  cases inputs <;> cases applied <;> cases represented <;> first
    | exact .integer _
    | exact .bool _
    | exact .word _

/-- The actual compiler body preserves independent source application and
keeps the whole native store supplied after argument evaluation unchanged. -/
theorem preserves
    (observations : CompatibleEquality.FunctionObservations checked.catalog functions identities)
    {function : BuiltinFunctionId} {arguments : List Dynamic.Value} {values : List Value}
    (represented : ValuesRep checked registry functions mapping world function.parameterTypes arguments values
      (argumentTypes function))
    {sourceResult : Dynamic.Value} (application : Dynamic.BuiltinApplies function arguments sourceResult)
    (captured : Environment) (store : Store) :
    ∃ nativeResult,
      ValueRep checked registry functions mapping world function.returnType sourceResult nativeResult
        (SourceCoreInteger.builtinResult function) ∧
      Evaluates (packValues values :: captured) store
        (LanguageResult.success (SourceCoreInteger.builtinBody function))
        (.inRight .word nativeResult) store := by
  have inputs := input_of_values observations represented
  obtain ⟨actualSource, nativeResult, applied, related, evaluated⟩ := inputs.body_meaning captured store
  have same := applied.functional application
  subst actualSource
  exact ⟨nativeResult, result_represents inputs application related, evaluated⟩

/-- A completed actual builtin body constructs the independent source
application and its compatible result, without assuming a source execution. -/
theorem reflects
    (observations : CompatibleEquality.FunctionObservations checked.catalog functions identities)
    {function : BuiltinFunctionId} {arguments : List Dynamic.Value} {values : List Value}
    (represented : ValuesRep checked registry functions mapping world function.parameterTypes arguments values
      (argumentTypes function))
    {captured : Environment} {store finalStore : Store} {result : Value}
    (completed : Evaluates (packValues values :: captured) store
      (LanguageResult.success (SourceCoreInteger.builtinBody function)) result finalStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function arguments sourceResult ∧
      ValueRep checked registry functions mapping world function.returnType sourceResult nativeResult
        (SourceCoreInteger.builtinResult function) ∧
      result = .inRight .word nativeResult ∧ finalStore = store := by
  have inputs := input_of_values observations represented
  obtain ⟨sourceResult, nativeResult, applied, related, resultEq, storeEq⟩ := inputs.body_reflects completed
  exact ⟨sourceResult, nativeResult, applied, result_represents inputs applied related, resultEq, storeEq⟩
end Solcore.SourceSemantics.CoreLowering.CompatibleBuiltinMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.BuiltinCallProtocol
/-! Finite builtin invocation beneath the real tagged/contracted call helpers.
The pure callee and builtin gates cannot fail. Whole completion exposes argument
completion first, so a caller can apply its independent child reflection theorem.
Argument effects occur once and are retained by the actual builtin body. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinCalls.Protocol
open Core Frontend SourceInference BuiltinBodyMeaning

def tagged (function : BuiltinFunctionId) (identity : Word) : Expr :=
  LanguageResult.success (TaggedFunction.identified identity (SourceCoreInteger.builtinClosure function))

def taggedValue (function : BuiltinFunctionId) (identity : Word) (captured : Environment) : Value :=
  .pair (.inRight .unit (.word identity))
    (.closure (SourceCoreInteger.builtinParameter function)
      (LanguageResult.resultType (SourceCoreInteger.builtinResult function))
      (LanguageResult.success (SourceCoreInteger.builtinBody function)) captured)

def contracted (function : BuiltinFunctionId) (identity contract : Word) : Expr :=
  LanguageResult.success (CallableContract.wrap contract
    (TaggedFunction.identified identity (SourceCoreInteger.builtinClosure function)))

def contractedValue (function : BuiltinFunctionId) (identity contract : Word) (captured : Environment) : Value :=
  .pair (taggedValue function identity captured) (.word contract)

theorem tagged_evaluates (function : BuiltinFunctionId) (identity : Word)
    (environment : Environment) (store : Store) :
    Evaluates environment store (tagged function identity)
      (.inRight .word (taggedValue function identity environment)) store :=
  .inRight (.pair (.inRight .word) .lambda)

theorem contracted_evaluates (function : BuiltinFunctionId) (identity contract : Word)
    (environment : Environment) (store : Store) :
    Evaluates environment store (contracted function identity contract)
      (.inRight .word (contractedValue function identity contract environment)) store :=
  .inRight (.pair (.pair (.inRight .word) .lambda) .word)

theorem gates_accept (contract unknown : Word) (phase : CallableContract.Phase) :
    CallableContract.decision [⟨contract, none, none⟩] phase unknown contract = none := by
  cases phase <;> simp [CallableContract.decision, CallableContract.Gate.reason]

theorem tagged_argument_completes {function : BuiltinFunctionId} {identity : Word}
    {environment : Environment} {store finalStore : Store} {arguments : Expr} {result : Value}
    (completed : Evaluates environment store
      (TaggedFunction.call (SourceCoreInteger.builtinResult function) (tagged function identity) arguments)
      result finalStore) :
    ∃ argumentValue argumentStore,
      Evaluates (taggedValue function identity environment :: environment) store
        (arguments.weakenAt 0) argumentValue argumentStore := by
  have tail := (LanguageResult.bind_success_iff (tagged_evaluates function identity environment store)).mp completed
  cases tail with
  | caseLeft argument _ => exact ⟨_, _, argument⟩
  | caseRight argument _ => exact ⟨_, _, argument⟩

theorem contracted_argument_completes {function : BuiltinFunctionId} {identity contract unknown : Word}
    {environment : Environment} {store finalStore : Store} {arguments : Expr} {result : Value}
    (completed : Evaluates environment store
      (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
        (contracted function identity contract) arguments) result finalStore) :
    ∃ argumentValue argumentStore,
      Evaluates (.unit :: contractedValue function identity contract environment :: environment) store
        ((arguments.weakenAt 0).weakenAt 0) argumentValue argumentStore := by
  have tail := (LanguageResult.bind_success_iff
    (contracted_evaluates function identity contract environment store)).mp completed
  have stage := CallableContract.dispatch_evaluates [⟨contract, none, none⟩] .beforeArguments unknown contract
    (show Evaluates (contractedValue function identity contract environment :: environment) store
      (.second (.var 0)) (.word contract) store from .second (.var rfl))
  rw [gates_accept] at stage
  have argumentsTail := (LanguageResult.bind_success_iff stage).mp tail
  cases argumentsTail with
  | caseLeft argument _ => exact ⟨_, _, argument⟩
  | caseRight argument _ => exact ⟨_, _, argument⟩

theorem tagged_preserves {function : BuiltinFunctionId} {sources : List Dynamic.Value} {input : Value}
    (inputs : InputRep function sources input) {identity : Word}
    {environment : Environment} {store argumentStore : Store} {arguments : Expr}
    (argumentsEvaluated : Evaluates (taggedValue function identity environment :: environment) store
      (arguments.weakenAt 0) (.inRight .word input) argumentStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function sources sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      Evaluates environment store
        (TaggedFunction.call (SourceCoreInteger.builtinResult function) (tagged function identity) arguments)
        (.inRight .word nativeResult) argumentStore := by
  obtain ⟨sourceResult, nativeResult, applied, related, body⟩ := inputs.body_meaning environment argumentStore
  exact ⟨sourceResult, nativeResult, applied, related,
    TaggedFunction.call_success (tagged_evaluates function identity environment store) argumentsEvaluated body⟩

theorem contracted_preserves {function : BuiltinFunctionId} {sources : List Dynamic.Value} {input : Value}
    (inputs : InputRep function sources input) {identity contract unknown : Word}
    {environment : Environment} {store argumentStore : Store} {arguments : Expr}
    (argumentsEvaluated : Evaluates (.unit :: contractedValue function identity contract environment :: environment) store
      ((arguments.weakenAt 0).weakenAt 0) (.inRight .word input) argumentStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function sources sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      Evaluates environment store
        (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
          (contracted function identity contract) arguments)
        (.inRight .word nativeResult) argumentStore := by
  obtain ⟨sourceResult, nativeResult, applied, related, body⟩ := inputs.body_meaning environment argumentStore
  exact ⟨sourceResult, nativeResult, applied, related,
    CallableContract.call_success [⟨contract, none, none⟩] unknown
      (contracted_evaluates function identity contract environment store)
      (gates_accept contract unknown .beforeArguments) argumentsEvaluated
      (gates_accept contract unknown .beforeApplication) body⟩

theorem tagged_reflects {function : BuiltinFunctionId} {sources : List Dynamic.Value} {input : Value}
    (inputs : InputRep function sources input) {identity : Word}
    {environment : Environment} {store argumentStore finalStore : Store} {arguments : Expr} {result : Value}
    (argumentsEvaluated : Evaluates (taggedValue function identity environment :: environment) store
      (arguments.weakenAt 0) (.inRight .word input) argumentStore)
    (completed : Evaluates environment store
      (TaggedFunction.call (SourceCoreInteger.builtinResult function) (tagged function identity) arguments)
      result finalStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function sources sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      result = .inRight .word nativeResult ∧ finalStore = argumentStore := by
  obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ := tagged_preserves inputs argumentsEvaluated
  obtain ⟨same, stores⟩ := evaluation_deterministic completed evaluated
  exact ⟨sourceResult, nativeResult, applied, related, same, stores⟩

theorem contracted_reflects {function : BuiltinFunctionId} {sources : List Dynamic.Value} {input : Value}
    (inputs : InputRep function sources input) {identity contract unknown : Word}
    {environment : Environment} {store argumentStore finalStore : Store} {arguments : Expr} {result : Value}
    (argumentsEvaluated : Evaluates (.unit :: contractedValue function identity contract environment :: environment) store
      ((arguments.weakenAt 0).weakenAt 0) (.inRight .word input) argumentStore)
    (completed : Evaluates environment store
      (CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
        (contracted function identity contract) arguments) result finalStore) :
    ∃ sourceResult nativeResult,
      Dynamic.BuiltinApplies function sources sourceResult ∧
      IntegerPrimitives.ResultRepresents sourceResult nativeResult ∧
      result = .inRight .word nativeResult ∧ finalStore = argumentStore := by
  obtain ⟨sourceResult, nativeResult, applied, related, evaluated⟩ := contracted_preserves inputs argumentsEvaluated
  obtain ⟨same, stores⟩ := evaluation_deterministic completed evaluated
  exact ⟨sourceResult, nativeResult, applied, related, same, stores⟩
end Solcore.SourceSemantics.CoreLowering.BuiltinCalls.Protocol
end

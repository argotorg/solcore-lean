import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.Frontend.SourceCore.Lowering

/-!
# Primitive expressions

Primitive operations and expressions and the fault contracts of scalar expressions.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ScalarExpressionFaultPostContracts
/-! Finite post transport uses the actual scalar Source form and layout.
It keeps the same token and final tuple and evaluates no expression. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ScalarExpressionFaultPostContracts
open Core Frontend SourceInference CompatibleExpressionReads
open ExpressionFailurePostContracts

variable {post : ExpressionFaultPost} {listPost : ExpressionsFaultPost}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource}

theorem ordinary_layout {checked : SourceCoreCompatibleCatalog.Checked}
    {id : ExpressionId} {node : ExpressionNode} {type : Ty}
    (metadata : Metadata checked source id node type) :
    Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [] := by
  rw [metadata.requirements, metadata.coercions]
  rfl

theorem expression_fault_outcome
    (joins : CompositionJoins post listPost program context evidence source)
    {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id child : ExpressionId} {childType parentType : Ty} {reason : Dynamic.SemanticFault} {token : Word}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {store : Store}
    (link : ExpressionLink program context evidence source environment before id middle child)
    (failed : Dynamic.ExpressionFaults program context evidence source environment middle child reason after)
    (retained : OutcomePost post program context evidence source environment middle child childType
      (.fault reason) after (.inLeft childType (.word token)) mapping world store) :
    OutcomePost post program context evidence source environment before id parentType
      (.fault reason) after (.inLeft parentType (.word token)) mapping world store :=
  ⟨token, rfl, joins.expression link failed (OutcomePost.fault retained)⟩

theorem tuple_outcome (joins : CompositionJoins post listPost program context evidence source)
    {checked : SourceCoreCompatibleCatalog.Checked} {id : ExpressionId} {node : ExpressionNode}
    {nativeType type : Ty} {ids : List ExpressionId} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {sequence : DataExpressionSequence.Outcome}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {store : Store}
    (metadata : Metadata checked source id node nativeType) (form : node.form = .tuple ids)
    (trace : DataExpressionSequence.Trace program context evidence source environment before ids sequence after)
    (packed : CompatibleExpressionProducts.PacksOutcome sequence outcome)
    (retained : ListOutcomePost listPost program context evidence source environment before ids type
      sequence after value mapping world store) :
    OutcomePost post program context evidence source environment before id type
      outcome after value mapping world store := by
  cases packed with
  | values _ => trivial
  | fault reason =>
    cases trace with
    | fault failed =>
      obtain ⟨token, same, retained⟩ := retained
      exact ⟨token, same, joins.expressions
        (.tuple (lookupExpression?_sound metadata.found) form (ordinary_layout metadata)) failed retained⟩

end Solcore.SourceSemantics.CoreLowering.ScalarExpressionFaultPostContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PrimitiveOperations
/-! Source primitive relations agree with the exact Core bodies used by the
primitive compiler. These lemmas inspect neither the executable source runtime
nor an assumed child evaluation result. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.PrimitiveExpressions

open Frontend Frontend.SourceInference TypeSystem LocalCell

theorem unary_value (operator : Syntax.UnaryOp) (value : SourceStagedValue.Value)
    (typed : SourceStagedValue.coreType value = (SourceCorePrimitive.unaryOperator operator).operandType) :
    ∃ result : SourceStagedValue.Value,
      SourceStagedValue.coreType result = (SourceCorePrimitive.unaryOperator operator).resultType ∧
      Dynamic.UnaryPrimitiveApplies operator (StagedValue.toSource value) (StagedValue.toSource result) ∧
      (SourceCorePrimitive.unaryOperator operator).apply (SourceStagedValue.toCore value) =
        some (SourceStagedValue.toCore result) := by
  cases operator <;> cases value <;>
    simp only [SourceCorePrimitive.unaryOperator, Core.UnaryOp.operandType, SourceStagedValue.coreType] at typed <;>
    try contradiction
  · exact ⟨.bool _, rfl, .logicalNot _, rfl⟩
  · exact ⟨.word _, rfl, .wordBitNot _, rfl⟩

theorem strict_operand_word {operator : Syntax.BinaryOp}
    (strict : Dynamic.StrictBinaryOperator operator) : SourceCorePrimitive.binaryOperandType operator = .word := by
  cases strict <;> rfl

theorem binary_result_payload (operator : Syntax.BinaryOp) :
    Core.CellPayload (SourceCorePrimitive.binaryResultType operator) := by
  cases operator <;> constructor

theorem unary_result_payload (operator : Syntax.UnaryOp) :
    Core.CellPayload (SourceCorePrimitive.unaryOperator operator).resultType := by
  cases operator <;> constructor

theorem binary_strict {operator : Syntax.BinaryOp} (strict : Dynamic.StrictBinaryOperator operator)
    (left right : Core.Expr) :
    SourceCorePrimitive.binary operator left right = Core.LocalPrimitiveResults.binaryWith
      (SourceCorePrimitive.binaryResultType operator) left right (SourceCorePrimitive.strictBinaryBody operator) := by
  cases strict <;> rfl

theorem binary_left_failure {operator : Syntax.BinaryOp} {environment : Core.Environment}
    {store : Core.Store} {left right : Core.Expr} {reason : Core.Word}
    (evaluation : Core.Evaluates environment store left
      (.inLeft (SourceCorePrimitive.binaryOperandType operator) (.word reason)) store) :
    Core.Evaluates environment store (SourceCorePrimitive.binary operator left right)
      (.inLeft (SourceCorePrimitive.binaryResultType operator) (.word reason)) store := by
  cases operator <;> first
    | exact Core.LocalPrimitiveResults.logicalAnd_failure evaluation
    | exact Core.LocalPrimitiveResults.logicalOr_failure evaluation
    | exact Core.LocalPrimitiveResults.binaryWith_left_failure evaluation

theorem binary_nonstrict {operator : Syntax.BinaryOp}
    (nonstrict : ¬ Dynamic.StrictBinaryOperator operator) :
    operator = .logicalAnd ∨ operator = .logicalOr := by
  cases operator <;> first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact False.elim (nonstrict (by constructor))

theorem bool_of_type (value : SourceStagedValue.Value)
    (typed : SourceStagedValue.coreType value = .bool) : ∃ boolean, value = .bool boolean := by
  cases value <;> simp_all [SourceStagedValue.coreType]

theorem word_of_type (value : SourceStagedValue.Value)
    (typed : SourceStagedValue.coreType value = .word) : ∃ word, value = .word word := by
  cases value <;> simp_all [SourceStagedValue.coreType]

private theorem not_gt (left right : Core.Word) :
    (!decide (left > right)) = decide (left ≤ right) := by
  rw [← decide_not]
  exact decide_eq_decide.mpr Fin.not_lt

private theorem not_lt (left right : Core.Word) :
    (!decide (right > left)) = decide (left ≥ right) := by
  rw [← decide_not]
  exact decide_eq_decide.mpr Fin.not_lt

/-- Swapped comparisons operate on already evaluated payloads. The source
operand order is independent of the Core comparison's argument order. -/
theorem strict_binary_value {operator : Syntax.BinaryOp}
    (strict : Dynamic.StrictBinaryOperator operator) (left right : Core.Word) :
    ∃ result : SourceStagedValue.Value,
      SourceStagedValue.coreType result = SourceCorePrimitive.binaryResultType operator ∧
      Dynamic.BinaryPrimitiveApplies operator (.word left) (.word right) (StagedValue.toSource result) ∧
      ∀ environment store, Core.Evaluates (.word right :: .word left :: environment) store
        (SourceCorePrimitive.strictBinaryBody operator) (SourceStagedValue.toCore result) store := by
  cases strict with
  | multiply => exact ⟨.word _, rfl, .wordMultiply _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | divide => exact ⟨.word _, rfl, .wordDivide _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | modulo => exact ⟨.word _, rfl, .wordModulo _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | add => exact ⟨.word _, rfl, .wordAdd _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | subtract => exact ⟨.word _, rfl, .wordSubtract _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | shiftLeft => exact ⟨.word _, rfl, .wordShiftLeft _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | shiftRight => exact ⟨.word _, rfl, .wordShiftRight _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | uncheckedAdd => exact ⟨.word _, rfl, .wordUncheckedAdd _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | uncheckedSubtract => exact ⟨.word _, rfl, .wordUncheckedSubtract _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | uncheckedMultiply => exact ⟨.word _, rfl, .wordUncheckedMultiply _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | bitAnd => exact ⟨.word _, rfl, .wordBitAnd _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | bitXor => exact ⟨.word _, rfl, .wordBitXor _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | bitOr => exact ⟨.word _, rfl, .wordBitOr _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | greater => exact ⟨.bool _, rfl, .wordGreater _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | less => exact ⟨.bool _, rfl, .wordLess _ _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | lessEqual =>
      refine ⟨.bool _, rfl, .wordLessEqual _ _, fun _ _ => .unary (.binary (.var rfl) (.var rfl) rfl) ?_⟩
      simp [Core.UnaryOp.apply, SourceStagedValue.toCore, not_gt]
  | greaterEqual =>
      refine ⟨.bool _, rfl, .wordGreaterEqual _ _, fun _ _ => .unary (.binary (.var rfl) (.var rfl) rfl) ?_⟩
      simp [Core.UnaryOp.apply, SourceStagedValue.toCore, not_lt]
  | equal =>
      by_cases same : left = right
      · subst right
        exact ⟨.bool true, rfl, .equalTrue ⟨rfl, .word _⟩,
          fun _ _ => .binary (.var rfl) (.var rfl) (by simp [Core.BinaryOp.apply, SourceStagedValue.toCore])⟩
      · exact ⟨.bool false, rfl, .equalFalse (fun equivalent => same (Dynamic.Value.word.inj equivalent.1)),
          fun _ _ => .binary (.var rfl) (.var rfl) (by simp [Core.BinaryOp.apply, SourceStagedValue.toCore, beq_eq_false_iff_ne.mpr same])⟩
  | notEqual =>
      by_cases same : left = right
      · subst right
        exact ⟨.bool false, rfl, .notEqualFalse ⟨rfl, .word _⟩,
          fun _ _ => .unary (.binary (result := .bool true) (.var rfl) (.var rfl) (by simp [Core.BinaryOp.apply])) rfl⟩
      · exact ⟨.bool true, rfl, .notEqualTrue (fun equivalent => same (Dynamic.Value.word.inj equivalent.1)),
          fun _ _ => .unary (.binary (result := .bool false) (.var rfl) (.var rfl) (by simp [Core.BinaryOp.apply, beq_eq_false_iff_ne.mpr same])) rfl⟩

end Solcore.SourceSemantics.CoreLowering.PrimitiveExpressions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.PrimitiveExpressions
/-! Accepted primitive expression lowering is connected to independent source
semantics. Literal evidence and primitive arithmetic are checked separately;
no child evaluation is a field of the structural compilation certificate. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.PrimitiveExpressions

open Frontend Frontend.SourceInference TypeSystem LocalCell

abbrev Metadata := BasicExpressions.Metadata

/-- The evidence ledger passed to compilation has its declarative meaning in
this source context. It is a static premise, not an evaluation assumption. -/
structure ContextValid (compilation : SourceCorePrimitive.Context) (context : Context) : Prop where
  ledger : context.solvedRequirements = compilation.solvedRequirements
  valid : RequirementLedgerWellFormed context

structure IntegerMetadata (compilation : SourceCorePrimitive.Context) (source : TypedSource)
    (id : ExpressionId) (node : ExpressionNode) (literal : Syntax.CoreLiteralValue)
    (resolution : IntegerLiteralResolution) : Prop where
  contains : ContainsExpression source id node
  owned : id.occurrence.owner = source.owner
  type : node.type = .word
  target : resolution.targetType = .word
  requirements : node.requirements = [resolution.requirement]
  coercions : node.coercions = []
  meaning : NumericLiteralDenotes literal resolution.rawValue
  requirement : ∃ solved, solved ∈ compilation.solvedRequirements ∧
    solved.id = resolution.requirement ∧ solved.predicate = ProgramSignatures.builtinIntPredicate .word

inductive Tree (compilation : SourceCorePrimitive.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Core.Word) :
    ExpressionId → Core.Ty → Core.Expr → Nat → Prop where
  | control {id type code depth}
      (tree : ControlExpressions.Tree source scope reasonAt id type code depth) :
      Tree compilation source scope reasonAt id type code depth
  | integerLiteral {id node literal resolution}
      (metadata : IntegerMetadata compilation source id node literal resolution)
      (form : node.form = .integerLiteral literal resolution) :
      Tree compilation source scope reasonAt id .word
        (Core.LanguageResult.success (.word (Core.Word.ofNatModulo resolution.rawValue))) 1
  | unary {id operand node operandCode operandDepth}
      (operator : Syntax.UnaryOp)
      (metadata : Metadata source id node (SourceCorePrimitive.unaryOperator operator).resultType)
      (form : node.form = .unary operator operand)
      (child : Tree compilation source scope reasonAt operand
        (SourceCorePrimitive.unaryOperator operator).operandType operandCode operandDepth) :
      Tree compilation source scope reasonAt id (SourceCorePrimitive.unaryOperator operator).resultType
        (Core.LocalPrimitiveResults.unary (SourceCorePrimitive.unaryOperator operator) operandCode) (operandDepth + 1)
  | binary {id left right node leftCode rightCode leftDepth rightDepth}
      (operator : Syntax.BinaryOp)
      (metadata : Metadata source id node (SourceCorePrimitive.binaryResultType operator))
      (form : node.form = .binary left operator right)
      (leftTree : Tree compilation source scope reasonAt left (SourceCorePrimitive.binaryOperandType operator) leftCode leftDepth)
      (rightTree : Tree compilation source scope reasonAt right (SourceCorePrimitive.binaryOperandType operator) rightCode rightDepth) :
      Tree compilation source scope reasonAt id (SourceCorePrimitive.binaryResultType operator)
        (SourceCorePrimitive.binary operator leftCode rightCode) (max leftDepth rightDepth + 1)
  | group {id inner node type code depth}
      (metadata : Metadata source id node type) (form : node.form = .group inner)
      (child : Tree compilation source scope reasonAt inner type code depth) :
      Tree compilation source scope reasonAt id type code (depth + 1)
  | pair {id left right node leftType rightType leftCode rightCode leftDepth rightDepth}
      (metadata : Metadata source id node (.product leftType rightType)) (form : node.form = .tuple [left, right])
      (leftTree : Tree compilation source scope reasonAt left leftType leftCode leftDepth)
      (rightTree : Tree compilation source scope reasonAt right rightType rightCode rightDepth) :
      Tree compilation source scope reasonAt id (.product leftType rightType)
        (Core.LocalSequence.pair leftType rightType leftCode rightCode) (max leftDepth rightDepth + 1)
  | conditional {id condition thenId elseId node type conditionCode thenCode elseCode conditionDepth thenDepth elseDepth}
      (metadata : Metadata source id node type) (form : node.form = .conditional condition thenId elseId)
      (conditionTree : Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth)
      (thenTree : Tree compilation source scope reasonAt thenId type thenCode thenDepth)
      (elseTree : Tree compilation source scope reasonAt elseId type elseCode elseDepth) :
      Tree compilation source scope reasonAt id type (Core.LocalControl.choose type conditionCode thenCode elseCode)
        (max conditionDepth (max thenDepth elseDepth) + 1)

theorem Tree.cellPayload {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type code depth) : Core.CellPayload type := by
  cases tree with
  | control tree => exact tree.cellPayload
  | integerLiteral => exact .word
  | unary operator => exact unary_result_payload operator
  | binary operator => exact binary_result_payload operator
  | group metadata _ _ | pair metadata _ _ _ | conditional metadata _ _ _ _ => exact metadata.types.cellPayload

theorem Tree.hasType {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type code depth) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) code (Core.LanguageResult.resultType type) := by
  induction tree with
  | control tree => exact tree.hasType
  | integerLiteral => exact Core.LanguageResult.success_hasType .word
  | unary _ _ _ _ ih => exact Core.LocalPrimitiveResults.unary_hasType ih
  | binary _ _ _ _ _ left right => exact SourceCorePrimitive.binary_hasType left right
  | group _ _ _ ih => exact ih
  | pair _ _ leftTree rightTree left right =>
      exact Core.LocalSequence.pair_hasType leftTree.cellPayload.wellFormed rightTree.cellPayload.wellFormed left right
  | conditional metadata _ _ _ _ condition thenBranch elseBranch =>
      exact Core.LocalControl.choose_hasType (metadata.types.wellFormed []) condition thenBranch elseBranch

/-- Occurrence provenance follows the evaluated source path. In particular,
right tuple elements require a successful left prefix, and conditional branches
require the matching Boolean condition. -/
inductive UninitializedAt (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    ExpressionId → ExpressionId → Dynamic.Location → Prop where
  | control {root site : ExpressionId} {location : Dynamic.Location}
      (provenance : ControlExpressions.UninitializedAt program context evidence source environment heap root site location) :
      UninitializedAt program context evidence source environment heap root site location
  | unary {id operand site : ExpressionId} {operator : Syntax.UnaryOp} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .unary operator operand)
      (child : UninitializedAt program context evidence source environment heap operand site location) :
      UninitializedAt program context evidence source environment heap id site location
  | binaryLeft {id left right site : ExpressionId} {operator : Syntax.BinaryOp} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .binary left operator right)
      (child : UninitializedAt program context evidence source environment heap left site location) :
      UninitializedAt program context evidence source environment heap id site location
  | binaryRight {id left right site : ExpressionId} {operator : Syntax.BinaryOp} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty} {leftValue : Dynamic.Value}
      (metadata : Metadata source id node type) (form : node.form = .binary left operator right)
      (evaluatedPrefix : Dynamic.ExpressionEvaluates program context evidence source environment heap left leftValue heap)
      (evaluateRight : Dynamic.EvaluatesRightOperand operator leftValue)
      (child : UninitializedAt program context evidence source environment heap right site location) :
      UninitializedAt program context evidence source environment heap id site location
  | group {id inner site : ExpressionId} {location : Dynamic.Location} {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .group inner)
      (child : UninitializedAt program context evidence source environment heap inner site location) :
      UninitializedAt program context evidence source environment heap id site location
  | pairLeft {id left right site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .tuple [left, right])
      (child : UninitializedAt program context evidence source environment heap left site location) :
      UninitializedAt program context evidence source environment heap id site location
  | pairRight {id left right site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty} {leftValue : Dynamic.Value}
      (metadata : Metadata source id node type) (form : node.form = .tuple [left, right])
      (evaluatedPrefix : Dynamic.ExpressionEvaluates program context evidence source environment heap left leftValue heap)
      (child : UninitializedAt program context evidence source environment heap right site location) :
      UninitializedAt program context evidence source environment heap id site location
  | condition {id condition thenId elseId site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .conditional condition thenId elseId)
      (child : UninitializedAt program context evidence source environment heap condition site location) :
      UninitializedAt program context evidence source environment heap id site location
  | thenBranch {id condition thenId elseId site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .conditional condition thenId elseId)
      (evaluatedPrefix : Dynamic.ExpressionEvaluates program context evidence source environment heap condition (.bool true) heap)
      (child : UninitializedAt program context evidence source environment heap thenId site location) :
      UninitializedAt program context evidence source environment heap id site location
  | elseBranch {id condition thenId elseId site : ExpressionId} {location : Dynamic.Location}
      {node : ExpressionNode} {type : Core.Ty}
      (metadata : Metadata source id node type) (form : node.form = .conditional condition thenId elseId)
      (evaluatedPrefix : Dynamic.ExpressionEvaluates program context evidence source environment heap condition (.bool false) heap)
      (child : UninitializedAt program context evidence source environment heap elseId site location) :
      UninitializedAt program context evidence source environment heap id site location

theorem UninitializedAt.faults
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {root site : ExpressionId} {location : Dynamic.Location}
    (provenance : UninitializedAt program context evidence source environment heap root site location) :
    Dynamic.ExpressionFaults program context evidence source environment heap root
      (.uninitializedLocation location) heap := by
  induction provenance with
  | control provenance => exact provenance.faults
  | unary metadata form _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .unaryOperand (owned := []) rfl ih
  | binaryLeft metadata form _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .binaryLeft (owned := []) rfl ih
  | binaryRight metadata form evaluatedPrefix evaluateRight _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .binaryRight (owned := []) rfl evaluatedPrefix evaluateRight ih
  | group metadata form _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .group rfl ih
  | pairLeft metadata form _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .tuple rfl (.head ih)
  | pairRight metadata form evaluatedPrefix _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .tuple rfl (.tail evaluatedPrefix (.head ih))
  | condition metadata form _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .conditionalCondition rfl ih
  | thenBranch metadata form evaluatedPrefix _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .conditionalTrueBranch rfl evaluatedPrefix ih
  | elseBranch metadata form evaluatedPrefix _ ih =>
      apply Dynamic.ExpressionFaults.form metadata.contains
      rw [form, metadata.requirements, metadata.coercions]
      exact .conditionalFalseBranch rfl evaluatedPrefix ih

/-- The propagated occurrence names an actual absent ordinary local cell.
No injectivity assumption is imposed on the caller's reason provider. -/
theorem UninitializedAt.read_site
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {root site : ExpressionId} {location : Dynamic.Location}
    (provenance : UninitializedAt program context evidence source environment heap root site location) :
    ∃ (scope : SourceCoreLocalCell.Scope) (type : Core.Ty)
      (readSite : ReadSite source scope site type) (cell : Dynamic.Cell),
      Dynamic.Environment.LooksUp environment readSite.binder location ∧
      Dynamic.Heap.Reads heap location cell ∧ cell.type = readSite.node.type ∧
      cell.generalized = none ∧ cell.value = none := by
  induction provenance with
  | control provenance => exact provenance.read_site
  | unary _ _ _ ih | binaryLeft _ _ _ ih | binaryRight _ _ _ _ _ ih => exact ih
  | group _ _ _ ih | pairLeft _ _ _ ih | pairRight _ _ _ _ ih
  | condition _ _ _ ih | thenBranch _ _ _ _ ih | elseBranch _ _ _ _ ih => exact ih

inductive OutcomeRepresents (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    (reasonAt : ExpressionId → Core.Word) (root : ExpressionId) (type : Core.Ty) :
    Dynamic.ExpressionOutcome → Core.Value → Prop where
  | value (value : SourceStagedValue.Value) (typed : SourceStagedValue.coreType value = type) :
      OutcomeRepresents program context evidence source environment heap reasonAt root type
        (.value (StagedValue.toSource value)) (.inRight .word (SourceStagedValue.toCore value))
  | uninitialized (site : ExpressionId) (location : Dynamic.Location)
      (provenance : UninitializedAt program context evidence source environment heap root site location) :
      OutcomeRepresents program context evidence source environment heap reasonAt root type
        (.fault (.uninitializedLocation location)) (.inLeft type (.word (reasonAt site)))


private theorem OutcomeRepresents.mapRoot
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {reasonAt : ExpressionId → Core.Word} {root parent : ExpressionId} {type : Core.Ty}
    {sourceOutcome : Dynamic.ExpressionOutcome} {coreValue : Core.Value}
    (related : OutcomeRepresents program context evidence source environment heap reasonAt root type sourceOutcome coreValue)
    (lift : ∀ site location, UninitializedAt program context evidence source environment heap root site location →
      UninitializedAt program context evidence source environment heap parent site location) :
    OutcomeRepresents program context evidence source environment heap reasonAt parent type sourceOutcome coreValue := by
  cases related with
  | value staged typed => exact .value staged typed
  | uninitialized site location provenance => exact .uninitialized site location (lift site location provenance)

private theorem binary_evaluates
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id left right : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    {operator : Syntax.BinaryOp} {leftValue rightValue result : Dynamic.Value}
    (metadata : Metadata source id node type) (form : node.form = .binary left operator right)
    (leftSource : Dynamic.ExpressionEvaluates program context evidence source environment heap left leftValue heap)
    (evaluateRight : Dynamic.EvaluatesRightOperand operator leftValue)
    (rightSource : Dynamic.ExpressionEvaluates program context evidence source environment heap right rightValue heap)
    (applied : Dynamic.BinaryPrimitiveApplies operator leftValue rightValue result) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id result heap := by
  apply Dynamic.ExpressionEvaluates.intro metadata.contains
  · rw [form, metadata.requirements, metadata.coercions]
    exact .binaryEvaluateRight (owned := []) rfl leftSource evaluateRight rightSource (.primitive applied)
  · rw [metadata.coercions]; exact .nil

private theorem shortCircuit_evaluates
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {id left right : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    {operator : Syntax.BinaryOp} {leftValue result : Dynamic.Value}
    (metadata : Metadata source id node type) (form : node.form = .binary left operator right)
    (leftSource : Dynamic.ExpressionEvaluates program context evidence source environment heap left leftValue heap)
    (circuit : Dynamic.ShortCircuits operator leftValue result) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id result heap := by
  apply Dynamic.ExpressionEvaluates.intro metadata.contains
  · rw [form, metadata.requirements, metadata.coercions]
    exact .binaryShortCircuit (owned := []) rfl leftSource circuit rfl
  · rw [metadata.coercions]; exact .nil


/-- The certificate supplies both independent source and Core derivations.
Neither heap changes, including when a child read fails. -/
theorem Tree.preserves {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {expression : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type expression depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
        sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store expression coreValue store := by
  induction tree with
  | control tree =>
      obtain ⟨outcome, value, sourceEvaluation, related, coreEvaluation⟩ :=
        tree.preserves program context evidence environments heaps
      refine ⟨outcome, value, sourceEvaluation, ?_, coreEvaluation⟩
      cases related with
      | value staged typed => exact .value staged typed
      | uninitialized site location provenance => exact .uninitialized site location (.control provenance)
  | @integerLiteral id node literal resolution metadata form =>
      have proves : RequirementProves context resolution.requirement (ProgramSignatures.builtinIntPredicate .word) := by
        obtain ⟨solved, member, identifier, predicate⟩ := metadata.requirement
        have contains : solved ∈ context.solvedRequirements := by rw [valid.ledger]; exact member
        exact ⟨solved, ⟨contains, identifier⟩, predicate, valid.valid.entriesValid solved contains⟩
      have constructs : Dynamic.ResolvedIntegerLiteralConstructs context literal resolution
          (.word (Core.Word.ofNatModulo resolution.rawValue)) := by
        cases resolution with
        | mk raw target requirement =>
            have targetEq := metadata.target
            dsimp only at targetEq
            subst target
            exact .word metadata.meaning proves
      refine ⟨_, _, .value ?_, .value (.word _) rfl, .inRight .word⟩
      apply Dynamic.ExpressionEvaluates.intro metadata.contains
      · rw [form, metadata.requirements, metadata.coercions]
        exact .integerLiteral rfl constructs
      · rw [metadata.coercions]; exact .nil
  | @unary id operand node operandCode operandDepth operator metadata form child ih =>
      obtain ⟨outcome, coreValue, sourceEvaluation, related, coreEvaluation⟩ := ih
      cases related with
      | uninitialized site location provenance =>
          have propagated := UninitializedAt.unary metadata form provenance
          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
            Core.LocalPrimitiveResults.unary_failure coreEvaluation⟩
      | value staged typed =>
          cases sourceEvaluation with
          | value sourceEvaluation =>
              obtain ⟨result, resultTyped, sourceApplied, coreApplied⟩ := unary_value operator staged typed
              refine ⟨_, _, .value ?_, .value result resultTyped,
                Core.LocalPrimitiveResults.unary_success coreEvaluation coreApplied⟩
              apply Dynamic.ExpressionEvaluates.intro metadata.contains
              · rw [form, metadata.requirements, metadata.coercions]
                exact .unary (owned := []) rfl sourceEvaluation (.primitive sourceApplied)
              · rw [metadata.coercions]; exact .nil
  | @binary id left right node leftCode rightCode leftDepth rightDepth operator metadata form
      leftTree rightTree leftIH rightIH =>
      obtain ⟨leftOutcome, leftValue, leftSource, leftRelated, leftCore⟩ := leftIH
      cases leftRelated with
      | uninitialized site location provenance =>
          have propagated := UninitializedAt.binaryLeft metadata form provenance
          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
            binary_left_failure leftCore⟩
      | value leftValue leftTyped =>
          cases leftSource with
          | value leftSource =>
              by_cases strict : Dynamic.StrictBinaryOperator operator
              · have leftWord := word_of_type leftValue (leftTyped.trans (strict_operand_word strict))
                obtain ⟨leftWord, rfl⟩ := leftWord
                obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightIH
                have shifted := rightCore.weakenAt_zero_cellPayload rightTree.hasType
                  (.sum .word rightTree.cellPayload) (environments.runtime_hasTypes [])
                  (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes (.word leftWord)
                cases rightRelated with
                | uninitialized site location provenance =>
                    have propagated := UninitializedAt.binaryRight metadata form leftSource (.strict strict) provenance
                    refine ⟨_, _, .fault propagated.faults, .uninitialized site location propagated, ?_⟩
                    rw [binary_strict strict]
                    exact Core.LocalPrimitiveResults.binaryWith_right_failure leftCore shifted
                | value rightValue rightTyped =>
                    cases rightSource with
                    | value rightSource =>
                        obtain ⟨rightWord, rfl⟩ := word_of_type rightValue (rightTyped.trans (strict_operand_word strict))
                        obtain ⟨result, resultTyped, applied, bodyEvaluation⟩ := strict_binary_value strict leftWord rightWord
                        refine ⟨_, _, .value (binary_evaluates metadata form leftSource (.strict strict) rightSource applied),
                          .value result resultTyped, ?_⟩
                        rw [binary_strict strict]
                        exact Core.LocalPrimitiveResults.binaryWith_success leftCore shifted (bodyEvaluation _ _)
              · rcases binary_nonstrict strict with isAnd | isOr
                · subst operator
                  obtain ⟨leftBoolean, rfl⟩ := bool_of_type leftValue leftTyped
                  cases leftBoolean with
                  | false =>
                      exact ⟨_, _, .value (shortCircuit_evaluates metadata form leftSource .andFalse),
                        .value (.bool false) rfl, Core.LocalPrimitiveResults.logicalAnd_shortCircuit leftCore⟩
                  | true =>
                      obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightIH
                      have shifted := rightCore.weakenAt_zero_cellPayload rightTree.hasType
                        (.sum .word rightTree.cellPayload) (environments.runtime_hasTypes [])
                        (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes (.bool true)
                      cases rightRelated with
                      | uninitialized site location provenance =>
                          have propagated := UninitializedAt.binaryRight metadata form leftSource .andTrue provenance
                          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
                            Core.LocalPrimitiveResults.logicalAnd_right leftCore shifted⟩
                      | value rightValue rightTyped =>
                          cases rightSource with
                          | value rightSource =>
                              obtain ⟨rightBoolean, rfl⟩ := bool_of_type rightValue rightTyped
                              exact ⟨_, _, .value (binary_evaluates metadata form leftSource .andTrue rightSource
                                (.logicalAnd true rightBoolean)), .value (.bool rightBoolean) rfl,
                                Core.LocalPrimitiveResults.logicalAnd_right leftCore shifted⟩
                · subst operator
                  obtain ⟨leftBoolean, rfl⟩ := bool_of_type leftValue leftTyped
                  cases leftBoolean with
                  | true =>
                      exact ⟨_, _, .value (shortCircuit_evaluates metadata form leftSource .orTrue),
                        .value (.bool true) rfl, Core.LocalPrimitiveResults.logicalOr_shortCircuit leftCore⟩
                  | false =>
                      obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightIH
                      have shifted := rightCore.weakenAt_zero_cellPayload rightTree.hasType
                        (.sum .word rightTree.cellPayload) (environments.runtime_hasTypes [])
                        (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes (.bool false)
                      cases rightRelated with
                      | uninitialized site location provenance =>
                          have propagated := UninitializedAt.binaryRight metadata form leftSource .orFalse provenance
                          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
                            Core.LocalPrimitiveResults.logicalOr_right leftCore shifted⟩
                      | value rightValue rightTyped =>
                          cases rightSource with
                          | value rightSource =>
                              obtain ⟨rightBoolean, rfl⟩ := bool_of_type rightValue rightTyped
                              exact ⟨_, _, .value (binary_evaluates metadata form leftSource .orFalse rightSource
                                (.logicalOr false rightBoolean)), .value (.bool rightBoolean) rfl,
                                Core.LocalPrimitiveResults.logicalOr_right leftCore shifted⟩
  | group metadata form child inductionHypothesis =>
      obtain ⟨outcome, coreValue, evaluated, related, coreEvaluated⟩ := inductionHypothesis
      refine ⟨outcome, coreValue, ?_, related.mapRoot (fun _ _ trace => .group metadata form trace), coreEvaluated⟩
      cases evaluated with
      | value evaluated =>
          apply Dynamic.ExpressionEvaluatesOutcome.value
          apply Dynamic.ExpressionEvaluates.intro metadata.contains
          · rw [form, metadata.requirements, metadata.coercions]; exact .group rfl evaluated
          · rw [metadata.coercions]; exact .nil
      | fault fault =>
          apply Dynamic.ExpressionEvaluatesOutcome.fault
          apply Dynamic.ExpressionFaults.form metadata.contains
          rw [form, metadata.requirements, metadata.coercions]
          exact .group rfl fault
  | @pair id left right node leftType rightType leftCode rightCode leftDepth rightDepth
      metadata form leftTree rightTree leftInduction rightInduction =>
      obtain ⟨leftOutcome, leftValue, leftSource, leftRelated, leftCore⟩ := leftInduction
      cases leftRelated with
      | uninitialized faultSite location provenance =>
          cases leftSource with
          | fault fault =>
              refine ⟨_, _, .fault ?_, .uninitialized faultSite location (.pairLeft metadata form provenance),
                Core.LocalSequence.pair_left_failure leftType rightType leftCore⟩
              apply Dynamic.ExpressionFaults.form metadata.contains
              rw [form, metadata.requirements, metadata.coercions]
              exact .tuple rfl (.head fault)
      | value leftValue leftTypeEq =>
          cases leftSource with
          | value leftSource =>
              obtain ⟨rightOutcome, rightValue, rightSource, rightRelated, rightCore⟩ := rightInduction
              have weakened := rightCore.weakenAt_zero_cellPayload rightTree.hasType
                (.sum .word rightTree.cellPayload) (environments.runtime_hasTypes [])
                (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes
                (SourceStagedValue.toCore leftValue)
              cases rightRelated with
              | uninitialized faultSite location provenance =>
                  cases rightSource with
                  | fault fault =>
                      refine ⟨_, _, .fault ?_, .uninitialized faultSite location (.pairRight metadata form leftSource provenance),
                        Core.LocalSequence.pair_right_failure leftType rightType leftCore weakened⟩
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .tuple rfl (.tail leftSource (.head fault))
              | value rightValue rightTypeEq =>
                  cases rightSource with
                  | value rightSource =>
                      refine ⟨.value (StagedValue.toSource (.product leftValue rightValue)),
                        .inRight .word (SourceStagedValue.toCore (.product leftValue rightValue)),
                        .value ?_, .value (.product leftValue rightValue) ?_,
                        Core.LocalSequence.pair_success leftType rightType leftCore weakened⟩
                      · apply Dynamic.ExpressionEvaluates.intro metadata.contains
                        · rw [form, metadata.requirements, metadata.coercions]
                          exact .tuple rfl (.cons leftSource (.cons rightSource .nil))
                            (.cons (.singleton _))
                        · rw [metadata.coercions]; exact .nil
                      · simp [SourceStagedValue.coreType, leftTypeEq, rightTypeEq]
  | @conditional id condition thenId elseId node type conditionCode thenCode elseCode
      conditionDepth thenDepth elseDepth metadata form conditionTree thenTree elseTree
      conditionIH thenIH elseIH =>
      obtain ⟨conditionOutcome, conditionValue, conditionSource, conditionRelated, conditionCore⟩ := conditionIH
      cases conditionRelated with
      | uninitialized site location provenance =>
          have propagated := UninitializedAt.condition metadata form provenance
          exact ⟨_, _, .fault propagated.faults, .uninitialized site location propagated,
            Core.LocalControl.choose_failure type conditionCore⟩
      | value staged typed =>
          have boolean : ∃ value, staged = .bool value := by
            cases staged <;> simp_all [SourceStagedValue.coreType]
          obtain ⟨boolean, rfl⟩ := boolean
          cases conditionSource with
          | value conditionSource =>
              cases boolean with
              | true =>
                  obtain ⟨outcome, coreValue, branchSource, branchRelated, branchCore⟩ := thenIH
                  have shifted := branchCore.weakenAt_zero_cellPayload thenTree.hasType
                    (.sum .word thenTree.cellPayload) (environments.runtime_hasTypes [])
                    (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes (.bool true)
                  refine ⟨outcome, coreValue, ?_,
                    branchRelated.mapRoot (fun _ _ trace => .thenBranch metadata form conditionSource trace),
                    Core.LocalControl.choose_true type conditionCore shifted⟩
                  cases branchSource with
                  | value evaluated =>
                      apply Dynamic.ExpressionEvaluatesOutcome.value
                      apply Dynamic.ExpressionEvaluates.intro metadata.contains
                      · rw [form, metadata.requirements, metadata.coercions]
                        exact .conditionalTrue rfl conditionSource evaluated
                      · rw [metadata.coercions]; exact .nil
                  | fault fault =>
                      apply Dynamic.ExpressionEvaluatesOutcome.fault
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .conditionalTrueBranch rfl conditionSource fault
              | false =>
                  obtain ⟨outcome, coreValue, branchSource, branchRelated, branchCore⟩ := elseIH
                  have shifted := branchCore.weakenAt_zero_cellPayload elseTree.hasType
                    (.sum .word elseTree.cellPayload) (environments.runtime_hasTypes [])
                    (heaps.runtime_hasTypes []) heaps.firstOrder_hasTypes (.bool false)
                  refine ⟨outcome, coreValue, ?_,
                    branchRelated.mapRoot (fun _ _ trace => .elseBranch metadata form conditionSource trace),
                    Core.LocalControl.choose_false type conditionCore shifted⟩
                  cases branchSource with
                  | value evaluated =>
                      apply Dynamic.ExpressionEvaluatesOutcome.value
                      apply Dynamic.ExpressionEvaluates.intro metadata.contains
                      · rw [form, metadata.requirements, metadata.coercions]
                        exact .conditionalFalse rfl conditionSource evaluated
                      · rw [metadata.coercions]; exact .nil
                  | fault fault =>
                      apply Dynamic.ExpressionEvaluatesOutcome.fault
                      apply Dynamic.ExpressionFaults.form metadata.contains
                      rw [form, metadata.requirements, metadata.coercions]
                      exact .conditionalFalseBranch rfl conditionSource fault



private theorem bind_ok {α β : Type} {computation : Except SourceCoreBasic.Error α}
    {next : α → Except SourceCoreBasic.Error β} {result : β}
    (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted


/-- Literal facts come from the shared validator's proved certificate, including
numeric spelling and the exact retained obligation. -/
private theorem integer_metadata_of_validation
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {literal : Syntax.CoreLiteralValue} {resolution : IntegerLiteralResolution}
    {validated : SourceCoreElaboration.WordIntegerLiteral}
    (owned : id.occurrence.owner = source.owner) (found : source.lookupExpression? id = some node)
    (accepted : SourceCoreElaboration.validateWordIntegerLiteral compilation.solvedRequirements
      node literal resolution = .ok validated) :
    IntegerMetadata compilation source id node literal resolution ∧
      validated.value = Core.Word.ofNatModulo resolution.rawValue := by
  have certificate := SourceCoreElaboration.validateWordIntegerLiteral_sound accepted
  exact ⟨⟨lookupExpression?_sound found, owned, certificate.nodeType, certificate.targetType,
    certificate.requirements, certificate.coercions, certificate.meaning, certificate.solved⟩, certificate.value⟩

/-- All successful branches of the actual primitive compiler produce a static
tree. Child compilation is inspected recursively; no child meaning is assumed. -/
theorem tree_of_lowerExpression
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasonAt = .ok lowered) :
    ∃ depth, depth ≤ fuel ∧ Tree compilation source scope reasonAt id lowered.type lowered.expression depth := by
  induction fuel generalizing id lowered with
  | zero => cases accepted
  | succ fuel ih =>
      by_cases owned : id.occurrence.owner = source.owner
      · cases found : source.lookupExpression? id with
        | none =>
            simp [SourceCorePrimitive.lowerExpressionWithReasons, owned, found, bind, Except.bind] at accepted
        | some node =>
            simp only [SourceCorePrimitive.lowerExpressionWithReasons, owned, found, ne_eq,
              not_true_eq_false, ↓reduceIte, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
            split at accepted
            next literal resolution form =>
              cases validation : SourceCoreElaboration.validateWordIntegerLiteral compilation.solvedRequirements
                  node literal resolution with
              | error error => simp [validation, Except.mapError] at accepted
              | ok validated =>
                  simp only [validation, Except.mapError, Except.ok.injEq] at accepted
                  cases accepted
                  obtain ⟨metadata, same⟩ := integer_metadata_of_validation owned found validation
                  rw [same]
                  exact ⟨1, by omega, .integerLiteral metadata form⟩
            next notInteger =>
              obtain ⟨⟨selected, type⟩, read, accepted⟩ := bind_ok accepted
              obtain ⟨_, metadata⟩ := BasicExpressions.readExpression_certificate read
              cases form : selected.form with
              | unary operator operand =>
                  simp only [form] at accepted
                  obtain ⟨operand, operandAccepted, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, operandChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  cases accepted
                  obtain ⟨operandDepth, operandBound, operandTree⟩ := ih operandAccepted
                  rw [← ensureType_ok operandChecked] at operandTree
                  rw [← ensureType_ok resultChecked]
                  exact ⟨operandDepth + 1, by omega,
                    .unary operator ((ensureType_ok resultChecked).symm ▸ metadata) form operandTree⟩
              | binary left operator right =>
                  simp only [form] at accepted
                  obtain ⟨leftResult, leftAccepted, accepted⟩ := bind_ok accepted
                  obtain ⟨rightResult, rightAccepted, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, leftChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨checkedUnit, rightChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨checkedUnit, resultChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  cases accepted
                  obtain ⟨leftDepth, leftBound, leftTree⟩ := ih leftAccepted
                  obtain ⟨rightDepth, rightBound, rightTree⟩ := ih rightAccepted
                  rw [← ensureType_ok leftChecked] at leftTree
                  rw [← ensureType_ok rightChecked] at rightTree
                  rw [← ensureType_ok resultChecked]
                  exact ⟨max leftDepth rightDepth + 1, by omega,
                    .binary operator ((ensureType_ok resultChecked).symm ▸ metadata) form leftTree rightTree⟩
              | conditional condition thenId elseId =>
                  simp only [form] at accepted
                  obtain ⟨condition, conditionAccepted, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, conditionChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨thenBranch, thenAccepted, accepted⟩ := bind_ok accepted
                  obtain ⟨elseBranch, elseAccepted, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, thenChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  obtain ⟨checkedUnit, elseChecked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  cases accepted
                  obtain ⟨conditionDepth, conditionBound, conditionTree⟩ := ih conditionAccepted
                  obtain ⟨thenDepth, thenBound, thenTree⟩ := ih thenAccepted
                  obtain ⟨elseDepth, elseBound, elseTree⟩ := ih elseAccepted
                  rw [← ensureType_ok conditionChecked] at conditionTree
                  rw [← ensureType_ok thenChecked] at thenTree
                  rw [← ensureType_ok elseChecked] at elseTree
                  exact ⟨max conditionDepth (max thenDepth elseDepth) + 1, by omega,
                    .conditional metadata form conditionTree thenTree elseTree⟩
              | group inner =>
                  simp only [form] at accepted
                  obtain ⟨child, childAccepted, accepted⟩ := bind_ok accepted
                  obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                  cases checkedUnit
                  cases accepted
                  obtain ⟨depth, bound, childTree⟩ := ih childAccepted
                  exact ⟨depth + 1, by omega, .group (ensureType_ok checked ▸ metadata) form childTree⟩
              | tuple elements =>
                  cases elements with
                  | nil =>
                      have controlAccepted : SourceCoreControl.lowerExpressionWithReasons (fuel + 1)
                          source scope id reasonAt = .ok lowered := by
                        simpa only [SourceCoreControl.lowerExpressionWithReasons, read, form, bind, Except.bind]
                          using accepted
                      obtain ⟨depth, bound, tree⟩ := ControlExpressions.tree_of_lowerExpression unique controlAccepted
                      exact ⟨depth, bound, .control tree⟩
                  | cons left rest =>
                      cases rest with
                      | nil =>
                          have controlAccepted : SourceCoreControl.lowerExpressionWithReasons (fuel + 1)
                              source scope id reasonAt = .ok lowered := by
                            simpa only [SourceCoreControl.lowerExpressionWithReasons, read, form, bind, Except.bind]
                              using accepted
                          obtain ⟨depth, bound, tree⟩ := ControlExpressions.tree_of_lowerExpression unique controlAccepted
                          exact ⟨depth, bound, .control tree⟩
                      | cons right rest =>
                          cases rest with
                          | cons =>
                              have controlAccepted : SourceCoreControl.lowerExpressionWithReasons (fuel + 1)
                                  source scope id reasonAt = .ok lowered := by
                                simpa only [SourceCoreControl.lowerExpressionWithReasons, read, form, bind, Except.bind]
                                  using accepted
                              obtain ⟨depth, bound, tree⟩ := ControlExpressions.tree_of_lowerExpression unique controlAccepted
                              exact ⟨depth, bound, .control tree⟩
                          | nil =>
                              simp only [form] at accepted
                              obtain ⟨leftResult, leftAccepted, accepted⟩ := bind_ok accepted
                              obtain ⟨rightResult, rightAccepted, accepted⟩ := bind_ok accepted
                              obtain ⟨checkedUnit, checked, accepted⟩ := bind_ok accepted
                              cases checkedUnit
                              cases accepted
                              obtain ⟨leftDepth, leftBound, leftTree⟩ := ih leftAccepted
                              obtain ⟨rightDepth, rightBound, rightTree⟩ := ih rightAccepted
                              have same := ensureType_ok checked
                              rw [same]
                              exact ⟨max leftDepth rightDepth + 1, by omega,
                                .pair (same ▸ metadata) form leftTree rightTree⟩
              | literal | reference | integerLiteral | lambda | call | constructor | member | proxy | index =>
                  have controlAccepted : SourceCoreControl.lowerExpressionWithReasons (fuel + 1)
                      source scope id reasonAt = .ok lowered := by
                    simpa only [SourceCoreControl.lowerExpressionWithReasons, read, form, bind, Except.bind]
                      using accepted
                  obtain ⟨depth, bound, tree⟩ := ControlExpressions.tree_of_lowerExpression unique controlAccepted
                  exact ⟨depth, bound, .control tree⟩
      · simp [SourceCorePrimitive.lowerExpressionWithReasons, owned, bind, Except.bind] at accepted

/-- Common metadata for ordinary and evidence-bearing integer nodes. Integer
requirements are deliberately retained; this certificate does not claim that
`SourceCoreBasic.readExpression` accepts those nodes. -/
structure RootMetadata (source : TypedSource) (id : ExpressionId)
    (node : ExpressionNode) (type : Core.Ty) : Prop where
  contains : ContainsExpression source id node
  owned : id.occurrence.owner = source.owner
  types : TypeRepresents node.type type
  coercions : node.coercions = []

private theorem Metadata.root {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {type : Core.Ty} (metadata : Metadata source id node type) :
    RootMetadata source id node type :=
  ⟨metadata.contains, metadata.owned, metadata.types, metadata.coercions⟩

theorem Tree.metadata {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : Tree compilation source scope reasonAt id type code depth) :
    ∃ node, RootMetadata source id node type := by
  cases tree with
  | control tree =>
      obtain ⟨node, metadata⟩ := tree.metadata
      exact ⟨node, Metadata.root metadata⟩
  | integerLiteral metadata _ =>
      exact ⟨_, metadata.contains, metadata.owned, metadata.type ▸ .word, metadata.coercions⟩
  | unary _ metadata _ _ | binary _ metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ | conditional metadata _ _ _ _ =>
      exact ⟨_, Metadata.root metadata⟩

theorem lowerExpression_hasType
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasonAt = .ok lowered) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) lowered.expression
      (Core.LanguageResult.resultType lowered.type) := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  exact tree.hasType

theorem lowerExpression_metadata
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasonAt = .ok lowered) :
    ∃ node, source.lookupExpression? id = some node ∧ RootMetadata source id node lowered.type := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  obtain ⟨node, metadata⟩ := tree.metadata
  exact ⟨node, lookupExpression?_complete unique metadata.contains, metadata⟩

/-- Successful compilation supplies both independent evaluations. The only
literal evidence premise is the static validity of the retained source ledger. -/
theorem lowerExpression_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    ∃ sourceOutcome coreValue,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      Core.Evaluates coreEnvironment store lowered.expression coreValue store := by
  obtain ⟨_, _, tree⟩ := tree_of_lowerExpression unique accepted
  exact tree.preserves program context evidence valid environments heaps

/-- All completed runs agree with the derived source outcome, including exact
executed read reasons. Sufficient fuel follows from this finite expression
grammar; no unrestricted source normalization or fault completeness is claimed. -/
theorem lowerExpression_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Core.Word}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasonAt = .ok lowered)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    (environments : EnvRepresents world scope environment coreEnvironment)
    (heaps : HeapRepresents heap.cells store world) :
    Core.infer? (SourceCoreLocalCell.coreContext scope) lowered.expression =
      some (Core.LanguageResult.resultType lowered.type) ∧
    ∃ sourceOutcome coreValue required,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id sourceOutcome heap ∧
      OutcomeRepresents program context evidence source environment heap reasonAt id lowered.type sourceOutcome coreValue ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial lowered.expression coreEnvironment store) =
        .done coreValue store) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial lowered.expression coreEnvironment store) =
        .done actual actualStore → actual = coreValue ∧ actualStore = store) := by
  obtain ⟨sourceOutcome, coreValue, sourceEvaluation, related, coreEvaluation⟩ :=
    lowerExpression_preserves unique accepted program context evidence valid environments heaps
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel coreEvaluation
  refine ⟨Core.infer_complete (lowerExpression_hasType unique accepted),
    sourceOutcome, coreValue, required, sourceEvaluation, related, completes, ?_⟩
  intro fuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) coreEvaluation

end Solcore.SourceSemantics.CoreLowering.PrimitiveExpressions
end

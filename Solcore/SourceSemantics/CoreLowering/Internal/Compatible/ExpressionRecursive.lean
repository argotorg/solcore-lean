import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionIndices
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.GeneralExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConditionals
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.ScalarReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionContextualConstructors
import Solcore.Frontend.SourceCoreGeneralFunctions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors

/-!
# Compatible expressions: recursive forms and indices

Recursive expressions, index meaning, and contextual indices, reads and proxies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursiveTree
/-! One recursive expression grammar composes constructors, members, products,
primitive operators and conditionals at every child position. Static receipts
retain raw metadata and actual generated code; they contain no execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursive
open Core Frontend SourceInference CompatibleExpressionPrimitives
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | fragment {id} (child : CompatibleExpressionMembers.Syntax source id) : Syntax source id
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

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | fragment {id lowered}
      (child : CompatibleExpressionMembers.Tree fuel values source context solved reasonAt scope id lowered) :
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


private theorem member_projected {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionMembers.Tree fuel values source context solved reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | fragment child =>
      cases child with
      | fragment child => exact child.projected found
      | constructor receipt _ _ _ _ _ =>
          have same := Option.some.inj (receipt.metadata.found.symm.trans found)
          exact same ▸ receipt.metadata.projected
  | member metadata _ _ _ _ =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      exact same ▸ metadata.projected

theorem Tree.projected {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree fuel values source context solved reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | fragment child => exact member_projected child found
  | constructor receipt _ _ _ _ _ =>
      have same := Option.some.inj (receipt.metadata.found.symm.trans found)
      exact same ▸ receipt.metadata.projected
  | group metadata _ _ _ _ | pair metadata _ _ _ _ _ _ | unary metadata _ _ _ _ _ _ | binary metadata _ _ _ _ _ _ _ _ _ | conditional metadata _ _ _ _ _ _ _ _ _ _ | member metadata _ _ _ _ =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      exact same ▸ metadata.projected

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursive
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursiveMeaning
/-! Recursive data and control composition over compatible heaps. Each child
semantic obligation is discharged by the tree induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursive
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open DataPatternValues

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : Scope}

/-- Static leaf support indexes the existing tree and its exact children.
It contains only leaf membership, with no execution or heap law. -/
inductive Tree.LiteralSites (literals : GenericExpressionMeaning.Certificate) :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Tree fuel values source context solved reasonAt scope id lowered → Prop where
  | fragment {id lowered}
      (child : CompatibleExpressionMembers.Tree fuel values source context solved reasonAt scope id lowered)
      (childSites : CompatibleExpressionMembers.Tree.LiteralSites literals child) :
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

/-- The exact old tree restricted to the supplied static leaf certificates. -/
def Tree.WithLiterals (literals : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun current id lowered => ∃ tree : Tree fuel values source context solved reasonAt current id lowered,
    tree.LiteralSites literals

/-- Ordinary literal membership supplies support for every original tree. -/
theorem Tree.literalSites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree fuel values source context solved reasonAt scope id lowered) :
    tree.LiteralSites (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code) := by
  induction tree with
  | fragment child => exact .fragment child child.literalSites
  | group metadata form innerFound sourceType child childIH => exact .group metadata form innerFound sourceType child childIH
  | pair metadata form leftFound rightFound sourceType firstTree secondTree firstTreeIH secondTreeIH => exact .pair metadata form leftFound rightFound sourceType firstTree secondTree firstTreeIH secondTreeIH
  | unary metadata form found inputType outputType profile child childIH => exact .unary metadata form found inputType outputType profile child childIH
  | binary metadata form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH => exact .binary metadata form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH
  | conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeIH thenTreeIH elseTreeIH => exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree conditionTreeIH thenTreeIH elseTreeIH
  | constructor receipt form valid count nodes children childrenIH => exact .constructor receipt form valid count nodes children childrenIH
  | member metadata baseMetadata form layout childTree childTreeIH => exact .member metadata baseMetadata form layout childTree childTreeIH

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


private def Children (scope : Scope) (ids : List ExpressionId) (codes : List SourceCoreBasic.LoweredExpr) :
    GenericExpressionMeaning.Certificate := fun current id code => current = scope ∧ (id, code) ∈ ids.zip codes

theorem construct_rename (tag : ConstructorId) (header : Word) (arguments : Expr) (ξ : Renaming) :
    (SourceCoreCompatibleDataExpressions.construct tag header arguments).rename ξ =
      SourceCoreCompatibleDataExpressions.construct tag header (arguments.rename ξ) := by
  simp [SourceCoreCompatibleDataExpressions.construct, LanguageResult.bind, LanguageResult.success, Expr.rename, Renaming.lift]

theorem construct_success {environment : Environment} {before after : Store}
    (tag : ConstructorId) (header : Word) {arguments : Expr} {value : Value}
    (evaluated : Evaluates environment before arguments (.inRight .word value) after) :
    Evaluates environment before (SourceCoreCompatibleDataExpressions.construct tag header arguments)
      (.inRight .word (.constructed tag (.pair (.word header) value))) after :=
  LanguageResult.bind_success _ evaluated (.inRight (.construct (.pair .word (.var rfl))))

theorem construct_failure {environment : Environment} {before after : Store}
    (tag : ConstructorId) (header : Word) {arguments : Expr} {type : Ty} {reason : Word}
    (evaluated : Evaluates environment before arguments (.inLeft type (.word reason)) after) :
    Evaluates environment before (SourceCoreCompatibleDataExpressions.construct tag header arguments)
      (.inLeft (.namedData tag.owner) (.word reason)) after :=
  LanguageResult.bind_failure _ evaluated

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
  {literals : GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))

include extension unique in
theorem preserves_with_literals_and_post
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (constructorJoins : ScalarConstructorFaultPostContracts.Joins post listPost values program context evidence source)
    (memberJoins : ScalarMemberFaultPostContracts.Joins post values program context evidence source)
    (literalMeaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults post)
    (readMeaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults post) :
    ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults post := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | fragment child childSites =>
    exact CompatibleExpressionMembers.preserves_with_literals_and_post functions extension program evidence unique sequenceJoins ordinaryJoins constructorJoins memberJoins literalMeaning readMeaning ⟨child, childSites⟩
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
          (ScalarExpressionFaultPostContracts.ordinary_layout metadata))
        (CompatibleExpressionProducts.group_inv metadata form unique trace) retained⟩
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
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
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
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
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
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, _, firstMetadata, _firstPost⟩ :=
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
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
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
              (.conditionalFalse (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata) conditionTrace)
              branchTrace retained⟩
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
              (.conditionalTrue (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata) conditionTrace)
              branchTrace retained⟩
          · rw [choose_rename]; exact LocalControl.choose_true type first branch
          · simpa only [thenType] using represented
    | invalid childTrace invalid runtimeType =>
      obtain ⟨_, _, _, _, _, represented, _⟩ := conditionIH conditionFound environments heaps locals agrees (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨flag, rfl, _⟩ := bool_fields payload
        exact False.elim (invalid trivial)


  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children childrenSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after environments heaps locals agrees trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have meaning : ExpressionFailurePostContracts.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Children scope ids codes) faults post := by
      intro current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member
    have sequence := sequence_of_nodes (scope := scope) (certificate := Children scope ids codes) count nodes (fun id code member => (⟨rfl, member⟩ : Children scope ids codes scope id code))
    obtain ⟨sourceOutcome, sourceTrace, packed⟩ := constructor_inv receipt.metadata form unique valid trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      sequence.preserves_with_post sequenceJoins meaning environments heaps locals agrees sourceTrace
    cases represented with
    | @values sources payloadValues payloads =>
      cases packed
      have projected := receipt.metadata.projected
      rw [receipt.sourceType] at projected
      refine ⟨.inRight .word (.constructed tag (.pair (.word header) (packValues payloadValues))), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
      · rw [construct_rename]; exact construct_success tag header evaluated
      · rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
          receipt.selected projected receipt.registered (valuesRep payloads))
    | fault matched =>
      cases packed
      cases sourceTrace with
      | fault failed =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [construct_rename]; exact construct_failure tag header evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          ScalarConstructorFaultPostContracts.arguments_fault_outcome constructorJoins
            receipt form valid count nodes failed retained⟩

  | @member id node base baseNode name index identity branches result child metadata baseMetadata form layout childTree childTreeSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after environments heaps locals agrees trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have raw := member_inv metadata form unique trace
    cases raw with
    | value childTrace selected =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees (.value childTrace)
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
        ih baseMetadata.found environments heaps locals agrees (.fault childTrace)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [member_rename layout]; exact LanguageResult.bind_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          ScalarMemberFaultPostContracts.base_fault_outcome memberJoins metadata baseMetadata form layout childTrace retained⟩
    | shape childTrace invalid =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, _⟩ := member_success layout payload evaluated
        subst_vars
        exact False.elim (invalid .intro)
    | position childTrace missing =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, _⟩ :=
        ih baseMetadata.found environments heaps locals agrees (.value childTrace)
      cases represented with
      | value payload =>
        obtain ⟨_, _, _, _, shape, selected, _⟩ := member_success layout payload evaluated
        cases shape
        exact False.elim (missing_excludes missing selected)

include extension unique uninitialized in
theorem preserves_with_literals
    (literalMeaning : GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.Preserves.forget
    (preserves_with_literals_and_post (functions := functions) (extension := extension) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence) (unique := unique)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
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

include extension in
theorem reflects_with_literals_and_post
    {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}
    (sequenceJoins : ExpressionFailurePostContracts.SequenceJoins post listPost program context evidence source)
    (ordinaryJoins : ExpressionFailurePostContracts.CompositionJoins post listPost program context evidence source)
    (constructorJoins : ScalarConstructorFaultPostContracts.Joins post listPost values program context evidence source)
    (memberJoins : ScalarMemberFaultPostContracts.Joins post values program context evidence source)
    (literalMeaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults post)
    (readMeaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionReads.LoweredRead fuel values source context reasonAt) faults post) :
    ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults post := by
  intro scope id lowered ⟨tree, sites⟩
  induction sites with
  | fragment child childSites =>
    exact CompatibleExpressionMembers.reflects_with_literals_and_post functions extension program evidence sequenceJoins ordinaryJoins constructorJoins memberJoins literalMeaning readMeaning ⟨child, childSites⟩
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
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
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
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
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
                (.conditionalFalse (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata) conditionTrace)
                branchTrace retained⟩
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
                (.conditionalTrue (lookupExpression?_sound metadata.found) form (ScalarExpressionFaultPostContracts.ordinary_layout metadata) conditionTrace)
                branchTrace retained⟩
            simpa only [thenType] using represented


  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children childrenSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore environments heaps locals agrees evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have meaning : ExpressionFailurePostContracts.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (Children scope ids codes) faults post := by
      intro current child code entry
      obtain ⟨rfl, member⟩ := entry
      exact ih child code member
    have sequence := sequence_of_nodes (scope := scope) (certificate := Children scope ids codes) count nodes (fun id code member => (⟨rfl, member⟩ : Children scope ids codes scope id code))
    rw [construct_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        sequence.reflects_with_post sequenceJoins meaning environments heaps locals agrees childEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (construct_failure tag header childEvaluation)
        cases trace with
        | fault failed =>
          exact ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid (.fault failed) (.fault _),
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
            ScalarConstructorFaultPostContracts.arguments_fault_outcome constructorJoins
              receipt form valid count nodes failed retained⟩
    | caseRight childEvaluation branch =>
      obtain ⟨sourceOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        sequence.reflects_with_post sequenceJoins meaning environments heaps locals agrees childEvaluation
      cases represented with
      | values payloads =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (construct_success tag header childEvaluation)
        have projected := receipt.metadata.projected
        rw [receipt.sourceType] at projected
        refine ⟨_, after, finalMap, finalWorld, constructor_intro receipt.metadata form valid trace (.values _),
          ?_, finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩
        rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans values.registryOwner)
          receipt.selected projected receipt.registered (valuesRep payloads))

  | @member id node base baseNode name index identity branches result child metadata baseMetadata form layout childTree childTreeSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    rw [member_rename layout] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
        ih baseMetadata.found environments heaps locals agrees baseEvaluation
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
        ih baseMetadata.found environments heaps locals agrees baseEvaluation
      cases represented with
      | value payload =>
        obtain ⟨actualMetadata, sources, selected, native, shape, sourceAt, related, expected⟩ := member_success layout payload baseEvaluation
        subst_vars
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
        cases trace with
        | value childTrace =>
          exact ⟨_, after, finalMap, finalWorld, member_intro metadata form (.value childTrace sourceAt), .value related,
            finalHeaps, maps, worlds, frame, heapMetadata, trivial⟩

include extension uninitialized in
theorem reflects_with_literals
    (literalMeaning : GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source literals faults) :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree.WithLiterals (fuel := fuel) (values := values) (source := source)
        (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults := by
  exact ExpressionFailurePostContracts.Reflects.forget
    (reflects_with_literals_and_post (functions := functions) (extension := extension) (fuel := fuel) (reasonAt := reasonAt)
      (program := program) (evidence := evidence)
      (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
      (ExpressionFailurePostContracts.trivial_composition_joins program context evidence source)
      (ScalarConstructorFaultPostContracts.trivial_joins values program context evidence source)
      (ScalarMemberFaultPostContracts.trivial_joins values program context evidence source)
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

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursive
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursiveCertificates
/-! Successful ordinary Functions lowering extracts the full recursive data
and control tree. Raw constructor/member types come from independent typing;
actual native operand checks select the admitted primitive operation. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursive
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
  | fragment syntaxTree =>
    refine (fun ⟨tree, sites⟩ => ⟨_, Tree.LiteralSites.fragment tree sites⟩) (CompatibleExpressionMembers.tree_of_functions_with_literals literals literalFactory unique declarations signatures (constructorValid.restrict (fun _ child => .fragment child)) ?_ ?_ syntaxTree found typed accepted)
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

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursive
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualRecursive
/-! The actual contextual dispatcher supplies the ordinary recursive data/control policy.
Static occurrence metadata excludes local specialization and output coercions.
The final receipt contains no child lowering or runtime execution hypothesis. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursive
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
                  have localBinder := ordinary.localBinder _ _ _ _ (.fragment (.fragment (.fragment (.primitive (.product (.read found form)))))) found form
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

private theorem fragment_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : Syntax source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases syntaxTree with
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

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionRecursive
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexMeaning
/-! Whole finite index trees evaluate base, then key, then the actual generated
comparator. Every child meaning is discharged by structural induction; actual
hidden slots are typed because comparator closures capture those slots. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleMapping
open GenericExpressionMeaning (agree_prefix rename_prefix)

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

include unique in
theorem preserves_with_post {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    (fragment : ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionMembers.Tree fuel values source context solved reasonAt) faults post)
    (terminalProvider : IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt SourceScalar faults post)
    (joins : IndexFaultPostContracts.IndexJoins post values program context evidence source) :
    ExpressionFailurePostContracts.TypedPreserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults post := by
  intro scope id lowered tree
  induction tree with
  | fragment child =>
    exact fragment child
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType scalar firstTree secondTree firstIH secondIH =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped trace
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rcases (index_inv header.metadata form unique trace).split with ⟨reason, rfl, failed⟩ | ⟨baseSource, middle, baseTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, childPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, metadata,
          joins.base_outcome header keyFound form sourceType failed childPost⟩
        rw [index_rename comparison header.registered header.comparisonType]
        exact LanguageResult.bind_failure _ evaluated
    · obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        firstIH header.baseMetadata.found environments heaps locals agrees actualTyped (.value baseTrace)
      cases represented with
      | @value _ baseValue baseRep =>
        have keyEnvironment := RuntimeEnvironmentHasTypes.cons baseRep.runtime_hasType (actualTyped.weaken firstWorlds)
        rcases tail with ⟨reason, rfl, failed⟩ | ⟨keySource, keyTrace, terminal⟩
        · obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame, metadata, childPost⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (.fault failed)
          cases represented with
          | fault matched =>
            refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
              joins.key_outcome header keyFound form sourceType baseTrace failed childPost⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            exact LanguageResult.bind_success _ firstEval (LanguageResult.bind_failure _ secondEval)
        · obtain ⟨value, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, _keyPost⟩ :=
            secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) keyEnvironment (.value keyTrace)
          cases represented with
          | @value _ keyValue keyRep =>
            obtain ⟨actualOutcome, result, finalStore, finalWorld, terminal', related, lookup, finalHeaps, worlds, frame, uniqueResult, _terminalTrace, terminalPost⟩ :=
              terminalProvider header sourceType scalar (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace keyTrace
            have same := uniqueResult outcome terminal
            subst actualOutcome
            refine ⟨result, finalStore, keyMap, finalWorld, ?_, related, finalHeaps,
              firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
              (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, terminalPost⟩
            rw [index_rename comparison header.registered header.comparisonType]
            rw [rename_prefix] at secondEval
            apply SourceCoreCompatibleDataExpressions.index_completed layout (reasonAt id) firstEval secondEval
            simpa only [Transport.expression_weaken] using lookup

theorem reflects_with_post {post : ExpressionFailurePostContracts.ExpressionFaultPost}
    (fragment : ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (CompatibleExpressionMembers.Tree fuel values source context solved reasonAt) faults post)
    (terminalProvider : IndexFaultPostContracts.TerminalProvider values source functions registry program context evidence
      reasonAt SourceScalar faults post)
    (joins : IndexFaultPostContracts.IndexJoins post values program context evidence source) :
    ExpressionFailurePostContracts.TypedReflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults post := by
  intro scope id lowered tree
  induction tree with
  | fragment child =>
    exact fragment child
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType scalar firstTree secondTree firstIH secondIH =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees actualTyped evaluated
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst root
    rw [index_rename comparison header.registered header.comparisonType] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft baseEvaluation branch =>
      obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, childPost⟩ :=
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
            joins.base_outcome header keyFound form sourceType failed childPost⟩
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
            obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, childPost⟩ :=
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
                  joins.key_outcome header keyFound form sourceType baseTrace failed childPost⟩
          | caseRight keyEvaluation lookupEvaluation =>
            rw [← rename_prefix] at keyEvaluation
            obtain ⟨outcome, after, keyMap, keyWorld, trace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, _keyPost⟩ :=
              secondIH keyFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (agree_prefix agrees _) keyEnvironment keyEvaluation
            cases represented with
            | @value keySource keyValue keyRep =>
              cases trace with
              | value keyTrace =>
                obtain ⟨outcome, result, endStore, finalWorld, terminal, related, lookup, finalHeaps, worlds, frame, uniqueResult, _terminalTrace, terminalPost⟩ :=
                  terminalProvider header sourceType scalar (baseRep.extend (.refl _) keyMaps keyWorlds) keyRep
                    (actualTyped.weaken (firstWorlds.trans keyWorlds)) keyHeaps keyFound form baseTrace keyTrace
                rw [rename_prefix] at keyEvaluation
                have expected := SourceCoreCompatibleDataExpressions.index_completed (comparison := comparison.expression) layout (reasonAt id) baseEvaluation keyEvaluation
                  (by simpa only [Transport.expression_weaken] using lookup)
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete expected
                exact ⟨outcome, after, keyMap, finalWorld, index_intro header.metadata form (terminal.trace baseTrace keyTrace),
                    related, finalHeaps, firstMaps.trans keyMaps, (firstWorlds.trans keyWorlds).trans worlds,
                    (firstFrame.trans keyFrame).trans frame, firstMetadata.trans keyMetadata, terminalPost⟩

include extension valid unique uninitialized missing in
theorem preserves :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  exact ExpressionFailurePostContracts.TypedPreserves.forget
    (preserves_with_post (functions := functions) (program := program) (evidence := evidence) (unique := unique)
      (ExpressionFailurePostContracts.TypedPreserves.of_trivial
        (TypedGenericExpressionMeaning.preserves_of_unrestricted
        (CompatibleExpressionMembers.preserves functions extension program evidence valid unique uninitialized)))
      (IndexFaultPostContracts.trivial_scalar_terminal functions registry program context evidence reasonAt missing)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source))

include extension valid uninitialized missing in
theorem reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  exact ExpressionFailurePostContracts.TypedReflects.forget
    (reflects_with_post (functions := functions) (program := program) (evidence := evidence)
      (ExpressionFailurePostContracts.TypedReflects.of_trivial
        (TypedGenericExpressionMeaning.reflects_of_unrestricted
        (CompatibleExpressionMembers.reflects functions extension program evidence valid uninitialized)))
      (IndexFaultPostContracts.trivial_scalar_terminal functions registry program context evidence reasonAt missing)
      (IndexFaultPostContracts.trivial_index_joins values program context evidence source))

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexExtraction
/-! Accepted ordinary index lowering supplies the entire static tree. Raw
mapping/key types follow independent source typing, while the real compiler
supplies comparator preparation and registered layout receipts. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference CompatibleExpressionReads

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

theorem index_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {id base key : ExpressionId} {node baseNode : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (baseFound : source.lookupExpression? base = some baseNode)
    (form : node.form = .index base key)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) context source scope id reasonAt = .ok lowered) :
    ∃ layout comparison first second,
      lowered = ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)⟩ ∧
      Header values source id base node baseNode layout comparison first second ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope base reasonAt = .ok first ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope key reasonAt = .ok second := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) context childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form, readPolicy, bind, Except.bind, pure, Except.pure] at accepted
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error error => simp [read] at accepted
      | ok pair =>
        rcases pair with ⟨other, type⟩
        have metadata := metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        simp only [read, form, leafPolicy] at accepted
        unfold SourceCoreCompatibleDataExpressions.leafLowerer at accepted
        simp only [read, bind, Except.bind, form] at accepted
        obtain ⟨layout, comparison, first, second, output, header, firstGenerated, secondGenerated⟩ :=
          index_of_lower found baseFound form accepted
        exact ⟨layout, comparison, first, second, output, header,
          by simpa only [Nat.min_self] using firstGenerated,
          by simpa only [Nat.min_self] using secondGenerated⟩
  · simp [owner, bind, Except.bind] at accepted

theorem tree_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
    (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
  | fragment syntaxTree =>
    refine .fragment (CompatibleExpressionMembers.tree_of_functions unique declarations signatures closed residual ?_ ?_ syntaxTree found typed accepted)
    · exact ⟨fun id child => policyFor.special id (.fragment child), fun id child => policyFor.read id (.fragment child), policyFor.lower, policyFor.leaf⟩
    · exact fun id node child => coercions id node (.fragment child)
  | @index id original base key keyNode originalFound form keyFound scalar firstSyntax secondSyntax firstIH secondIH =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have syntaxTree : Syntax source id := .index originalFound form keyFound scalar firstSyntax secondSyntax
      obtain ⟨keyType, baseTyped, keyTyped⟩ := index_source_types unique originalFound form
        (coercions _ _ syntaxTree originalFound) typed
      obtain ⟨baseNode, baseContains, baseType⟩ := baseTyped.stored_type
      obtain ⟨actualKeyNode, keyContains, actualKeyType⟩ := keyTyped.stored_type
      have keySame := Option.some.inj ((lookupExpression?_complete unique keyContains).symm.trans keyFound)
      subst actualKeyNode
      have baseFound := lookupExpression?_complete unique baseContains
      rw [← actualKeyType] at keyTyped baseType baseTyped
      rw [← baseType] at baseTyped
      obtain ⟨layout, comparison, first, second, rfl, header, firstGenerated, secondGenerated⟩ :=
        index_of_functions originalFound baseFound form
          (policyFor.special _ syntaxTree) (policyFor.read _ syntaxTree) policyFor.leaf accepted
      exact .index header keyFound form baseType scalar (firstIH baseFound baseTyped firstGenerated)
        (secondIH keyFound keyTyped secondGenerated)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualIndices
/-! The actual contextual dispatcher supplies the ordinary recursive-index policy.
Static occurrence metadata excludes local specialization and output coercions.
The final receipt contains no child lowering or runtime execution hypothesis. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
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
  | fragment previous =>
    cases previous with
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
                have localBinder := ordinary.localBinder _ _ _ _ (.fragment (.fragment (.fragment (.primitive (.product (.read found form)))))) found form
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
  | index found form _ _ _ _ =>
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
  | fragment previous =>
    cases previous with
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
  | index originalFound form _ _ _ _ =>
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
      CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

private theorem fragment_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : Syntax source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases syntaxTree with
  | fragment previous =>
    cases previous with
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
  | index found _ _ _ _ _ => exact ⟨_, found⟩

private theorem context_bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Finite scalar-key index trees are extracted from the production
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

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedTree
/-! Typed recursive data/control grammar includes proxies and scalar-key mapping indices
at every child position. Static receipts preserve the actual comparator, raw
metadata and generated code, while meaning later uses actual environment typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTyped
open Core Frontend SourceInference CompatibleExpressionPrimitives
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | proxy {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .proxy inner) : Syntax source id
  | fragment {id} (child : CompatibleExpressionRecursive.Syntax source id) : Syntax source id
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
      (scalar : CompatibleExpressionIndices.SourceScalar keyNode.type)
      (first : Syntax source base) (second : Syntax source key) : Syntax source id

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | proxy {id lowered} (receipt : CompatibleExpressionProxies.Certificate values source scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | fragment {id lowered}
      (child : CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope id lowered) :
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
      (scalar : CompatibleExpressionIndices.SourceScalar keyNode.type)
      (firstTree : Tree fuel values source context solved reasonAt scope base first)
      (secondTree : Tree fuel values source context solved reasonAt scope key second) :
      Tree fuel values source context solved reasonAt scope id
        ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)⟩

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
  | constructor receipt _ _ _ _ _ =>
      have same := Option.some.inj (receipt.metadata.found.symm.trans found)
      exact same ▸ receipt.metadata.projected
  | index header _ _ _ _ _ _ =>
      have same := Option.some.inj (header.metadata.found.symm.trans found)
      exact same ▸ header.metadata.projected
  | group metadata _ _ _ _ | pair metadata _ _ _ _ _ _ | unary metadata _ _ _ _ _ _ | binary metadata _ _ _ _ _ _ _ _ _ | conditional metadata _ _ _ _ _ _ _ _ _ _ | member metadata _ _ _ _ =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      exact same ▸ metadata.projected

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTyped
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralTree
/-! Typed recursive data/control grammar includes proxies and general mapping indices
at every child position. Static receipts preserve the actual comparator, raw
metadata and generated code, while meaning later uses actual environment typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneral
open Core Frontend SourceInference CompatibleExpressionPrimitives
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | proxy {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .proxy inner) : Syntax source id
  | fragment {id} (child : CompatibleExpressionRecursive.Syntax source id) : Syntax source id
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

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | proxy {id lowered} (receipt : CompatibleExpressionProxies.Certificate values source scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | fragment {id lowered}
      (child : CompatibleExpressionRecursive.Tree fuel values source context solved reasonAt scope id lowered) :
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
  | constructor receipt _ _ _ _ _ =>
      have same := Option.some.inj (receipt.metadata.found.symm.trans found)
      exact same ▸ receipt.metadata.projected
  | index header _ _ _ _ _ =>
      have same := Option.some.inj (header.metadata.found.symm.trans found)
      exact same ▸ header.metadata.projected
  | group metadata _ _ _ _ | pair metadata _ _ _ _ _ _ | unary metadata _ _ _ _ _ _ | binary metadata _ _ _ _ _ _ _ _ _ | conditional metadata _ _ _ _ _ _ _ _ _ _ | member metadata _ _ _ _ =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      exact same ▸ metadata.projected

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneral
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMissingSourceReceipts
/-! Actual expression and place suffixes retain their literal missing rows.
Ownership uses the checked fresh reason and the real selected key; Source views
and receiving metadata remain independent query receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMissingSourceReceipts
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaceFaultSites
abbrev Key := SourceSpecialization.SpecializationKey
abbrev IndexSite := SourceCoreDataFaultSites.IndexSite
abbrev PlaceSite := SourceCoreDataPlaceFaultSites.Site

/-- This is the accepted expression suffix at its actual Source node. -/
def ExpressionAt (indices : List IndexSite) (owner : Key) (source : TypedSource)
    (node : ExpressionNode) (row : MissingSite) : Prop :=
  ∃ mapping key baseNode keyType valueType selected,
    node.form = .index mapping key ∧ source.lookupExpression? mapping = some baseNode ∧
    SourceCoreRawMetadata.runtimeType baseNode.type = .mapping keyType valueType ∧
    SourceCoreRawMetadata.runtimeType node.type = valueType ∧
    indices.find? (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = some selected ∧
    row = ⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, selected.reason⟩

/-- The actual place and key lookup fix the appended route row. -/
def PlaceAt (places : List PlaceSite) (owner : Key) (source : TypedSource)
    (node : StatementNode) (assignment : AssignmentResolution) (row : MissingSite) : Prop :=
  ∃ place key keyNode valueType,
    place ∈ places ∧ place.owner = owner ∧ place.location = .occurrence node.id.occurrence ∧
    place.binder = assignment.target.root ∧ place.missingType = some valueType ∧
    source.lookupExpression? key = some keyNode ∧
    row = ⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
      keyNode.type, valueType, node.span, place.reason⟩

def Origin (sources : List (Key × TypedSource)) (indices : List IndexSite)
    (places : List PlaceSite) (row : MissingSite) : Prop :=
  (∃ owner source node, (owner, source) ∈ sources ∧ source.owner = owner.declaration ∧
    SourceSemantics.ContainsExpression source node.id node ∧ ExpressionAt indices owner source node row) ∨
  (∃ owner source node assignment, (owner, source) ∈ sources ∧ source.owner = owner.declaration ∧
    SourceSemantics.ContainsStatement source node.id node ∧ PlaceAt places owner source node assignment row)

structure Ownership (indices : List IndexSite) (places : List PlaceSite) : Prop where
  index : ∀ left, left ∈ indices → ∀ right, right ∈ indices → left.reason = right.reason →
    left.owner = right.owner ∧ left.expression = right.expression
  separate : ∀ index, index ∈ indices → ∀ place, place ∈ places →
    ∀ type, place.missingType = some type → index.reason ≠ place.reason

def NodesCovered (owner : Key) (source : TypedSource) (nodes : List Node)
    (indices : List IndexSite) (missing : List MissingSite) : Prop :=
  ∀ node, Node.expression node ∈ nodes → ∀ mapping key, node.form = .index mapping key →
    ∃ row, row ∈ missing ∧ ExpressionAt indices owner source node row

def SourcesCovered (sources : List (Key × TypedSource)) (indices : List IndexSite)
    (missing : List MissingSite) : Prop :=
  ∀ owner source, (owner, source) ∈ sources → NodesCovered owner source source.nodes indices missing

structure Inventory (sources visited : List (Key × TypedSource)) (indices : List IndexSite)
    (places : List PlaceSite) (missing : List MissingSite) : Prop where
  origins : ∀ row, row ∈ missing → Origin sources indices places row
  ownership : Ownership indices places
  covered : SourcesCovered visited indices missing

structure NodeInventory (sources visited : List (Key × TypedSource)) (owner : Key)
    (source : TypedSource) (seen : List Node) (indices : List IndexSite)
    (places : List PlaceSite) (missing : List MissingSite) : Prop where
  inventory : Inventory sources visited indices places missing
  covered : NodesCovered owner source seen indices missing

/-- Route changes are independent of any global Source inventory. -/
structure RouteChanges (owner : Key) (source : TypedSource) (node : StatementNode)
    (assignment : AssignmentResolution) (start : Nat) (beforePlaces afterPlaces : List PlaceSite)
    (beforeMissing afterMissing : List MissingSite) : Prop where
  places : ∃ added, afterPlaces = beforePlaces ++ added ∧
    ∀ place, place ∈ added → start ≤ place.reason.val
  missing : ∃ added, afterMissing = beforeMissing ++ added ∧
    ∀ row, row ∈ added → PlaceAt afterPlaces owner source node assignment row

theorem ExpressionAt.append {indices : List IndexSite} {owner : Key} {source : TypedSource}
    {node : ExpressionNode} {row : MissingSite} (receipt : ExpressionAt indices owner source node row)
    (later : List IndexSite) : ExpressionAt (indices ++ later) owner source node row := by
  obtain ⟨mapping, key, base, keyType, valueType, selected, form, found, mappingView, valueView, chosen, same⟩ := receipt
  exact ⟨mapping, key, base, keyType, valueType, selected, form, found, mappingView, valueView,
    by simp only [List.find?_append, chosen]; rfl, same⟩

theorem PlaceAt.mono {places later : List PlaceSite} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution} {row : MissingSite}
    (receipt : PlaceAt places owner source node assignment row)
    (includes : ∀ place, place ∈ places → place ∈ later) : PlaceAt later owner source node assignment row := by
  obtain ⟨place, key, keyNode, valueType, member, owns, location, binder, kind, found, same⟩ := receipt
  exact ⟨place, key, keyNode, valueType, includes place member, owns, location, binder, kind, found, same⟩

theorem Origin.mono {sources : List (Key × TypedSource)} {indices : List IndexSite}
    {places laterPlaces : List PlaceSite} {row : MissingSite}
    (origin : Origin sources indices places row) (laterIndices : List IndexSite)
    (includes : ∀ place, place ∈ places → place ∈ laterPlaces) :
    Origin sources (indices ++ laterIndices) laterPlaces row := by
  rcases origin with ⟨owner, source, node, member, owns, contains, receipt⟩ |
    ⟨owner, source, node, assignment, member, owns, contains, receipt⟩
  · exact .inl ⟨owner, source, node, member, owns, contains, receipt.append laterIndices⟩
  · exact .inr ⟨owner, source, node, assignment, member, owns, contains, receipt.mono includes⟩

theorem NodesCovered.mono {owner : Key} {source : TypedSource} {nodes : List Node}
    {indices : List IndexSite} {missing laterMissing : List MissingSite}
    (covered : NodesCovered owner source nodes indices missing) (laterIndices : List IndexSite)
    (includes : ∀ row, row ∈ missing → row ∈ laterMissing) :
    NodesCovered owner source nodes (indices ++ laterIndices) laterMissing := by
  intro node member mapping key form
  obtain ⟨row, present, receipt⟩ := covered node member mapping key form
  exact ⟨row, includes row present, receipt.append laterIndices⟩

theorem Inventory.empty (sources : List (Key × TypedSource)) : Inventory sources [] [] [] [] := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro item member; cases member
  · intro item member; cases member
  · intro item member; cases member
  · intro owner source member; cases member

theorem Ownership.append_index {indices : List IndexSite} {places : List PlaceSite}
    (ownership : Ownership indices places) (site : IndexSite)
    (freshIndex : ∀ old, old ∈ indices → old.reason ≠ site.reason)
    (freshPlace : ∀ old, old ∈ places → ∀ type, old.missingType = some type → old.reason ≠ site.reason) :
    Ownership (indices ++ [site]) places := by
  refine ⟨?_, ?_⟩
  · intro left leftMember right rightMember same
    rcases List.mem_append.mp leftMember with leftOld | leftNew
    · rcases List.mem_append.mp rightMember with rightOld | rightNew
      · exact ownership.index left leftOld right rightOld same
      · cases List.mem_singleton.mp rightNew
        exact False.elim (freshIndex left leftOld same)
    · cases List.mem_singleton.mp leftNew
      rcases List.mem_append.mp rightMember with rightOld | rightNew
      · exact False.elim (freshIndex right rightOld same.symm)
      · cases List.mem_singleton.mp rightNew
        exact ⟨rfl, rfl⟩
  · intro index member place placeMember type kind same
    rcases List.mem_append.mp member with old | new
    · exact ownership.separate index old place placeMember type kind same
    · cases List.mem_singleton.mp new
      exact freshPlace place placeMember type kind same.symm

theorem Inventory.append_index {sources visited : List (Key × TypedSource)}
    {indices : List IndexSite} {places : List PlaceSite} {missing : List MissingSite}
    (inventory : Inventory sources visited indices places missing) (site : IndexSite)
    (freshIndex : ∀ old, old ∈ indices → old.reason ≠ site.reason)
    (freshPlace : ∀ old, old ∈ places → ∀ type, old.missingType = some type → old.reason ≠ site.reason) :
    Inventory sources visited (indices ++ [site]) places missing := by
  refine ⟨?_, inventory.ownership.append_index site freshIndex freshPlace, ?_⟩
  · intro row member
    exact (inventory.origins row member).mono [site] (fun _ member => member)
  · intro owner source member
    exact (inventory.covered owner source member).mono [site] (fun _ member => member)

theorem Inventory.fixed_place {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    {places : List PlaceSite} {missing : List MissingSite} (inventory : Inventory sources visited indices places missing)
    (place : PlaceSite) (kind : place.missingType = none) :
    Inventory sources visited indices (places ++ [place]) missing := by
  refine ⟨?_, ⟨inventory.ownership.index, ?_⟩, inventory.covered⟩
  · intro row member
    simpa only [List.append_nil] using (inventory.origins row member).mono []
      (fun _ member => List.mem_append_left _ member)
  · intro index indexMember current member type currentKind
    rcases List.mem_append.mp member with old | new
    · exact inventory.ownership.separate index indexMember current old type currentKind
    · cases List.mem_singleton.mp new
      rw [kind] at currentKind
      cases currentKind

theorem Inventory.append_expression {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    {places : List PlaceSite} {missing : List MissingSite} (inventory : Inventory sources visited indices places missing)
    {owner : Key} {source : TypedSource} {node : ExpressionNode} {row : MissingSite}
    (member : (owner, source) ∈ sources) (owns : source.owner = owner.declaration)
    (contains : SourceSemantics.ContainsExpression source node.id node)
    (receipt : ExpressionAt indices owner source node row) :
    Inventory sources visited indices places (missing ++ [row]) := by
  refine ⟨?_, inventory.ownership, ?_⟩
  · intro current currentMember
    rcases List.mem_append.mp currentMember with old | new
    · exact inventory.origins current old
    · cases List.mem_singleton.mp new
      exact .inl ⟨owner, source, node, member, owns, contains, receipt⟩
  · intro owner source member
    simpa only [List.append_nil] using (inventory.covered owner source member).mono []
      (fun _ member => List.mem_append_left _ member)

theorem RouteChanges.refl (owner : Key) (source : TypedSource) (node : StatementNode)
    (assignment : AssignmentResolution) (start : Nat) (places : List PlaceSite) (missing : List MissingSite) :
    RouteChanges owner source node assignment start places places missing missing := by
  refine ⟨⟨[], by simp, ?_⟩, ⟨[], by simp, ?_⟩⟩
  all_goals intro item member; cases member

theorem RouteChanges.trans {owner : Key} {source : TypedSource} {node : StatementNode}
    {assignment : AssignmentResolution} {start middle : Nat} {beforePlaces currentPlaces afterPlaces : List PlaceSite}
    {beforeMissing currentMissing afterMissing : List MissingSite}
    (first : RouteChanges owner source node assignment start beforePlaces currentPlaces beforeMissing currentMissing)
    (second : RouteChanges owner source node assignment middle currentPlaces afterPlaces currentMissing afterMissing)
    (grows : start ≤ middle) :
    RouteChanges owner source node assignment start beforePlaces afterPlaces beforeMissing afterMissing := by
  obtain ⟨firstPlaces, placesEq, placesBound⟩ := first.places
  obtain ⟨laterPlaces, laterEq, laterBound⟩ := second.places
  obtain ⟨firstMissing, missingEq, missingAt⟩ := first.missing
  obtain ⟨laterMissing, laterMissingEq, laterAt⟩ := second.missing
  refine ⟨⟨firstPlaces ++ laterPlaces, by rw [laterEq, placesEq, List.append_assoc], ?_⟩,
    ⟨firstMissing ++ laterMissing, by rw [laterMissingEq, missingEq, List.append_assoc], ?_⟩⟩
  · intro place member
    rcases List.mem_append.mp member with old | new
    · exact placesBound place old
    · exact Nat.le_trans grows (laterBound place new)
  · intro row member
    rcases List.mem_append.mp member with old | new
    · exact (missingAt row old).mono (fun _ member => laterEq ▸ List.mem_append_left _ member)
    · exact laterAt row new

theorem RouteChanges.apply {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    {beforePlaces afterPlaces : List PlaceSite} {beforeMissing afterMissing : List MissingSite}
    {owner : Key} {source : TypedSource} {node : StatementNode} {assignment : AssignmentResolution} {start : Nat}
    (changes : RouteChanges owner source node assignment start beforePlaces afterPlaces beforeMissing afterMissing)
    (inventory : Inventory sources visited indices beforePlaces beforeMissing)
    (member : (owner, source) ∈ sources) (owns : source.owner = owner.declaration)
    (contains : SourceSemantics.ContainsStatement source node.id node)
    (below : ∀ index, index ∈ indices → index.reason.val < start) :
    Inventory sources visited indices afterPlaces afterMissing := by
  obtain ⟨addedPlaces, placesEq, placesBound⟩ := changes.places
  obtain ⟨addedMissing, missingEq, missingAt⟩ := changes.missing
  refine ⟨?_, ⟨inventory.ownership.index, ?_⟩, ?_⟩
  · intro row rowMember
    rw [missingEq] at rowMember
    rcases List.mem_append.mp rowMember with old | new
    · simpa only [List.append_nil] using (inventory.origins row old).mono []
        (fun _ member => placesEq ▸ List.mem_append_left _ member)
    · exact .inr ⟨owner, source, node, assignment, member, owns, contains, missingAt row new⟩
  · intro index indexMember place placeMember type kind same
    rw [placesEq] at placeMember
    rcases List.mem_append.mp placeMember with old | new
    · exact inventory.ownership.separate index indexMember place old type kind same
    · have oldBound := below index indexMember
      have newBound := placesBound place new
      have number := congrArg Fin.val same
      omega
  · intro owner source member
    simpa only [List.append_nil] using (inventory.covered owner source member).mono []
      (fun _ member => missingEq ▸ List.mem_append_left _ member)

theorem NodeInventory.start {sources visited : List (Key × TypedSource)} {indices : List IndexSite}
    {places : List PlaceSite} {missing : List MissingSite} (inventory : Inventory sources visited indices places missing)
    (owner : Key) (source : TypedSource) : NodeInventory sources visited owner source [] indices places missing := by
  refine ⟨inventory, ?_⟩
  intro node member; cases member

theorem NodeInventory.step {sources visited : List (Key × TypedSource)} {owner : Key} {source : TypedSource}
    {seen : List Node} {indices : List IndexSite} {places : List PlaceSite} {missing : List MissingSite} {retained : Node}
    (inventory : NodeInventory sources visited owner source seen indices places missing)
    (selected : ∀ node, retained = .expression node → ∀ mapping key, node.form = .index mapping key →
      ∃ row, row ∈ missing ∧ ExpressionAt indices owner source node row) :
    NodeInventory sources visited owner source (seen ++ [retained]) indices places missing := by
  refine ⟨inventory.inventory, ?_⟩
  intro node member mapping key form
  rcases List.mem_append.mp member with old | new
  · exact inventory.covered node old mapping key form
  · exact selected node (List.mem_singleton.mp new).symm mapping key form

theorem NodeInventory.finish {sources visited : List (Key × TypedSource)} {owner : Key} {source : TypedSource}
    {indices : List IndexSite} {places : List PlaceSite} {missing : List MissingSite}
    (inventory : NodeInventory sources visited owner source source.nodes indices places missing) :
    Inventory sources (visited ++ [(owner, source)]) indices places missing := by
  refine ⟨inventory.inventory.origins, inventory.inventory.ownership, ?_⟩
  intro key actual member
  rcases List.mem_append.mp member with old | new
  · exact inventory.inventory.covered key actual old
  · cases List.mem_singleton.mp new
    exact inventory.covered

theorem NodeInventory.replace {sources visited : List (Key × TypedSource)} {owner : Key} {source : TypedSource}
    {seen : List Node} {indices : List IndexSite} {places : List PlaceSite} {missing : List MissingSite}
    (previous : NodeInventory sources visited owner source seen indices places missing)
    (laterIndices : List IndexSite) {laterPlaces : List PlaceSite} {laterMissing : List MissingSite}
    (inventory : Inventory sources visited (indices ++ laterIndices) laterPlaces laterMissing)
    (includes : ∀ row, row ∈ missing → row ∈ laterMissing) :
    NodeInventory sources visited owner source seen (indices ++ laterIndices) laterPlaces laterMissing :=
  ⟨inventory, previous.covered.mono laterIndices includes⟩

/-- The finite accepted suffix fields do not require global membership. -/
def ExpressionSuffix (source : TypedSource) (node : ExpressionNode) (mapping : ExpressionId)
    (reason : Word) (row : MissingSite) (owner : Key) : Prop :=
  ∃ baseNode keyType valueType, source.lookupExpression? mapping = some baseNode ∧
    SourceCoreRawMetadata.runtimeType baseNode.type = .mapping keyType valueType ∧
    SourceCoreRawMetadata.runtimeType node.type = valueType ∧
    row = ⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, reason⟩

theorem ExpressionSuffix.at_index {source : TypedSource} {node : ExpressionNode} {mapping key : ExpressionId}
    {reason : Word} {row : MissingSite} {owner : Key} (suffix : ExpressionSuffix source node mapping reason row owner)
    (indices : List IndexSite) (form : node.form = .index mapping key) {selected : IndexSite}
    (found : indices.find? (fun site => decide (site.owner = owner ∧ site.expression = node.id)) = some selected)
    (same : selected.reason = reason) : ExpressionAt indices owner source node row := by
  obtain ⟨base, keyType, valueType, lookup, mappingView, valueView, rowEq⟩ := suffix
  exact ⟨mapping, key, base, keyType, valueType, selected, form, lookup, mappingView, valueView, found,
    by rw [rowEq, same]⟩

def Receipt {context : SourceCoreCompatibleDataPlaceFaultSites.Context} (plan : SourceSpecializationWorklist.Plan)
    (root : Key) (sources : List (Key × TypedSource)) (program : SourceCoreCompatibleDataPlaceFaultSites.Program context) : Prop :=
  CompatibleExpressionIndexSourceReceipts.Receipt plan root sources program ∧
    Inventory (plan.specializations.map (fun row => (row.key, row.function.typedBody)) ++ sources)
      (plan.specializations.map (fun row => (row.key, row.function.typedBody)) ++ sources)
      program.program.expressions.indices program.program.places program.missing

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMissingSourceReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionDataLeafNativeTyping
/-! Production data leaves use their exact registered layouts and comparator.
Proxy typing needs no child receipt. Index typing consumes the enclosing
structural induction's actual base and key code, including compound keys. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionDataLeafNativeTyping
open Core Frontend SourceInference
open CompatibleExpressionScalarNativeTyping

theorem proxy_native {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionProxies.Certificate values source scope id lowered)
    (context : Core.Context) : NativeTyping values.checked.catalog.definitions context lowered := by
  cases receipt with
  | proxy header =>
    obtain ⟨_, registered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner header.registered
    exact ⟨.namedData registered, LanguageResult.success_hasType (.construct header.registered .word)⟩

private theorem closed_native {definitions : DataEnvironment} {code : Expr} {type : Ty}
    (typed : HasType [] code type definitions) (context : Core.Context) : HasType context code type definitions := by
  have extended := typed.rename (mapping := Renaming.id) (target := context)
    (by intro index type found; cases found)
  simpa using extended

/-- The real prepared comparator is checked in an empty context and is then
transported statically. No runtime closure weakening is assumed. -/
theorem index_native {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {id base : ExpressionId} {node baseNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr} {context : Core.Context}
    (receipt : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
    (baseTyped : NativeTyping values.checked.catalog.definitions context first)
    (keyTyped : NativeTyping values.checked.catalog.definitions context second)
    (reason : Word) :
    NativeTyping values.checked.catalog.definitions context
      ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression
        first.expression second.expression reason⟩ := by
  refine ⟨receipt.registered.valueWellFormed, SourceCoreCompatibleDataExpressions.index_hasType reason
    receipt.registered ?_ ?_ ?_⟩
  · simpa only [receipt.comparisonType, SourceCoreCompatibleDataEquality.comparatorType,
      SourceCoreDataEquality.comparatorType] using closed_native comparison.typed context
  · simpa only [receipt.baseType] using baseTyped.2
  · simpa only [receipt.keyType] using keyTyped.2

theorem proxy_native_at {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionProxies.Certificate values source scope id lowered)
    (context : Core.Context) {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions) : NativeTyping definitions context lowered := by
  obtain ⟨wellFormed, native⟩ := proxy_native receipt context
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

theorem index_native_at {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {id base : ExpressionId} {node baseNode : ExpressionNode} {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
    {first second : SourceCoreBasic.LoweredExpr} {context : Core.Context} {definitions : DataEnvironment}
    (receipt : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
    (baseTyped : NativeTyping definitions context first)
    (keyTyped : NativeTyping definitions context second)
    (reason : Word)
    (extension : values.checked.catalog.definitions.Extends definitions) :
    NativeTyping definitions context
      ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression
        first.expression second.expression reason⟩ := by
  have registered := receipt.registered.extend_definitions extension
  refine ⟨registered.valueWellFormed, SourceCoreCompatibleDataExpressions.index_hasType reason
    registered ?_ ?_ ?_⟩
  · simpa only [receipt.comparisonType, SourceCoreCompatibleDataEquality.comparatorType,
      SourceCoreDataEquality.comparatorType] using closed_native (comparison.typed.extend_definitions extension) context
  · simpa only [receipt.baseType] using baseTyped.2
  · simpa only [receipt.keyType] using keyTyped.2

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionDataLeafNativeTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualReads
/-! Ordinary local reads through the actual shared contextual traversal.
Static catalog exclusion identifies this branch; it does not assume any child
execution or derive source metadata from native projection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Core Frontend SourceInference

private theorem contextualSource_ordinary
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (ordinary : locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  simp only [SourceCoreGeneralFunctions.contextualSource, found, bind, Except.bind, pure, Except.pure,
    form, ordinary, Bool.false_eq_true, ↓reduceIte]

private theorem evidence_ordinary (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (found : source.lookupExpression? id = some node) (form : node.form = .reference name (.local binder))
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, found, form, owned, requirements, coercions,
    bind, Except.bind, pure, Except.pure]

private theorem functions_read_receipts
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer} {fuel readFuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .reference name (.local binder))
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (lowerPolicy : policy.lowerRead source scope id (reasonAt id) =
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values source scope id (reasonAt id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel context source scope id reasonAt = .ok lowered) :
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type) ∧
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values source scope id (reasonAt id) = .ok lowered.expression := by
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, form,
        readPolicy, bind, Except.bind, pure, Except.pure] at accepted
      have bypass := special (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel) context
          childSource childScope childId childReasonAt) (fuel + 1)
      cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
      all_goals
        try rw [bypass] at accepted
      all_goals
        cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
        | error error => simp [read] at accepted
        | ok pair =>
          obtain ⟨other, type⟩ := pair
          have metadata := metadata_of_read read
          have same := Option.some.inj (metadata.found.symm.trans found)
          subst other
          simp only [read, form, lowerPolicy] at accepted
          cases generated : SourceCoreCompatibleDataExpressions.lowerRead readFuel values source scope id (reasonAt id) with
          | error error => simp [generated] at accepted
          | ok code =>
            simp only [generated, Except.ok.injEq] at accepted
            subst lowered
            exact ⟨rfl, rfl⟩
    · simp [owner, bind, Except.bind] at accepted

private theorem bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The actual contextual traversal supplies both low-level read receipts.
An ordinary occurrence is outside the generalized binder/initializer catalogs;
its retained requirement and coercion spines are empty. These are static
metadata conditions, with no source or Core child execution premise. -/
theorem contextual_read_receipts
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .reference name (.local binder))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : locals.bindings.any (fun binding => decide (binding.caller = context.owner ∧ binding.binder.id = binder)) = false)
    (notInitializer : locals.bindings.find? (fun binding => decide (binding.caller = context.owner ∧ binding.initializer = id)) = none)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type) ∧
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values source scope id (reasonAt id) = .ok lowered.expression := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine functions_read_receipts (values := values) (readFuel := readFuel) found form ?_ ?_ ?_ accepted
      · intro child budget
        dsimp only
        rw [contextualSource_ordinary program context.plan locals context.owner (some prepared) found form ordinary]
        simp only [found, notInitializer, Option.filter]
        rw [evidence_ordinary program _ prepared.caller context child budget scope reasonAt _ found form requirements coercions]
        simp only [form, ordinary, Bool.false_eq_true, ↓reduceIte]
      · change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner (some prepared) source id
          representation.expressions.readExpression viewed id) = _
        rw [contextualSource_ordinary program context.plan locals context.owner (some prepared) found form ordinary]
        simp only [bind, Except.bind, readPolicy]
      · exact congrFun (congrFun (congrFun (congrFun lowerPolicy source) scope) id) (reasonAt id)
    | none =>
      dsimp only at accepted
      obtain ⟨caller, selected, generated⟩ := bind_accepted accepted
      refine functions_read_receipts (values := values) (readFuel := readFuel) found form ?_ ?_ ?_ generated
      · intro child budget
        dsimp only
        rw [contextualSource_ordinary program context.plan locals context.owner none found form ordinary]
        simp only [bind, Except.bind, pure, Except.pure, found, notInitializer, Option.filter]
        rw [evidence_ordinary program _ caller context child budget scope reasonAt _ found form requirements coercions]
        simp only [form, ordinary, Bool.false_eq_true, ↓reduceIte]
      · change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner none source id
          representation.expressions.readExpression viewed id) = _
        rw [contextualSource_ordinary program context.plan locals context.owner none found form ordinary]
        simp only [bind, Except.bind, readPolicy]
      · exact congrFun (congrFun (congrFun (congrFun lowerPolicy source) scope) id) (reasonAt id)

/-- Real contextual compiler success supplies the certificate consumed by the
universal read preservation/reflection theorems. Source typing and lexical scope
alignment remain explicit; no child semantic induction hypothesis is needed. -/
theorem loweredRead_of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {binder : Resolved.LocalId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .reference name (.local binder))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : locals.bindings.any (fun binding => decide (binding.caller = context.owner ∧ binding.binder.id = binder)) = false)
    (notInitializer : locals.bindings.find? (fun binding => decide (binding.caller = context.owner ∧ binding.initializer = id)) = none)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered)
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id node.type) :
    LoweredRead readFuel values source sourceContext reasonAt scope id lowered := by
  obtain ⟨read, generated⟩ := contextual_read_receipts found form requirements coercions ordinary notInitializer
    readPolicy lowerPolicy accepted
  exact loweredRead_of_accepted generated read unique declarations typed

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualProxies
/-! The production contextual dispatcher preserves an ordinary proxy occurrence
unchanged. Empty requirements/coercions and the absence of a specialized local
initializer exclude its actual overrides; both root and full parent contexts
then yield the same authenticated proxy leaf certificate. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxies
open Core Frontend SourceInference

private theorem source_view
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    {node : ExpressionNode} {inner : TypeSystem.Ty}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem evidence_bypass (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {inner : TypeSystem.Ty}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    rfl
  simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinary, requirements, coercions,
    bind, Except.bind, pure, Except.pure]

/-- Real contextual lowering supplies every proxy metadata and layout receipt.
The typed source's raw inner type is retained even when its runtime identity
normalizes staging annotations. No whole-program or source-history claim is made. -/
theorem certificate_of_contextual
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {context : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel : Nat} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode} {inner : TypeSystem.Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (notInitializer : locals.bindings.find?
      (fun binding => decide (binding.caller = context.owner ∧ binding.initializer = id)) = none)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression program representation signatures locals parents assignments
      diagnostics context native parent skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Certificate values source scope id lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    cases parent with
    | some prepared =>
      dsimp only at accepted
      simp only [bind, Except.bind, pure, Except.pure] at accepted
      refine certificate_of_functions found form ?_ ?_ ?_ accepted
      · intro child budget
        dsimp only
        rw [source_view program context.plan locals context.owner (some prepared) found form]
        simp only [found, notInitializer, Option.filter]
        rw [evidence_bypass program _ prepared.caller context child budget scope reasonAt _ found form requirements coercions]
        simp only [form]
      · change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner (some prepared) source id
          representation.expressions.readExpression viewed id) = _
        rw [source_view program context.plan locals context.owner (some prepared) found form]
        simp only [bind, Except.bind, readPolicy]
      · exact leafPolicy
    | none =>
      dsimp only at accepted
      obtain ⟨caller, selected, generated⟩ := CompatibleEncoding.bind_ok accepted
      refine certificate_of_functions found form ?_ ?_ ?_ generated
      · intro child budget
        dsimp only
        rw [source_view program context.plan locals context.owner none found form]
        simp only [bind, Except.bind, pure, Except.pure, found, notInitializer, Option.filter]
        rw [evidence_bypass program _ caller context child budget scope reasonAt _ found form requirements coercions]
        simp only [form]
      · change (do
          let viewed ← SourceCoreGeneralFunctions.contextualSource program context.plan locals context.owner none source id
          representation.expressions.readExpression viewed id) = _
        rw [source_view program context.plan locals context.owner none found form]
        simp only [bind, Except.bind, readPolicy]
      · exact leafPolicy

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxies
end

import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.PrimitiveExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.Frontend.SourceCore.Lowering

/-!
# Compatible expressions: primitives and products

Primitive values, operations, execution and meaning, and products.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductMeaning
/-! Whole finite product trees discharge the universal child interfaces.
The existing argument sequence theorem inserts actual payload slots and
composes heap/world/admin preservation. Its child obligations are proved here
by structural induction, rather than supplied by the final caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : Scope}

/-- Static leaf support indexes the existing tree and its exact children.
It contains only leaf membership, with no execution or heap law. -/
inductive Tree.LiteralSites (literals : GenericExpressionMeaning.Certificate) :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Tree fuel values source context solved reasonAt scope id lowered → Prop where
  | literal {id lowered} (receipt : CompatibleExpressionLiterals.Certificate solved source id lowered)
      (leaf : literals scope id lowered) :
      LiteralSites literals (Tree.literal (scope := scope) receipt)
  | read {id lowered} (receipt : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id lowered)
      :
      LiteralSites literals (Tree.read (scope := scope) receipt)
  | group {id node inner innerNode lowered}
      (metadata : Metadata values.checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Tree fuel values source context solved reasonAt scope inner lowered)
      (childSites : Tree.LiteralSites literals child) :
      LiteralSites literals (Tree.group (scope := scope) metadata form innerFound sourceType child)
  | pair {id node left right leftNode rightNode first second}
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (sourceType : node.type = .product leftNode.type rightNode.type)
      (firstTree : Tree fuel values source context solved reasonAt scope left first)
      (secondTree : Tree fuel values source context solved reasonAt scope right second)
      (firstTreeSites : Tree.LiteralSites literals firstTree) (secondTreeSites : Tree.LiteralSites literals secondTree) :
      LiteralSites literals (Tree.pair (scope := scope) metadata form leftFound rightFound sourceType firstTree secondTree)

/-- The exact old tree restricted to the supplied static leaf certificates. -/
def Tree.WithLiterals (literals : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun current id lowered => ∃ tree : Tree fuel values source context solved reasonAt current id lowered,
    tree.LiteralSites literals

/-- Ordinary literal membership supplies support for every original tree. -/
theorem Tree.literalSites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree fuel values source context solved reasonAt scope id lowered) :
    tree.LiteralSites (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code) := by
  induction tree with
  | literal receipt => exact .literal receipt receipt
  | read receipt => exact .read receipt
  | group metadata form innerFound sourceType child childIH => exact .group metadata form innerFound sourceType child childIH
  | pair metadata form leftFound rightFound sourceType firstTree secondTree firstTreeIH secondTreeIH => exact .pair metadata form leftFound rightFound sourceType firstTree secondTree firstTreeIH secondTreeIH

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
    ∃ outcome, PacksOutcome sequence outcome ∧
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
theorem preserves_with_literals_and_post [FunctionCalls.FaultTokens faults]
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
  | literal receipt leaf =>
    exact literalMeaning leaf
  | read receipt =>
    exact readMeaning receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ outcome after
      environments heaps locals agrees trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      ih innerFound environments heaps locals agrees (group_inv metadata form unique trace)
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
      ExpressionFailurePostContracts.OutcomePost.expression ordinaryJoins
        (.group (lookupExpression?_sound metadata.found) form
          (ScalarExpressionFaultPostContracts.ordinary_layout metadata)) (group_inv metadata form unique trace) retained⟩
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
    obtain ⟨sequence, sourceTrace, packed⟩ := pair_inv metadata form unique trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      (two_tree (first := first) (second := second) leftFound rightFound).preserves_with_post sequenceJoins children environments heaps locals agrees sourceTrace
    obtain ⟨actualOutcome, actualPack, payload⟩ := pair_result represented
    have sameOutcome := actualPack.functional packed
    subst actualOutcome
    refine ⟨value, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
      ScalarExpressionFaultPostContracts.tuple_outcome ordinaryJoins metadata form sourceTrace packed retained⟩
    simpa only [sourceType] using payload

theorem reflects_with_literals_and_post [FunctionCalls.FaultTokens faults]
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
  | literal receipt leaf =>
    exact literalMeaning leaf
  | read receipt =>
    exact readMeaning receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
    intro root found mapping world administrative environment canonical actual before store ξ value finalStore
      environments heaps locals agrees evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, retained⟩ :=
      ih innerFound environments heaps locals agrees evaluated
    refine ⟨outcome, after, finalMap, finalWorld, group_intro metadata form trace, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
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
    refine ⟨outcome, after, finalMap, finalWorld, pair_intro metadata form sourceTrace packed, ?_, finalHeaps, maps, worlds, frame, heapMetadata,
      ScalarExpressionFaultPostContracts.tuple_outcome ordinaryJoins metadata form sourceTrace packed retained⟩
    simpa only [sourceType] using payload

include extension unique uninitialized in
/-- Every independent completed source execution is preserved for the entire
certified tree. There is no external child semantic hypothesis. -/
theorem preserves_with_literals [FunctionCalls.FaultTokens faults]
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
theorem preserves [FunctionCalls.FaultTokens faults] :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact preserves_with_literals functions extension program evidence unique uninitialized
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults) ⟨tree, tree.literalSites⟩


include extension uninitialized in
/-- Every native completion reconstructs the independent source execution of
the whole tree, including a fault after an effectful successful left prefix. -/
theorem reflects_with_literals [FunctionCalls.FaultTokens faults]
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
theorem reflects [FunctionCalls.FaultTokens faults] :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact reflects_with_literals functions extension program evidence uninitialized
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults) ⟨tree, tree.literalSites⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues
/-! Scalar inversion for the compatible payload relation and the exact pure
primitive bodies emitted by the ordinary compiler. Function authentication is
not an additional premise: its projected product carrier cannot be a scalar.
All typing refers to the actual ambient definitions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference GeneralHeap CompatiblePayload

private def ScalarFields (source : Dynamic.Value) (value : Value) : Ty → Prop
  | .bool => ∃ boolean, source = .bool boolean ∧ value = .bool boolean
  | .word => ∃ word, source = .word word ∧ value = .word word
  | .integer => ∃ integer, source = .integer integer ∧ value = .integer integer
  | _ => True

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
  {source : Dynamic.Value} {value : Value} {type : Ty}

private theorem scalar_fields (represented : ValueRep checked registry functions mapping world sourceType source value type) :
    ScalarFields source value type := by
  induction represented using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | product | proxy | constructed | mappingValue => trivial
  | bool boolean => exact ⟨boolean, rfl, rfl⟩
  | word word => exact ⟨word, rfl, rfl⟩
  | fixed word => exact ⟨word, rfl, rfl⟩
  | integer integer => exact ⟨integer, rfl, rfl⟩
  | @function parameter result source value type related =>
    have projected := functions.projection related
    simp only [SourceCoreCompatibleCatalog.Catalog.project] at projected
    cases parameterEq : checked.catalog.project parameter with
    | error error => simp [parameterEq, bind, Except.bind] at projected
    | ok parameter =>
      cases resultEq : checked.catalog.project result with
      | error error => simp [parameterEq, resultEq, bind, Except.bind] at projected
      | ok result =>
        simp only [parameterEq, resultEq, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at projected
        subst type
        unfold SourceCoreCompatibleCatalog.Catalog.functionType
        split <;> trivial
  | compatible _ _ ih => exact ih
  | nil | cons | empty | entry | absent | present => trivial

theorem bool_fields (represented : ValueRep checked registry functions mapping world sourceType source value .bool) :
    ∃ boolean, source = .bool boolean ∧ value = .bool boolean := scalar_fields represented

theorem word_fields (represented : ValueRep checked registry functions mapping world sourceType source value .word) :
    ∃ word, source = .word word ∧ value = .word word := scalar_fields represented

theorem integer_fields (represented : ValueRep checked registry functions mapping world sourceType source value .integer) :
    ∃ integer, source = .integer integer ∧ value = .integer integer := scalar_fields represented

/-- Empty evidence admits exactly these scalar unary profiles. -/
inductive UnaryProfile : Syntax.UnaryOp → TypeSystem.Ty → TypeSystem.Ty → UnaryOp → Prop where
  | logicalNot : UnaryProfile .logicalNot .bool .bool .boolNot
  | wordNot : UnaryProfile .bitNot .word .word .wordNot
  | integerNot : UnaryProfile .bitNot .integer .integer .integerNot

theorem UnaryProfile.of_typing {context : SourceSemantics.Context} {operator : Syntax.UnaryOp}
    {operand result : TypeSystem.Ty} (typed : UnaryOperatorHasType context operator operand result []) :
    ∃ core, UnaryProfile operator operand result core := by
  cases typed with
  | logicalNot => exact ⟨_, .logicalNot⟩
  | wordBitNot => exact ⟨_, .wordNot⟩
  | integerBitNot => exact ⟨_, .integerNot⟩
  | trait _ profile evidence => cases profile; cases evidence

theorem UnaryProfile.preserves {operator : Syntax.UnaryOp} {operand result : TypeSystem.Ty} {core : UnaryOp}
    (profile : UnaryProfile operator operand result core)
    (represented : ValueRep checked registry functions mapping world operand source value core.operandType) :
    ∃ sourceResult coreResult,
      Dynamic.UnaryPrimitiveApplies operator source sourceResult ∧ core.apply value = some coreResult ∧
      ValueRep checked registry functions mapping world result sourceResult coreResult core.resultType := by
  cases profile with
  | logicalNot =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    exact ⟨_, _, .logicalNot boolean, rfl, .bool _⟩
  | wordNot =>
    obtain ⟨word, rfl, rfl⟩ := word_fields represented
    exact ⟨_, _, .wordBitNot word, rfl, .word _⟩
  | integerNot =>
    obtain ⟨integer, rfl, rfl⟩ := integer_fields represented
    exact ⟨_, _, .integerBitNot integer, rfl, .integer _⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveOperations
/-! Actual Word/Integer compiler bodies agree with independent scalar source
operations. Reversed comparisons reorder already evaluated values only. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference GeneralHeap CompatiblePayload

inductive Mode where
  | word
  | integer
  deriving DecidableEq

def Mode.operandType (mode : Mode) (operator : Syntax.BinaryOp) : Ty :=
  match mode with
  | .word => SourceCorePrimitive.binaryOperandType operator
  | .integer => SourceCoreInteger.binaryOperandType operator

def Mode.resultType (mode : Mode) (operator : Syntax.BinaryOp) : Ty :=
  match mode with
  | .word => SourceCorePrimitive.binaryResultType operator
  | .integer => SourceCoreInteger.binaryResultType operator

def Mode.body (mode : Mode) (operator : Syntax.BinaryOp) : Expr :=
  match mode with
  | .word => SourceCorePrimitive.strictBinaryBody operator
  | .integer => SourceCoreInteger.strictBinaryBody operator

def Mode.binary (mode : Mode) (operator : Syntax.BinaryOp) (left right : Expr) : Expr :=
  match mode with
  | .word => SourceCorePrimitive.binary operator left right
  | .integer => SourceCoreInteger.binary operator left right

def scalarSource : Ty → TypeSystem.Ty
  | .bool => .bool
  | .word => .word
  | .integer => .integer
  | _ => .unit

inductive BinaryProfile : Syntax.BinaryOp → TypeSystem.Ty → TypeSystem.Ty → Mode → Prop where
  | word {operator} (strict : Dynamic.StrictBinaryOperator operator) :
      BinaryProfile operator .word (scalarSource (SourceCorePrimitive.binaryResultType operator)) .word
  | integer {operator} (strict : Dynamic.IntegerStrictBinaryOperator operator) :
      BinaryProfile operator .integer (scalarSource (SourceCoreInteger.binaryResultType operator)) .integer
  /-- Unchecked `/` and `%` on Words, which panic on a zero divisor. -/
  | panicking {operator} (panicking : Dynamic.PanickingBinaryOperator operator) :
      BinaryProfile operator .word .word .word
  | logicalAnd : BinaryProfile .logicalAnd .bool .bool .word
  | logicalOr : BinaryProfile .logicalOr .bool .bool .word

theorem BinaryProfile.of_typing {context : SourceSemantics.Context} {operator : Syntax.BinaryOp}
    {operand result : TypeSystem.Ty} (typed : BinaryOperatorHasType context operator operand operand result []) :
    ∃ mode, BinaryProfile operator operand result mode := by
  cases typed with
  | wordArithmetic kind => cases kind <;> exact ⟨_, .word (by constructor)⟩
  | wordComparison kind => cases kind <;> exact ⟨_, .word (by constructor)⟩
  | wordShift kind => cases kind <;> exact ⟨_, .word (by constructor)⟩
  | wordUnchecked kind =>
    cases kind <;> first | exact ⟨_, .word (by constructor)⟩ | exact ⟨_, .panicking (by constructor)⟩
  | integerArithmetic kind => cases kind <;> exact ⟨_, .integer (by constructor)⟩
  | integerComparison kind => cases kind <;> exact ⟨_, .integer (by constructor)⟩
  | booleanAnd => exact ⟨_, .logicalAnd⟩
  | booleanOr => exact ⟨_, .logicalOr⟩
  | trait _ profile evidence => cases profile; cases evidence

theorem Mode.binary_strict {operator : Syntax.BinaryOp} (mode : Mode)
    (strict : Dynamic.StrictBinaryOperator operator) (left right : Expr) :
    mode.binary operator left right = LocalPrimitiveResults.binaryWith
      (mode.resultType operator) left right (mode.body operator) := by
  cases mode <;> cases strict <;> rfl

theorem Mode.body_rename (mode : Mode) (operator : Syntax.BinaryOp) (ξ : Renaming) :
    (mode.body operator).rename (Renaming.lift (Renaming.lift ξ)) = mode.body operator := by
  cases mode <;> cases operator <;> rfl

private theorem not_lt (left right : Int) :
    (!decide (left < right)) = decide (right ≤ left) := by
  rw [← decide_not]
  exact decide_eq_decide.mpr Int.not_lt

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

private theorem staged_payload (value : SourceStagedValue.Value) :
    ValueRep checked registry functions mapping world (SourceStagedValue.sourceType value)
      (StagedValue.toSource value) (SourceStagedValue.toCore value) (SourceStagedValue.coreType value) := by
  induction value with
  | unit => exact .unit
  | bool value => exact .bool value
  | word value => exact .word value
  | product _ _ first second => exact .product first second

private theorem staged_scalar_result {operator : Syntax.BinaryOp} {value : SourceStagedValue.Value}
    (typed : SourceStagedValue.coreType value = SourceCorePrimitive.binaryResultType operator) :
    SourceStagedValue.sourceType value = scalarSource (SourceCorePrimitive.binaryResultType operator) := by
  cases operator <;> cases value <;> simp_all [SourceStagedValue.coreType, SourceStagedValue.sourceType,
    SourceCorePrimitive.binaryResultType, scalarSource]

theorem word_body {operator : Syntax.BinaryOp} (strict : Dynamic.StrictBinaryOperator operator) (left right : Word) :
    ∃ sourceResult coreResult,
      Dynamic.BinaryPrimitiveApplies operator (.word left) (.word right) sourceResult ∧
      ValueRep checked registry functions mapping world (scalarSource (SourceCorePrimitive.binaryResultType operator))
        sourceResult coreResult (SourceCorePrimitive.binaryResultType operator) ∧
      ∀ environment store, Evaluates (.word right :: .word left :: environment) store
        (SourceCorePrimitive.strictBinaryBody operator) coreResult store := by
  obtain ⟨result, typed, applied, evaluated⟩ := PrimitiveExpressions.strict_binary_value strict left right
  refine ⟨_, _, applied, ?_, evaluated⟩
  simpa only [typed, staged_scalar_result typed] using (staged_payload (functions := functions) (registry := registry)
    (mapping := mapping) (world := world) result)

theorem integer_body {operator : Syntax.BinaryOp} (strict : Dynamic.IntegerStrictBinaryOperator operator) (left right : Int) :
    ∃ sourceResult coreResult,
      Dynamic.BinaryPrimitiveApplies operator (.integer left) (.integer right) sourceResult ∧
      ValueRep checked registry functions mapping world (scalarSource (SourceCoreInteger.binaryResultType operator))
        sourceResult coreResult (SourceCoreInteger.binaryResultType operator) ∧
      ∀ environment store, Evaluates (.integer right :: .integer left :: environment) store
        (SourceCoreInteger.strictBinaryBody operator) coreResult store := by
  cases strict with
  | multiply => exact ⟨_, _, .integerMultiply _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | divide => exact ⟨_, _, IntegerPrimitives.divide_source _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | modulo => exact ⟨_, _, IntegerPrimitives.modulo_source _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | add => exact ⟨_, _, .integerAdd _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | subtract => exact ⟨_, _, .integerSubtract _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | bitAnd => exact ⟨_, _, IntegerPrimitives.bitAnd_source _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | bitXor => exact ⟨_, _, IntegerPrimitives.bitXor_source _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | bitOr => exact ⟨_, _, IntegerPrimitives.bitOr_source _ _, .integer _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | less => exact ⟨_, _, .integerLess _ _, .bool _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | greater => exact ⟨_, _, .integerGreater _ _, .bool _, fun _ _ => .binary (.var rfl) (.var rfl) rfl⟩
  | lessEqual =>
    refine ⟨_, _, .integerLessEqual _ _, .bool _, fun _ _ => .unary (.binary (.var rfl) (.var rfl) rfl) ?_⟩
    simp [UnaryOp.apply, not_lt]
  | greaterEqual =>
    refine ⟨_, _, .integerGreaterEqual _ _, .bool _, fun _ _ => .unary (.binary (.var rfl) (.var rfl) rfl) ?_⟩
    simp [UnaryOp.apply, not_lt]
  | equal =>
    by_cases same : left = right
    · subst right
      exact ⟨_, _, .equalTrue ⟨rfl, .integer _⟩, .bool true,
        fun _ _ => .binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply])⟩
    · exact ⟨_, _, .equalFalse (fun equivalent => same (Dynamic.Value.integer.inj equivalent.1)), .bool false,
        fun _ _ => .binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, beq_eq_false_iff_ne.mpr same])⟩
  | notEqual =>
    by_cases same : left = right
    · subst right
      exact ⟨_, _, .notEqualFalse ⟨rfl, .integer _⟩, .bool false,
        fun _ _ => .unary (.binary (result := .bool true) (.var rfl) (.var rfl) (by simp [BinaryOp.apply])) rfl⟩
    · exact ⟨_, _, .notEqualTrue (fun equivalent => same (Dynamic.Value.integer.inj equivalent.1)), .bool true,
        fun _ _ => .unary (.binary (result := .bool false) (.var rfl) (.var rfl)
          (by simp [BinaryOp.apply, beq_eq_false_iff_ne.mpr same])) rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveSource
/-! Independent source decomposition for empty-evidence primitive nodes.
Faulting operands and invalid operations are distinguished before the scalar
representation proof excludes the invalid-operation alternatives. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference
abbrev Metadata := CompatibleExpressionReads.Metadata

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

theorem evaluation_raw
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

theorem fault_raw
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

theorem no_owned {owned : List RequirementId}
    (layout : Dynamic.OrdinaryRequirementLayout [] [] owned) : owned = [] := by
  simpa [Dynamic.OrdinaryRequirementLayout, coercionRequirementIds] using layout.symm

inductive UnaryTrace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (operand : ExpressionId) (operator : Syntax.UnaryOp) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {input output after}
      (child : Dynamic.ExpressionEvaluates program context evidence source environment before operand input after)
      (applies : Dynamic.UnaryPrimitiveApplies operator input output) : UnaryTrace program context evidence source environment before operand operator (.value output) after
  | fault {reason after}
      (child : Dynamic.ExpressionFaults program context evidence source environment before operand reason after) :
      UnaryTrace program context evidence source environment before operand operator (.fault reason) after
  | invalid {input reason middle after}
      (child : Dynamic.ExpressionEvaluates program context evidence source environment before operand input middle)
      (fault : Dynamic.UnaryOperationFaults program context evidence middle operator [] input reason after) :
      UnaryTrace program context evidence source environment before operand operator (.fault reason) after

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome} {operator : Syntax.UnaryOp} {operand : ExpressionId}

theorem unary_inv (metadata : Metadata checked source id node type)
    (form : node.form = .unary operator operand) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    UnaryTrace program context evidence source environment before operand operator outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | unary layout child applies =>
      have empty := no_owned layout
      subst empty
      cases applies with
      | primitive applied => exact .value child applied
      | method _ selected _ => cases selected
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | unaryOperand _ child => exact .fault child
    | unaryApply layout child failed =>
      have empty := no_owned layout
      subst empty
      exact .invalid child failed

theorem unary_intro (metadata : Metadata checked source id node type)
    (form : node.form = .unary operator operand)
    (trace : UnaryTrace program context evidence source environment before operand operator outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | value child applied =>
    apply Dynamic.ExpressionEvaluatesOutcome.value
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]; exact .unary (owned := []) rfl child (.primitive applied)
    · rw [metadata.coercions]; exact .nil
  | fault child =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .unaryOperand (owned := []) rfl child
  | invalid child failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .unaryApply (owned := []) rfl child failed

theorem unary_fault_excluded {input output : Dynamic.Value} {reason : Dynamic.SemanticFault}
    (applied : Dynamic.UnaryPrimitiveApplies operator input output)
    (fault : Dynamic.UnaryOperationFaults program context evidence before operator [] input reason after) : False := by
  cases fault with
  | primitive invalid => exact invalid.excludes_application ⟨output, applied⟩
  | requirement failed => cases failed
  | method _ selected _ => cases selected


inductive BinaryTrace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (left right : ExpressionId) (operator : Syntax.BinaryOp) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | leftFault {reason after}
      (child : Dynamic.ExpressionFaults program context evidence source environment before left reason after) :
      BinaryTrace program context evidence source environment before left right operator (.fault reason) after
  | leftInvalid {input after}
      (child : Dynamic.ExpressionEvaluates program context evidence source environment before left input after)
      (invalid : Dynamic.BinaryLeftOperandInvalid operator input) :
      BinaryTrace program context evidence source environment before left right operator (.fault (.invalidBinaryOperands operator)) after
  | short {input output after}
      (child : Dynamic.ExpressionEvaluates program context evidence source environment before left input after)
      (circuit : Dynamic.ShortCircuits operator input output) :
      BinaryTrace program context evidence source environment before left right operator (.value output) after
  | rightFault {input reason middle after}
      (first : Dynamic.ExpressionEvaluates program context evidence source environment before left input middle)
      (continues : Dynamic.EvaluatesRightOperand operator input)
      (second : Dynamic.ExpressionFaults program context evidence source environment middle right reason after) :
      BinaryTrace program context evidence source environment before left right operator (.fault reason) after
  | value {a b output middle after}
      (first : Dynamic.ExpressionEvaluates program context evidence source environment before left a middle)
      (continues : Dynamic.EvaluatesRightOperand operator a)
      (second : Dynamic.ExpressionEvaluates program context evidence source environment middle right b after)
      (applies : Dynamic.BinaryPrimitiveApplies operator a b output) :
      BinaryTrace program context evidence source environment before left right operator (.value output) after
  | invalid {a b reason middle operated after}
      (first : Dynamic.ExpressionEvaluates program context evidence source environment before left a middle)
      (continues : Dynamic.EvaluatesRightOperand operator a)
      (second : Dynamic.ExpressionEvaluates program context evidence source environment middle right b operated)
      (failed : Dynamic.BinaryOperationFaults program context evidence operated operator [] a b reason after) :
      BinaryTrace program context evidence source environment before left right operator (.fault reason) after

theorem binary_inv {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (metadata : Metadata checked source id node type)
    (form : node.form = .binary left operator right) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    BinaryTrace program context evidence source environment before left right operator outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | binaryShortCircuit _ child circuit _ => exact .short child circuit
    | binaryEvaluateRight layout first continues second applies =>
      have empty := no_owned layout
      subst empty
      cases applies with
      | primitive applied => exact .value first continues second applied
      | method _ selected _ => cases selected
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | binaryLeft _ child => exact .leftFault child
    | binaryLeftOperand _ child invalid => exact .leftInvalid child invalid
    | binaryRight _ first continues second => exact .rightFault first continues second
    | binaryApply layout first continues second failed =>
      have empty := no_owned layout
      subst empty
      exact .invalid first continues second failed

theorem binary_intro {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (metadata : Metadata checked source id node type) (form : node.form = .binary left operator right)
    (trace : BinaryTrace program context evidence source environment before left right operator outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | short child circuit =>
    apply Dynamic.ExpressionEvaluatesOutcome.value
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]; exact .binaryShortCircuit (owned := []) rfl child circuit rfl
    · rw [metadata.coercions]; exact .nil
  | value first continues second applied =>
    apply Dynamic.ExpressionEvaluatesOutcome.value
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]
      exact .binaryEvaluateRight (owned := []) rfl first continues second (.primitive applied)
    · rw [metadata.coercions]; exact .nil
  | leftFault child =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .binaryLeft (owned := []) rfl child
  | leftInvalid child invalid =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .binaryLeftOperand (owned := []) rfl child invalid
  | rightFault first continues second =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .binaryRight (owned := []) rfl first continues second
  | invalid first continues second failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .binaryApply (owned := []) rfl first continues second failed

theorem binary_fault_excluded {operator : Syntax.BinaryOp} {left right output : Dynamic.Value} {reason : Dynamic.SemanticFault}
    (applied : Dynamic.BinaryPrimitiveApplies operator left right output)
    (fault : Dynamic.BinaryOperationFaults program context evidence before operator [] left right reason after) : False := by
  cases fault with
  | primitive invalid => exact invalid.excludes_application ⟨output, applied⟩
  | panic panics => exact panics.excludes_application applied
  | requirement failed => cases failed
  | method _ selected _ => cases selected

/-- A fault of an operation that panics is that panic. -/
theorem binary_fault_panic {operator : Syntax.BinaryOp} {left right : Dynamic.Value} {code : UInt8}
    {reason : Dynamic.SemanticFault}
    (panics : Dynamic.BinaryPrimitivePanics operator left right code)
    (fault : Dynamic.BinaryOperationFaults program context evidence before operator [] left right reason after) :
    reason = .panic code ∧ after = before := by
  cases fault with
  | primitive invalid => exact (invalid.excludes_panic panics).elim
  | panic other => exact ⟨by rw [panics.functional other], rfl⟩
  | requirement failed => cases failed
  | method _ selected _ => cases selected

/-- A primitive panic of a binary node, as its source fault. -/
theorem binary_panic_fault {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (metadata : Metadata checked source id node type) (form : node.form = .binary left operator right)
    {a b : Dynamic.Value} {middle operated : Dynamic.Heap} {code : UInt8}
    (first : Dynamic.ExpressionEvaluates program context evidence source environment before left a middle)
    (continues : Dynamic.EvaluatesRightOperand operator a)
    (second : Dynamic.ExpressionEvaluates program context evidence source environment middle right b operated)
    (panics : Dynamic.BinaryPrimitivePanics operator a b code) :
    Dynamic.ExpressionFaults program context evidence source environment before id (.panic code) operated := by
  apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
  rw [form, metadata.requirements, metadata.coercions]
  exact .binaryApply (owned := []) rfl first continues second (.panic panics)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductCertificates
/-! Actual shared compiler receipts for the finite product fragment. Source
product and group types come from independent typing. Successful child compiler
results are eliminated by the structural extraction induction. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
open Core Frontend SourceInference

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

private inductive Compound : ExpressionForm → Prop where
  | read (name : String) (binder : Resolved.LocalId) : Compound (.reference name (.local binder))
  | group (inner : ExpressionId) : Compound (.group inner)
  | pair (left right : ExpressionId) : Compound (.tuple [left, right])

private inductive Step (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel readFuel : Nat) (context : SourceCoreFunctions.Context) (values : ValuesContext)
    (source : TypedSource) (scope : Scope) (reasonAt : ExpressionId → Word)
    (id : ExpressionId) (node : ExpressionNode) : SourceCoreBasic.LoweredExpr → Prop where
  | read {name binder lowered}
      (form : node.form = .reference name (.local binder))
      (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
      (generated : SourceCoreCompatibleDataExpressions.lowerRead readFuel values source scope id (reasonAt id) = .ok lowered.expression) :
      Step policy body fuel readFuel context values source scope reasonAt id node lowered
  | group {inner lowered}
      (form : node.form = .group inner) (metadata : Metadata values.checked source id node lowered.type)
      (generated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope inner reasonAt = .ok lowered) :
      Step policy body fuel readFuel context values source scope reasonAt id node lowered
  | pair {left right first second}
      (form : node.form = .tuple [left, right])
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (firstGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope left reasonAt = .ok first)
      (secondGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope right reasonAt = .ok second) :
      Step policy body fuel readFuel context values source scope reasonAt id node
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩

private theorem step_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (compound : Compound node.form)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (lowerPolicy : policy.lowerRead source scope id (reasonAt id) =
      SourceCoreCompatibleDataExpressions.lowerRead readFuel values source scope id (reasonAt id))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) context source scope id reasonAt = .ok lowered) :
    Step policy body fuel readFuel context values source scope reasonAt id node lowered := by
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
        simp only [read, form, lowerPolicy] at accepted
        first
        | obtain ⟨code, generated, outputEq⟩ := bind_accepted accepted
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .read form read generated
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
  · simp [owner, bind, Except.bind] at accepted

/-- The only extra literal raw-type fact follows from the independent empty
source tuple typing rule, including the empty output coercion path. -/
private theorem unit_source_type {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (coercions : node.coercions = []) (typed : ExpressionHasType source context id node.type)
    (form : node.form = .tuple []) : node.type = .unit := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := requirements.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize rawTypeEq : node.type = rawType at raw
    cases raw with
    | tuple elements => cases elements; rfl

/-- The metadata conditions are about syntax and actual policy results. They
contain no source evaluation, Core evaluation, or desired semantic tree. -/
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

/-- Policy facts are needed only at occurrences admitted by the enclosing
body. The closed set is supplied independently of compiler execution. -/
structure PolicyOn (policy : SourceCoreFunctions.Policy) (context : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource) (scope : Scope)
    (reasonAt : ExpressionId → Word) (allowed : ExpressionId → Prop) : Prop where
  special : ∀ id, allowed id → Syntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower context child budget source scope id reasonAt) = .ok none
  read : ∀ id, allowed id → Syntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

/-- Existing global profiles supply every restricted profile. -/
theorem PolicyFor.on {policy : SourceCoreFunctions.Policy} {context : SourceCoreFunctions.Context}
    {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {reasonAt : ExpressionId → Word}
    (profile : PolicyFor policy context readFuel values source scope reasonAt)
    (allowed : ExpressionId → Prop) : PolicyOn policy context readFuel values source scope reasonAt allowed :=
  ⟨fun id _ tree => profile.special id tree, fun id _ tree => profile.read id tree, profile.lower, profile.leaf⟩

/- Actual successful compilation extracts the complete finite tree. The
source typing proof supplies raw group/product shape and ordinary local scheme
agreement; successful native projection is not used as a substitute. -/
/-- Static extraction at the exact accepted atomic compiler action. No runtime
law or assumption about unrelated source occurrences is a field. -/
def LiteralFactory (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (context : SourceCoreFunctions.Context) (values : ValuesContext) (source : TypedSource)
    (scope : Scope) (reasonAt : ExpressionId → Word)
    (literals : GenericExpressionMeaning.Certificate) : Prop :=
  ∀ {id node fuel lowered}, source.lookupExpression? id = some node →
    CompatibleExpressionLiterals.Atomic node.form → (node.form = .tuple [] → node.type = .unit) →
    (∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none) →
    policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id →
    policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values →
    SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered →
    CompatibleExpressionLiterals.Certificate context.solvedRequirements source id lowered ∧ literals scope id lowered

/-- The former ordinary extractor supplies both copies of the same leaf receipt. -/
theorem LiteralFactory.ordinary {policy body context values source scope reasonAt} :
    LiteralFactory policy body context values source scope reasonAt
      (fun _ id lowered => CompatibleExpressionLiterals.Certificate context.solvedRequirements source id lowered) := by
  intro id node fuel lowered found atomic unitType special readPolicy leafPolicy accepted
  have receipt := CompatibleExpressionLiterals.of_functions found atomic unitType special readPolicy leafPolicy accepted
  exact ⟨receipt, receipt⟩

theorem tree_of_functions_with_literals_on
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (literals : GenericExpressionMeaning.Certificate)
    (literalFactory : CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt literals)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    {allowed : ExpressionId → Prop}
    (policyFor : PolicyOn policy context readFuel values source scope reasonAt allowed)
    (closed : ∀ {parent node child}, allowed parent → source.lookupExpression? parent = some node →
      (.expression child : NodeId) ∈ node.form.references → allowed child)
    (coercions : ∀ id node, allowed id → Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) (admitted : allowed id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree.WithLiterals (fuel := readFuel) (values := values) (source := source)
      (context := sourceContext) (solved := context.solvedRequirements) (reasonAt := reasonAt) literals scope id lowered := by
  revert admitted
  induction syntaxTree generalizing node fuel lowered with
  | literal originalFound atomic =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    obtain ⟨receipt, leaf⟩ := literalFactory originalFound atomic
      (unit_source_type unique originalFound (coercions _ _ admitted (.literal originalFound atomic) originalFound) typed)
      (policyFor.special _ admitted (.literal originalFound atomic)) (policyFor.read _ admitted (.literal originalFound atomic)) policyFor.leaf accepted
    exact ⟨_, .literal receipt leaf⟩
  | read originalFound form =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ admitted (.read originalFound form)) (policyFor.read _ admitted (.read originalFound form))
        (congrFun (congrFun (congrFun (congrFun policyFor.lower source) scope) _) _) accepted
      cases step with
      | read otherForm read generated =>
        exact ⟨_, .read (CompatibleExpressionReads.loweredRead_of_accepted generated read unique declarations typed)⟩
      | group otherForm _ _ => simp [form] at otherForm
      | pair otherForm _ _ _ => simp [form] at otherForm
  | group originalFound form child ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ admitted (.group originalFound form child)) (policyFor.read _ admitted (.group originalFound form child))
        (congrFun (congrFun (congrFun (congrFun policyFor.lower source) scope) _) _) accepted
      cases step with
      | read otherForm _ _ => simp [form] at otherForm
      | group otherForm metadata generated =>
        have same := ExpressionForm.group.inj (form.symm.trans otherForm)
        subst_vars
        obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ := group_source_types unique originalFound form metadata.coercions typed
        obtain ⟨acceptedChild1, acceptedChild1Sites⟩ := ih innerFound childTyped generated (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        exact ⟨_, .group metadata form innerFound sourceType acceptedChild1 acceptedChild1Sites⟩
      | pair otherForm _ _ _ => simp [form] at otherForm
  | pair originalFound form first second leftIH rightIH =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ admitted (.pair originalFound form first second)) (policyFor.read _ admitted (.pair originalFound form first second))
        (congrFun (congrFun (congrFun (congrFun policyFor.lower source) scope) _) _) accepted
      cases step with
      | read otherForm _ _ => simp [form] at otherForm
      | group otherForm _ _ => simp [form] at otherForm
      | pair otherForm metadata generated secondGenerated =>
        have same := ExpressionForm.tuple.inj (form.symm.trans otherForm)
        simp only [List.cons.injEq, and_true] at same
        obtain ⟨rfl, rfl⟩ := same
        obtain ⟨leftNode, rightNode, leftFound, rightFound, sourceType, leftTyped, rightTyped⟩ :=
          pair_source_types unique originalFound form metadata.coercions typed
        obtain ⟨acceptedChild2, acceptedChild2Sites⟩ := leftIH leftFound leftTyped generated (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        obtain ⟨acceptedChild3, acceptedChild3Sites⟩ := rightIH rightFound rightTyped secondGenerated (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        exact ⟨_, .pair metadata form leftFound rightFound sourceType
          acceptedChild2 acceptedChild3 acceptedChild2Sites acceptedChild3Sites⟩

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
  exact tree_of_functions_with_literals_on literals literalFactory unique declarations
    (policyFor.on (fun _ => True)) (fun _ _ _ => trivial)
    (fun id node _ tree found => coercions id node tree found) syntaxTree trivial found typed accepted

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

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveTree
/-! Primitive trees contain static metadata and operator profiles only.
Product fragments retain their existing actual compiler certificates. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | product {id} (child : CompatibleExpressionProducts.Syntax source id) : Syntax source id
  | group {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .group inner) (child : Syntax source inner) : Syntax source id
  | pair {id node left right} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple [left, right]) (first : Syntax source left) (second : Syntax source right) : Syntax source id
  | unary {id node operand operator} (found : source.lookupExpression? id = some node)
      (form : node.form = .unary operator operand) (child : Syntax source operand) : Syntax source id
  | binary {id node left right operator} (found : source.lookupExpression? id = some node)
      (form : node.form = .binary left operator right)
      (first : Syntax source left) (second : Syntax source right) : Syntax source id

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | product {id lowered}
      (child : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered) :
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

private theorem contains_node {source : TypedSource} {id : ExpressionId} {node other : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (contains : ContainsExpression source id other) : other = node :=
  Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)

theorem unary_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id operand : ExpressionId} {node : ExpressionNode} {operator : Syntax.UnaryOp}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .unary operator operand) (coercions : node.coercions = [])
    (requirements : node.requirements = []) (typed : ExpressionHasType source context id node.type) :
    ∃ childNode core, source.lookupExpression? operand = some childNode ∧
      ExpressionHasType source context operand childNode.type ∧ UnaryProfile operator childNode.type node.type core := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := contains_node unique found contains
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw valid
    cases raw with
    | unary child operatorTyped =>
      cases valid with
      | ordinary _ _ layout =>
        rw [requirements, coercions] at layout
        simp only [coercionRequirementIds, List.flatMap_nil, List.append_nil] at layout
        rw [← layout] at operatorTyped
        obtain ⟨childNode, contains, typeEq⟩ := child.stored_type
        obtain ⟨core, profile⟩ := UnaryProfile.of_typing operatorTyped
        exact ⟨childNode, core, lookupExpression?_complete unique contains, typeEq ▸ child, typeEq ▸ (resultEq ▸ profile)⟩

theorem binary_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id left right : ExpressionId} {node : ExpressionNode} {operator : Syntax.BinaryOp}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .binary left operator right) (coercions : node.coercions = [])
    (requirements : node.requirements = []) (typed : ExpressionHasType source context id node.type) :
    ∃ leftNode rightNode mode, source.lookupExpression? left = some leftNode ∧
      source.lookupExpression? right = some rightNode ∧ leftNode.type = rightNode.type ∧
      ExpressionHasType source context left leftNode.type ∧ ExpressionHasType source context right rightNode.type ∧
      BinaryProfile operator leftNode.type node.type mode := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := contains_node unique found contains
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw valid
    cases raw with
    | binary first second operatorTyped =>
      cases valid with
      | ordinary _ _ layout =>
        rw [requirements, coercions] at layout
        simp only [coercionRequirementIds, List.flatMap_nil, List.append_nil] at layout
        rw [← layout] at operatorTyped
        obtain ⟨leftNode, leftContains, leftType⟩ := first.stored_type
        obtain ⟨rightNode, rightContains, rightType⟩ := second.stored_type
        obtain ⟨mode, profile⟩ := BinaryProfile.of_typing operatorTyped
        exact ⟨leftNode, rightNode, mode, lookupExpression?_complete unique leftContains,
          lookupExpression?_complete unique rightContains, leftType.trans rightType.symm,
          leftType ▸ first, rightType ▸ second, leftType ▸ (resultEq ▸ profile)⟩


private theorem product_projection {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | literal receipt =>
    obtain ⟨original, originalFound, literal⟩ := receipt
    have same := Option.some.inj (originalFound.symm.trans found)
    subst original
    rcases lowered with ⟨type, code⟩
    cases literal with
    | unit _ type | bool _ _ type | word _ _ type => rw [type]; rfl
    | resolvedWord _ metadata => rw [metadata.nodeType]; rfl
    | resolvedInteger _ metadata => rw [metadata.nodeType]; rfl
  | read receipt =>
    obtain ⟨certificate, typeEq, _⟩ := receipt
    have same := Option.some.inj (certificate.metadata.found.symm.trans found)
    rw [← same, ← typeEq]
    exact certificate.metadata.projected
  | group metadata _ _ _ _ | pair metadata _ _ _ _ _ _ =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    exact same ▸ metadata.projected

theorem Tree.projected {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree fuel values source context solved reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | product child => exact product_projection child found
  | group metadata _ _ _ _ | pair metadata _ _ _ _ _ _ | unary metadata _ _ _ _ _ _ | binary metadata _ _ _ _ _ _ _ _ _ =>
    have same := Option.some.inj (metadata.found.symm.trans found)
    exact same ▸ metadata.projected

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveExecution
/-! Native helper composition consumes the actual shifted right environment.
The pure operator proof is independent of the heap; operand effects remain in
the supplied finite derivations, in their original order. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference GeneralHeap CompatiblePayload

/-- The step after both operands: the body, or for unchecked `/` and `%` on
Words, the divisor check before it. -/
def Mode.continuation (mode : Mode) (operator : Syntax.BinaryOp) : Expr :=
  match mode, operator with
  | .word, .uncheckedDivide | .word, .uncheckedModulo => SourceCorePrimitive.panickingBody operator
  | _, _ => LanguageResult.success (mode.body operator)

def Mode.tail (mode : Mode) (operator : Syntax.BinaryOp) (right : Expr) : Expr :=
  match operator with
  | .logicalAnd => .ifE (.var 0) (right.weakenAt 0) (LanguageResult.success (.bool false))
  | .logicalOr => .ifE (.var 0) (LanguageResult.success (.bool true)) (right.weakenAt 0)
  | _ => LanguageResult.bind (mode.resultType operator) (right.weakenAt 0) (mode.continuation operator)

theorem Mode.binary_eq (mode : Mode) (operator : Syntax.BinaryOp) (left right : Expr) :
    mode.binary operator left right = .caseE left
      (.inLeft (mode.resultType operator) (.var 0)) (mode.tail operator right) := by
  cases mode <;> cases operator <;> simp [Mode.binary, Mode.tail, Mode.continuation, Mode.resultType, Mode.body, SourceCorePrimitive.binaryResultType, SourceCoreInteger.binaryResultType, SourceCorePrimitive.binary, SourceCorePrimitive.binaryPanicking, SourceCoreInteger.binary, LocalPrimitiveResults.logicalAnd, LocalPrimitiveResults.logicalOr, LocalPrimitiveResults.binaryWith, LocalControl.choose, LanguageResult.bind, LanguageResult.success, Expr.weakenAt]

theorem Mode.binary_rename (mode : Mode) (operator : Syntax.BinaryOp) (left right : Expr) (ξ : Renaming) :
    (mode.binary operator left right).rename ξ = mode.binary operator (left.rename ξ) (right.rename ξ) := by
  cases mode <;> cases operator <;>
    simp [Mode.binary, SourceCorePrimitive.binary, SourceCorePrimitive.binaryPanicking, SourceCoreInteger.binary,
      LocalPrimitiveResults.binaryWith, LocalPrimitiveResults.logicalAnd, LocalPrimitiveResults.logicalOr,
      LocalControl.choose, LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.rename,
      Expr.weakenAt, SourceCorePrimitive.strictBinaryBody, SourceCorePrimitive.panickingBody,
      SourceCoreInteger.strictBinaryBody, Renaming.lift]


variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping} {operator : Syntax.BinaryOp}
  {operand result : TypeSystem.Ty} {mode : Mode} {a b : Dynamic.Value} {x y : Value}

theorem BinaryProfile.left_progress (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked registry functions mapping world operand a x (mode.operandType operator)) :
    (∃ output, Dynamic.ShortCircuits operator a output) ∨ Dynamic.EvaluatesRightOperand operator a := by
  cases profile with
  | word strict => exact .inr (.strict strict)
  | integer strict => exact .inr (.strict strict.toStrict)
  | panicking panicking => exact .inr (.panicking panicking)
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases boolean
    · exact .inl ⟨_, .andFalse⟩
    · exact .inr .andTrue
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases boolean
    · exact .inr .orFalse
    · exact .inl ⟨_, .orTrue⟩

theorem BinaryProfile.left_valid (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked registry functions mapping world operand a x (mode.operandType operator)) :
    ¬ Dynamic.BinaryLeftOperandInvalid operator a := by
  intro invalid
  cases profile with
  | word strict => cases invalid <;> cases strict
  | integer strict => cases invalid <;> cases strict
  | panicking panicking => cases invalid <;> cases panicking
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases invalid with | logicalAnd invalid => exact invalid trivial
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases invalid with | logicalOr invalid => exact invalid trivial

theorem Mode.left_failure {environment : Environment} {before after : Store} {left right : Expr} {reason : Word}
    (mode : Mode) (operator : Syntax.BinaryOp)
    (evaluated : Evaluates environment before left (.inLeft (mode.operandType operator) (.word reason)) after) :
    Evaluates environment before (mode.binary operator left right) (.inLeft (mode.resultType operator) (.word reason)) after := by
  cases mode <;> cases operator <;> first
    | exact LocalPrimitiveResults.logicalAnd_failure evaluated
    | exact LocalPrimitiveResults.logicalOr_failure evaluated
    | exact LocalPrimitiveResults.binaryWith_left_failure evaluated
    | exact SourceCorePrimitive.binaryPanicking_left_failure evaluated

theorem BinaryProfile.short {environment : Environment} {before after : Store} {left right : Expr} {output : Dynamic.Value}
    (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked registry functions mapping world operand a x (mode.operandType operator))
    (circuit : Dynamic.ShortCircuits operator a output)
    (evaluated : Evaluates environment before left (.inRight .word x) after) :
    ∃ value, ValueRep checked registry functions mapping world result output value (mode.resultType operator) ∧
      Evaluates environment before (mode.binary operator left right) (.inRight .word value) after := by
  cases profile with
  | word strict => cases circuit <;> cases strict
  | integer strict => cases circuit <;> cases strict
  | panicking panicking => cases circuit <;> cases panicking
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases circuit
    exact ⟨_, .bool false, LocalPrimitiveResults.logicalAnd_shortCircuit evaluated⟩
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases circuit
    exact ⟨_, .bool true, LocalPrimitiveResults.logicalOr_shortCircuit evaluated⟩

theorem BinaryProfile.right_failure {environment : Environment} {before middle after : Store}
    {left right : Expr} {reason : Word}
    (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked registry functions mapping world operand a x (mode.operandType operator))
    (continues : Dynamic.EvaluatesRightOperand operator a)
    (first : Evaluates environment before left (.inRight .word x) middle)
    (second : Evaluates (x :: environment) middle (right.weakenAt 0) (.inLeft (mode.operandType operator) (.word reason)) after) :
    Evaluates environment before (mode.binary operator left right) (.inLeft (mode.resultType operator) (.word reason)) after := by
  cases profile with
  | word strict => rw [Mode.binary_strict _ strict]; exact LocalPrimitiveResults.binaryWith_right_failure first second
  | integer strict => rw [Mode.binary_strict _ strict.toStrict]; exact LocalPrimitiveResults.binaryWith_right_failure first second
  | panicking panicking =>
    cases panicking <;> exact SourceCorePrimitive.binaryPanicking_right_failure first second
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict | panicking strict => cases strict
    | andTrue => exact LocalPrimitiveResults.logicalAnd_right first second
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict | panicking strict => cases strict
    | orFalse => exact LocalPrimitiveResults.logicalOr_right first second

/-- After both operands, the operation either applies or, for unchecked `/`
and `%` with a zero divisor, panics. -/
theorem BinaryProfile.right_outcome {environment : Environment} {before middle after : Store} {left right : Expr}
    (profile : BinaryProfile operator operand result mode)
    (leftRep : ValueRep checked registry functions mapping world operand a x (mode.operandType operator))
    (rightRep : ValueRep checked registry functions mapping world operand b y (mode.operandType operator))
    (continues : Dynamic.EvaluatesRightOperand operator a)
    (first : Evaluates environment before left (.inRight .word x) middle)
    (second : Evaluates (x :: environment) middle (right.weakenAt 0) (.inRight .word y) after) :
    (∃ sourceResult coreResult, Dynamic.BinaryPrimitiveApplies operator a b sourceResult ∧
      ValueRep checked registry functions mapping world result sourceResult coreResult (mode.resultType operator) ∧
      Evaluates environment before (mode.binary operator left right) (.inRight .word coreResult) after) ∨
    (∃ code, Dynamic.BinaryPrimitivePanics operator a b code ∧
      Evaluates environment before (mode.binary operator left right)
        (.inLeft (mode.resultType operator) (.word (SourceCorePanics.reason code))) after) := by
  cases profile with
  | panicking panicking =>
    obtain ⟨a, rfl, rfl⟩ := word_fields (by cases panicking <;> exact leftRep)
    obtain ⟨b, rfl, rfl⟩ := word_fields (by cases panicking <;> exact rightRep)
    cases panicking with
    | uncheckedDivide =>
      by_cases zero : b = Word.zero
      · subst zero
        exact .inr ⟨_, .wordUncheckedDivide a, SourceCorePrimitive.binaryPanicking_panic first second⟩
      · exact .inl ⟨_, _, .wordUncheckedDivide a b zero, .word _,
          SourceCorePrimitive.binaryPanicking_success first second zero fun _ => .binary (.var rfl) (.var rfl) rfl⟩
    | uncheckedModulo =>
      by_cases zero : b = Word.zero
      · subst zero
        exact .inr ⟨_, .wordUncheckedModulo a, SourceCorePrimitive.binaryPanicking_panic first second⟩
      · exact .inl ⟨_, _, .wordUncheckedModulo a b zero, .word _,
          SourceCorePrimitive.binaryPanicking_success first second zero fun _ => .binary (.var rfl) (.var rfl) rfl⟩
  | word strict =>
    refine .inl ?_
    have operandEq := PrimitiveExpressions.strict_operand_word strict
    obtain ⟨a, rfl, rfl⟩ := word_fields (by simpa only [Mode.operandType, operandEq] using leftRep)
    obtain ⟨b, rfl, rfl⟩ := word_fields (by simpa only [Mode.operandType, operandEq] using rightRep)
    obtain ⟨sourceResult, coreResult, applied, represented, body⟩ := word_body (functions := functions) (registry := registry)
      (mapping := mapping) (world := world) strict a b
    exact ⟨sourceResult, coreResult, applied, represented, by
      rw [Mode.binary_strict _ strict]
      exact LocalPrimitiveResults.binaryWith_success first second (body _ _)⟩
  | integer strict =>
    refine .inl ?_
    have operandEq : SourceCoreInteger.binaryOperandType operator = .integer := by cases strict <;> rfl
    obtain ⟨a, rfl, rfl⟩ := integer_fields (by simpa only [Mode.operandType, operandEq] using leftRep)
    obtain ⟨b, rfl, rfl⟩ := integer_fields (by simpa only [Mode.operandType, operandEq] using rightRep)
    obtain ⟨sourceResult, coreResult, applied, represented, body⟩ := integer_body (functions := functions) (registry := registry)
      (mapping := mapping) (world := world) strict a b
    exact ⟨sourceResult, coreResult, applied, represented, by
      rw [Mode.binary_strict _ strict.toStrict]
      exact LocalPrimitiveResults.binaryWith_success first second (body _ _)⟩
  | logicalAnd =>
    refine .inl ?_
    obtain ⟨a, rfl, rfl⟩ := bool_fields leftRep
    obtain ⟨b, rfl, rfl⟩ := bool_fields rightRep
    cases continues with
    | strict strict | panicking strict => cases strict
    | andTrue => exact ⟨_, _, .logicalAnd true b, .bool b, LocalPrimitiveResults.logicalAnd_right first second⟩
  | logicalOr =>
    refine .inl ?_
    obtain ⟨a, rfl, rfl⟩ := bool_fields leftRep
    obtain ⟨b, rfl, rfl⟩ := bool_fields rightRep
    cases continues with
    | strict strict | panicking strict => cases strict
    | orFalse => exact ⟨_, _, .logicalOr false b, .bool b, LocalPrimitiveResults.logicalOr_right first second⟩

/-- An operation that the source applies also completes in Core. -/
theorem BinaryProfile.right_success {environment : Environment} {before middle after : Store} {left right : Expr}
    {output : Dynamic.Value}
    (profile : BinaryProfile operator operand result mode)
    (leftRep : ValueRep checked registry functions mapping world operand a x (mode.operandType operator))
    (rightRep : ValueRep checked registry functions mapping world operand b y (mode.operandType operator))
    (continues : Dynamic.EvaluatesRightOperand operator a)
    (first : Evaluates environment before left (.inRight .word x) middle)
    (second : Evaluates (x :: environment) middle (right.weakenAt 0) (.inRight .word y) after)
    (applies : Dynamic.BinaryPrimitiveApplies operator a b output) :
    ∃ sourceResult coreResult, Dynamic.BinaryPrimitiveApplies operator a b sourceResult ∧
      ValueRep checked registry functions mapping world result sourceResult coreResult (mode.resultType operator) ∧
      Evaluates environment before (mode.binary operator left right) (.inRight .word coreResult) after := by
  rcases profile.right_outcome leftRep rightRep continues first second with success | ⟨_, panics, _⟩
  · exact success
  · exact (panics.excludes_application applies).elim

/-- A source panic is the same Core panic. -/
theorem BinaryProfile.right_panic {environment : Environment} {before middle after : Store} {left right : Expr}
    {code : UInt8}
    (profile : BinaryProfile operator operand result mode)
    (leftRep : ValueRep checked registry functions mapping world operand a x (mode.operandType operator))
    (rightRep : ValueRep checked registry functions mapping world operand b y (mode.operandType operator))
    (continues : Dynamic.EvaluatesRightOperand operator a)
    (first : Evaluates environment before left (.inRight .word x) middle)
    (second : Evaluates (x :: environment) middle (right.weakenAt 0) (.inRight .word y) after)
    (panics : Dynamic.BinaryPrimitivePanics operator a b code) :
    Evaluates environment before (mode.binary operator left right)
      (.inLeft (mode.resultType operator) (.word (SourceCorePanics.reason code))) after := by
  rcases profile.right_outcome leftRep rightRep continues first second with ⟨_, _, applies, _⟩ | ⟨other, panicked, ran⟩
  · exact (panics.excludes_application applies).elim
  · rwa [panics.functional panicked]


/-- In a branch selected by the independent left-value rule, native completion
contains a real right-operand derivation at the single inserted payload slot. -/
theorem BinaryProfile.right_evaluated {environment : Environment} {before after : Store} {right : Expr} {value : Value}
    (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked registry functions mapping world operand a x (mode.operandType operator))
    (continues : Dynamic.EvaluatesRightOperand operator a)
    (evaluated : Evaluates (x :: environment) before (mode.tail operator right) value after) :
    ∃ rightValue rightStore, Evaluates (x :: environment) before (right.weakenAt 0) rightValue rightStore := by
  cases profile with
  | word strict => cases strict <;> cases evaluated <;> exact ⟨_, _, by assumption⟩
  | integer strict => cases strict <;> cases evaluated <;> exact ⟨_, _, by assumption⟩
  | panicking panicking => cases panicking <;> cases evaluated <;> exact ⟨_, _, by assumption⟩
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict | panicking strict => cases strict
    | andTrue =>
      cases evaluated with
      | ifTrue condition right =>
        obtain ⟨_, rfl⟩ := evaluation_deterministic condition (Evaluates.var rfl)
        exact ⟨_, _, right⟩
      | ifFalse condition right =>
        have same := (evaluation_deterministic condition (Evaluates.var rfl)).1
        cases same
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict | panicking strict => cases strict
    | orFalse =>
      cases evaluated with
      | ifFalse condition right =>
        obtain ⟨_, rfl⟩ := evaluation_deterministic condition (Evaluates.var rfl)
        exact ⟨_, _, right⟩
      | ifTrue condition right =>
        have same := (evaluation_deterministic condition (Evaluates.var rfl)).1
        cases same

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveMeaning
/-! Structural primitive composition over compatible heaps. Each child
semantic obligation is discharged by the tree induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

variable {fuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : Scope}

/-- Static leaf support indexes the existing tree and its exact children.
It contains only leaf membership, with no execution or heap law. -/
inductive Tree.LiteralSites (literals : GenericExpressionMeaning.Certificate) :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Tree fuel values source context solved reasonAt scope id lowered → Prop where
  | product {id lowered}
      (child : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered)
      (childSites : CompatibleExpressionProducts.Tree.LiteralSites literals child) :
      LiteralSites literals (Tree.product (scope := scope) child)
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

/-- The exact old tree restricted to the supplied static leaf certificates. -/
def Tree.WithLiterals (literals : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun current id lowered => ∃ tree : Tree fuel values source context solved reasonAt current id lowered,
    tree.LiteralSites literals

/-- Ordinary literal membership supplies support for every original tree. -/
theorem Tree.literalSites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree fuel values source context solved reasonAt scope id lowered) :
    tree.LiteralSites (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code) := by
  induction tree with
  | product child => exact .product child child.literalSites
  | group metadata form innerFound sourceType child childIH => exact .group metadata form innerFound sourceType child childIH
  | pair metadata form leftFound rightFound sourceType firstTree secondTree firstTreeIH secondTreeIH => exact .pair metadata form leftFound rightFound sourceType firstTree secondTree firstTreeIH secondTreeIH
  | unary metadata form found inputType outputType profile child childIH => exact .unary metadata form found inputType outputType profile child childIH
  | binary metadata form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH => exact .binary metadata form leftFound rightFound leftType rightType outputType profile first second firstIH secondIH

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

theorem unary_rename (operator : UnaryOp) (operand : Expr) (ξ : Renaming) :
    (LocalPrimitiveResults.unary operator operand).rename ξ =
      LocalPrimitiveResults.unary operator (operand.rename ξ) := rfl

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
theorem preserves_with_literals_and_post [FunctionCalls.FaultTokens faults]
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
  | product child childSites =>
    exact CompatibleExpressionProducts.preserves_with_literals_and_post (fuel := fuel) (reasonAt := reasonAt) functions program evidence unique sequenceJoins ordinaryJoins literalMeaning readMeaning ⟨child, childSites⟩
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
          obtain ⟨sourceResult, result, actualApplied, resultRep, combined⟩ :=
            profile.right_success leftPayload rightPayload continues first second applied
          have same := actualApplied.functional applied
          subst sourceResult
          exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
            .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans heapMetadata, trivial⟩
    | invalid firstTrace continues secondTrace failed =>
      obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, _⟩ :=
        leftIH leftFound environments heaps locals agrees (.value firstTrace)
      cases represented with
      | @value _ coreValue payload =>
        rw [leftType] at payload
        obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, _⟩ :=
          rightIH rightFound (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue) (.value secondTrace)
        rw [GenericExpressionMeaning.rename_prefix] at second
        cases represented with
        | value rightPayload =>
          rw [rightType] at rightPayload
          have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
          rcases profile.right_outcome leftPayload rightPayload continues first second with
            ⟨_, _, applied, _, _⟩ | ⟨code, panics, combined⟩
          · exact False.elim (binary_fault_excluded applied failed)
          · obtain ⟨rfl, rfl⟩ := binary_fault_panic panics failed
            exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
              .fault (FunctionCalls.FaultTokens.panic code), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata,
              ExpressionFailurePostContracts.OutcomePost.panic ordinaryJoins
                (binary_panic_fault metadata form firstTrace continues secondTrace panics)⟩


theorem reflects_with_literals_and_post [FunctionCalls.FaultTokens faults]
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
  | product child childSites =>
    exact CompatibleExpressionProducts.reflects_with_literals_and_post (fuel := fuel) (reasonAt := reasonAt) functions program evidence sequenceJoins ordinaryJoins literalMeaning readMeaning ⟨child, childSites⟩
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
              rcases profile.right_outcome leftPayload rightPayload continues leftEvaluation rightEvaluation with
                ⟨sourceResult, result, applied, resultRep, combined⟩ | ⟨code, panics, combined⟩
              · obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                cases trace with
                | value secondTrace =>
                  exact ⟨_, after, finalMap, finalWorld, binary_intro metadata form (.value firstTrace continues secondTrace applied),
                    .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                    firstFrame.trans frame, firstMetadata.trans heapMetadata, trivial⟩
              · obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                cases trace with
                | value secondTrace =>
                  exact ⟨_, after, finalMap, finalWorld,
                    binary_intro metadata form (.invalid firstTrace continues secondTrace (.panic panics)),
                    .fault (FunctionCalls.FaultTokens.panic code), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                    firstFrame.trans frame, firstMetadata.trans heapMetadata,
                    ExpressionFailurePostContracts.OutcomePost.panic ordinaryJoins
                      (binary_panic_fault metadata form firstTrace continues secondTrace panics)⟩


include extension unique uninitialized in
theorem preserves_with_literals [FunctionCalls.FaultTokens faults]
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
theorem preserves [FunctionCalls.FaultTokens faults] :
    GenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact preserves_with_literals functions extension program evidence unique uninitialized
    (CompatibleExpressionLiterals.preserves functions program context evidence valid unique faults) ⟨tree, tree.literalSites⟩


include extension uninitialized in
theorem reflects_with_literals [FunctionCalls.FaultTokens faults]
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
theorem reflects [FunctionCalls.FaultTokens faults] :
    GenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (Tree fuel values source context solved reasonAt) faults := by
  intro scope id lowered tree
  exact reflects_with_literals functions extension program evidence uninitialized
    (CompatibleExpressionLiterals.reflects functions program context evidence valid source faults) ⟨tree, tree.literalSites⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveCertificates
/-! Successful ordinary Functions lowering extracts the complete primitive
syntax tree. Operator admission follows empty retained evidence and independent
source typing; actual native operand checks select Word versus Integer. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference

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

private theorem UnaryProfile.selected {catalog : SourceCoreCompatibleCatalog.Catalog}
    {operator : Syntax.UnaryOp} {operand result : TypeSystem.Ty} {core : UnaryOp} {type : Ty}
    (profile : UnaryProfile operator operand result core) (projected : catalog.project operand = .ok type) :
    selectedUnary operator type = core := by
  cases profile <;> cases projected <;> rfl
private theorem BinaryProfile.selected {catalog : SourceCoreCompatibleCatalog.Catalog}
    {operator : Syntax.BinaryOp} {operand result : TypeSystem.Ty} {mode : Mode} {type : Ty}
    (profile : BinaryProfile operator operand result mode) (projected : catalog.project operand = .ok type) :
    selectedMode type = mode := by
  cases profile <;> cases projected <;> rfl

private inductive Compound : ExpressionForm → Prop where
  | unary (operator : Syntax.UnaryOp) (operand : ExpressionId) : Compound (.unary operator operand)
  | binary (operator : Syntax.BinaryOp) (left right : ExpressionId) : Compound (.binary left operator right)
  | group (inner : ExpressionId) : Compound (.group inner)
  | pair (left right : ExpressionId) : Compound (.tuple [left, right])

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
  | product syntaxTree =>
    refine (fun ⟨tree, sites⟩ => ⟨_, Tree.LiteralSites.product tree sites⟩) (CompatibleExpressionProducts.tree_of_functions_with_literals literals literalFactory unique declarations ?_ ?_ syntaxTree found typed accepted)
    · exact ⟨fun id child => policyFor.special id (.product child),
        fun id child => policyFor.read id (.product child), policyFor.lower, policyFor.leaf⟩
    · exact fun id node child => coercions id node (.product child)
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
        have chosen := profile.selected (childTree.projected childFound)
        rw [chosen] at metadata inputChecked ⊢
        obtain ⟨childType, childCode⟩ := compiled
        dsimp only at inputChecked childTree ⊢
        subst childType
        exact ⟨_, .unary metadata form childFound rfl rfl profile childTree childTreeSites⟩
      | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ => simp [form] at otherForm
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
        have chosen := profile.selected (firstTree.projected leftFound)
        rw [chosen] at metadata leftChecked rightChecked ⊢
        obtain ⟨firstType, leftCode⟩ := first
        obtain ⟨secondType, rightCode⟩ := second
        dsimp only at leftChecked rightChecked firstTree secondTree ⊢
        subst firstType secondType
        exact ⟨_, .binary metadata form leftFound rightFound rfl sameType.symm rfl profile firstTree secondTree firstTreeSites secondTreeSites⟩
      | unary otherForm _ _ _ | group otherForm _ _ | pair otherForm _ _ _ => simp [form] at otherForm
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
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | pair otherForm _ _ _ => simp [form] at otherForm
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
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ => simp [form] at otherForm

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

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
end

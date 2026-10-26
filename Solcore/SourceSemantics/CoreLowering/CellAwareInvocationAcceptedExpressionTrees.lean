import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCollectors

/-! The first closed expression subset of the actual named-row compiler:
literals, ordinary local reads, groups, pairs, primitive unary and binary
operators and conditionals. `Subset` recognizes those compiler sites; `Tree`
retains only the static receipts of the accepted compiler at them. No child
execution or dynamic result appears in a constructor. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionTrees
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareNamedExpressionSyntax (Site)

/-- Named-row sites of the closed subset. Every `Site` has no coercions, no
requirements except at an integer literal, is not a generalized initializer and
reads only ordinary binders, so the compiler's special callback declines it. -/
inductive Subset {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) : ExpressionId → Prop where
  | literal {id} (site : Site prepared named source id)
      (atomic : CompatibleExpressionLiterals.Atomic site.node.form) : Subset prepared named source id
  | read {id name binder} (site : Site prepared named source id)
      (form : site.node.form = .reference name (.local binder)) : Subset prepared named source id
  | unary {id operator operand} (site : Site prepared named source id)
      (form : site.node.form = .unary operator operand)
      (child : Subset prepared named source operand) : Subset prepared named source id
  | binary {id operator left right} (site : Site prepared named source id)
      (form : site.node.form = .binary left operator right)
      (first : Subset prepared named source left) (second : Subset prepared named source right) :
      Subset prepared named source id
  | conditional {id condition thenId elseId} (site : Site prepared named source id)
      (form : site.node.form = .conditional condition thenId elseId)
      (test : Subset prepared named source condition) (yes : Subset prepared named source thenId)
      (no : Subset prepared named source elseId) : Subset prepared named source id
  | group {id inner} (site : Site prepared named source id) (form : site.node.form = .group inner)
      (child : Subset prepared named source inner) : Subset prepared named source id
  | pair {id left right} (site : Site prepared named source id) (form : site.node.form = .tuple [left, right])
      (first : Subset prepared named source left) (second : Subset prepared named source right) :
      Subset prepared named source id

/-- Static receipts of the accepted compiler at subset sites. Literal, read,
group and pair trees keep the read-product certificate; operator, conditional
and enclosing group and pair nodes keep the compiler's metadata, operator
profile and lowered children. -/
inductive Tree (checked : SourceCoreCompatibleCatalog.Checked) (readFuel : Nat)
    (solved : List SolvedRequirement) (source : TypedSource) (sourceContext : SourceSemantics.Context)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | plain {id lowered}
      (receipt : CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate readFuel
        (.initial checked) source sourceContext solved reasonAt scope id lowered) :
      Tree checked readFuel solved source sourceContext reasonAt scope id lowered
  | group {id node inner innerNode lowered}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node lowered.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode) (type : node.type = innerNode.type)
      (child : Tree checked readFuel solved source sourceContext reasonAt scope inner lowered) :
      Tree checked readFuel solved source sourceContext reasonAt scope id lowered
  | pair {id node left right leftNode rightNode first second}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node (.product first.type second.type))
      (form : node.form = .tuple [left, right])
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (type : node.type = .product leftNode.type rightNode.type)
      (leftChild : Tree checked readFuel solved source sourceContext reasonAt scope left first)
      (rightChild : Tree checked readFuel solved source sourceContext reasonAt scope right second) :
      Tree checked readFuel solved source sourceContext reasonAt scope id
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩
  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : CompatibleExpressionPrimitives.UnaryProfile operator operandType resultType core)
      (child : Tree checked readFuel solved source sourceContext reasonAt scope operand ⟨core.operandType, childCode⟩) :
      Tree checked readFuel solved source sourceContext reasonAt scope id
        ⟨core.resultType, LocalPrimitiveResults.unary core childCode⟩
  | binary {id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = operandType)
      (outputType : node.type = resultType)
      (profile : CompatibleExpressionPrimitives.BinaryProfile operator operandType resultType mode)
      (first : Tree checked readFuel solved source sourceContext reasonAt scope left ⟨mode.operandType operator, leftCode⟩)
      (second : Tree checked readFuel solved source sourceContext reasonAt scope right ⟨mode.operandType operator, rightCode⟩) :
      Tree checked readFuel solved source sourceContext reasonAt scope id
        ⟨mode.resultType operator, mode.binary operator leftCode rightCode⟩
  | conditional {id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      (metadata : CompatibleExpressionPrimitives.Metadata checked source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (thenFound : source.lookupExpression? thenId = some thenNode)
      (elseFound : source.lookupExpression? elseId = some elseNode)
      (conditionType : conditionNode.type = .bool)
      (thenType : thenNode.type = node.type) (elseType : elseNode.type = node.type)
      (conditionTree : Tree checked readFuel solved source sourceContext reasonAt scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Tree checked readFuel solved source sourceContext reasonAt scope thenId ⟨type, thenCode⟩)
      (elseTree : Tree checked readFuel solved source sourceContext reasonAt scope elseId ⟨type, elseCode⟩) :
      Tree checked readFuel solved source sourceContext reasonAt scope id
        ⟨type, LocalControl.choose type conditionCode thenCode elseCode⟩

section Projection
variable {checked : SourceCoreCompatibleCatalog.Checked} {readFuel : Nat} {solved : List SolvedRequirement}
  {source : TypedSource} {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- Every receipt fixes its native type as the projection of its Source type. -/
theorem projected (tree : Tree checked readFuel solved source sourceContext reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | plain receipt => exact CompatibleExpressionPrimitives.Tree.projected (.product receipt.1) found
  | group metadata _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | pair metadata _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | unary metadata _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | binary metadata _ _ _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | conditional metadata _ _ _ _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected

end Projection

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code) (rootFuel : Nat)
  {source : TypedSource} {sourceContext : SourceSemantics.Context}
  {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}

private theorem special {id : ExpressionId} (site : Site prepared named source id) :
    ∀ child budget, (match (namedPolicy compiled rootFuel).lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context prepared named) child budget source scope id reasonAt) = .ok none :=
  fun child budget => CellAwareNamedExpressionPolicies.special compiled site rootFuel child budget scope reasonAt

private theorem plain {id : ExpressionId} (site : Site prepared named source id)
    (syntaxTree : CompatibleExpressionProducts.Syntax source id)
    (empty : site.node.form.references = [])
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id site.node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) fuel (context prepared named) source scope id reasonAt = .ok lowered) :
    Tree checked prepared.fuel (context prepared named).solvedRequirements source sourceContext reasonAt
      scope id lowered := by
  have policy : CompatibleExpressionProducts.PolicyOn (namedPolicy compiled rootFuel) (context prepared named)
      prepared.fuel (.initial checked) source scope reasonAt (fun child => child = id) := {
    special := by intro child same _; subst child; exact special compiled rootFuel site
    read := by intro child same _; subst child; exact CellAwareNamedExpressionPolicies.read compiled site rootFuel
    lower := (GeneralizedLocalInitializerCompilation.namedPolicy_recipe compiled rootFuel).lowerRead
    leaf := (GeneralizedLocalInitializerCompilation.namedPolicy_recipe compiled rootFuel).leafLowerer }
  apply Tree.plain
  apply CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions_on unique declarations policy
    ?_ ?_ syntaxTree rfl site.found typed accepted
  · intro parent node child same found member
    subst parent
    have sameNode := Option.some.inj (site.found.symm.trans found)
    subst node
    rw [empty] at member
    cases member
  · intro child node same _ found
    subst child
    have sameNode := Option.some.inj (site.found.symm.trans found)
    exact sameNode ▸ site.coercions

/-- The accepted named compiler yields the receipt tree at every subset site.
The policy's root fuel stays fixed while each child uses its true smaller
compiler budget; original Source typing selects each physical child. -/
theorem of_subset {id : ExpressionId}
    (subset : Subset prepared named source id)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) fuel (context prepared named) source scope id reasonAt = .ok lowered) :
    Tree checked prepared.fuel (context prepared named).solvedRequirements source sourceContext reasonAt
      scope id lowered := by
  induction subset generalizing node fuel lowered with
  | literal site atomic =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    exact plain compiled rootFuel site (.literal site.found atomic)
      (by generalize form : site.node.form = actual at atomic ⊢; cases atomic <;> rfl) unique declarations typed accepted
  | read site form =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    exact plain compiled rootFuel site (.read site.found form)
      (by simp [form, ExpressionForm.references]) unique declarations typed accepted
  | unary site form child ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (context := context prepared named) (values := .initial checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel) accepted
      cases step with
      | @unary operator operand childCode otherForm metadata generated inputChecked =>
        obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (form.symm.trans otherForm)
        obtain ⟨childNode, core, childFound, childTyped, profile⟩ :=
          CompatibleExpressionPrimitives.unary_source_types unique site.found form metadata.coercions metadata.requirements typed
        have childTree := ih childFound childTyped generated
        have chosen := CompatibleExpressionConditionals.unary_selected profile (projected childTree childFound)
        rw [chosen] at metadata inputChecked ⊢
        obtain ⟨childType, native⟩ := childCode
        dsimp only at inputChecked childTree ⊢
        subst childType
        exact .unary metadata form childFound rfl rfl profile childTree
      | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | binary site form first second firstIH secondIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (context := context prepared named) (values := .initial checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel) accepted
      cases step with
      | @binary operator left right first second otherForm metadata firstGenerated secondGenerated leftChecked rightChecked =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, mode, leftFound, rightFound, sameType, leftTyped, rightTyped, profile⟩ :=
          CompatibleExpressionPrimitives.binary_source_types unique site.found form metadata.coercions metadata.requirements typed
        have firstTree := firstIH leftFound leftTyped firstGenerated
        have secondTree := secondIH rightFound rightTyped secondGenerated
        have chosen := CompatibleExpressionConditionals.binary_selected profile (projected firstTree leftFound)
        rw [chosen] at metadata leftChecked rightChecked ⊢
        obtain ⟨firstType, leftCode⟩ := first
        obtain ⟨secondType, rightCode⟩ := second
        dsimp only at leftChecked rightChecked firstTree secondTree ⊢
        subst firstType secondType
        exact .binary metadata form leftFound rightFound rfl sameType.symm rfl profile firstTree secondTree
      | unary otherForm _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | conditional site form test yes no testIH thenIH elseIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (context := context prepared named) (values := .initial checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel) accepted
      cases step with
      | conditional otherForm metadata testGenerated thenGenerated elseGenerated =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.conditional.inj (form.symm.trans otherForm)
        obtain ⟨testNode, thenNode, elseNode, testFound, thenFound, elseFound,
            testType, thenType, elseType, testTyped, thenTyped, elseTyped⟩ :=
          CompatibleExpressionConditionals.conditional_source_types unique site.found form site.coercions typed
        exact .conditional metadata form testFound thenFound elseFound testType thenType elseType
          (testIH testFound testTyped testGenerated) (thenIH thenFound thenTyped thenGenerated)
          (elseIH elseFound elseTyped elseGenerated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ =>
        simp [form] at otherForm
  | group site form child ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (context := context prepared named) (values := .initial checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel) accepted
      cases step with
      | group otherForm metadata generated =>
        cases ExpressionForm.group.inj (form.symm.trans otherForm)
        obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ :=
          CompatibleExpressionProducts.group_source_types unique site.found form site.coercions typed
        exact .group metadata form innerFound sourceType (ih innerFound childTyped generated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | pair site form first second firstIH secondIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (context := context prepared named) (values := .initial checked)
        (scope := scope) (reasonAt := reasonAt) site.found (by rw [form]; constructor)
        (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel) accepted
      cases step with
      | pair otherForm metadata firstGenerated secondGenerated =>
        obtain ⟨rfl, rfl⟩ := by simpa using ExpressionForm.tuple.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, leftFound, rightFound, sourceType, leftTyped, rightTyped⟩ :=
          CompatibleExpressionProducts.pair_source_types unique site.found form site.coercions typed
        exact .pair metadata form leftFound rightFound sourceType
          (firstIH leftFound leftTyped firstGenerated) (secondIH rightFound rightTyped secondGenerated)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionTrees

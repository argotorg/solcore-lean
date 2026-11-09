import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationExpressions
import Solcore.SourceSemantics.CoreLowering.AcceptedStatements
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenStoredCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching

/-!
# Accepted bodies: the first expression closure

Discharges the expression premise of the statement closure for a first subset of
named-row bodies, and connects those bodies to a named row.

Main declarations:
- `CellAwareInvocationAcceptedExpressionTrees.Subset`, the sites of the subset, and
  `CellAwareInvocationAcceptedExpressionTrees.Tree`, their receipt trees;
- `CellAwareInvocationAcceptedExpressions.Closed` and
  `CellAwareInvocationAcceptedExpressions.Reads`, the premises in place of `Expressions`;
- `CellAwareInvocationAcceptedExpressions.expressions`,
  `CellAwareInvocationAcceptedExpressions.body_preserves` and
  `CellAwareInvocationAcceptedExpressions.body_reflects`, the whole-body theorems;
- `CellAwareInvocationAcceptedSubsetCheck.closed`, the runtime check of the subset;
- `CellAwareInvocationAcceptedNamedHeaders.static_inputs` and
  `CellAwareInvocationAcceptedNamedInvocation.preserves_selected`,
  `CellAwareInvocationAcceptedNamedInvocation.reflects_selected`, the named-row entry.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionTrees
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionBounds
/-! Structural recursion on the accepted expression receipt tree fills every
child of the invocation-family expression heads. Literal and read leaves use
their actual read-product receipts; operator, conditional, group and pair
nodes use their existing heads. No expression meaning is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CellAwareInvocationAcceptedExpressionTrees (Tree)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (faults : RecursiveStageMeaning.FaultRep)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, faults (.semantic (.uninitializedLocation location)) (reasonAt id))
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "trees" => Tree compiled.compatible.checked readFuel solved invocation.source context reasonAt

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private def Three (scope : SourceCoreLocalCell.Scope) (test yes no : ExpressionId)
    (a b c : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = test ∧ code = a) ∨ (child = yes ∧ code = b) ∨ (child = no ∧ code = c))

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues (model := valueModel) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include extension sameLedger uninitialized selectedBodies runtime covers in
/-- Every receipt tree preserves its original staged Source execution at every
Source grade, including failures and the reached mixed-cell heap. -/
theorem preserves_tree [RecursiveStageMeaning.FaultTokens faults] {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} (tree : trees scope id lowered) (size : Nat) :
    PreservesAt (attachment := attachment) bridge context valueModel index registry invocation
      (Point scope id lowered) faults size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  induction tree generalizing size with
  | plain receipt =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationReadProductBounds.preserves bridge functions extension
      GeneralizedLocalDescriptorHeap.ordinary_cells sameLedger runtime.requirements faults
      (semanticFaults := fun reason token => faults (.semantic reason) token) uninitialized
      (fun _ _ proof => proof) unique size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    have children : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Point scope inner lowered) faults size :=
      fun childSize _smaller => ih childSize
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationGroups.group_preserves bridge unique size children size (Nat.le_refl _)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    have children : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Two scope left right first second) faults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationPairBounds.pair_preserves bridge unique (product_values functions) size children
      size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    have children : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Point scope operand ⟨core.operandType, childCode⟩) faults size :=
      fun childSize _smaller => ih childSize
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.preserves_at_selected bridge functions size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.unary metadata form childFound inputType outputType operatorProfile ⟨rfl, rfl, rfl⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH rightIH =>
    have children : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩)
        faults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.preserves_at_selected bridge functions size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.binary metadata form leftFound rightFound leftType rightType outputType operatorProfile
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    have children : PreservesBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) faults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; exact testIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; exact yesIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; exact noIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.preserves_at_selected bridge functions size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.conditional metadata form testFound yesFound noFound testType yesType noType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩)

include extension sameLedger uninitialized selectedBodies runtime covers in
/-- Every completed native run of a receipt tree reconstructs an independent
Source grade, the same outcome and the reached heap. -/
theorem reflects_tree [RecursiveStageMeaning.FaultTokens faults] {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} (tree : trees scope id lowered) (size : Nat) :
    ReflectsAt (attachment := attachment) bridge context valueModel index registry invocation
      (Point scope id lowered) faults size := by
  have unique := runtime.graph.nodeOccurrencesUnique
  induction tree generalizing size with
  | plain receipt =>
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationReadProductBounds.reflects bridge functions extension
      GeneralizedLocalDescriptorHeap.ordinary_cells sameLedger runtime.requirements faults
      (semanticFaults := fun reason token => faults (.semantic reason) token) uninitialized
      (fun _ _ proof => proof) unique size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationGroups.group_reflects bridge unique size (ih size)
      (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftIH rightIH =>
    have children : ReflectsBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Two scope left right first second) faults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationPairBounds.pair_reflects bridge unique (product_values functions) size children
      size (Nat.le_refl _)
      (.actual metadata form leftFound rightFound sourceType ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @unary id node operand childNode operator operandType resultType core childCode
      metadata form childFound inputType outputType operatorProfile child ih =>
    have children : ReflectsBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Point scope operand ⟨core.operandType, childCode⟩) faults size :=
      fun childSize _smaller => ih childSize
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.reflects_at_selected bridge functions size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.unary metadata form childFound inputType outputType operatorProfile ⟨rfl, rfl, rfl⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode
      metadata form leftFound rightFound leftType rightType outputType operatorProfile leftTree rightTree leftIH rightIH =>
    have children : ReflectsBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Two scope left right ⟨mode.operandType operator, leftCode⟩ ⟨mode.operandType operator, rightCode⟩)
        faults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      cases alternative with
      | inl first => obtain ⟨rfl, rfl⟩ := first; exact leftIH childSize ⟨rfl, rfl, rfl⟩
      | inr second => obtain ⟨rfl, rfl⟩ := second; exact rightIH childSize ⟨rfl, rfl, rfl⟩
    intro current expression code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.reflects_at_selected bridge functions size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.binary metadata form leftFound rightFound leftType rightType outputType operatorProfile
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)
  | @conditional id node test yes no testNode yesNode noNode type testCode yesCode noCode
      metadata form testFound yesFound noFound testType yesType noType testTree yesTree noTree testIH yesIH noIH =>
    have children : ReflectsBelow (attachment := attachment) bridge context valueModel index registry invocation
        (Three scope test yes no ⟨.bool, testCode⟩ ⟨type, yesCode⟩ ⟨type, noCode⟩) faults size := by
      intro childSize _smaller current child code point
      obtain ⟨rfl, alternative⟩ := point
      rcases alternative with test | yes | no
      · obtain ⟨rfl, rfl⟩ := test; exact testIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := yes; exact yesIH childSize ⟨rfl, rfl, rfl⟩
      · obtain ⟨rfl, rfl⟩ := no; exact noIH childSize ⟨rfl, rfl, rfl⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CellAwareInvocationOperatorBounds.reflects_at_selected bridge functions size size (Nat.le_refl _)
      unique selectedBodies runtime covers children
      (.conditional metadata form testFound yesFound noFound testType yesType noType
        ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr (.inl ⟨rfl, rfl⟩)⟩ ⟨rfl, .inr (.inr ⟨rfl, rfl⟩)⟩)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressionBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressions
/-! The first expression closure of the accepted-body route. Meaning is proved
for exactly the expressions the actual compiler accepted for a named-row body
when they lie in the closed subset of `CellAwareInvocationAcceptedExpressionTrees`.
Each receipt is extracted from the compiler's own acceptance at its root fuel
and closed by structural recursion; no expression or body execution law is an
input. `Closed` discharges the `Expressions` premise of the body theorems.
Contextual closures and the remaining expression forms are not covered. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationAcceptedTerminals (children)
open CellAwareInvocationAcceptedFlow (Covered)

section Predicates
variable {whole : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : ActualBodyInvocation.BodyRelation}

/-- Compiler sites of the closed subset in a named-row body. Contextual
closures are not yet covered. -/
def InSubset : ActualBodyInvocation.Index whole bodyRelation → ExpressionId → Prop
  | @ActualBodyInvocation.Index.named _ _ named _ _ _ _ =>
      CellAwareInvocationAcceptedExpressionTrees.Subset whole.indexed named
        (CallableIndexedNamedGeneration.source named)
  | .contextual _ _ => fun _ => False

/-- The closed subset as a predicate on the actual accepted expression
receipts: the compiler accepted the expression at this fuel and scope, and it
is a site of the subset. -/
def Accepted (index : ActualBodyInvocation.Index whole bodyRelation) (fuel : Nat) :
    GenericExpressionMeaning.Certificate :=
  fun scope expression lowered => children index fuel scope expression lowered ∧ InSubset index expression

/-- Every expression the compiler accepts for this body, at any fuel and
scope, lies in the closed subset. -/
def Closed (index : ActualBodyInvocation.Index whole bodyRelation) : Prop :=
  ∀ fuel scope expression lowered, children index fuel scope expression lowered → InSubset index expression

/-- Fault interpretation of the body's read diagnostic words: an
uninitialized local read keeps the reason word of its own expression. -/
def Reads (index : ActualBodyInvocation.Index whole bodyRelation) (faults : RecursiveStageMeaning.FaultRep) : Prop :=
  ∀ id node name binder, index.source.lookupExpression? id = some node →
    node.form = .reference name (.local binder) →
    ∀ location, faults (.semantic (.uninitializedLocation location)) (index.reasonAt id)

private theorem found_of_lowered {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreBasic.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id
      reasonAt = .ok lowered) :
    ∃ node, source.lookupExpression? id = some node := by
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    cases found : source.lookupExpression? id with
    | some node => exact ⟨node, rfl⟩
    | none =>
      rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
      by_cases owner : id.occurrence.owner = source.owner
      · simp [owner, found, bind, Except.bind] at accepted
      · simp [owner, bind, Except.bind] at accepted

/-- The actual compiler accepts only expressions it finds in its own view. -/
theorem found_of_children (index : ActualBodyInvocation.Index whole bodyRelation)
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr} (generated : children index fuel scope expression lowered) :
    ∃ node, index.compilerSource.lookupExpression? expression = some node := by
  cases index with
  | named receipt selected =>
    change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
    cases fuel with
    | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
    | succ fuel =>
      rw [GeneralizedLocalInitializerCompilation.named_contextual receipt selected] at generated
      exact found_of_lowered generated
  | contextual material view =>
    change (GeneralizedLocalAcceptedBodyCompiler.policy material).lowerExpression _ _ _ _ _ = _ at generated
    rw [GeneralizedLocalAcceptedBodyCompiler.expression_reader] at generated
    exact found_of_lowered generated

/-- `Closed` follows from the body's expression nodes alone: a body whose
every expression node is a site of the subset is closed. -/
theorem closed_of_nodes (index : ActualBodyInvocation.Index whole bodyRelation)
    (nodes : ∀ expression node, index.compilerSource.lookupExpression? expression = some node →
      InSubset index expression) :
    Closed index := by
  intro fuel scope expression lowered generated
  obtain ⟨node, found⟩ := found_of_children index generated
  exact nodes expression node found

end Predicates

section Closure
variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  (index : ActualBodyInvocation.Index whole bodyRelation)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

private theorem reads_lowered {fuel : Nat} {context : SourceSemantics.Context}
    (sourceEq : invocation.source = index.source) (reads : Reads index faults) :
    ∀ scope id lowered,
      CompatibleExpressionReads.LoweredRead fuel
        (SourceCoreCompatibleValues.Context.initial whole.compatible.checked)
        invocation.source context index.reasonAt scope id lowered →
      ∀ location, faults (.semantic (.uninitializedLocation location)) (index.reasonAt id) := by
  intro scope id lowered receipt location
  obtain ⟨certificate, _type, _binding⟩ := receipt
  exact reads id certificate.node certificate.name certificate.binder
    (sourceEq ▸ certificate.metadata.found) certificate.form location

/-- Every accepted subset expression of a named-row body preserves its staged
Source execution at every grade. The receipt tree is extracted from the
compiler's own acceptance at the reached scope and Source context. -/
theorem preserves [RecursiveStageMeaning.FaultTokens faults] (fuel : Nat) {context : SourceSemantics.Context}
    (sourceEq : invocation.source = index.source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : Reads index faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    (runtime : Dynamic.SourceRuntimeValid program context index.source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = index.compilation.solvedRequirements) (size : Nat) :
    CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) bridge context model index
      registry invocation (Accepted index fuel) faults size := by
  have sourceRuntime : Dynamic.SourceRuntimeValid program context invocation.source := sourceEq ▸ runtime
  have uninitialized := reads_lowered index invocation faults (fuel := whole.indexed.fuel) (context := context)
    sourceEq reads
  cases index with
  | contextual material view =>
    intro scope id lowered accepted
    exact accepted.2.elim
  | @named named diagnostics output receipt selected =>
    intro scope id lowered accepted node found typed mapping world administrative environment canonical
      actual actualContext before store ξ outcome after environments heaps locals agrees actualTyped
      initial admitted authority physical
    obtain ⟨generated, subset⟩ := accepted
    have sourceNamed : invocation.source = CallableIndexedNamedGeneration.source named := sourceEq
    change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
    cases fuel with
    | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
    | succ rootFuel =>
      rw [GeneralizedLocalInitializerCompilation.named_contextual receipt selected] at generated
      have unique := sourceRuntime.graph.nodeOccurrencesUnique
      rw [sourceNamed] at unique found typed
      have tree := CellAwareInvocationAcceptedExpressionTrees.of_subset receipt rootFuel subset unique
        physical.declarations found typed generated
      rw [← sourceNamed] at tree found typed
      exact CellAwareInvocationAcceptedExpressionBounds.preserves_tree bridge functions extension sameLedger
        faults uninitialized selectedBodies sourceRuntime covers tree size ⟨rfl, rfl, rfl⟩ found typed
        environments heaps locals agrees actualTyped initial admitted authority physical

/-- Every completed native run of an accepted subset expression of a named-row
body reconstructs an independent Source grade, outcome and reached heap. -/
theorem reflects [RecursiveStageMeaning.FaultTokens faults] (fuel : Nat) {context : SourceSemantics.Context}
    (sourceEq : invocation.source = index.source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : Reads index faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    (runtime : Dynamic.SourceRuntimeValid program context index.source)
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = index.compilation.solvedRequirements) (size : Nat) :
    CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) bridge context model index
      registry invocation (Accepted index fuel) faults size := by
  have sourceRuntime : Dynamic.SourceRuntimeValid program context invocation.source := sourceEq ▸ runtime
  have uninitialized := reads_lowered index invocation faults (fuel := whole.indexed.fuel) (context := context)
    sourceEq reads
  cases index with
  | contextual material view =>
    intro scope id lowered accepted
    exact accepted.2.elim
  | @named named diagnostics output receipt selected =>
    intro scope id lowered accepted node found typed mapping world administrative environment canonical
      actual actualContext before store ξ value finalStore environments heaps locals agrees actualTyped
      initial admitted authority physical
    obtain ⟨generated, subset⟩ := accepted
    have sourceNamed : invocation.source = CallableIndexedNamedGeneration.source named := sourceEq
    change SourceCoreGeneralFunctions.lowerContextualExpression _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at generated
    cases fuel with
    | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at generated
    | succ rootFuel =>
      rw [GeneralizedLocalInitializerCompilation.named_contextual receipt selected] at generated
      have unique := sourceRuntime.graph.nodeOccurrencesUnique
      rw [sourceNamed] at unique found typed
      have tree := CellAwareInvocationAcceptedExpressionTrees.of_subset receipt rootFuel subset unique
        physical.declarations found typed generated
      rw [← sourceNamed] at tree found typed
      exact CellAwareInvocationAcceptedExpressionBounds.reflects_tree bridge functions extension sameLedger
        faults uninitialized selectedBodies sourceRuntime covers tree size ⟨rfl, rfl, rfl⟩ found typed
        environments heaps locals agrees actualTyped initial admitted authority physical

end Closure

section Discharge
variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

/-- A body whose accepted expressions all lie in the closed subset discharges
the accepted-expression input of the statement closure at every budget. -/
theorem expressions [RecursiveStageMeaning.FaultTokens faults] (closed : Closed index) (budget : Nat)
    (sourceEq : invocation.source = index.source)
    (extension : SourceCoreRawMetadata.Extends
      (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
    (reads : Reads index faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry) :
    CellAwareInvocationAcceptedInputs.Expressions (attachment := attachment) (receiving := receiving)
      (functions := functions) bridge index registry invocation faults budget := by
  intro fuel context runtime covers sameLedger
  refine ⟨?_, ?_⟩
  · intro size _ scope id lowered generated
    exact preserves bridge index registry invocation faults fuel sourceEq extension reads selectedBodies
      runtime covers sameLedger size ⟨generated, closed fuel scope id lowered generated⟩
  · intro size _ scope id lowered generated
    exact reflects bridge index registry invocation faults fuel sourceEq extension reads selectedBodies
      runtime covers sameLedger size ⟨generated, closed fuel scope id lowered generated⟩

end Discharge

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed)}
  (index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)

local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions

include bindings transport registered in
/-- The complete accepted body of an actual invocation whose accepted
expressions all lie in the closed subset: `body_preserves` without the
accepted-expression premise. -/
theorem body_preserves [RecursiveStageMeaning.FaultTokens faults] (budget : Nat) (closed : Closed index) (reads : Reads index faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {control : ControlContext} {expected : TypeSystem.Ty} {context staticFinal : SourceSemantics.Context}
    {facts : BodyFacts} (result : control.returnType = expected) (depth : control.loopDepth = 0)
    (signatures : context.signatures = whole.compatible.checked.signatures)
    (sourceTyped : StatementsHaveType index.source control context index.statements staticFinal facts)
    (projection : whole.compatible.checked.catalog.project expected = .ok index.result)
    (body : AcceptedNamedBodyFlow.Body index.policy index.fuel index.compilerSource index.scope index.statements
      index.result index.reasonAt index.fellThrough index.escaped index.body)
    (covered : Covered index.source expected (CellAwareInvocationAcceptedMatches.Admitted index)
      (CellAwareInvocationAcceptedInputs.Generalized (attachment := attachment) index) body.tree)
    (native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext index.scope ++ administrative) index.body
      nativeType whole.indexed.layouts.definitions) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative index.scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (index.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (index.source) context index.statements →
    ∀ initial : protocol.State ⟨index.scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context index.scope
      canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {finalContext outcome after},
    Staging.Recursive.Size.Statements program registry size invocation context environment before
      index.statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (index.body.rename embedding) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected index.result faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨index.scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge
          context expected (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached :=
  CellAwareInvocationAcceptedFlow.body_preserves bridge bindings transport index producer registered registry
    invocation faults administrative budget
    (expressions bridge index registry invocation faults closed budget sourceEq writes.extension reads selectedBodies)
    writes artifact checked sourceEq unique result depth signatures sourceTyped projection body covered native

include bindings transport registered in
/-- Native completion of the same complete accepted body reconstructs an
original Source execution: `body_reflects` without the accepted-expression
premise. -/
theorem body_reflects [RecursiveStageMeaning.FaultTokens faults] (budget : Nat) (closed : Closed index) (reads : Reads index faults)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    (writes : CellAwareInvocationAcceptedInputs.Writes (receiving := receiving) (functions := functions)
      (protocol := protocol) index invocation faults)
    {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
    (artifact : sourceCompiled.artifact? = some whole)
    (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
    (sourceEq : invocation.source = index.source) (unique : NodeOccurrencesUnique invocation.source)
    {control : ControlContext} {expected : TypeSystem.Ty} {context staticFinal : SourceSemantics.Context}
    {facts : BodyFacts} (result : control.returnType = expected) (depth : control.loopDepth = 0)
    (signatures : context.signatures = whole.compatible.checked.signatures)
    (sourceTyped : StatementsHaveType index.source control context index.statements staticFinal facts)
    (projection : whole.compatible.checked.catalog.project expected = .ok index.result)
    (body : AcceptedNamedBodyFlow.Body index.policy index.fuel index.compilerSource index.scope index.statements
      index.result index.reasonAt index.fellThrough index.escaped index.body)
    (covered : Covered index.source expected (CellAwareInvocationAcceptedMatches.Admitted index)
      (CellAwareInvocationAcceptedInputs.Generalized (attachment := attachment) index) body.tree)
    (native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext index.scope ++ administrative) index.body
      nativeType whole.indexed.layouts.definitions) :
    ∀ {size}, size ≤ budget →
    ∀ {mapping world actualContext environment canonical actual before store embedding},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative index.scope environment canonical whole.indexed.layouts.definitions →
    GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
      mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree embedding canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions →
    Dynamic.SourceRuntimeValid program context (index.source) →
    invocation.evidence.Covers context →
    context.solvedRequirements = index.compilation.solvedRequirements →
    ProtectedStateImperativeTypedSourceSites.Statements (index.source) context index.statements →
    ∀ initial : protocol.State ⟨index.scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      index.owner index.active mapping world before store environment →
    ∀ physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole index context index.scope
      canonical mapping world before store environment,
    ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location →
    ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native →
    ∀ {value finalStore}, EvaluationSize size actual store (index.body.rename embedding) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment before
        index.statements finalContext outcome after ∧
      Staging.Recursive.BodyResult expected outcome (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected index.result faults
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) value ∧
      GenericHeap.CellHeapRepresents
        (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment))
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : protocol.State ⟨index.scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge
          context expected (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) reached :=
  CellAwareInvocationAcceptedFlow.body_reflects bridge bindings transport index producer registered registry
    invocation faults administrative budget
    (expressions bridge index registry invocation faults closed budget sourceEq writes.extension reads selectedBodies)
    writes artifact checked sourceEq unique result depth signatures sourceTyped projection body covered native

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSubsetCheck
/-! A finite check of the closed expression subset. It reads only a row's
Source nodes and the prepared local inventory, so it runs on an actually
compiled program, and its result is a proof that every expression node of the
row is a site of `CellAwareInvocationAcceptedExpressionTrees.Subset`. A site
depends on its row only through the row's key, so the proof transports to every
row with that key; `closed` turns it into `Closed` for the row's accepted-body
index. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSubsetCheck
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareNamedExpressionSyntax (Site site?)
open CellAwareInvocationAcceptedExpressionTrees (Subset)

/-- Proof-producing recognition of one subset site and its children. -/
def subset? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (Subset prepared named source id))
  | 0, _ => none
  | fuel + 1, id => do
    let site ← site? prepared named source id
    match form : site.node.form with
    | .integerLiteral literal resolution => pure ⟨.literal site (form ▸ .integer literal resolution)⟩
    | .reference name (.builtinBoolean value) => pure ⟨.literal site (form ▸ .bool name value)⟩
    | .literal literal => pure ⟨.literal site (form ▸ .word literal)⟩
    | .tuple [] => pure ⟨.literal site (form ▸ .unit)⟩
    | .reference _name (.local _binder) => pure ⟨.read site form⟩
    | .unary _operator operand => do
      let ⟨child⟩ ← subset? prepared named source fuel operand
      pure ⟨.unary site form child⟩
    | .binary left _operator right => do
      let ⟨first⟩ ← subset? prepared named source fuel left
      let ⟨second⟩ ← subset? prepared named source fuel right
      pure ⟨.binary site form first second⟩
    | .conditional condition thenId elseId => do
      let ⟨test⟩ ← subset? prepared named source fuel condition
      let ⟨yes⟩ ← subset? prepared named source fuel thenId
      let ⟨no⟩ ← subset? prepared named source fuel elseId
      pure ⟨.conditional site form test yes no⟩
    | .group inner => do
      let ⟨child⟩ ← subset? prepared named source fuel inner
      pure ⟨.group site form child⟩
    | .tuple [left, right] => do
      let ⟨first⟩ ← subset? prepared named source fuel left
      let ⟨second⟩ ← subset? prepared named source fuel right
      pure ⟨.pair site form first second⟩
    | _ => none

private def sweep? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (fuel : Nat) :
    (nodes : List Node) → Option (PLift (∀ node, Node.expression node ∈ nodes → Subset prepared named source node.id))
  | [] => some ⟨by intro node member; cases member⟩
  | .expression node :: rest => do
    let ⟨head⟩ ← subset? prepared named source fuel node.id
    let ⟨tail⟩ ← sweep? prepared named source fuel rest
    pure ⟨by
      intro other member
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact head
      · exact tail other member⟩
  | .statement _ :: rest => do
    let ⟨tail⟩ ← sweep? prepared named source fuel rest
    pure ⟨by
      intro other member
      rcases List.mem_cons.mp member with same | member
      · cases same
      · exact tail other member⟩

/-- Every expression node of the Source is a subset site. The fuel bounds the
depth of the expression graph, which the node count bounds. -/
def nodes? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) :
    Option (PLift (∀ id node, source.lookupExpression? id = some node → Subset prepared named source id)) := do
  let ⟨all⟩ ← sweep? prepared named source (source.nodes.length + 1) source.nodes
  pure ⟨by
    intro id node found
    obtain ⟨member, same⟩ := lookupExpression?_sound found
    exact same ▸ all node member⟩

section Transport
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked} {source : TypedSource}
  {first second : SourceCoreGeneralFunctions.Function}

/-- A site retains its node and changes only the key of its local-inventory
lookups. -/
def transportSite (keyEq : first.signature.key = second.signature.key) {id : ExpressionId}
    (site : Site prepared first source id) : Site prepared second source id where
  node := site.node
  found := site.found
  form := site.form
  coercions := site.coercions
  requirements := site.requirements
  notInitializer := keyEq ▸ site.notInitializer
  ordinary := keyEq ▸ site.ordinary

/-- `Subset` depends on its row only through the row's key. -/
theorem transport (keyEq : first.signature.key = second.signature.key) {id : ExpressionId}
    (subset : Subset prepared first source id) : Subset prepared second source id := by
  induction subset with
  | literal site atomic => exact .literal (transportSite keyEq site) atomic
  | read site form => exact .read (transportSite keyEq site) form
  | unary site form _ child => exact .unary (transportSite keyEq site) form child
  | binary site form _ _ left right => exact .binary (transportSite keyEq site) form left right
  | conditional site form _ _ _ test yes no => exact .conditional (transportSite keyEq site) form test yes no
  | group site form _ child => exact .group (transportSite keyEq site) form child
  | pair site form _ _ left right => exact .pair (transportSite keyEq site) form left right
end Transport

/-- A named row whose every expression node is a subset site, checked at any
row with the same key, is closed. -/
theorem closed {whole : SourceCoreUnifiedCompilation.Compiled} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
      .ok named.specialized)
    {checkedRow : SourceCoreGeneralFunctions.Function} (keyEq : checkedRow.signature.key = named.signature.key)
    (nodes : ∀ id node, (CallableIndexedNamedGeneration.source named).lookupExpression? id = some node →
      Subset whole.indexed checkedRow (CallableIndexedNamedGeneration.source named) id) :
    CellAwareInvocationAcceptedExpressions.Closed
      (ActualBodyInvocation.Index.named generation record :
        ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView) :=
  CellAwareInvocationAcceptedExpressions.closed_of_nodes _ fun id node found =>
    transport keyEq (nodes id node found)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSubsetCheck
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedHeaders
/-! An actual prepared named header determines its accepted-body invocation.
Checker certification, the header's result projection and the Core typing of
the compiled body discharge the static premises of the accepted-body theorems;
expression meaning, coverage and the physical entry state are not derived here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedHeaders
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared whole row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
theorem record :
    SourceCompilationPlan.exactSpecialization whole.indexed.base.plan prepared.named.signature.key =
      .ok prepared.named.specialized := by
  simpa only [aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record whole header

/-- The named cache row's own accepted-body invocation. -/
def index : ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView :=
  .named prepared.compilation (record prepared aligned)

/-- Static inputs of `CellAwareInvocationAcceptedFlow.body_preserves` and
`body_reflects` at the actual header: the context signatures, fixed-control
checker typing of the compiled statements, the result projection and the native
typing of the body. -/
theorem static_inputs
    (ready : SourceCoreIndexedSession.Recipe.prepare whole = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry whole.indexed.layouts}
    (member : entry ∈ whole.indexed.entries)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    (index prepared aligned).source = header.function.source ∧
    header.context.signatures = whole.compatible.checked.signatures ∧
    (∃ control : ControlContext, ∃ staticFinal facts,
      control.returnType = header.function.resultType ∧ control.loopDepth = 0 ∧
      StatementsHaveType (index prepared aligned).source control header.context
        (index prepared aligned).statements staticFinal facts) ∧
    whole.compatible.checked.catalog.project header.function.resultType = .ok (index prepared aligned).result ∧
    ∃ nativeType, HasType (SourceCoreLocalCell.coreContext (index prepared aligned).scope ++
        RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
      (index prepared aligned).body nativeType whole.indexed.layouts.definitions := by
  have sourceEq : header.function.source = source prepared.named := by
    rw [header.agreement.source, aligned.named]
    rfl
  have statementsEq : header.function.body = prepared.compilation.statements := by
    rw [aligned.function]
    rfl
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  rw [sourceEq, statementsEq] at typed
  have native := CallableIndexedOwnedPreparedNamedLexicalCollectors.body_typed prepared aligned ready member
  have projection : whole.compatible.checked.catalog.project header.function.resultType =
      .ok prepared.named.signature.resultType := by
    simpa only [← header.resultType, aligned.named] using aligned.projection
  have bodyTyped : HasType (SourceCoreLocalCell.coreContext
        (prepared.named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) ++
        RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial whole.compatible.checked) header)
      prepared.compilation.body (LanguageResult.resultType header.output) whole.indexed.layouts.definitions := by
    simpa only [CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.parameterScope, aligned.bindings,
      aligned.body] using native
  exact ⟨sourceEq.symm, RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header),
    ⟨_, final, facts, rfl, rfl, typed⟩, projection, _, bodyTyped⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedHeaders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedInvocation
/-! One genuine named invocation of an accepted body whose expressions lie in
the closed subset. The actual named parameter entry supplies the physical entry
state of the body's own accepted-body index, the accepted-body theorem relates
the compiled body to independent Source execution, and the saved physical
caller is restored. The read and write inputs of the accepted-body theorem come
from the issued compilation and the public receiver. The caller's heap is
represented with the profiled instance model of the older family; each of its
snapshots embeds in the accepted instance model, in which the result is
stated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)

section Instances
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {ordinary : GenericHeap.PayloadModel catalog projects prepared.layouts.definitions}
  {mapping : LocationMap} {world : StoreTyping}

private theorem rows_of_profiled {function : Dynamic.GeneralizedClosure}
    {binding : SourceCoreLocalPolymorphism.Binding} {lexical : TypeSystem.Substitution}
    {entries : List SourceCoreLocalPolymorphism.Instance} {values : List Core.Value}
    (rows : SourceCoreLocalPolymorphism.ProductBundle.Pointwise
      ((GeneralizedLocalInstanceValues.model prepared).Represents mapping world function binding lexical)
      entries values) :
    SourceCoreLocalPolymorphism.ProductBundle.Pointwise
      ((GeneralizedLocalAcceptedInstances.modelWith prepared (fun _ _ _ => True)).Represents
        mapping world function binding lexical) entries values := by
  induction rows with
  | nil => exact .nil
  | cons head _ ih =>
    obtain ⟨location, framed⟩ := GeneralizedLocalAcceptedInstances.of_profiled head
    exact .cons ⟨location, framed.forget_attachment⟩ ih

/-- A cell of the profiled instance model is a cell of the accepted instance
model with the trivial attachment: every snapshot keeps its packet, captures,
location and value, and its profiled body yields an accepted body receipt. -/
theorem cell_of_profiled {cell : Dynamic.Cell} {value : Core.Value} {payload : Core.Ty}
    (represented : (GeneralizedLocalDescriptorHeap.cellModel ordinary
      (GeneralizedLocalInstanceValues.model prepared)).Represents mapping world cell value payload) :
    (GeneralizedLocalDescriptorHeap.cellModel ordinary
      (GeneralizedLocalAcceptedInstances.modelWith prepared (fun _ _ _ => True))).Represents
        mapping world cell value payload := by
  cases represented with
  | ordinary represented => exact .ordinary represented
  | generalized stored =>
    cases stored with
    | bundle binding lexical registered captures origin binder initializer rows =>
      exact .generalized (GeneralizedLocalDescriptorHeap.Stored.bundle
        (model := GeneralizedLocalAcceptedInstances.modelWith prepared (fun _ _ _ => True))
        binding lexical registered captures origin binder initializer (rows_of_profiled rows))

end Instances

/-- The accepted-body index of an actual named cache row. -/
abbrev rowIndex {compiled : SourceCoreUnifiedCompilation.Compiled} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key =
      .ok named.specialized) :
    ActualBodyInvocation.Index compiled ActualBodyInvocation.ReachedView :=
  .named generation record

section Reads
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key =
    .ok named.specialized)
  (issuer : CellAwareNamedDiagnosticIssuer.Named compiled.indexed named (diagnostics.reasonAt named.signature.key))
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)

include issuer receiver in
/-- The read-fault input of the accepted-body theorems at a named row. The
selected compiler row and the retained issuer fix the diagnostic of every
ordinary local read, as `CellAwareNamedReadDiagnostics.uninitialized` does for
the older named family. -/
theorem reads (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source named)) :
    CellAwareInvocationAcceptedExpressions.Reads (rowIndex generation record)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) := by
  intro id node name binder found form location
  change CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
    (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id)
  obtain ⟨issued, present, callback, own, ownFound⟩ := issuer
  have contains : ContainsExpression named.specialized.function.typedBody id node :=
    lookupExpression?_sound found
  obtain ⟨read, _expression, _binder, _span, token, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic compiled receiver present
      record unique contains form ownFound
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  exact CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
    (by simpa only [callback, token] using decoded) (.readUninitialized location binder)

end Reads

section Writes
variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
    .ok named.specialized)
  (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics)
  (assignments : ∃ first, SourceCoreAssignmentFaultSites.prepare (CallableIndexedNamedGeneration.source named) first =
    .ok generation.own.assignments)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)

include profile issued assignments receiver in
/-- The write inputs of the accepted-body theorems at a named row. The issued
compilation, its prepared assignment table and the public receiver interpret
the operand, unary and place diagnostics of every typed assignment occurrence,
as `CallableIndexedOwnedIssuedAssignmentRecipes.operands` and
`CellAwareNamedAssignmentDiagnostics.ready` do for the older named family. The
registry extension is the receiver's own, and the identity and runtime views
are those of the physical function origins. -/
def writes {invocation : Staging.Recursive.Scope}
    (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
    (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source named)) :
    CellAwareInvocationAcceptedInputs.Writes (receiving := completion.result.context.registry)
      (functions := CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile)
      (protocol := protocol) (rowIndex generation record) invocation
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) where
  extension := completion.result.extension
  operands := by
    intro context site assignment operator rhs origin typed
    obtain ⟨first, prepared⟩ := assignments
    rw [sourceEq] at origin typed
    have raw : operator = .equal ∨ assignment.target.type = .word := by
      cases typed with
      | equal => exact .inl rfl
      | wordCompound _ place _ _ =>
        cases place with
        | intro _ _ same => exact .inr same
    exact PreparedBranchingAssignmentDiagnostics.operands prepared
      (fun _ _ represented => CallableIndexedOwnedIssuedAssignmentRecipes.operands generation issued receiver represented)
      origin raw
  unary := by
    intro context site assignment origin typed
    obtain ⟨first, prepared⟩ := assignments
    rw [sourceEq] at origin typed
    cases typed with
    | intro place _ =>
      cases place with
      | intro _ _ word =>
        exact GenericAssignmentUnaryDiagnostics.prepared_unary_included prepared
          (fun _ _ represented => CallableIndexedOwnedPublicUnaryAssignmentDiagnostics.compilation_unary
            generation issued receiver represented) origin word
  identities := CallableIndexedLambdaValues.Identity whole.indexed
  faithful := CallableIndexedLambdaValues.identity_faithful whole.indexed
  observations := CellAwarePhysicalFunctionOrigins.observations profile
  functionTypes := CellAwarePhysicalFunctionOrigins.runtime_views profile
  placeDiagnostics := by
    rw [sourceEq]
    exact CellAwareNamedAssignmentDiagnostics.ready record unique issued receiver _ protocol

end Writes

private theorem monomorphic_context {owner : Resolved.DeclarationId} {context final : SourceSemantics.Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend owner context parameters types final)
    (initial : ∀ id scheme, (id, scheme) ∈ context.locals → scheme.quantified = []) :
    ∀ id scheme, (id, scheme) ∈ final.locals → scheme.quantified = [] := by
  induction extended with
  | nil => exact initial
  | @cons context binder next rest types final payload mono head tail ih =>
    apply ih
    cases head
    intro id scheme member
    rcases List.mem_cons.mp member with same | member
    · cases same
      simp only [mono, TypeSystem.Scheme.mono]
    · exact initial id scheme member

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}

private theorem statements (header : Header whole (Program.ofChecked whole.sourceProgram))
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed header.named diagnostics code) :
    generation.statements = header.function.body := by
  have same := (RecursiveNamedPreparedSourceFrames.compiled_roots_eq generation).symm.trans
    (header.agreement.source ▸ header.agreement.roots)
  exact (List.map_inj_right (fun _ _ same => NodeId.statement.inj same)).mp same

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header whole (Program.ofChecked whole.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
    .ok named.specialized)
  (sameNamed : header.named = named)
  (sameLayouts : header.layouts = whole.indexed.layouts)
  (sameGlobals : header.globals = whole.indexed.base.globals.length)
  (sameBindings : header.bindings = named.inputs)
  (sameBody : header.body = generation.body)
  (sameSolved : header.solved = named.specialized.function.solvedRequirements)
  {invocation : Staging.Recursive.Scope}
  (selected : (SelectedCompilationPhysicalProgramSupport.stages whole).Closure header.function invocation)
  (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
  (projection : whole.compatible.checked.catalog.project header.function.resultType = .ok named.signature.resultType)
  (support : SelectedCompilationNamedSupport.Support whole)
  {arguments : List Dynamic.Value} {payloads : List Value}

local notation "namedFunctions" =>
  CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" =>
  CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry namedFunctions
local notation "profiled" =>
  GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)
local notation "accepted" => GeneralizedLocalDescriptorHeap.cellModel model
  (GeneralizedLocalAcceptedInstances.modelWith whole.indexed (fun _ _ _ => True))
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "bridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

variable
  (closed : CellAwareInvocationAcceptedExpressions.Closed (rowIndex generation record))
  (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics)
  (assignments : ∃ first, SourceCoreAssignmentFaultSites.prepare (CallableIndexedNamedGeneration.source named) first =
    .ok generation.own.assignments)
  {workspace : Workspace.RawWorkspace} {checkFuel : Nat} {sourceCompiled : SourceCoreCompiler.Compiled}
  (artifact : sourceCompiled.artifact? = some whole)
  (checked : checkProgram workspace checkFuel = .ok sourceCompiled.program)
  (body : AcceptedNamedBodyFlow.Body (rowIndex generation record).policy (rowIndex generation record).fuel
    (rowIndex generation record).compilerSource (rowIndex generation record).scope
    (rowIndex generation record).statements (rowIndex generation record).result
    (rowIndex generation record).reasonAt (rowIndex generation record).fellThrough
    (rowIndex generation record).escaped (rowIndex generation record).body)
  (covered : CellAwareInvocationAcceptedFlow.Covered (rowIndex generation record).source header.function.resultType
    (CellAwareInvocationAcceptedMatches.Admitted (rowIndex generation record))
    (CellAwareInvocationAcceptedInputs.Generalized (rowIndex generation record)) body.tree)
  (native : ∃ nativeType, HasType (SourceCoreLocalCell.coreContext (rowIndex generation record).scope ++
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative))
    (rowIndex generation record).body nativeType whole.indexed.layouts.definitions)

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved selected issuer
  projection support closed issued assignments artifact checked covered native in
/-- The Source allocation and body trace are independent inputs. The native
entry, the accepted body and the saved-caller restoration are constructed from
the compiler; no body or expression execution law is assumed. -/
theorem preserves_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents profiled mapping world before store)
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {size : Nat}
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (allocated : Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound)
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
      header.context environment bound header.function.body finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        namedFunctions accepted owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree whole receiver)
  subst sameNamed
  have certified := support.certified header
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      prefixFrame, prefixEffect, _lexical, reached, related, rows, physical, frameEq, wrap, _unwrap⟩ :=
    CellAwareNamedEntry.prepare_selected owner caller header capture sameLayouts sameGlobals record certified
      heapTyped argumentsTyped represented heaps stable
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entryAllocated allocated
  rw [← sameEnvironment, ← sameHeap, ← statements header generation] at trace
  have sourceEq : invocation.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : invocation.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence selected] using sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements :=
    header.valid.ledger.trans sameSolved
  obtain ⟨typingFinal, typingFacts, originalTyped, _completes⟩ := sourceReceipt.bodyTyped
  have functionTyped : StatementsHaveType (CallableIndexedNamedGeneration.source header.named)
      {returnType := header.function.resultType} header.context generation.statements typingFinal typingFacts := by
    simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source]
      using originalTyped
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements :=
    ⟨_, typingFinal, typingFacts, functionTyped⟩
  have unique : NodeOccurrencesUnique invocation.source := sourceEq ▸ runtime.graph.nodeOccurrencesUnique
  obtain ⟨_facts, certificate⟩ := certified
  have empty : header.function.context.locals = [] := by
    rw [header.frame.context]
    exact certificate.locals_empty
  have monomorphic := monomorphic_context header.extended
    (by intro id scheme member; rw [empty] at member; cases member)
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) headers keys accepted
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index reached read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CallableIndexedOwnedCellAllocationProducer.producer, frameEq, OwnedKey.key] using result
  let frame : ActualBodyInvocation.Frame (rowIndex generation record) :=
    ⟨physical.native, .named physical.id, CallableIndexedNamedGeneration.state header.named, physical.carried,
      .named (CallableIndexedNamedGeneration.seed whole.indexed physical.selected record), rfl, rfl⟩
  let bodyPhysical : CellAwareInvocationPhysical.Physical (attachment := fun _ _ _ => True) whole
      (rowIndex generation record)
      header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entryCanonical entryMap entryWorld entryHeap entryStore entryEnvironment :=
    CellAwareInvocationPhysical.Physical.of_monomorphic (attachment := fun _ _ _ => True) frame physical.declarations
    physical.ownership physical.sourceDeclarations physical.location physical.reference physical.read physical.unmapped
    sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  have scopeEq : (rowIndex generation record).scope =
      header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) := by
    rw [sameBindings]
    rfl
  have meaning := CellAwareInvocationAcceptedExpressions.body_preserves (attachment := fun _ _ _ => True) bridge
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys) (rowIndex generation record) producer
    (CallableIndexedAmbient.frame_registered whole.indexed) stages invocation faults
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative) size closed
    (reads generation record issuer receiver runtime.graph.nodeOccurrencesUnique) support.registryBodies
    (writes profile generation record issued assignments receiver (protocol := protocol headers keys) sourceEq
      runtime.graph.nodeOccurrencesUnique)
    artifact checked sourceEq unique (control := {returnType := header.function.resultType})
    (expected := header.function.resultType) rfl rfl
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
    functionTyped projection body covered native (Nat.le_refl size)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  rw [scopeEq] at meaning
  obtain ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, bodyHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, _bodyEffect, bodyState, bodyRelated, bodyPost⟩ :=
    meaning environments (entryHeaps.includes cell_of_profiled) sourceReceipt.locals agrees actualTyped runtime
      covers sameLedger typed reached ⟨sourceReceipt.heapTyped, rows⟩
      (CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic)
      bodyPhysical owner frameEq.symm ready trace
  have evaluatedHeader : Evaluates entryActual entryStore (header.body.rename entryEmbedding) value bodyStore := by
    rw [sameBody]
    exact evaluated
  have resultEq : (rowIndex generation record).result = header.output :=
    header.resultType
  rw [resultEq] at result
  have worlds := prefixEffect.worlds.trans bodyWorlds
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState owner.position bodyHeaps worlds
      (prefixFrame.trans bodyFrame) (related.trans bodyRelated)
  let returned := CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position
  have supports := Dynamic.TypeContextSupports.ofClosed rfl sourceReceipt.runtime.closed sourceReceipt.runtime.closed
    sourceReceipt.runtime.variables_closed sourceReceipt.runtime.residual_variables_open
  have post := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨value, _, finalMap, finalWorld, wrap evaluatedHeader, ?_⟩
  exact ⟨result, restoredHeaps, prefixEffect.maps.trans bodyMaps, worlds,
    restoredFrame, prefixEffect.metadata.trans bodyMetadata, returned, restoredRelated, post⟩

include profile receiver record sameNamed sameLayouts sameGlobals sameBindings sameBody sameSolved selected issuer
  projection support closed issued assignments artifact checked covered native in
/-- Actual native completion is unwrapped through the same named entry and
reconstructs an independent Source execution with the restored caller. -/
theorem reflects_selected
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : GenericHeap.CellHeapRepresents profiled mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ size environment bound finalContext outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      Staging.Recursive.Size.Statements (Program.ofChecked whole.sourceProgram) stages size invocation
        header.context environment bound header.function.body finalContext outcome after ∧
      Staging.Recursive.BodyResult header.function.resultType outcome
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) ∧
      CellAwarePublicApplicationResult.NamedResultAt (registry := completion.result.context.registry)
        namedFunctions accepted owner caller header capture payloads header.context
        (CallableIndexedOwnedAdmittedStagedLexicalFlow.result outcome) after value finalStore finalMap finalWorld faults := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree whole receiver)
  subst sameNamed
  have certified := support.certified header
  obtain ⟨entryEnvironment, entryHeap, entryCanonical, entryActual, entryContext, entryStore, entryMap, entryWorld,
      entryEmbedding, entryAllocated, environments, entryHeaps, sourceReceipt, agrees, actualTyped,
      prefixFrame, prefixEffect, _lexical, reached, related, rows, physical, frameEq, _wrap, unwrap⟩ :=
    CellAwareNamedEntry.prepare_selected owner caller header capture sameLayouts sameGlobals record certified
      heapTyped argumentsTyped represented heaps stable
  obtain ⟨bodyStore, bodyEvaluation, finalEq⟩ := unwrap completed
  have compiledEvaluation : Evaluates entryActual entryStore (generation.body.rename entryEmbedding) value bodyStore := by
    rw [← sameBody]
    exact bodyEvaluation
  obtain ⟨nativeSize, nativeTrace⟩ := evaluation_has_size compiledEvaluation
  have sourceEq : invocation.source = CallableIndexedNamedGeneration.source header.named :=
    ((SelectedCompilationPhysicalProgramSupport.stages whole).source selected).trans header.agreement.source
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked whole.sourceProgram) header.context
      (CallableIndexedNamedGeneration.source header.named) := by
    simpa only [CallableIndexedNamedGeneration.source, header.agreement.source] using sourceReceipt.runtime
  have covers : invocation.evidence.Covers header.context := by
    simpa only [(SelectedCompilationPhysicalProgramSupport.stages whole).evidence selected] using sourceReceipt.covers
  have sameLedger : header.context.solvedRequirements =
      (CallableIndexedNamedGeneration.context whole.indexed header.named).solvedRequirements :=
    header.valid.ledger.trans sameSolved
  obtain ⟨typingFinal, typingFacts, originalTyped, _completes⟩ := sourceReceipt.bodyTyped
  have functionTyped : StatementsHaveType (CallableIndexedNamedGeneration.source header.named)
      {returnType := header.function.resultType} header.context generation.statements typingFinal typingFacts := by
    simpa only [statements header generation, CallableIndexedNamedGeneration.source, header.agreement.source]
      using originalTyped
  have typed : ProtectedStateImperativeTypedSourceSites.Statements
      (CallableIndexedNamedGeneration.source header.named) header.context generation.statements :=
    ⟨_, typingFinal, typingFacts, functionTyped⟩
  have unique : NodeOccurrencesUnique invocation.source := sourceEq ▸ runtime.graph.nodeOccurrencesUnique
  obtain ⟨_facts, certificate⟩ := certified
  have empty : header.function.context.locals = [] := by
    rw [header.frame.context]
    exact certificate.locals_empty
  have monomorphic := monomorphic_context header.extended
    (by intro id scheme member; rw [empty] at member; cases member)
  let producer := CallableIndexedOwnedCellAllocationProducer.producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) headers keys accepted
  have ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native := by
    intro index reached read
    have result := CallableIndexedOwnedAllocationProducer.ready_of_stable_read reached owner.position
      (by simpa only [frameEq, OwnedKey.key] using read) physical.carried
    simpa only [producer, CallableIndexedOwnedCellAllocationProducer.producer, frameEq, OwnedKey.key] using result
  let frame : ActualBodyInvocation.Frame (rowIndex generation record) :=
    ⟨physical.native, .named physical.id, CallableIndexedNamedGeneration.state header.named, physical.carried,
      .named (CallableIndexedNamedGeneration.seed whole.indexed physical.selected record), rfl, rfl⟩
  let bodyPhysical : CellAwareInvocationPhysical.Physical (attachment := fun _ _ _ => True) whole
      (rowIndex generation record)
      header.context (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entryCanonical entryMap entryWorld entryHeap entryStore entryEnvironment :=
    CellAwareInvocationPhysical.Physical.of_monomorphic (attachment := fun _ _ _ => True) frame physical.declarations
    physical.ownership physical.sourceDeclarations physical.location physical.reference physical.read physical.unmapped
    sourceReceipt.locals sourceReceipt.heapTyped monomorphic
  have scopeEq : (rowIndex generation record).scope =
      header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)) := by
    rw [sameBindings]
    rfl
  have meaning := CellAwareInvocationAcceptedExpressions.body_reflects (attachment := fun _ _ _ => True) bridge
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (CallableIndexedOwnedFunctionState.administrativeTransport headers keys) (rowIndex generation record) producer
    (CallableIndexedAmbient.frame_registered whole.indexed) stages invocation faults
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative) nativeSize closed
    (reads generation record issuer receiver runtime.graph.nodeOccurrencesUnique) support.registryBodies
    (writes profile generation record issued assignments receiver (protocol := protocol headers keys) sourceEq
      runtime.graph.nodeOccurrencesUnique)
    artifact checked sourceEq unique (control := {returnType := header.function.resultType})
    (expected := header.function.resultType) rfl rfl
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
    functionTyped projection body covered native (Nat.le_refl nativeSize)
    (mapping := entryMap) (world := entryWorld) (actualContext := entryContext)
    (environment := entryEnvironment) (canonical := entryCanonical) (actual := entryActual)
    (before := entryHeap) (store := entryStore) (embedding := entryEmbedding)
  rw [scopeEq] at meaning
  obtain ⟨sourceSize, bodyContext, bodyOutcome, after, finalMap, finalWorld, trace, matched, result, bodyHeaps,
      bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, _bodyEffect, bodyState, bodyRelated, bodyPost⟩ :=
    meaning environments (entryHeaps.includes cell_of_profiled) sourceReceipt.locals agrees actualTyped runtime
      covers sameLedger typed reached ⟨sourceReceipt.heapTyped, rows⟩
      (CellAwareScopeAuthority.At.of_monomorphic sourceReceipt.locals sourceReceipt.heapTyped monomorphic)
      bodyPhysical owner frameEq.symm ready nativeTrace
  have resultEq : (rowIndex generation record).result = header.output :=
    header.resultType
  rw [resultEq] at result
  have worlds := prefixEffect.worlds.trans bodyWorlds
  obtain ⟨restoredHeaps, restoredFrame, _cell, restoredRelated⟩ :=
    CellAwareOwnedBodyRestoration.restore_return caller bodyState owner.position bodyHeaps worlds
      (prefixFrame.trans bodyFrame) (related.trans bodyRelated)
  let returned := CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position
  have supports := Dynamic.TypeContextSupports.ofClosed rfl sourceReceipt.runtime.closed sourceReceipt.runtime.closed
    sourceReceipt.runtime.variables_closed sourceReceipt.runtime.residual_variables_open
  have post := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨sourceSize, entryEnvironment, entryHeap, bodyContext, bodyOutcome, after, finalMap, finalWorld,
    entryAllocated, ?_, matched, completed, ?_⟩
  · rw [← statements header generation]
    exact trace
  · rw [finalEq]
    exact ⟨result, restoredHeaps, prefixEffect.maps.trans bodyMaps, worlds,
      restoredFrame, prefixEffect.metadata.trans bodyMetadata, returned, restoredRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedNamedInvocation
end

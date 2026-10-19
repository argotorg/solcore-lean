import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionScalarProjection
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCertificates

/-! Accepted named expression compilation yields the mixed tree recursively.
Original Source typing selects each physical child; no child execution is an
input to this extraction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCollectors
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareNamedExpressionSyntax (Site)
open CellAwareNamedExpressionCertificates (Tree)
open CompatibleEncoding (bind_ok)

section Generic
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}

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

end Generic

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
    Tree compiled rootFuel source sourceContext reasonAt scope id lowered := by
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

private theorem builtin {id : ExpressionId} (site : Site prepared named source id)
    {name : String} {function : BuiltinFunctionId}
    (form : site.node.form = .reference name (.builtinFunction function))
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) fuel (context prepared named) source scope id reasonAt = .ok lowered) :
    Nonempty (CellAwareBuiltinValueCertificates.Header prepared source id lowered) := by
  cases fuel with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel =>
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = source.owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, site.found,
        bind, Except.bind, pure, Except.pure] at accepted
      have bypass := special compiled rootFuel (scope := scope) (reasonAt := reasonAt) site
        (fun budget childSource childScope childId childReasonAt =>
          SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
            (namedLowerBody compiled) (min budget fuel) (context prepared named)
            childSource childScope childId childReasonAt) (fuel + 1)
      change CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
        (context prepared named) _ _ _ _ _ _ = .ok none at bypass
      simp only [show (namedPolicy compiled rootFuel).lowerSpecial? = some
        (CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel) from rfl] at accepted
      rw [bypass] at accepted
      simp only [form,
        CellAwareNamedExpressionPolicies.read compiled site rootFuel] at accepted
      obtain ⟨pair, read, rest⟩ := bind_ok accepted
      obtain ⟨other, type⟩ := pair
      have metadata := CompatibleExpressionReads.metadata_of_read read
      have same := Option.some.inj (metadata.found.symm.trans site.found)
      subst other
      simp only [form] at rest
      obtain ⟨code, reference, rest⟩ := bind_ok rest
      obtain ⟨done, _sameType, rest⟩ := bind_ok rest
      cases done
      cases rest
      exact CellAwareBuiltinValueCertificates.of_reference prepared rfl site.found form
        metadata.requirements metadata.coercions reference
    · simp [owner, bind, Except.bind] at accepted

/-- The actual root callback remains fixed while each recursive child uses
its true smaller compiler budget. -/
theorem of_policy {id : ExpressionId}
    (syntaxTree : CellAwareNamedExpressionSyntax.Syntax prepared named source id)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled rootFuel)
      (namedLowerBody compiled) fuel (context prepared named) source scope id reasonAt = .ok lowered) :
    Tree compiled rootFuel source sourceContext reasonAt scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
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
  | builtin site form =>
    obtain ⟨receipt⟩ := builtin compiled rootFuel site form accepted
    exact .builtin receipt
  | generalized observed recipe =>
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨receipt⟩ := GeneralizedLocalNamedReadCompilation.of_policy compiled observed accepted
      obtain ⟨recipe⟩ := GeneralizedLocalNamedRecipeCompilation.of_certificate recipe receipt
      exact .generalized receipt recipe
  | index site form first second firstIH secondIH =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨keyType, baseTyped, keyTyped⟩ := CompatibleExpressionIndices.index_source_types
        unique site.found form site.coercions typed
      obtain ⟨baseNode, baseContains, baseType⟩ := baseTyped.stored_type
      obtain ⟨keyNode, keyContains, actualKeyType⟩ := keyTyped.stored_type
      have baseFound := lookupExpression?_complete unique baseContains
      have keyFound := lookupExpression?_complete unique keyContains
      rw [← actualKeyType] at keyTyped baseType baseTyped
      rw [← baseType] at baseTyped
      obtain ⟨layout, comparison, firstCode, secondCode, rfl, header, firstGenerated, secondGenerated⟩ :=
        CompatibleExpressionIndices.index_of_functions
          (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
          (context := context prepared named) (values := .initial checked)
          (scope := scope) (reasonAt := reasonAt) site.found baseFound form
          (special compiled rootFuel site) (CellAwareNamedExpressionPolicies.read compiled site rootFuel)
          (by rfl) accepted
      exact .index header keyFound form baseType (firstIH baseFound baseTyped firstGenerated)
        (secondIH keyFound keyTyped secondGenerated)
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
        have scalar : CellAwareNamedExpressionScalarProjection.Scalar childCode.type :=
          inputChecked ▸ CellAwareNamedExpressionScalarProjection.unary_input_scalar _ childCode.type
        have chosen := CompatibleExpressionConditionals.unary_selected profile
          (CellAwareNamedExpressionScalarProjection.projected childTree childFound scalar)
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
        have scalar : CellAwareNamedExpressionScalarProjection.Scalar first.type :=
          leftChecked ▸ CellAwareNamedExpressionScalarProjection.binary_input_scalar
            (CompatibleExpressionConditionals.selectedMode first.type) _
        have chosen := CompatibleExpressionConditionals.binary_selected profile
          (CellAwareNamedExpressionScalarProjection.projected firstTree leftFound scalar)
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
  | @call id callee ids metadata site form calleeObserved calleeRecipe children ih =>
    have same := Option.some.inj (site.found.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have bypass := special compiled rootFuel (scope := scope) (reasonAt := reasonAt) site
      have readPolicy := CellAwareNamedExpressionPolicies.read compiled site rootFuel
      obtain ⟨type, read⟩ := call_read (values := .initial checked) site.found form bypass readPolicy accepted
      obtain ⟨compiler⟩ := CallableIndirectCallCertificates.of_functions
        (policy := namedPolicy compiled rootFuel) (body := namedLowerBody compiled)
        (compilation := context prepared named) (scope := scope) (reasonAt := reasonAt)
        site.found form bypass read form accepted
      have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent compiler readPolicy
      have originalSame := Option.some.inj (compiler.found.symm.trans site.found)
      have parentTyped : ExpressionHasType source sourceContext id compiler.original.type := by
        simpa [originalSame] using typed
      obtain ⟨parameter, result, types, _calleeTyped, argumentsTyped, _bundle, _result⟩ :=
        CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
          compiler parent unique parentTyped
      obtain ⟨calleeReceipt⟩ : Nonempty (GeneralizedLocalNamedReadCompilation.Certificate
          prepared named source scope callee reasonAt compiler.calleeCode) := by
        cases fuel with
        | zero =>
          have impossible := compiler.calleeAccepted
          simp [SourceCoreFunctions.lowerExpressionWithPolicy] at impossible
        | succ fuel =>
          exact GeneralizedLocalNamedReadCompilation.of_policy compiled calleeObserved compiler.calleeAccepted
      obtain ⟨calleeRecipe⟩ := GeneralizedLocalNamedRecipeCompilation.of_certificate calleeRecipe calleeReceipt
      have calleeCertified : Tree compiled rootFuel source sourceContext reasonAt scope callee compiler.calleeCode :=
        .generalized calleeReceipt calleeRecipe
      obtain ⟨count, nodes, certified⟩ := child_certificates unique argumentsTyped compiler.argumentsAccepted
        (fun child member childNode lowered childFound childTyped childAccepted =>
          ih child member childFound childTyped childAccepted)
      refine .call compiler calleeReceipt calleeRecipe parent (CompatibleExpressionConstructors.sequence_of_nodes count nodes ?_) ?_
      · intro child lowered member
        exact ⟨rfl, List.mem_cons_of_mem _ member⟩
      · intro child lowered member
        rcases List.mem_cons.mp member with head | remaining
        · cases head; exact calleeCertified
        · exact certified child lowered remaining

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCollectors

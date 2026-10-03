import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionInstantiationLaws
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorMeaning

/-! Actual successful Functions lowering supplies recursive constructor
receipts; raw source typing supplies original payload types and closed
constructor validity. Child semantic evaluations are never premises. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
open Core Frontend SourceInference DataPatternValues
open CompatibleEncoding (bind_ok)

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

theorem constructor_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    {context : SourceCoreFunctions.Context} {values : ValuesContext} {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {node : ExpressionNode} {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .constructor instantiation ids)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) context source scope id reasonAt = .ok lowered) :
    ∃ tag header codes, lowered = ⟨.namedData tag.owner,
        SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩ ∧
      Header values source id node instantiation tag header codes ∧ ids.length = instantiation.payloadTypes.length ∧
      ListRel (Argument values (fun budget source scope id reasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy body budget context source scope id reasonAt)
        fuel source scope reasonAt) (ids.zip instantiation.payloadTypes) codes := by
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
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        simp only [read, form, leafPolicy] at accepted
        unfold SourceCoreCompatibleDataExpressions.leafLowerer at accepted
        simp only [read, bind, Except.bind, form] at accepted
        obtain ⟨tag, header, codes, codeEq, receipt, count, arguments⟩ := constructor_of_lower found form accepted
        refine ⟨tag, header, codes, codeEq, receipt, count, ?_⟩
        generalize inputsEq : ids.zip instantiation.payloadTypes = inputs at arguments ⊢
        clear codeEq receipt inputsEq
        induction arguments with
        | nil => exact .nil
        | cons head tail ih => exact .cons ⟨head.projected, by simpa only [Nat.min_self] using head.generated⟩ ih
  · simp [owner, bind, Except.bind] at accepted

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
    Nodes source ids types codes ∧ ∀ id code, (id, code) ∈ ids.zip codes →
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
    Nodes source ids types codes ∧ ∀ id code, (id, code) ∈ ids.zip codes →
      Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id code := by
  exact child_certificates unique typed generated extract

/-- Independent source instantiation validity is consumed at each stored
constructor occurrence; native representations do not supply this law. -/
theorem tree_of_functions_with_literals
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    (literals : GenericExpressionMeaning.Certificate)
    (literalFactory : CompatibleExpressionProducts.LiteralFactory policy body context values source scope reasonAt literals)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree.WithLiterals (fuel := readFuel) (values := values) (source := source)
      (context := sourceContext) (solved := context.solvedRequirements) (reasonAt := reasonAt) literals scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
  | fragment syntaxTree =>
    refine (fun ⟨tree, sites⟩ => ⟨_, Tree.LiteralSites.fragment tree sites⟩) (CompatibleExpressionConditionals.tree_of_functions_with_literals literals literalFactory unique declarations ?_ ?_ syntaxTree found typed accepted)
    · exact ⟨fun id child => policyFor.special id (.fragment child), fun id child => policyFor.read id (.fragment child), policyFor.lower, policyFor.leaf⟩
    · exact fun id node child => coercions id node (.fragment child)
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

/-- Original tree-only API, projected from the single supported extraction. -/
theorem tree_of_functions_with_validity
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  exact (tree_of_functions_with_literals
    (fun _ id lowered => CompatibleExpressionLiterals.Certificate context.solvedRequirements source id lowered)
    CompatibleExpressionProducts.LiteralFactory.ordinary unique declarations constructorValid policyFor coercions syntaxTree found typed accepted).choose

/-- Compatibility with the former false residual scope. -/
theorem tree_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_functions_with_validity (policy := policy) (body := body) (readFuel := readFuel)
    (context := context) (values := values) (source := source) (scope := scope) (reasonAt := reasonAt)
    (sourceContext := sourceContext) (unique := unique) (declarations := declarations)
    (constructorValid := CompatibleExpressionInstantiationLaws.ConstructorLaw.of_closed closed residual)
    (policyFor := policyFor) (coercions := coercions) (id := id) (syntaxTree := syntaxTree) (node := node)
    (found := found) (typed := typed) (fuel := fuel) (lowered := lowered) (accepted := accepted)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors

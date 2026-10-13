import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedCallEvidence

/-! Actual named policy recipes retain declaration-call evidence hooks. Other
recursive forms keep their original native metadata restrictions. The compiler
step returns the same static receipt and original ordered child callbacks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (SupportedForm syntax_node contextual_same evidence_none)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt Supported Child)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named} {source : TypedSource}
  {directSites : DeclarationInstantiation → Prop}

/-- Only declaration calls may carry additional ordinary requirement IDs.
Their actual compiler branch authenticates every retained dictionary entry. -/
structure MetadataFor (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : Named) (source : TypedSource) (directSites : DeclarationInstantiation → Prop) : Prop where
  requirements : ∀ id, GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node →
    node.requirements = [] ∨ (∃ literal resolution, node.form = .integerLiteral literal resolution) ∨
      ∃ callee ids instantiation, node.form = .call callee ids (.declaration instantiation)
  coercions : ∀ id, GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node → node.coercions = []
  initializer : ∀ id, GeneralSyntax source id directSites →
    prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id, GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node → ∀ callee ids metadata,
      node.form = .call callee ids (.indirect metadata) → metadata.argumentCoercions = []
  localRead : ∀ id, GeneralSyntax source id directSites → ∀ node,
    source.lookupExpression? id = some node → ∀ name binder,
      node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = (context prepared named).owner ∧ binding.binder.id = binder)) = false

theorem MetadataFor.of_native
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor prepared named source directSites) :
    MetadataFor prepared named source directSites := by
  refine ⟨?_, metadata.coercions, metadata.initializer, metadata.arguments, metadata.localRead⟩
  intro id tree node found
  rcases metadata.requirements id tree node found with empty | literal
  · exact .inl empty
  · exact .inr (.inl literal)

theorem MetadataFor.non_direct_requirements (metadata : MetadataFor prepared named source directSites)
    {id : ExpressionId} (tree : GeneralSyntax source id directSites) (ordinary : tree.NonDirect)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    node.requirements = [] ∨ ∃ literal resolution, node.form = .integerLiteral literal resolution := by
  rcases metadata.requirements id tree node found with empty | literal | ⟨callee, ids, instantiation, form⟩
  · exact .inl empty
  · exact .inr literal
  · exact False.elim (ordinary node found callee ids instantiation form)

/-- The original contextual step agrees with the actual evidence lowerer at a
named declaration call. No second compiler policy is selected. -/
theorem direct_hook
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source directSites)
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower (context prepared named) child budget source scope id reasonAt) =
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) := by
  have same := contextual_same found (form ▸ SupportedForm.direct callee ids instantiation)
    (metadata.localRead id tree node found)
  rw [recipe.lowerSpecial]
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [same, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id tree, Option.filter_none]
  cases actual : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
  | error error => rfl
  | ok output => cases output <;> simp [form]

theorem special_none
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat)
    (metadata : MetadataFor prepared named source directSites)
    {id : ExpressionId} (tree : GeneralSyntax source id directSites) (ordinary : tree.NonDirect)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compilation rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  obtain ⟨node, found, supported⟩ := syntax_node tree
  have sameSource := contextual_same found supported (metadata.localRead id tree node found)
  have noEvidence := evidence_none prepared.base.sourceProgram
    ((representation prepared).atContext named.signature.key []).expressions.projectType
    named.specialized (context prepared named) child budget scope reasonAt
    (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) found supported
    (metadata.non_direct_requirements tree ordinary found) (metadata.coercions id tree node found)
    (metadata.arguments id tree node found)
    (fun callee ids instantiation form => False.elim (ordinary node found callee ids instantiation form))
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure,
    metadata.initializer id tree, Option.filter_none, noEvidence]
  generalize form : node.form = shape at supported
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | read name binder => simp only [metadata.localRead id tree node found name binder form, Bool.false_eq_true, ↓reduceIte]
  | index | unary | binary | conditional | group | constructor | direct | builtin => rfl
  | tuple => rfl
  | call => rfl

theorem read_policy
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source directSites)
    {id : ExpressionId} (tree : GeneralSyntax source id directSites) :
    policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  obtain ⟨node, found, supported⟩ := syntax_node tree
  have sameSource := contextual_same found supported (metadata.localRead id tree node found)
  rw [recipe.readExpression]
  simp only [sameSource, bind, Except.bind]
  rfl

/-- The authentic accepted expression either took the ordinary branch or
returned the exact code supplied by its evidence hook. -/
theorem accepted_direct_action
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (metadata : MetadataFor prepared named source directSites)
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : GeneralSyntax source id directSites)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      (context prepared named) source scope id reasonAt = .ok lowered) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) (Child policy body fuel (context prepared named))
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none ∨
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) (Child policy body fuel (context prepared named))
      (fuel + 1) source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok (some lowered) := by
  have owner : id.occurrence.owner = source.owner := by
    apply Classical.byContradiction
    intro mismatch
    simp [SourceCoreFunctions.lowerExpressionWithPolicy, mismatch, bind, Except.bind] at accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
  have hook := direct_hook recipe metadata tree found form
    (Child policy body fuel (context prepared named)) (fuel + 1) scope reasonAt
  cases selectedHook : policy.lowerSpecial? with
  | none =>
    simp only [selectedHook] at hook
    exact .inl hook.symm
  | some lower =>
    simp only [selectedHook] at hook accepted
    rw [hook] at accepted
    cases action : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
        ((representation prepared).atContext named.signature.key []).expressions.projectType
        named.specialized (context prepared named) (Child policy body fuel (context prepared named))
        (fuel + 1) source scope id reasonAt
        (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
    | error error => rw [action] at accepted; cases accepted
    | ok output =>
      cases output with
      | none => exact .inl rfl
      | some actual =>
        rw [action] at accepted
        cases Except.ok.inj accepted
        exact .inr rfl

theorem recipe_policy_for
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation prepared named diagnostics namedCode} {rootFuel : Nat}
    {policy : SourceCoreFunctions.Policy}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel policy)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [])
    (supported : ∀ instantiation, directSites instantiation → Supported (context prepared named).plan instantiation)
    (metadata : MetadataFor prepared named source directSites)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    StepPolicyFor policy (context prepared named) prepared.fuel
      (.initial checked) source scope reasonAt directSites := by
  constructor
  · intro id _ tree ordinary child budget
    rw [recipe.lowerSpecial]
    exact special_none compilation rootFuel metadata tree ordinary child budget scope reasonAt
  · intro id _ tree _
    exact read_policy recipe metadata tree
  · exact recipe.lowerRead
  · exact recipe.leafLowerer
  · intro body fuel id callee ids instantiation node lowered _ found form site children accepted
    have tree := GeneralSyntax.direct found form site children
    rcases accepted_direct_action recipe metadata tree found form accepted with bypass | authentic
    · obtain ⟨requirements, assumptions⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.evidence_none_direct found form bypass
      exact CallableIndexedOwnedPreparedStagedDirectCallCertificates.of_supported found form
        (supported instantiation site) (fun child budget => by
          exact (direct_hook recipe metadata tree found form child budget scope reasonAt).trans
            (CallableCallEvidenceCertificates.direct_bypass found form requirements
              (metadata.coercions id tree node found) assumptions))
        (read_policy recipe metadata tree) accepted
    · obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted found form authentic
      have projected := actual.suffix.outputProjection
      change SourceCoreCompatibleDataExpressions.projectType checked
        (.occurrence node.id.occurrence) node.type = .ok lowered.type at projected
      have actualPolicy : CallableCoercionExpressionCertificates.Direct prepared.base.sourceProgram
          ((representation prepared).atContext named.signature.key []).expressions.projectType
          named.specialized (context prepared named) (Child policy body fuel (context prepared named))
          (fuel + 1) source scope id callee ids instantiation reasonAt policy.callables node lowered := by
        rw [callables]
        exact actual
      exact CallableIndexedOwnedPreparedStagedDirectCallCertificates.of_evidence
        (supported instantiation site) (metadata.coercions id tree node found)
        (CompatibleExpressionReads.projectType_of_accepted projected) actualPolicy accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles

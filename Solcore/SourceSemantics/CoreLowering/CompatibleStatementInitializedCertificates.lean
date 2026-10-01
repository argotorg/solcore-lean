import Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitializedTree

/-! Static extraction follows the actual initialized-let branch. The accepted
initializer precedes its marked allocation; the tail scope receives the new
reference only after that initializer's successful result binder. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitialized
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource}
  {context nextContext finalContext : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}

/-- Actual successful lowering closes all allocator receipt obligations. The
remaining expression callbacks are static, separately discharged below. -/
theorem tree_of_flow
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext = context ∨ sourceContext = finalContext →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionConstructors.Syntax source id → source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionConstructors.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    {scope : Scope} {id : StatementId} {rest : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context nextContext finalContext id rest expected)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt true selfReason = .ok code) :
    Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
      scope id rest expected type code := by
  cases syntaxTree with
  | @initialized node binder initializer initializerNode found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact .initialized found form mono extended ordinary initializerFound sourceType
        (expressions context (.inl rfl) declarations initializerSyntax initializerFound typed generated)
        allocation annotation same
        (CompatibleStatementBindings.tree_of_flow readPolicy binderPolicy allocationPolicy (expressions finalContext (.inr rfl))
          remaining (CompatibleStatementBindings.scope_bind lowered.type declarations declaration extended) projection generatedBody)

/-- The production final-result wrapper preserves the extracted structure. -/
theorem tree_of_body
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext = context ∨ sourceContext = finalContext →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      CompatibleExpressionConstructors.Syntax source id → source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      CompatibleExpressionConstructors.Tree readFuel values source sourceContext solved reasonAt scope id lowered)
    {scope : Scope} {id : StatementId} {rest : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source context nextContext finalContext id rest expected)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext solved reasonAt
        scope id rest expected type flow := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  exact ⟨flow, rfl, tree_of_flow readPolicy binderPolicy allocationPolicy expressions syntaxTree declarations projection generated⟩

/-- Exact contextual expression compilation closes both initializer and tail
static callbacks at their respective source lexical contexts. -/
theorem tree_of_contextual_body
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : Option SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel : Nat} {scope : Scope}
    (ordinary : CompatibleExpressionConstructors.Ordinary source locals compilation.owner)
    (unique : NodeOccurrencesUnique source)
    (closed : ∀ sourceContext, sourceContext = context ∨ sourceContext = finalContext → sourceContext.typeVariables = [])
    (residual : ∀ sourceContext, sourceContext = context ∨ sourceContext = finalContext → sourceContext.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (representationBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    (lowerBinder : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals compilation.owner [])
    (sourceCells : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation native parent skipInitializer)
    {id : StatementId} {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (syntaxTree : Syntax source context nextContext finalContext id rest expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      Tree layouts owner active frame globals onError readFuel values source context nextContext finalContext compilation.solvedRequirements reasonAt
        scope id rest expected type flow := by
  apply tree_of_body readStatement ?_ sourceCells ?_ syntaxTree declarations projection accepted
  · intro scope binder mono
    simp only [lowerBinder, SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil,
      ↓reduceIte, representationBinder]
  · intro sourceContext reachable currentScope budget id node lowered currentDeclarations syntaxValue found typed generated
    rw [lowerExpression] at generated
    exact CompatibleExpressionConstructors.tree_of_contextual ordinary unique (closed _ reachable) (residual _ reachable) currentDeclarations
      syntaxValue found typed readExpression lowerRead leafLowerer generated
end Solcore.SourceSemantics.CoreLowering.CompatibleStatementInitialized

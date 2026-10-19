import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaGeneration
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes

/-! The actual generalized initializer compiles its finite candidate list in
order. This receipt retains every candidate and raw lambda, including repeated
native types; a later read uses the cumulative candidate key. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerCompilation
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism DataPatternValues
open GeneralizedLocalInstanceCompilation (Inputs)

structure Receipt (inputs : Inputs) (binding : Binding) (active : Substitution)
    (lowered : SourceCoreBasic.LoweredExpr) where
  closures : List Core.Expr
  generated : (binding.atContext active).mapM (GeneralizedLocalInstanceCompilation.compile inputs) = .ok closures
  rows : ListRel (fun candidate raw => Nonempty (GeneralizedLocalInstanceCompilation.Receipt inputs candidate raw))
    (binding.atContext active) closures
  emitted : lowered = ⟨binding.bundleType active, LanguageResult.success (ProductBundle.expression closures)⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) : ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ} {result : α}
    (accepted : action.mapError change = .ok result) : action = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

private theorem rows_of_mapM (inputs : Inputs) {candidates : List Instance} {closures : List Core.Expr}
    (accepted : candidates.mapM (GeneralizedLocalInstanceCompilation.compile inputs) = .ok closures) :
    ListRel (fun candidate raw => Nonempty (GeneralizedLocalInstanceCompilation.Receipt inputs candidate raw))
      candidates closures := by
  induction candidates generalizing closures with
  | nil => simp at accepted; subst closures; exact .nil
  | cons candidate tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨raw, compiled, accepted⟩ := bind_ok accepted
    obtain ⟨rest, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    exact .cons (GeneralizedLocalInstanceCompilation.of_accepted compiled) (ih remaining)

theorem of_accepted {inputs : Inputs} {binding : Binding} {active : Substitution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : lowerInitializer binding active (GeneralizedLocalInstanceCompilation.compile inputs) = .ok lowered) :
    Nonempty (Receipt inputs binding active lowered) := by
  unfold lowerInitializer at accepted
  obtain ⟨closures, generated, accepted⟩ := bind_ok accepted
  exact ⟨⟨closures, generated, rows_of_mapM inputs generated, (Except.ok.inj accepted).symm⟩⟩

/-- The callback inputs are the literal fields of the named compiler's
special branch, including the original root fuel and current child budget. -/
def namedInputs {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (rootFuel budget : Nat) (current : SourceCoreFunctions.Context)
    (scope : SourceCoreBasic.Scope) (id : ExpressionId) (reasonAt : ExpressionId → Word) : Inputs where
  program := prepared.base.sourceProgram
  representation := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
  signatures := prepared.base.sourceProgram.signatures
  locals := prepared.base.locals
  candidateParents := compiled.parents
  assignments := compiled.own.assignments
  diagnostics
  current
  native := prepared.base.callableContext
  parent := none
  budget
  fuel := rootFuel
  initializer := id
  scope
  reasonAt

/-- A reached initializer override returns the same binding and ordered
instance compilation receipts. No Source initializer evaluation is involved. -/
theorem of_named_special_output {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    {rootFuel budget : Nat} {current : SourceCoreFunctions.Context}
    {child : SourceCoreFunctions.ExpressionLowerer} {source : TypedSource} {scope : SourceCoreBasic.Scope}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId} {reasonAt : ExpressionId → Word} {initial : Binding}
    {output : Option SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (selected : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)) = some initial)
    (accepted : CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel current child budget
      source scope id reasonAt = .ok output) :
    ∃ binding lowered, output = some lowered ∧
      prepared.base.locals.binding current.owner initial.binder.id = .ok binding ∧
      Nonempty (Receipt (namedInputs compiled rootFuel budget current scope id reasonAt) binding [] lowered) := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special at accepted
  have unchanged : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram current.plan
      prepared.base.locals current.owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  rw [unchanged] at accepted
  simp only [bind, Except.bind, pure, Except.pure, found, selected, Option.filter_some,
    ne_eq, reduceCtorEq, not_false_eq_true, decide_true, ↓reduceIte] at accepted
  obtain ⟨binding, located, accepted⟩ := bind_ok accepted
  have located := mapError_ok located
  obtain ⟨actual, generated, accepted⟩ := bind_ok accepted
  have generated := mapError_ok generated
  exact ⟨binding, actual, (Except.ok.inj accepted).symm, located, of_accepted generated⟩

/-- Invert the original accepted expression at its actual compiler policy.
The generated initializer is the reached override, before ordinary lambda
formation could be selected. -/
theorem of_named_policy {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    {rootFuel fuel : Nat} {current : SourceCoreFunctions.Context}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    (recipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compiled rootFuel policy)
    {source : TypedSource} {scope : SourceCoreBasic.Scope}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId} {reasonAt : ExpressionId → Word} {initial : Binding}
    {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (selected : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)) = some initial)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      current source scope id reasonAt = .ok lowered) :
    ∃ binding, prepared.base.locals.binding current.owner initial.binder.id = .ok binding ∧
      Nonempty (Receipt (namedInputs compiled rootFuel (fuel + 1) current scope id reasonAt) binding [] lowered) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
  rw [recipe.lowerSpecial] at accepted
  obtain ⟨output, generated, accepted⟩ := bind_ok accepted
  obtain ⟨binding, actual, rfl, located, receipt⟩ :=
    of_named_special_output compiled found form selected generated
  have same : actual = lowered := Except.ok.inj accepted
  subst actual
  exact ⟨binding, located, receipt⟩

/-- The outer named expression uses this exact policy before any local read
has selected a generalized descriptor. -/
def namedPolicy {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (rootFuel : Nat) : SourceCoreFunctions.Policy :=
  let representation := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
  { representation.expressions with
    callables := SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder representation prepared.base.locals named.signature.key []
    readExpression := fun source id => do
      let viewed ← SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
        (CallableIndexedNamedGeneration.context prepared named).plan prepared.base.locals
        named.signature.key none source id
      representation.expressions.readExpression viewed id
    lowerSpecial? := some (CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel) }

def namedLowerBody {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) :=
  let representation := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
  SourceCoreGeneralFunctions.bodyLowererWithRepresentation representation
    named.specialized.function.solvedRequirements compiled.own.assignments diagnostics named.signature.key
    (SourceCoreGeneralFunctions.contextualBinder representation prepared.base.locals named.signature.key [])

theorem namedPolicy_recipe {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code) (rootFuel : Nat) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compiled rootFuel (namedPolicy compiled rootFuel) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem named_contextual {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    (fuel : Nat) (source : TypedSource) (scope : SourceCoreBasic.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) :
    SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
      prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
      diagnostics (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext
      none none (fuel + 1) source scope id reasonAt =
    SourceCoreFunctions.lowerExpressionWithPolicy (namedPolicy compiled fuel) (namedLowerBody compiled)
      (fuel + 1) (CallableIndexedNamedGeneration.context prepared named) source scope id reasonAt := by
  rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def]
  dsimp only
  change (SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key
    |>.mapError SourceCoreBasic.Error.callPreparation) >>= _ = _
  rw [record]
  rfl

/-- The accepted named compiler call yields its actual initialized bundle
without a separately selected expression policy. -/
theorem of_named_contextual {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreBasic.Scope}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {body : List StatementId} {reasonAt : ExpressionId → Word} {initial : Binding}
    {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .lambda parameters result body)
    (selected : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = some initial)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
      prepared.base.sourceProgram.signatures prepared.base.locals compiled.parents compiled.own.assignments
      diagnostics (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext
      none none fuel source scope id reasonAt = .ok lowered) :
    ∃ childFuel, fuel = childFuel + 1 ∧
      ∃ binding, prepared.base.locals.binding named.signature.key initial.binder.id = .ok binding ∧
        Nonempty (Receipt (namedInputs compiled childFuel fuel
          (CallableIndexedNamedGeneration.context prepared named) scope id reasonAt) binding [] lowered) := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  | succ fuel =>
    rw [named_contextual compiled record] at accepted
    have owner : id.occurrence.owner = source.owner := by
      by_cases same : id.occurrence.owner = source.owner
      · exact same
      · have rejected := accepted
        rw [SourceCoreFunctions.lowerExpressionWithPolicy] at rejected
        simp [same, throw, bind, Except.bind] at rejected
    obtain ⟨binding, located, receipt⟩ :=
      of_named_policy compiled (namedPolicy_recipe compiled fuel) owner found form selected accepted
    exact ⟨fuel, rfl, binding, located, receipt⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerCompilation

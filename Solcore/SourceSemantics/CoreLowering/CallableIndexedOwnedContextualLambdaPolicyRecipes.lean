import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaBodyRecipes

/-! The original outer contextual bind fixes the full policy and body recipe.
The same named Compilation witness remains inside Prop at the actual Code.
Compatible reads use prepared.fuel; the special callback keeps its original
root fuel when a nested child is compiled at a smaller budget.
No execution law or second accepted-policy selection is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- This is the actual original special callback, including its child budget cap. -/
def special
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat) :
    SourceCoreFunctions.Context → SourceCoreFunctions.ExpressionLowerer → Nat →
      TypedSource → SourceCoreLocalCell.Scope → ExpressionId → (ExpressionId → Word) →
      Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr) :=
  fun current child budget source scope id reasonAt => do
    let source ← SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      current.plan prepared.base.locals current.owner none source id
    let node ← match source.lookupExpression? id with
      | some node => pure node
      | none => throw (.missingExpression id)
    let onLocalError := fun (error : SourceCoreLocalPolymorphism.Error) => match error with
      | .metadata error => error
      | _ => SourceCoreBasic.Error.unsupportedExpression id node.form
    let initialized := prepared.base.locals.bindings.find? fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)
    if let some initialized := initialized.filter (fun _ => (none : Option ExpressionId) ≠ some id) then
      let binding ← (prepared.base.locals.binding current.owner initialized.binder.id).mapError onLocalError
      let lowered ← (SourceCoreLocalPolymorphism.lowerInitializer binding [] fun candidate => do
        let emission ← (SourceCoreLocalEvidence.prepareForEmission prepared.base.sourceProgram current.plan
          candidate none compilation.parents).mapError fun _ =>
            SourceCoreLocalPolymorphism.Error.initializerMetadataMismatch id
        let localPrepared := emission.prepared
        let childContext := { current with solvedRequirements := localPrepared.caller.function.solvedRequirements }
        let lowered ← (SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
          ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
          prepared.base.locals compilation.parents compilation.own.assignments diagnostics childContext
          prepared.base.callableContext (some localPrepared) (some id) (min budget rootFuel)
          localPrepared.source scope id reasonAt) |>.mapError SourceCoreLocalPolymorphism.Error.metadata
        (SourceCoreBasic.ensureType (.occurrence id.occurrence) candidate.type lowered.type)
          |>.mapError SourceCoreLocalPolymorphism.Error.metadata
        match lowered.expression with
        | .inRight .word closure => pure closure
        | _ => throw (.initializerMetadataMismatch id)).mapError onLocalError
      return some lowered
    let evidence ← SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized current child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [])
    if let some lowered := evidence then return some lowered
    match node.form with
    | .reference _ (.local binder) =>
      if prepared.base.locals.bindings.any (fun binding =>
          decide (binding.caller = current.owner ∧ binding.binder.id = binder)) then
        let lowered ← (SourceCoreLocalPolymorphism.lowerRead prepared.base.locals current.owner []
          source scope id (reasonAt id)) |>.mapError onLocalError
        let viewed ← ((representation prepared).atContext named.signature.key []).localReadView
          current.owner [] source scope id lowered
        SourceCoreBasic.ensureType (.occurrence id.occurrence) lowered.type viewed.type
        return some viewed
      else return none
    | _ => return none

/-- Literal policy fields of the one outer-bind choice, at its original compilation. -/
structure PolicyRecipe
    (compilation : Compilation prepared named diagnostics namedCode)
    (rootFuel : Nat) (policy : SourceCoreFunctions.Policy) : Prop where
  readExpression : policy.readExpression = fun source id => do
    let viewed ← SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals (context prepared named).owner none source id
    ((representation prepared).atContext named.signature.key []).expressions.readExpression viewed id
  lowerSpecial : policy.lowerSpecial? = some (special compilation rootFuel)
  lowerRead : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead prepared.fuel
    (SourceCoreCompatibleValues.Context.initial checked)
  leafLowerer : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer
    (SourceCoreCompatibleValues.Context.initial checked)
  projectType : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked
  sourceCells : policy.sourceCells = some (allocator prepared named)

/-- The body and complete policy use one original compilation. The policy keeps
its own root fuel when the same callback compiles a child at a smaller budget. -/
def Retained (named : Named) (code : Code prepared function scope administrative) : Prop :=
  ∃ (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat),
    CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation code ∧
      PolicyRecipe compilation rootFuel code.policy ∧ code.compilation = context prepared named

/-- Retain only the actual witness passed by the producer. -/
theorem Retained.of_recipes
    (compilation : Compilation prepared named diagnostics namedCode)
    {code : Code prepared function scope administrative} {rootFuel : Nat}
    (body : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation code)
    (policy : PolicyRecipe compilation rootFuel code.policy)
    (sameCompilation : code.compilation = context prepared named) : Retained named code :=
  ⟨diagnostics, namedCode, compilation, rootFuel, body, policy, sameCompilation⟩

/-- Existing body-recipe consumers can forget the additional policy equations. -/
theorem Retained.body_recipe {code : Code prepared function scope administrative}
    (retained : Retained named code) :
    CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, body, _policy, _sameCompilation⟩ := retained
  exact CallableIndexedOwnedContextualLambdaBodyRecipes.Retained.of_recipe compilation body

/-- The compatible read profile is global and keeps the original prepared fuel. -/
theorem Retained.lowerRead {code : Code prepared function scope administrative}
    (retained : Retained named code) :
    code.policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead prepared.fuel
      (SourceCoreCompatibleValues.Context.initial checked) := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, _body, policy, _sameCompilation⟩ := retained
  exact policy.lowerRead

/-- The literal compatible leaf callback is retained without choosing another policy. -/
theorem Retained.leafLowerer {code : Code prepared function scope administrative}
    (retained : Retained named code) :
    code.policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer
      (SourceCoreCompatibleValues.Context.initial checked) := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, _body, policy, _sameCompilation⟩ := retained
  exact policy.leafLowerer

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes

import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCompilerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaJointStaticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralPlaceDiagnosticShells

/-! Static policies for the exact lambda Site under a real Named compilation.
The same producer applies to an ordinary caller and a selected method. The
original assignment table and issued place providers remain explicit compiler
identities. No Source syntax, body typing, or execution law is inferred here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSitePolicies
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedLiteralPlaceDiagnosticShells (PlaceReasonsEq)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compilation : Compilation compiled.indexed named diagnostics namedCode)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (site : Site compiled.indexed named parameters result statements sourceContext evidence [] scope administrative)

/-- Keep the actual body callback's allocator and solved requirement ledger. -/
def baseMatch : SourceCoreCompatibleDataMatches.Context :=
  ⟨.initial compiled.compatible.checked, (context compiled.indexed named).solvedRequirements,
    (bodyPolicy compilation site.code).sourceCells, none⟩

/-- Only the definition environment changes when matching under the indexed program. -/
def ambientMatch : SourceCoreCompatibleDataMatches.Context :=
  CompatibleMatchAmbientLowering.withDefinitions (baseMatch compilation site) compiled.indexed.layouts.definitions

theorem match_policy : CompatibleMatchAmbientLowering.PolicySuccess
    (bodyPolicy compilation site.code) (ambientMatch compilation site) := by
  apply CompatibleMatchAmbientLowering.PolicySuccess.extend
    (compilation := baseMatch compilation site)
  · rfl
  · exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

theorem match_values : (ambientMatch compilation site).values = .initial compiled.compatible.checked := rfl

theorem match_definitions : (ambientMatch compilation site).definitions = compiled.indexed.layouts.definitions := rfl

theorem read_policy : (bodyPolicy compilation site.code).readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := rfl

theorem binder_policy (binder : TypedBinder) (childScope : SourceCoreLocalCell.Scope)
    (monomorphic : binder.scheme.quantified = []) :
    (bodyPolicy compilation site.code).lowerBinder site.code.view childScope binder =
      SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked site.code.view childScope binder := by
  change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
  simp only [SourceCoreGeneralFunctions.contextualBinder, monomorphic, List.isEmpty_nil, ↓reduceIte]
  rfl

/-- The actual Site layout fixes the hidden physical frame slot. -/
theorem reference_index : site.code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  unfold Code.referenceIndex
  rw [site.compilation]
  rfl

section Allocation
variable {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- The original root callback and same Site receipt select one allocator. -/
theorem allocation_policy (samePolicy : site.code.policy = root.selected.policy) :
    (bodyPolicy compilation site.code).sourceCells = some
      (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
        compiled.indexed.base.globals.length
        (compiled.indexed.layouts.allocatorAt site.code.compilation.owner site.code.active site.code.allocationError)) := by
  have actual : (bodyPolicy compilation site.code).sourceCells = root.selected.policy.sourceCells := by
    rw [root.sourceCells]
    rfl
  exact actual.trans ((congrArg SourceCoreFunctions.Policy.sourceCells samePolicy).symm.trans
    site.code.allocationProfile)

theorem match_allocator (samePolicy : site.code.policy = root.selected.policy) :
    (ambientMatch compilation site).sourceCells = some
      (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
        compiled.indexed.base.globals.length
        (compiled.indexed.layouts.allocatorAt site.code.compilation.owner site.code.active site.code.allocationError)) :=
  allocation_policy compilation site root samePolicy
end Allocation

section Diagnostics
variable (issued : IssuedSource compiled site.code.compilation.owner (source named))

private theorem missing_policy
    (samePlaces : PlaceReasonsEq issued.diagnostics.program diagnostics) :
    issued.missingDefault = fun childSite root type =>
      diagnostics.placeReason (context compiled.indexed named).owner childSite root (some type) := by
  funext childSite root type
  change issued.diagnostics.program.placeReason site.code.compilation.owner childSite root (some type) = _
  rw [samePlaces.function_eq, site.compilation]

/-- The exact selected assignment row and place providers construct the body policy. -/
theorem assignment_policy
    (sameAssignments : issued.assignments = compilation.own.assignments)
    (samePlaces : PlaceReasonsEq issued.diagnostics.program diagnostics) :
    CompatibleAssignmentStatements.AssignmentPolicy (bodyPolicy compilation site.code)
      (.initial compiled.compatible.checked) issued.invalidProjection issued.invalidOperand issued.missingDefault := by
  have missing := missing_policy site issued samePlaces
  refine ⟨read_policy compilation site, ?_, ?_⟩
  · rw [missing]
    dsimp only [IssuedSource.invalidProjection, IssuedSource.invalidOperand]
    simp only [sameAssignments, samePlaces.function_eq, site.compilation]
    rfl
  · rw [missing]
    dsimp only [IssuedSource.invalidProjection, IssuedSource.invalidOperand]
    simp only [sameAssignments, samePlaces.function_eq, site.compilation]
    change some _ = some _
    apply congrArg some
    funext expression fuel childSource childScope childSite assignment operator rhs output next reasonAt
    cases operator <;> rfl

/-- Unary assignment keeps those same genuine issued tokens and preparation. -/
theorem unary_policy
    (sameAssignments : issued.assignments = compilation.own.assignments)
    (samePlaces : PlaceReasonsEq issued.diagnostics.program diagnostics) :
    CompatibleBitNotStatements.Policy (bodyPolicy compilation site.code)
      (.initial compiled.compatible.checked) issued.invalidProjection issued.invalidUnary issued.missingDefault := by
  have missing := missing_policy site issued samePlaces
  unfold CompatibleBitNotStatements.Policy
  rw [missing]
  dsimp only [IssuedSource.invalidProjection, IssuedSource.invalidUnary]
  simp only [sameAssignments, samePlaces.function_eq, site.compilation]
  rfl
end Diagnostics
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeSitePolicies

import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyBindings
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionBoundaryExclusion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedMethodAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinarySyntaxTable

/-! Selected method cache entries retain the same complete compiler action as
ordinary entries. These receipts use that action without an ordinary origin or
Header. Original method instantiation supplies Source typing separately. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyReceipts
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open AcceptedNamedExpressionFlow
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallablePreparedMethodSelection (Cached)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (cached : Cached compiled method.specialized)

abbrev source := CallableIndexedNamedGeneration.source cached.named
abbrev policy := CallablePreparedMethodRuntimeProfileFactory.policy cached.compilation
abbrev reasonAt := cached.diagnostics.reasonAt cached.named.signature.key
abbrev parameterScope := CallablePreparedMethodRuntimeProfileFactory.scope (named := cached.named)

abbrev BodyAt := Body (policy cached) compiled.indexed.fuel (source cached)
  (parameterScope cached) cached.compilation.statements cached.named.signature.resultType
  (reasonAt cached) cached.compilation.own.fellThroughReason
  cached.compilation.own.table.escapedReason cached.compilation.body

def invalidProjection (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  cached.diagnostics.placeReason cached.named.signature.key site root none

def invalidOperand (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (operator : Solcore.Syntax.ValueAssignOp) : Word :=
  if operator = .equal then Word.zero else cached.compilation.own.assignments.reasonAt site root (.value operator)

def invalidUnary (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  cached.compilation.own.assignments.reasonAt site root .bitNot

def missingDefault (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (type : TypeSystem.Ty) : Word :=
  cached.diagnostics.placeReason cached.named.signature.key site root (some type)

/-- These are the callbacks in the retained method compilation itself. -/
theorem assignments : CompatibleAssignmentStatements.AssignmentPolicy
    (policy cached) (.initial compiled.compatible.checked)
    (invalidProjection cached) (invalidOperand cached) (missingDefault cached) := by
  refine ⟨rfl, rfl, ?_⟩
  change some _ = some _
  apply congrArg some
  funext expression fuel source scope site assignment operator rhs output next reasonAt
  cases operator <;> rfl

/-- The unary callback uses the same retained method assignment table. -/
theorem unary : CompatibleBitNotStatements.Policy
    (policy cached) (.initial compiled.compatible.checked)
    (invalidProjection cached) (invalidUnary cached) (missingDefault cached) := rfl

theorem read : (policy cached).readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := rfl

/-- The selected method keeps its actual matcher and final native table. -/
def matchContext : SourceCoreCompatibleDataMatches.Context :=
  CompatibleMatchAmbientLowering.withDefinitions
    ⟨.initial compiled.compatible.checked, cached.named.specialized.function.solvedRequirements,
      some (CallableIndexedNamedGeneration.allocator compiled.indexed cached.named), none⟩
    compiled.indexed.layouts.definitions

theorem match_policy : CompatibleMatchAmbientLowering.PolicySuccess
    (policy cached) (matchContext cached) := by
  apply CompatibleMatchAmbientLowering.PolicySuccess.extend (by rfl)
  exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

/-- The exact accepted body is refined only through its actual assignment
callbacks. The result preserves code, source, roots, scopes and child budgets. -/
theorem of_cached : ∃ receipt : BodyAt cached, receipt.tree.Ready := by
  obtain ⟨body⟩ := body_of_accepted cached.compilation.bodyCompiled
  obtain ⟨tree, ready⟩ := body.tree.refine (assignments cached) (unary cached) (match_policy cached)
  exact ⟨⟨body.flow, tree, body.emitted⟩, ready⟩

/-- Full cached specialization authenticates the method policy at this child. -/
theorem policy_receipt {scope : SourceCoreLocalCell.Scope} {fuel : Nat}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (policy cached).lowerExpression fuel (source cached) scope id
      (reasonAt cached) = .ok lowered) :
    ∃ predecessor, fuel = predecessor + 1 ∧
      Nonempty (CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
        (compiled := compiled) cached.named cached.diagnostics cached.code cached.compilation
        predecessor (source cached) scope id (reasonAt cached) lowered) := by
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext cached.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    cached.compilation.parents cached.compilation.own.assignments cached.diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed cached.named)
    compiled.indexed.base.callableContext none none fuel (source cached) scope id
    (reasonAt cached) = .ok lowered at accepted
  cases fuel with
  | zero => rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted; cases accepted
  | succ predecessor =>
    exact ⟨predecessor, rfl,
      CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
        cached.compilation
        (CallableIndexedActualNamedSourceReceipts.cached_record compiled cached.selected cached.compilation.hook)
        accepted⟩

/-- Original finite form and reachability facts exclude boundaries of the
actual recursive child trace. No expression grammar or execution law is an input. -/
theorem child_syntax
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (forms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    {scope : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (policy cached).lowerExpression fuel (source cached) scope id
      (reasonAt cached) = .ok lowered) (present : reached id) :
    GeneralSyntax (source cached) id (DirectSite table.rows) := by
  obtain ⟨catalog⟩ := CallableIndexedOwnedPreparedOrdinaryCatalog.of_compiled compiled wellFormed
  obtain ⟨predecessor, _same, ⟨root⟩⟩ := policy_receipt cached accepted
  obtain ⟨trace⟩ := Trace.of_accepted (root := root) metadata
    (fun _ site => site.supported (table.aligned catalog)) covered root.selected.accepted
  cases trace.syntax_or_boundary covered with
  | inl grammar => exact grammar
  | inr residual =>
    obtain ⟨boundary⟩ := residual
    exact False.elim (boundary.impossible metadata forms initializers arguments present)

end Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyReceipts

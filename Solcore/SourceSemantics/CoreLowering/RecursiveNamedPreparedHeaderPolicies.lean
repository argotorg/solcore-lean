import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaders
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedSelectedExpressionFactory

/-! Static policies for the actual second-pass named body. The compiler keeps
its base-table matcher; successful matcher checking is transported to the final
native definitions before the single Tree extraction. Actual child typing is
never demanded under the base table. Source admission, diagnostic interpretation,
inventory completeness and runtime entry remain independent obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
open Core Frontend SourceInference RecursiveNamedCatalog
open RecursiveNamedPublicSpecializationMeaning
open RecursiveNamedPreparedHeaders
open CompatibleMatchAmbientLowering

private theorem automatic_signatures {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {fuel : Nat} {limits : SourceCoreRawMetadata.Limits} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel limits = .ok automatic) :
    automatic.checked.signatures = program.signatures := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := CompatibleEncoding.bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := CompatibleEncoding.bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · rename_i checked registered
    obtain ⟨prepared, _, accepted⟩ := CompatibleEncoding.bind_ok accepted
    cases accepted
    exact SourceCoreCompatibleCatalog.prepare_signatures registered

namespace Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)

/-- The exact base context used by the existing public named compiler. -/
def baseMatch : SourceCoreCompatibleDataMatches.Context :=
  ⟨.initial compiled.compatible.checked, prepared.named.specialized.function.solvedRequirements,
    some (CallableIndexedNamedGeneration.allocator compiled.indexed prepared.named), none⟩

/-- The same context with its actual final table. No code callback is changed. -/
abbrev ambientMatch : SourceCoreCompatibleDataMatches.Context :=
  withDefinitions (baseMatch prepared) compiled.indexed.layouts.definitions

theorem base_match_policy : (RecursiveNamedPreparedHeaders.Prepared.policy prepared).lowerMatch =
    some (SourceCoreCompatibleDataMatches.lowerWithReasons (baseMatch prepared)) := rfl

theorem match_success : PolicySuccess (RecursiveNamedPreparedHeaders.Prepared.policy prepared) (ambientMatch prepared) := by
  apply PolicySuccess.extend (base_match_policy prepared)
  exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

def invalidProjection (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  prepared.diagnostics.placeReason prepared.named.signature.key site root none

def invalidOperand (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (operator : Solcore.Syntax.ValueAssignOp) : Word :=
  if operator = .equal then Word.zero else prepared.compilation.own.assignments.reasonAt site root (.value operator)

def invalidUnary (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  prepared.compilation.own.assignments.reasonAt site root .bitNot

def missingDefault (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) (type : TypeSystem.Ty) : Word :=
  prepared.diagnostics.placeReason prepared.named.signature.key site root (some type)

theorem assignments : CompatibleAssignmentStatements.AssignmentPolicy
    (RecursiveNamedPreparedHeaders.Prepared.policy prepared) (.initial compiled.compatible.checked)
    (invalidProjection prepared) (invalidOperand prepared) (missingDefault prepared) := by
  refine ⟨rfl, rfl, ?_⟩
  change some _ = some _
  apply congrArg some
  funext expression fuel source scope site assignment operator rhs output next reasonAt
  cases operator <;> rfl

theorem unary : CompatibleBitNotStatements.Policy
    (RecursiveNamedPreparedHeaders.Prepared.policy prepared) (.initial compiled.compatible.checked)
    (invalidProjection prepared) (invalidUnary prepared) (missingDefault prepared) := rfl

variable {instantiation : DeclarationInstantiation}
  {header : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions
    (Program.ofChecked compiled.sourceProgram)}
  (atHeader : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include atHeader

theorem header_match : PolicySuccess header.policy (ambientMatch prepared) := by
  rw [atHeader.policy]
  exact match_success prepared

theorem header_read : header.policy.readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := by
  rw [atHeader.policy]
  rfl

theorem header_binder (scope : SourceCoreBasic.Scope) (binder : TypedBinder)
    (monomorphic : binder.scheme.quantified = []) :
    header.policy.lowerBinder header.function.source scope binder =
      SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked header.function.source scope binder := by
  rw [atHeader.policy]
  change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
  simp only [SourceCoreGeneralFunctions.contextualBinder, monomorphic, List.isEmpty_nil, ↓reduceIte]
  rfl

theorem header_allocator : header.policy.sourceCells = some
    (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)) := by
  rw [atHeader.policy, atHeader.globals, atHeader.layouts, atHeader.owner, atHeader.active, atHeader.onError]
  rfl

theorem match_allocator : (ambientMatch prepared).sourceCells = some
    (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame header.globals
      (header.layouts.allocatorAt header.owner header.active header.onError)) := by
  rw [atHeader.globals, atHeader.layouts, atHeader.owner, atHeader.active, atHeader.onError]
  rfl

omit atHeader in
theorem header_signatures : header.context.signatures = compiled.compatible.checked.signatures :=
  (RecursiveNamedSelectedExpressionFactory.header_program_signatures
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
    (program := Program.ofChecked compiled.sourceProgram) header).trans
    (automatic_signatures compiled.compatiblePrepared).symm

variable {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    compiled.indexed.layouts.definitions (Program.ofChecked compiled.sourceProgram)}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {administrative : Core.Context} {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}

/-- Materialize the actual compiler's static policy fields. Expression admission,
source Syntax and hidden-source freshness stay explicit. The returned match
certificate uses final definitions; actual native child contexts are unchanged. -/
def inputs_with (authenticated : Bool)
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source (invalidOperand prepared))
    (hidden : GenericImperativeMatch.MatchHiddenFresh header.function.source)
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = compiled.compatible.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
        (program := Program.ofChecked compiled.sourceProgram) (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = compiled.compatible.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
        (program := Program.ofChecked compiled.sourceProgram) (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType) :
    RecursiveNamedCatalogRuntimeProfileFactory.InputsWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram)
      authenticated tracked diagnosticPolicy headers header compilation expressionSyntax administrative where
  matchCompilation := ambientMatch prepared
  invalidProjection := invalidProjection prepared
  invalidOperand := invalidOperand prepared
  invalidUnary := invalidUnary prepared
  missingDefault := missingDefault prepared
  factory := factory
  matchPolicy := header_match prepared atHeader
  matchValues := rfl
  matchDefinitions := rfl
  matchAllocator := match_allocator prepared atHeader
  matchLedger := atHeader.solved.symm
  matchChildStatic := GenericImperativeMatch.MatchChildStatic.of_hidden
    (matchCompilation := ambientMatch prepared) (definitions := compiled.indexed.layouts.definitions)
    (administrative := administrative)
    (certificates := fun context => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
      (program := Program.ofChecked compiled.sourceProgram)
      (if authenticated then some header.function.evidence else none) headers compilation header.readFuel header.function.source context header.solved header.reasonAt) hidden
  readPolicy := header_read prepared atHeader
  binderPolicy := header_binder prepared atHeader
  allocationPolicy := header_allocator prepared atHeader
  expressions := expressions
  assignments := by rw [atHeader.policy]; exact assignments prepared
  unaryPolicy := by rw [atHeader.policy]; exact unary prepared
  assignmentExpressions := assignmentExpressions
  syntaxTree := syntaxTree
  sourceSignatures := header_signatures (header := header)
  declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
    (program := Program.ofChecked compiled.sourceProgram) header
  projection := atHeader.projection
  accepted := atHeader.accepted

def inputs
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy header.function.source (invalidOperand prepared))
    (hidden : GenericImperativeMatch.MatchHiddenFresh header.function.source)
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = compiled.compatible.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext → expressionSyntax id →
      header.function.source.lookupExpression? id = some node → ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
      RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
        (program := Program.ofChecked compiled.sourceProgram) headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
      sourceContext.signatures = compiled.compatible.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
      expressionSyntax id → ∀ node, header.function.source.lookupExpression? id = some node →
      ExpressionHasType header.function.source sourceContext id node.type →
      header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
        RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked) (prepared := compiled.indexed.ancestry)
        (program := Program.ofChecked compiled.sourceProgram) headers compilation header.readFuel header.function.source sourceContext header.solved header.reasonAt scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source expressionSyntax header.context
      (.statements true header.function.body) header.function.resultType) :
    RecursiveNamedCatalogRuntimeProfileFactory.Inputs
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram)
      tracked diagnosticPolicy headers header compilation expressionSyntax administrative :=
  inputs_with prepared atHeader false factory hidden expressions assignmentExpressions syntaxTree

end Prepared
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies

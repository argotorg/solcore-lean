import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
import Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementCertificates

/-! Each actual named or contextual body policy has the shared compatible
assignment callbacks, with the diagnostic words of its own fault tables. An
accepted value assignment is therefore the shared place lowering. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference
open CompatibleAssignmentStatements (AssignmentPolicy)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}

/-- The assignment fault table compiled with this body. -/
def Index.assignmentTable : Index compiled bodyRelation → SourceCoreAssignmentFaultSites.Table
  | .named receipt _ => receipt.own.assignments
  | .contextual material _ => material.inputs.assignments

/-- The place-fault program and owner used by this body's assignment callbacks. -/
def Index.placeDiagnostics : Index compiled bodyRelation → SourceCoreDataPlaceFaultSites.Program
  | @Index.named _ _ _ diagnostics _ _ _ => diagnostics
  | .contextual material _ => material.inputs.diagnostics

def Index.placeOwner : Index compiled bodyRelation → SourceSpecialization.SpecializationKey
  | @Index.named _ _ callable _ _ _ _ => callable.signature.key
  | .contextual material _ => material.inputs.current.owner

def Index.invalidProjection (index : Index compiled bodyRelation)
    (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  index.placeDiagnostics.placeReason index.placeOwner site root none

def Index.invalidOperand (index : Index compiled bodyRelation)
    (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) (operator : Syntax.ValueAssignOp) : Word :=
  if operator = .equal then Word.zero else index.assignmentTable.reasonAt site root (.value operator)

def Index.missingDefault (index : Index compiled bodyRelation)
    (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) (type : TypeSystem.Ty) : Word :=
  index.placeDiagnostics.placeReason index.placeOwner site root (some type)

theorem Index.assignment_policy (index : Index compiled bodyRelation) :
    AssignmentPolicy index.policy (.initial compiled.compatible.checked) index.invalidProjection
      index.invalidOperand index.missingDefault := by
  cases index with
  | named receipt selected =>
    refine ⟨rfl, rfl, ?_⟩
    change some _ = some _
    apply congrArg some
    funext expression fuel source scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl
  | contextual material view =>
    change AssignmentPolicy (GeneralizedLocalAcceptedBodyCompiler.policy material) _ _ _ _
    unfold GeneralizedLocalAcceptedBodyCompiler.policy GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    refine ⟨rfl, rfl, ?_⟩
    change some _ = some _
    apply congrArg some
    funext expression fuel source scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl

/-- An accepted value assignment is the shared place lowering at the initial
values context, with this body's diagnostic words. -/
theorem Index.assignment_lowered (index : Index compiled bodyRelation) {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {output : Ty} {next code : Expr} {reasonAt : ExpressionId → Word}
    (accepted : SourceCoreLoops.assignValue index.policy fuel source scope site assignment operator rhs
      output next reasonAt = .ok code) :
    SourceCoreCompatibleDataPlaces.lower (.initial compiled.compatible.checked)
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.signatures
      index.policy.lowerExpression fuel source scope site assignment operator (some rhs) output next reasonAt
      (index.invalidProjection site assignment.target.root) (index.invalidOperand site assignment.target.root operator)
      (index.missingDefault site assignment.target.root) = .ok code := by
  have matched := index.assignment_policy
  cases operator <;> simpa only [SourceCoreLoops.assignValue, matched.equal, matched.value] using accepted

def Index.invalidUnary (index : Index compiled bodyRelation)
    (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) : Word :=
  index.assignmentTable.reasonAt site root .bitNot

theorem Index.bitNot_policy (index : Index compiled bodyRelation) :
    CompatibleBitNotStatements.Policy index.policy (.initial compiled.compatible.checked) index.invalidProjection
      index.invalidUnary index.missingDefault := by
  cases index with
  | named receipt selected => rfl
  | contextual material view =>
    change CompatibleBitNotStatements.Policy (GeneralizedLocalAcceptedBodyCompiler.policy material) _ _ _ _
    unfold GeneralizedLocalAcceptedBodyCompiler.policy GeneralizedLocalLambdaCompilation.representation
    rw [material.indexed.represented]
    rfl

/-- An accepted bit-not update is the shared absent-operand place lowering. -/
theorem Index.bitNot_lowered (index : Index compiled bodyRelation) {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {output : Ty} {next code : Expr} {reasonAt : ExpressionId → Word}
    {callback : SourceCoreCompatibleDataPlaces.ExpressionLowerer → Nat → TypedSource → SourceCoreLocalCell.Scope →
      SourceCoreElaboration.ErrorSite → AssignmentResolution → Ty → Expr →
      (ExpressionId → Word) → Except SourceCoreBasic.Error Expr}
    (selected : index.policy.assignBitNotWithExpression = some callback)
    (accepted : callback index.policy.lowerExpression fuel source scope site assignment output next reasonAt = .ok code) :
    SourceCoreCompatibleDataPlaces.lower (.initial compiled.compatible.checked)
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).checked.signatures
      index.policy.lowerExpression fuel source scope site assignment .equal none output next reasonAt
      (index.invalidProjection site assignment.target.root) (index.invalidUnary site assignment.target.root)
      (index.missingDefault site assignment.target.root) = .ok code := by
  have same := Option.some.inj (selected.symm.trans index.bitNot_policy)
  subst same
  exact accepted

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation

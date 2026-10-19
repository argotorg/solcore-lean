import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionSyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission

/-! Successful finite metadata checking retains facts for each original supported
node before any recursive expression grammar has been constructed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionMetadata
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedNamedSyntaxAdmission
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

theorem at_of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {source : TypedSource}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : metadata? prepared named source directSites = some receipt)
    {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (supported : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.SupportedForm node.form) :
    MetadataTest prepared named node := by
  unfold metadata? at accepted
  simp only [bind, Option.bind] at accepted
  split at accepted
  next => contradiction
  next facts selected =>
    exact facts.down _ (lookupExpression?_sound found).1 node rfl (by
      generalize shape : node.form = original at supported ⊢
      cases supported with
      | literal atomic => cases atomic <;> rfl
      | proxy | read | unary | binary | index | conditional | group | tuple | constructor | builtin | direct | call => rfl)


theorem indirect_of_accepted {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {source : TypedSource}
    {directSites : DeclarationInstantiation → Prop}
    {receipt : PLift (MetadataFor prepared named source directSites)}
    (accepted : metadata? prepared named source directSites = some receipt)
    {id : ExpressionId} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    {callee : ExpressionId} {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    (form : node.form = .call callee arguments (.indirect metadata)) :
    MetadataTest prepared named node := by
  exact at_of_accepted accepted found (form ▸ .call callee arguments metadata)

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionMetadata

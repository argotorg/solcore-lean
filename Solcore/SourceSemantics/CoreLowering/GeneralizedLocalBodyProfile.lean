import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryExpressionProfile
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaCompilation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts

/-! Bounded instance bodies retain their actual source lambda and terminal
ordinary expression tree. This finite profile contains no body execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfile
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal)

structure Profile (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (initializer : ExpressionId) where
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  found : source.lookupExpression? initializer = some node
  form : node.form = .lambda parameters result body
  expression : ExpressionId
  terminal : Terminal source expression body
  expressionSite : GeneralizedLocalOrdinaryExpressionProfile.Site locals owner source expression
  expressionTree : GeneralizedLocalOrdinaryExpressionProfile.Tree locals owner source expression

private def terminal? (source : TypedSource) (body : List StatementId) :
    Option (Sigma fun expression => PLift (Terminal source expression body)) :=
  match body with
  | [] => none
  | id :: rest =>
    match found : source.lookupStatement? id with
    | none => none
    | some node => match form : node.form with
      | .returnStmt (some expression) => some ⟨expression, ⟨.returning rest found form⟩⟩
      | .expression expression false =>
        match rest with
        | [] => some ⟨expression, ⟨.tail found form⟩⟩
        | _ :: _ => none
      | _ => none

def profile? (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (initializer : ExpressionId) :
    Option (Profile locals owner source initializer) :=
  match found : source.lookupExpression? initializer with
  | none => none
  | some node => match form : node.form with
    | .lambda parameters result body => do
      let ⟨expression, ⟨terminal⟩⟩ ← terminal? source body
      let site ← GeneralizedLocalOrdinaryExpressionProfile.site? locals owner source expression
      let ⟨tree⟩ ← GeneralizedLocalOrdinaryExpressionProfile.tree? locals owner source (source.nodes.length + 1) expression
      pure ⟨node, parameters, result, body, found, form, expression, terminal, site, tree⟩
    | _ => none

/-- The same source occurrence fixes the actual emitted lambda's body. -/
theorem Profile.packet_terminal {inputs : GeneralizedLocalInstanceCompilation.Inputs}
    {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw)
    (profile : Profile inputs.locals inputs.current.owner packet.original.emission.prepared.source inputs.initializer) :
    Terminal packet.original.emission.prepared.source profile.expression packet.statements := by
  have nodeEq := Option.some.inj (profile.found.symm.trans packet.found)
  have bodyEq := (ExpressionForm.lambda.inj (profile.form.symm.trans
    ((congrArg ExpressionNode.form nodeEq).trans packet.form))).2.2
  exact bodyEq ▸ profile.terminal

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfile

import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryExpressionProfile
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaCompilation
import Solcore.SourceSemantics.CoreLowering.CellAwareOrdinaryBodySyntax

/-! Materialized ordinary bodies reuse the common finite statement scanner.
The profile retains the original lambda and every expression-tree receipt.
Ordinary declarations, scoped blocks and conditionals are scanned structurally;
assignments, nested generalized declarations and loops are outside this finite lexical grammar. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyProfile
open Core Frontend SourceInference

abbrev Approved (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceCoreLocalPolymorphism.Key)
    (source : TypedSource) (id : ExpressionId) : Prop :=
  GeneralizedLocalOrdinaryExpressionProfile.Tree locals owner source id

structure Profile (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (initializer : ExpressionId) where
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  body : List StatementId
  found : source.lookupExpression? initializer = some node
  form : node.form = .lambda parameters result body
  scan : ScopedSourceBodyAdmission.Scan source (Approved locals owner source) result true body
  lexical : CellAwareOrdinaryBodySyntax.lexicalOnly source (source.nodes.length + 1) body = true

def profile? (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (initializer : ExpressionId) :
    Option (Profile locals owner source initializer) :=
  match found : source.lookupExpression? initializer with
  | none => none
  | some node => match form : node.form with
    | .lambda parameters result body => do
      let ⟨scan⟩ ← ScopedSourceBodyAdmission.scan? source
        (fun id => GeneralizedLocalOrdinaryExpressionProfile.tree? locals owner source (source.nodes.length + 1) id)
        result (source.nodes.length + 1) true body
      if lexical : CellAwareOrdinaryBodySyntax.lexicalOnly source (source.nodes.length + 1) body = true then
        pure ⟨node,parameters,result,body,found,form,scan,lexical⟩
      else none
    | _ => none

theorem Profile.packet_body {inputs : GeneralizedLocalInstanceCompilation.Inputs}
    {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw)
    (profile : Profile inputs.locals inputs.current.owner packet.original.emission.prepared.source inputs.initializer) :
    profile.parameters = packet.parameters ∧ profile.result = packet.result ∧ profile.body = packet.statements := by
  have same := Option.some.inj (profile.found.symm.trans packet.found)
  exact ExpressionForm.lambda.inj (profile.form.symm.trans ((congrArg ExpressionNode.form same).trans packet.form))

theorem Profile.packet_scan {inputs : GeneralizedLocalInstanceCompilation.Inputs}
    {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw)
    (profile : Profile inputs.locals inputs.current.owner packet.original.emission.prepared.source inputs.initializer) :
    ScopedSourceBodyAdmission.Scan packet.original.emission.prepared.source
      (Approved inputs.locals inputs.current.owner packet.original.emission.prepared.source)
      packet.result true packet.statements := by
  obtain ⟨_,result,body⟩ := profile.packet_body packet
  simpa only [result,body] using profile.scan

theorem Profile.packet_lexical {inputs : GeneralizedLocalInstanceCompilation.Inputs}
    {candidate : SourceCoreLocalPolymorphism.Instance} {raw : Expr}
    (packet : GeneralizedLocalLambdaCompilation.Packet inputs candidate raw)
    (profile : Profile inputs.locals inputs.current.owner packet.original.emission.prepared.source inputs.initializer) :
    CellAwareOrdinaryBodySyntax.lexicalOnly packet.original.emission.prepared.source
      (packet.original.emission.prepared.source.nodes.length + 1) packet.statements = true := by
  obtain ⟨_,_,body⟩ := profile.packet_body packet
  simpa only [body] using profile.lexical

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyProfile

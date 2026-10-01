import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorCertificates

/-! Recursive constructor trees retain original payload type metadata. Their
children are certified existing expressions or further constructors. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
open Core Frontend SourceInference DataPatternValues

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | fragment {id} (tree : CompatibleExpressionConditionals.Syntax source id) : Syntax source id
  | constructor {id node instantiation ids} (found : source.lookupExpression? id = some node)
      (form : node.form = .constructor instantiation ids)
      (children : ∀ child, child ∈ ids → Syntax source child) : Syntax source id

def Nodes (source : TypedSource) (ids : List ExpressionId) (types : List TypeSystem.Ty)
    (codes : List SourceCoreBasic.LoweredExpr) : Prop :=
  ListRel (fun (id, type) (_ : SourceCoreBasic.LoweredExpr) =>
    ∃ node, source.lookupExpression? id = some node ∧ node.type = type) (ids.zip types) codes

theorem sequence_of_nodes {source : TypedSource} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate}
    (count : ids.length = types.length) (nodes : Nodes source ids types codes)
    (children : ∀ id code, (id, code) ∈ ids.zip codes → certificate scope id code) :
    DataExpressionSequence.Tree source certificate scope ids types codes := by
  induction ids generalizing types codes with
  | nil => cases types with
    | nil => cases nodes; exact .nil
    | cons => cases count
  | cons id ids ih => cases types with
    | nil => cases count
    | cons type types =>
      cases nodes with
      | @cons _ _ code codes head tail =>
        obtain ⟨node, found, same⟩ := head
        have child := children id code (by simp)
        have rest := ih (Nat.succ.inj count) tail (fun id code member => children id code (by simp [member]))
        subst type
        cases rest with
        | nil => exact .single found child
        | single f g => exact .cons found child (.single f g)
        | cons f g rest => exact .cons found child (.cons f g rest)

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | fragment {id lowered}
      (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | constructor {id node instantiation ids tag header codes}
      (receipt : Header values source id node instantiation tag header codes)
      (form : node.form = .constructor instantiation ids)
      (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
      (count : ids.length = instantiation.payloadTypes.length)
      (nodes : Nodes source ids instantiation.payloadTypes codes)
      (children : ∀ child code, (child, code) ∈ ids.zip codes →
        Tree fuel values source context solved reasonAt scope child code) :
      Tree fuel values source context solved reasonAt scope id
        ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors

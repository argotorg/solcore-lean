import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralMeaning

/-! Original expression typing and the actual covering dictionary supply a
numeric leaf's evidence. The Source ledger may retain an assumption that the
compiler replaced with an authenticated implementation. No equality between
those complete ledgers is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedLiteralEvidence
open Frontend SourceInference CompatibleExpressionLiterals

theorem of_typed {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    {evidence : Dynamic.EvidenceEnvironment}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type)
    (idsUnique : RequirementIdsUnique context)
    (covers : evidence.Covers context) : NumericEvidence context evidence node := by
  intro literal resolution form
  cases typed with
  | intro contains raw _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    rw [form] at raw
    cases raw with
    | integerLiteral valid =>
      have proves : RequirementProves context resolution.requirement resolution.predicate := by
        cases valid with
        | word _ _ proves | integer _ _ proves => exact proves
      obtain ⟨closed, produced⟩ := Dynamic.RequirementProves.produces_of_covers covers proves
      exact ⟨proves, produced.excludes_unavailable idsUnique⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedLiteralEvidence

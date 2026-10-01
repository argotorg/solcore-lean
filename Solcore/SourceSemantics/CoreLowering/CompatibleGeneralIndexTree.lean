import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndexTerminal

/-! General mapping index chains over the full existing typed expression
fragment. Static receipts retain raw mapping types and the actual comparator;
compound keys require no additional runtime operation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex
open Core Frontend SourceInference
open CompatibleExpressionIndices (Header)
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | fragment {id} (tree : CompatibleExpressionTyped.Syntax source id) : Syntax source id
  | index {id node base key keyNode} (found : source.lookupExpression? id = some node)
      (form : node.form = .index base key) (keyFound : source.lookupExpression? key = some keyNode)
      (first : Syntax source base) (second : Syntax source key) : Syntax source id

inductive Tree (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | fragment {id lowered}
      (tree : CompatibleExpressionTyped.Tree fuel values source context solved reasonAt scope id lowered) :
      Tree fuel values source context solved reasonAt scope id lowered
  | index {id node base key baseNode keyNode layout comparison first second}
      (header : Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (firstTree : Tree fuel values source context solved reasonAt scope base first)
      (secondTree : Tree fuel values source context solved reasonAt scope key second) :
      Tree fuel values source context solved reasonAt scope id
        ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleGeneralIndex

import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinMeaning

/-! A recursive expression grammar with an open static call-head interface.
Each node retains a finite list of child compiler results. The children are
recursively certified at every ordinary data, control, index and argument
position; a call head contains static source/compiled receipts only.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls
open Core Frontend SourceInference CompatibleExpressionPrimitives
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev CallHeads := GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate

def Entries (scope : Scope) (entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)) :
    GenericExpressionMeaning.Certificate := fun current id code => current = scope ∧ (id, code) ∈ entries

inductive Head (calls : CallHeads) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (reasonAt : ExpressionId → Word)
    (children : GenericExpressionMeaning.Certificate) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | primitive {id code} (head : CompatibleExpressionTypedCompositions.Head values.checked source children scope id code) :
      Head calls values source context reasonAt children scope id code
  | constructor {id node instantiation ids tag header codes}
      (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
      (form : node.form = .constructor instantiation ids)
      (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
      (sequence : DataExpressionSequence.Tree source children scope ids instantiation.payloadTypes codes) :
      Head calls values source context reasonAt children scope id
        ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩
  | member {id node base baseNode name index identity branches result child}
      (metadata : Metadata values.checked source id node result)
      (baseMetadata : Metadata values.checked source base baseNode child.type)
      (form : node.form = .member base name index)
      (layout : CompatibleExpressionMembers.Layout values.checked (.occurrence id.occurrence) baseNode.type node.type index identity branches result)
      (certified : children scope base child) :
      Head calls values source context reasonAt children scope id
        ⟨result, SourceCoreDataExpressions.member identity result branches child.expression⟩
  | index {id node base key baseNode keyNode layout comparison first second}
      (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (baseCertified : children scope base first) (keyCertified : children scope key second) :
      Head calls values source context reasonAt children scope id
        ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression (reasonAt id)⟩
  | builtin {id code} (head : BuiltinCalls.Typed.Head values source children scope id code) :
      Head calls values source context reasonAt children scope id code
  | call {id code} (head : calls children scope id code) :
      Head calls values source context reasonAt children scope id code

inductive Tree (calls : CallHeads) (fuel : Nat) (values : ValuesContext) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | fragment {id lowered}
      (child : CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id lowered) :
      Tree calls fuel values source context solved reasonAt scope id lowered
  | node {id lowered entries}
      (head : Head calls values source context reasonAt (Entries scope entries) scope id lowered)
      (children : ∀ child code, (child, code) ∈ entries →
        Tree calls fuel values source context solved reasonAt scope child code) :
      Tree calls fuel values source context solved reasonAt scope id lowered

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls

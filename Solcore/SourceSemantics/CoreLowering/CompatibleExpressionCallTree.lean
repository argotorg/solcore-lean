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

variable {calls : CallHeads} {fuel : Nat} {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : Scope}

/-- Support follows the exact builtin fragment or the exact ordered child list.
It contains no called-body or runtime law. -/
inductive Tree.LiteralSites (literals : GenericExpressionMeaning.Certificate) :
    {id : ExpressionId} → {lowered : SourceCoreBasic.LoweredExpr} →
    Tree calls fuel values source context solved reasonAt scope id lowered → Prop where
  | fragment {id lowered}
      (child : CompatibleExpressionBuiltins.Tree fuel values source context solved reasonAt scope id lowered)
      (sites : child.LiteralSites literals) : LiteralSites literals (.fragment child)
  | node {id lowered entries}
      (head : Head calls values source context reasonAt (Entries scope entries) scope id lowered)
      (children : ∀ child code, (child, code) ∈ entries →
        Tree calls fuel values source context solved reasonAt scope child code)
      (sites : ∀ child code (member : (child, code) ∈ entries), LiteralSites literals (children child code member)) :
      LiteralSites literals (.node head children)

def Tree.WithLiterals (literals : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun current id lowered => ∃ tree : Tree calls fuel values source context solved reasonAt current id lowered,
    tree.LiteralSites literals

theorem Tree.literalSites {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree calls fuel values source context solved reasonAt scope id lowered) :
    tree.LiteralSites (fun _ id code => CompatibleExpressionLiterals.Certificate solved source id code) := by
  induction tree with
  | fragment child => exact .fragment child child.literalSites
  | node head children ih => exact .node head children ih

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCalls

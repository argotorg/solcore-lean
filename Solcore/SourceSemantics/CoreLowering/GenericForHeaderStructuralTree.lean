import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderStructuralElimination

/-! The actual structural receipt supplies the same-code success-prefix Tree.
Assignment and unary payloads are retained by the receipt and are consumed
separately by their actual fault and reflection endpoints. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader.Structural
open Core Frontend SourceInference
open TypedLexicalWhile (Scope ValuesContext)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {type : Ty}
  {continuation : SourceSemantics.Context → Scope → Expr → Prop}

/-- This finite builder consumes the existing eliminator at its actual code. -/
theorem tree_of_eliminates
    {AP : AssignmentPayload values source certificates administrative definitions} {UP : UnaryPayload}
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (receipt : Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (type := type) (continuation := continuation)
      AP UP context scope items code) :
    Nonempty (Tree layouts owner active frame globals onError values source certificates definitions administrative
      type continuation context scope items code) := by
  apply receipt (fun context scope items code => Nonempty (Tree layouts owner active frame globals onError values
    source certificates definitions administrative type continuation context scope items code))
  constructor
  · intro context scope code next
    exact ⟨.nil next⟩
  · intro context next scope binder rest body payload mono extended ordinary projected allocation annotation same child
    obtain ⟨tree⟩ := child
    exact ⟨.uninitialized mono extended ordinary projected allocation annotation same tree⟩
  · intro context next scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType initial allocation annotation same child
    obtain ⟨tree⟩ := child
    exact ⟨.initialized mono extended ordinary found sourceType initial allocation annotation same tree⟩
  · intro context scope expression expressionNode rest lowered body found value child
    obtain ⟨tree⟩ := child
    exact ⟨.discard found value tree⟩
  · intro context scope assignment operator rhs rest body head _receipt child
    obtain ⟨tree⟩ := child
    exact ⟨.assign head tree⟩
  · intro context scope assignment rest body head _receipt child
    obtain ⟨tree⟩ := child
    exact ⟨.bitNot head tree⟩
end Solcore.SourceSemantics.CoreLowering.GenericForHeader.Structural

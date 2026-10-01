import Solcore.SourceSemantics.CoreLowering.BuiltinBodySemanticReceipt
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinBodyTree
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping

/-! A real compiler-view certificate and canonical body semantics share the
same finished Core code. Local edit reachability transports independent static
syntax and the concrete builtin Tree; canonical compiler acceptance is neither
required nor manufactured. Lambda formation and runtime history remain in the
caller's separate code and capture receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSemanticReceipt
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

structure Receipt (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error) (readFuel : Nat) (values : SourceCoreCompatibleValues.Context)
    (source view : TypedSource) (context : SourceSemantics.Context) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty)
    (policy : SourceCoreLoops.Policy) (fuel : Nat) (fellThrough escaped : Word) (code : Expr) where private mk ::
  actual : BuiltinNamedBody.Certificate layouts owner active frame globals onError readFuel values view context solved reasonAt scope
    statements expected type policy fuel fellThrough escaped code
  canonical : BuiltinNamedBody.SemanticReceipt layouts owner active frame globals onError readFuel values source context solved reasonAt scope
    statements expected type fellThrough escaped code
  sameFlow : canonical.flow = actual.flow

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source view : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}

/-- The actual view acceptance is retained verbatim. Both canonical static
judgments are derived on the exact reached body, with no child meaning input. -/
def of_certificate {changed : List ExpressionId}
    (edited : LocalView source view changed)
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique source)
    (certificate : BuiltinNamedBody.Certificate layouts owner active frame globals onError readFuel values view context solved reasonAt scope
      statements expected type policy fuel fellThrough escaped code) :
    Receipt layouts owner active frame globals onError readFuel values source view context solved reasonAt scope
      statements expected type policy fuel fellThrough escaped code :=
  ⟨certificate,
    BuiltinNamedBody.SemanticReceipt.of_tree certificate.projection
      (CallableLambdaViewSourceTyping.body_syntax_original edited avoids unique certificate.syntaxTree)
      certificate.emitted
      (CallableLambdaViewBuiltinBodyTree.original edited avoids certificate.tree), rfl⟩

/-- This is the accepted equation at the actual compiler view. -/
theorem Receipt.accepted
    (receipt : Receipt layouts owner active frame globals onError readFuel values source view context solved reasonAt scope
      statements expected type policy fuel fellThrough escaped code) :
    SourceCoreLoops.lowerStatementsWithPolicy policy fuel view scope statements
      type reasonAt fellThrough escaped = .ok code :=
  receipt.actual.accepted

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSemanticReceipt

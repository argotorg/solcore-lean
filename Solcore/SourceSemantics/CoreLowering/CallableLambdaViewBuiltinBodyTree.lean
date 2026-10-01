import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBodyTree
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinTrees
import Solcore.SourceSemantics.CoreLowering.BuiltinLexicalStatements

/-! Concrete builtin lexical certificates across local lambda views.
The finite body keeps its source contexts, actual marker/snapshot allocator
receipts and exact Core code. Reached child transport is closed by the builtin
expression grammar, without a child execution or static transport premise.
Canonical source typing, syntax and compiler acceptance remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinBodyTree
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context}
  {source view : TypedSource} {changed : List ExpressionId}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

/-- Let, block, conditional, discard, return, tail and Unit certificates retain
exact code; the same ordered builtin child certificates hold at the view. -/
theorem body (edited : LocalView source view changed)
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source
      solved reasonAt context scope mode statements expected type code) :
    BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values view
      solved reasonAt context scope mode statements expected type code := by
  apply CallableLambdaViewBodyTree.body edited avoids ?_ tree
  intro context scope id lowered reached child
  exact CallableLambdaViewBuiltinTrees.builtins edited avoids child reached

/-- Recover the canonical body certificate from the actual compiler view.
Only the static Tree is recovered; no canonical typing or acceptance is asserted. -/
theorem original (edited : LocalView source view changed)
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (tree : BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values view
      solved reasonAt context scope mode statements expected type code) :
    BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source
      solved reasonAt context scope mode statements expected type code := by
  apply CallableLambdaViewBodyTree.original edited avoids ?_ tree
  intro context scope id lowered reached child
  exact CallableLambdaViewBuiltinTrees.builtins_original edited avoids child reached

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinBodyTree

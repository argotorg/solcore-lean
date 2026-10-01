import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementTree

/-! Static inversion of the seven administrative binders in actual compatible
assignment code. This removes syntax insertions, never captured runtime values. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperative.Native
open Core Frontend
open TypedLexicalWhile.Native

theorem execute_continuation {prepared : SourceCoreCompatibleDataPlaces.Prepared}
    {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {output result : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    {definitions : DataEnvironment} {context : Core.Context}
    (typed : HasType context
      (SourceCoreCompatibleDataPlaces.execute prepared reference keys rhs next output operator bitNot invalid)
      result definitions) : HasType context next result definitions := by
  cases typed with
  | letE reference first =>
    cases first with | caseE keys failure second =>
      cases second with | caseE snapshot failure third =>
        cases third with | caseE right failure fourth =>
          cases fourth with | caseE modified failure fifth =>
            cases fifth with | caseE updated failure last =>
              cases last with | letE written body =>
                exact remove_front (remove_front (remove_front (remove_front
                  (remove_front (remove_front (remove_front body))))))
end Solcore.SourceSemantics.CoreLowering.TypedImperative.Native

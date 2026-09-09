import Solcore.Frontend.LocalComputationFragment
import Solcore.Frontend.LocalComputationReturnTree
import Solcore.Resolved.LocalFragmentProperties

/-! Structural membership follows exact original lowering. Hidden discard
binders require closure of the entire mixed tail, including earlier weakenings. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationFragment.weakenAt {expr : Core.Expr}
    (fragment : LocalComputationFragment expr) (cutoff : Nat) :
    LocalComputationFragment (expr.weakenAt cutoff) := by
  induction fragment generalizing cutoff with
  | pure child => exact .pure (child.weakenAt cutoff)
  | application callee operand =>
      simp only [Core.Expr.weakenAt]
      exact .application (callee.weakenAt cutoff) (operand.weakenAt cutoff)
  | letE _ _ headIH tailIH =>
      simp only [Core.Expr.weakenAt]
      exact .letE (headIH cutoff) (tailIH (cutoff + 1))
  | ifE _ _ _ guardIH yesIH noIH =>
      simp only [Core.Expr.weakenAt]
      exact .ifE (guardIH cutoff) (yesIH cutoff) (noIH cutoff)

theorem LocalComputationElaborates.core_fragment
    {table : LocalNameTable} {context : Resolved.Context} {source : Syntax.Expr}
    {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationElaborates table context source core type) :
    LocalComputationFragment core := by
  cases elaboration with
  | pure _ lowered _ => exact .pure lowered.localFragment
  | application child =>
      cases child with
      | call _ callee _ _ operand _ => exact .application callee.localFragment operand.localFragment

theorem LocalComputationReturnTreeElaborates.core_fragment
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : LocalComputationReturnTreeElaborates types owner inputs body core type) :
    LocalComputationFragment core := by
  induction elaboration with
  | bare => exact .pure .unit
  | expression child => exact child.core_fragment
  | block _ ih => exact ih
  | binding _ _ child _ ih => exact .letE child.core_fragment ih
  | inferred _ child _ ih => exact .letE child.core_fragment ih
  | discard child _ ih => exact .letE child.core_fragment (ih.weakenAt 0)
  | conditional guard _ _ yesIH noIH => exact .ifE guard.core_fragment yesIH noIH

end Solcore.Frontend

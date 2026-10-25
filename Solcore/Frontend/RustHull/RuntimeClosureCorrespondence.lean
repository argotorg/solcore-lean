import Solcore.Frontend.RustHull.RuntimeFrameCorrespondence

/-! Runtime frame closures retain the environment at installation even when
called later from a different lexical environment. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution

inductive CapturedClosure : Core.Expr → Core.Environment → Core.Value → Prop where
  | lambda (parameter result : Core.Ty) (body : Core.Expr) (captured : Core.Environment) :
      CapturedClosure (.lambda parameter result body) captured (.closure parameter result body captured)

theorem CapturedClosure.evaluates {expression : Core.Expr} {captured : Core.Environment} {value : Core.Value}
    (related : CapturedClosure expression captured value) (store : Core.Store) :
    Core.Evaluates captured store expression value store := by cases related; exact .lambda

theorem frameUnpack_call_evaluates {slots : List (String × Core.Ty)} {values : List Core.Value}
    (length : values.length = slots.length) {environment captured : Core.Environment}
    {initial argumentsStore allocated final : Core.Store} {function argument body : Core.Expr}
    {closure result : Core.Value}
    (related : CapturedClosure (AccountRuntime.frameUnpack slots body) captured closure)
    (resolved : Core.Evaluates environment initial function closure argumentsStore)
    (supplied : Core.Evaluates environment argumentsStore argument (bundleValues values) allocated)
    (evaluated : Core.Evaluates (values.reverse ++ .unit :: bundleValues values :: captured)
      allocated body result final) :
    Core.Evaluates environment initial (.apply function argument) result final := by
  cases related
  apply Core.Evaluates.apply resolved supplied
  apply Core.Evaluates.letE .unit
  have unpacked := frameBindings_evaluate length (start := 0) (allValues := values)
    (by rfl : (Core.Value.unit :: bundleValues values :: captured)[1]? = some (bundleValues values))
    (fun index value found => by simpa only [Nat.zero_add] using found) evaluated
  simpa only [frameBindingCode, length] using unpacked

end Solcore.Frontend.RustHull.Correspondence

import Solcore.SourceSemantics.Staging.RecursiveScope

/-! Control transfers at a staged function boundary. Loop bodies retain their
transfers until the enclosing loop consumes them. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive.BodyOutcome

def NoEscapedControl (outcome : BodyOutcome) : Prop :=
  (∀ environment, outcome ≠ .breaking environment) ∧
  (∀ environment, outcome ≠ .continuing environment)

theorem NoEscapedControl.returned (value : Dynamic.Value) :
    NoEscapedControl (.returned value) := by
  constructor <;> intro other equal <;> cases equal

theorem NoEscapedControl.fault (failure : Failure) :
    NoEscapedControl (.fault failure) := by
  constructor <;> intro other equal <;> cases equal

theorem NoEscapedControl.fallthrough (environment : Dynamic.Environment) :
    NoEscapedControl (.fallthrough environment) := by
  constructor <;> intro other equal <;> cases equal

end Solcore.SourceSemantics.Staging.Recursive.BodyOutcome

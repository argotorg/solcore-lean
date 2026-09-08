import Solcore.Frontend.LocalInputs
import Solcore.Frontend.LocalExpressionTyping

/-! A proof-carrying input boundary for checked local expression execution.
Check failure is absent; fuel exhaustion retains its present stateful result. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

def check? (inputs : LocalInputs) (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  elaborateLocalExpression? inputs.names inputs.context source

/-- Execute the actual checked Core expression with its corresponding values.
No source-text parsing, external-value validation, or wire endpoint is added. -/
def run? (inputs : LocalInputs) (fuel : Nat) (source : Syntax.Expr) (store : Core.Store) :
    Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.check? source
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end Solcore.Frontend.LocalInputs

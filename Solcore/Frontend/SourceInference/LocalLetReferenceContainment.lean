import Solcore.Frontend.SourceInference.LocalReadScopeInference
import Solcore.Frontend.SourceInference.LocalGeneralizationRetiredInterval

/-! References to locals created and retired by an initializer already occur
before its enclosing let generalizes. The continuation is the actual successful
statement inference, not an assumed semantic body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceInference.LocalLetRequirementTiming.Receipt
open TypeSystem Detail LocalReadScopeProgress

variable {fuel : Nat} {context : Context} {statement : Syntax.Statement}
    {initial : State} {result : StatementResult}

theorem retired_absent (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) {retired : Resolved.LocalId}
    (created : initial.nextLocal ≤ retired.binderIndex)
    (retiredBeforeReturn : retired.binderIndex < receipt.ready.nextLocal) :
    Absent retired result.state.localBinders :=
  (receipt.retired_interval below).absent retired created retiredBeforeReturn

theorem retired_read_at_ready (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) {retired : Resolved.LocalId}
    (created : initial.nextLocal ≤ retired.binderIndex)
    (retiredBeforeReturn : retired.binderIndex < receipt.ready.nextLocal)
    {after : State} (continuation : Progress result.state after)
    {node : ExpressionNode} (member : .expression node ∈ after.nodes)
    {name : String} (form : node.form = .reference name (.local retired)) :
    ReadAt receipt.ready.nodes node.id retired :=
  ((receipt.retired_interval below).progress continuation).read created retiredBeforeReturn member form

/-- A real successful suffix cannot first introduce a reference to one of the
initializer's retired locals. Its original occurrence is already in Ready. -/
theorem statements_retired_read_at_ready (receipt : Receipt fuel context statement initial result)
    (below : initial.LocalBindersBelowNextLocal) {retired : Resolved.LocalId}
    (created : initial.nextLocal ≤ retired.binderIndex)
    (retiredBeforeReturn : retired.binderIndex < receipt.ready.nextLocal)
    {suffixFuel : Nat} {suffixContext : Context} {sourceStatements : List Syntax.Statement}
    {expected : Ty} {after : BlockResult}
    (accepted : inferStatementsFuel suffixFuel suffixContext sourceStatements expected result.state = .ok after)
    {node : ExpressionNode} (member : .expression node ∈ after.state.nodes)
    {name : String} (form : node.form = .reference name (.local retired)) :
    ReadAt receipt.ready.nodes node.id retired :=
  receipt.retired_read_at_ready below created retiredBeforeReturn
    (inferStatementsFuel_scope_progress accepted) member form

end Solcore.Frontend.SourceInference.LocalLetRequirementTiming.Receipt

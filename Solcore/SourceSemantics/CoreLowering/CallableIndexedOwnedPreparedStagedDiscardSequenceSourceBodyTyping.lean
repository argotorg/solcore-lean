import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability

/-! Original full body typing is threaded through every accepted semicolon
 discard prefix. Discards retain the same raw context and tail completeness;
 the actual terminal selects the declared raw result. Statement metadata is
 transported literally, and no expression type is transported through a view.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts (FlowReceipt)

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (same : node.form = form) :
    ∀ {other}, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj
    ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))
  cases nodeEq
  exact same

private theorem discard_typed {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression true)
    (typed : StatementHasType source control context id final facts) :
    ∃ type, final = context ∧
      facts = { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
      ExpressionHasType source context expression type := by
  have shape := @statement_shape _ _ _ _ unique contains form
  clear contains form
  cases typed <;> have actualForm := shape (by assumption) <;> simp_all
  exact ⟨_, by assumption⟩

/-- The actual typing cons supplies the tail at the same original context.
No target result equality or tail typing is assumed separately. -/
theorem discard_tail_typed {source : TypedSource}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {expression : ExpressionId} {expected : TypeSystem.Ty}
    {facts : BodyFacts}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression true) (nonempty : rest ≠ [])
    (typed : StatementsHaveType source { returnType := expected } context (id :: rest) final facts)
    (completes : BodyCompletes expected facts) :
    ∃ firstType tailFacts,
      ExpressionHasType source context expression firstType ∧
      StatementsHaveType source { returnType := expected } context rest final tailFacts ∧
      BodyCompletes expected tailFacts := by
  cases typed with
  | singleton first => exact False.elim (nonempty rfl)
  | @cons _ _ _ _ _ _ _ _ tailFacts first remaining =>
    obtain ⟨firstType, rfl, rfl, firstTyped⟩ := discard_typed unique contains form first
    have tailCompletes : BodyCompletes expected tailFacts := by
      simpa [BodyFacts.cons] using completes
    exact ⟨firstType, tailFacts, firstTyped, remaining, tailCompletes⟩

/-- Every recursive tail has a reached terminal statement, so it is nonempty. -/
theorem nonempty {policy : SourceCoreLoops.Policy} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {result : Ty} {reasonAt : ExpressionId → Word}
    {fellThrough escaped : Word} {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (receipt : FlowReceipt policy source scope result reasonAt fellThrough escaped fuel statements flow) :
    statements ≠ [] := by
  cases receipt with
  | terminal terminal generated => cases terminal.terminal <;> simp
  | discard found form first generated tail accepted => simp

private theorem reaches_mono {source : TypedSource} {left right : List NodeId} {id : NodeId}
    (subset : ∀ node, node ∈ left → node ∈ right)
    (reached : CallableLambdaBodyReachability.Reaches source left id) :
    CallableLambdaBodyReachability.Reaches source right id := by
  induction reached with
  | root member => exact .root (subset _ member)
  | expression parent found edge ih => exact .expression ih found edge
  | statement parent found edge ih => exact .statement ih found edge

/-- Original statement references authenticate every actual compiled child,
including ordered duplicate occurrences. This uses no expression type equality. -/
theorem children_reached {policy : SourceCoreLoops.Policy} {view : TypedSource}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
    {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (receipt : FlowReceipt policy view scope result reasonAt fellThrough escaped fuel statements flow)
    (metadata : LambdaMetadataViews.MetadataView source view) :
    ∀ expression child, receipt.Children expression child →
      CallableLambdaBodyReachability.Reaches source (statements.map NodeId.statement)
        (.expression expression) := by
  induction receipt with
  | terminal terminal generated =>
    intro expression child used
    rcases used with ⟨rfl, rfl⟩
    cases terminal.terminal with
    | returning rest found form =>
      exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])
    | tail found form =>
      exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])
  | discard found form first generated tail accepted ih =>
    intro expression child used
    rcases used with ⟨rfl, rfl⟩ | tailUsed
    · exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])
    · exact reaches_mono (by
        intro node member
        exact List.mem_cons_of_mem _ member) (ih expression child tailUsed)

/-- Every actual compiler child has its own stored original node and raw type.
The terminal result follows from complete body typing, not native projection. -/
theorem children_typed {policy : SourceCoreLoops.Policy} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {result : Ty} {reasonAt : ExpressionId → Word}
    {fellThrough escaped : Word} {fuel : Nat} {statements : List StatementId} {flow : Expr}
    {invocation : Staging.Recursive.Scope} {context final : SourceSemantics.Context}
    {expected : TypeSystem.Ty} {facts : BodyFacts}
    (receipt : FlowReceipt policy view scope result reasonAt fellThrough escaped fuel statements flow)
    (metadata : LambdaMetadataViews.MetadataView invocation.source view)
    (unique : NodeOccurrencesUnique invocation.source)
    (typed : StatementsHaveType invocation.source { returnType := expected }
      context statements final facts)
    (completes : BodyCompletes expected facts) :
    ∀ expression child, receipt.Children expression child →
      ∃ node, invocation.source.lookupExpression? expression = some node ∧
        ExpressionHasType invocation.source context expression node.type := by
  induction receipt generalizing final facts with
  | terminal terminal generated =>
    intro expression child used
    rcases used with ⟨rfl, rfl⟩
    obtain ⟨node, found, sameType, childTyped⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique
        (CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.source_head terminal metadata)
        typed completes
    exact ⟨node, found, childTyped⟩
  | discard found form first generated tail accepted ih =>
    obtain ⟨firstType, tailFacts, firstTyped, remaining, tailCompletes⟩ :=
      discard_tail_typed unique (lookupStatement?_sound (metadata.statement found))
        form (nonempty tail) typed completes
    intro expression child used
    rcases used with ⟨rfl, rfl⟩ | tailUsed
    · obtain ⟨node, contains, sameType⟩ := firstTyped.stored_type
      exact ⟨node, lookupExpression?_complete unique contains, sameType ▸ firstTyped⟩
    · exact ih remaining tailCompletes expression child tailUsed

/-- The actual closure frame and parameter extension manufacture complete
original typing before selecting any of the ordered compiler children. -/
theorem at_parameters {policy : SourceCoreLoops.Policy} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {result : Ty} {reasonAt : ExpressionId → Word}
    {fellThrough escaped : Word} {fuel : Nat} {statements : List StatementId} {flow : Expr}
    {program : Program} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {invocation : Staging.Recursive.Scope}
    (receipt : FlowReceipt policy view scope result reasonAt fellThrough escaped fuel statements flow)
    (metadata : LambdaMetadataViews.MetadataView invocation.source view)
    (frame : Dynamic.ClosureFrame program function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (source : invocation.source = function.source) (body : function.body = statements) :
    ∀ expression child, receipt.Children expression child →
      ∃ node, invocation.source.lookupExpression? expression = some node ∧
        ExpressionHasType invocation.source context expression node.type := by
  obtain ⟨final, facts, typed, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame extended
  have unique : NodeOccurrencesUnique invocation.source := by
    rw [source]
    exact frame.code.graph.nodeOccurrencesUnique
  rw [body, ← source] at typed
  exact children_typed receipt metadata unique typed completes

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping

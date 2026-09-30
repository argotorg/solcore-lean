import Solcore.SourceSemantics.CoreLowering.LoopFiniteComposition
import Solcore.SourceSemantics.CoreLowering.ScalarStatementViews

/-! Discharge the finite-loop body induction hypothesis for terminal bodies.
The code contains no generated closure, so its temporary lexical prefix can
be inserted exactly using the restricted expression-renaming theorem. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Internal

open Frontend Frontend.SourceInference TypeSystem LocalCell

private theorem shiftBody {code : Core.Expr} (restricted : Core.ReadOnly.Expression code)
    {environment : Core.Environment} {before after : Core.Store} {result : Core.Value}
    (evaluation : Core.Evaluates environment before code result after)
    (type : Core.Ty) (location : Core.Location) :
    Core.Evaluates (Core.LoopExecution.bodyEnvironment type location environment) before
      (Core.LoopExecution.bodyCode code) result after :=
  ((restricted.weakenAt 0).weakenAt 0).evaluation_weakenAt_zero
    ((restricted.weakenAt 0).evaluation_weakenAt_zero
      (restricted.evaluation_weakenAt_zero evaluation
        (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) location)) .unit) (.bool true)

theorem breaking_body_preserves
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {type : Core.Ty} {location : Core.Location} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node) (form : node.form = .breakStmt) :
    BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
      type location (id :: rest) (Core.LocalLoop.breaking type) := by
  intro mapping world heap after store finalContext outcome environments heaps actualTyped selfTyped execution
  rcases ScalarStatementViews.cons_view false unique contains (by simp) execution with
    ⟨_, _, _, head, _⟩ | ⟨head, _⟩
  · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head
    cases impossible
  · obtain ⟨rfl, rfl, rfl⟩ := ScalarStatementViews.breaking unique contains form head
    refine ⟨_, store, mapping, world, .breaking environment, ?_, heaps, .refl _, .refl _, .refl _ _⟩
    exact shiftBody (.inRight (.inRight (.inLeft .unit)))
      (Core.LocalLoop.breaking_evaluates type actual store) type location

theorem breaking_body_fault_preserves
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {type : Core.Ty} {location : Core.Location} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node) (form : node.form = .breakStmt) :
    BodyFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
      type location (id :: rest) (Core.LocalLoop.breaking type) reasonAt := by
  intro mapping world heap after store finalContext reason environments heaps actualTyped selfTyped execution
  rcases ScalarStatementViews.cons_fault_view false unique contains (by simp) execution with
    ⟨_, head⟩ | ⟨_, _, _, head, _⟩
  · exact False.elim (ScalarStatementViews.breaking_cannot_fault unique contains form head)
  · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head
    cases impossible

private theorem return_readOnly {type : Core.Ty} {value : Core.Expr}
    (restricted : Core.ReadOnly.Expression value) : Core.ReadOnly.Expression (Core.LocalLoop.returnValue type value) :=
  .caseE restricted (.inLeft .var) (.inRight (.inLeft (.inRight .var)))

theorem return_body_preserves
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {administrativeContext : Core.Context} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
    {type : Core.Ty} {location : Core.Location} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {reasonAt : ExpressionId → Core.Word} {expression : ExpressionId} {valueCode : Core.Expr} {depth : Nat}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt (some expression))
    (value : PrimitiveExpressions.Tree compilation source scope reasonAt expression type valueCode depth)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual) :
    BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
      type location (id :: rest) ((Core.LocalLoop.returnValue type valueCode).rename ξ) := by
  intro mapping world heap after store finalContext outcome environments heaps actualTyped selfTyped execution
  rcases ScalarStatementViews.cons_view false unique contains (by simp) execution with
    ⟨_, _, _, head, _⟩ | ⟨head, _⟩
  · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head
    cases impossible
  · obtain ⟨rfl, sourceValue, rfl, evaluated⟩ := ScalarStatementViews.returnValue unique contains form head
    obtain ⟨rfl, staged, rfl, typed, core⟩ := ScalarExpressionReflection.Primitive.source_success value unique environments heaps evaluated
    have restricted := return_readOnly (type := type) (GeneralExpressions.Primitive.readOnly value)
    have renamed := restricted.evaluation_rename (Core.LocalLoop.returnValue_success type core) agree
    exact ⟨_, store, mapping, world, .returned staged typed,
      shiftBody (restricted.rename ξ) renamed type location, heaps, .refl _, .refl _, .refl _ _⟩

theorem return_body_fault_preserves
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {administrativeContext : Core.Context} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
    {type : Core.Ty} {location : Core.Location} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {reasonAt : ExpressionId → Core.Word} {expression : ExpressionId} {valueCode : Core.Expr} {depth : Nat}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt (some expression))
    (value : PrimitiveExpressions.Tree compilation source scope reasonAt expression type valueCode depth)
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual) :
    BodyFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
      type location (id :: rest) ((Core.LocalLoop.returnValue type valueCode).rename ξ) reasonAt := by
  intro mapping world heap after store finalContext reason environments heaps actualTyped selfTyped execution
  rcases ScalarStatementViews.cons_fault_view false unique contains (by simp) execution with
    ⟨_, head⟩ | ⟨_, _, _, head, _⟩
  · have fault := ScalarStatementViews.returnValue_fault unique contains form head
    obtain ⟨rfl, site, sourceLocation, rfl, origin, core⟩ :=
      ScalarExpressionReflection.Primitive.source_fault value unique valid covers environments heaps fault
    have restricted := return_readOnly (type := type) (GeneralExpressions.Primitive.readOnly value)
    have renamed := restricted.evaluation_rename (Core.LocalLoop.returnValue_failure type core) agree
    exact ⟨_, store, mapping, world, .uninitialized site sourceLocation origin,
      shiftBody (restricted.rename ξ) renamed type location, heaps, .refl _, .refl _, .refl _ _⟩
  · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head
    cases impossible

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Internal

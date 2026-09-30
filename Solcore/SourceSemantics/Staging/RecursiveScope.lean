import Solcore.SourceSemantics.Staging.CallBoundary

/-! Independent invocation scopes for recursively staged traces. The scope
keeps the original caller marker/stage table and both declaration and local
substitutions. Selecting a closure's scope is a static provenance obligation.
It is not inferred from source/Core function typing. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference

structure Origin where
  declaration : Resolved.DeclarationId
  declarationSubstitution : TypeSystem.ParameterSubstitution
  localSubstitution : TypeSystem.Substitution

structure Scope where
  origin : Origin
  source : TypedSource
  owned : source.owner = origin.declaration
  context : Context
  evidence : Dynamic.EvidenceEnvironment
  guards : CallBoundary.Frame

/-- A profile supplies this relation from retained code/source receipts. It
may distinguish equal erased function types by their complete local context.
The fields constrain every selected body scope to the actual source closure. -/
structure Registry where
  Closure : Dynamic.Closure → Scope → Prop
  source : ∀ {function scope}, Closure function scope → scope.source = function.source
  context : ∀ {function scope}, Closure function scope → scope.context = function.context
  evidence : ∀ {function scope}, Closure function scope → scope.evidence = function.evidence

/-- Nested failures retain the original failing scope and occurrence. The
caller cannot relabel them with its own return marker or active substitution. -/
inductive Failure where
  | semantic (reason : Dynamic.SemanticFault)
  | stage (scope : Scope) (call : ExpressionId) (reason : CallGuard.Fault)

inductive Outcome where
  | value (value : Dynamic.Value)
  | fault (failure : Failure)

inductive ValuesOutcome where
  | values (values : List Dynamic.Value)
  | fault (failure : Failure)

inductive BodyOutcome where
  | fallthrough (environment : Dynamic.Environment)
  | returned (value : Dynamic.Value)
  | fault (failure : Failure)

/-- Exact uncoerced ordinary occurrence, independently of any compiler. -/
def Occurrence (scope : Scope) (id : ExpressionId) (form : ExpressionForm) : Prop :=
  ∃ node, ContainsExpression scope.source id node ∧ node.form = form ∧
    node.requirements = [] ∧ node.coercions = []

/-- Forms whose raw evaluation has no expression or callable-body child.
Their independent atomic Dynamic rules can be reused without bypassing a
nested stage guard. Output coercions are separately excluded. -/
inductive AtomicForm : ExpressionForm → Prop where
  | literal (value) : AtomicForm (.literal value)
  | integerLiteral (source resolution) : AtomicForm (.integerLiteral source resolution)
  | reference (name resolution) : AtomicForm (.reference name resolution)
  | lambda (parameters result body) : AtomicForm (.lambda parameters result body)
  | proxy (inner) : AtomicForm (.proxy inner)

end Solcore.SourceSemantics.Staging.Recursive

import Solcore.SourceSemantics.Dynamic.Value
import Solcore.SourceSemantics.Substitution
import Solcore.SourceSemantics.Binders
import Solcore.SourceSemantics.WellFormed

/-!
Materialization of one proof-facing generalized direct-lambda closure.

The principal carrier stores no dictionaries.  A use site supplies one
flexible substitution and the evidence assembled for that exact instance;
materialization then produces the ordinary closure consumed by the existing
call semantics.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend.SourceInference
open TypeSystem

namespace GeneralizedClosure

/-- Canonical principal descriptor captured from one direct-lambda local
initializer.  Evidence is intentionally absent: it is supplied only when a
particular use site materializes the descriptor. -/
def ofDirectLambda (context : Context) (source : TypedSource)
    (environment : Environment) (binder : TypedBinder)
    (initializer : ExpressionId) (parameters : List TypedBinder)
    (resultType : Ty) (body : List StatementId) : GeneralizedClosure := {
  binder
  initializer
  parameters
  resultType
  body
  source
  captured := environment
  definitionContext := context
}

@[simp] theorem ofDirectLambda_binder (context : Context) (source : TypedSource)
    (environment : Environment) (binder : TypedBinder)
    (initializer : ExpressionId) (parameters : List TypedBinder)
    (resultType : Ty) (body : List StatementId) :
    (ofDirectLambda context source environment binder initializer parameters
      resultType body).binder = binder :=
  rfl

@[simp] theorem ofDirectLambda_initializer (context : Context)
    (source : TypedSource) (environment : Environment) (binder : TypedBinder)
    (initializer : ExpressionId) (parameters : List TypedBinder)
    (resultType : Ty) (body : List StatementId) :
    (ofDirectLambda context source environment binder initializer parameters
      resultType body).initializer = initializer :=
  rfl

@[simp] theorem ofDirectLambda_source (context : Context) (source : TypedSource)
    (environment : Environment) (binder : TypedBinder)
    (initializer : ExpressionId) (parameters : List TypedBinder)
    (resultType : Ty) (body : List StatementId) :
    (ofDirectLambda context source environment binder initializer parameters
      resultType body).source = source :=
  rfl

@[simp] theorem ofDirectLambda_captured (context : Context)
    (source : TypedSource) (environment : Environment) (binder : TypedBinder)
    (initializer : ExpressionId) (parameters : List TypedBinder)
    (resultType : Ty) (body : List StatementId) :
    (ofDirectLambda context source environment binder initializer parameters
      resultType body).captured = environment :=
  rfl

@[simp] theorem ofDirectLambda_definitionContext (context : Context)
    (source : TypedSource) (environment : Environment) (binder : TypedBinder)
    (initializer : ExpressionId) (parameters : List TypedBinder)
    (resultType : Ty) (body : List StatementId) :
    (ofDirectLambda context source environment binder initializer parameters
      resultType body).definitionContext = context :=
  rfl

/-- Materialize a concrete ordinary closure for one generalized-local use.
The same substitution closes the lambda header, the retained source graph,
and the initializer context.  Statement identities, captured locations, and
the direct-lambda body spine remain unchanged. -/
def instantiate (function : GeneralizedClosure)
    (substitution : Substitution) (evidence : EvidenceEnvironment) : Closure := {
  parameters := function.parameters.map
    (TypedBinder.applySubstitution substitution)
  resultType := substitution.apply function.resultType
  body := function.body
  source := function.source.applySubstitution substitution
  captured := function.captured
  context := FlexibleSubstitution.closeContext substitution
    (localSchemeInitializerContext function.definitionContext function.binder)
  evidence
}

@[simp] theorem instantiate_parameters (function : GeneralizedClosure)
    (substitution : Substitution) (evidence : EvidenceEnvironment) :
    (function.instantiate substitution evidence).parameters =
      function.parameters.map (TypedBinder.applySubstitution substitution) :=
  rfl

@[simp] theorem instantiate_resultType (function : GeneralizedClosure)
    (substitution : Substitution) (evidence : EvidenceEnvironment) :
    (function.instantiate substitution evidence).resultType =
      substitution.apply function.resultType :=
  rfl

@[simp] theorem instantiate_body (function : GeneralizedClosure)
    (substitution : Substitution) (evidence : EvidenceEnvironment) :
    (function.instantiate substitution evidence).body = function.body :=
  rfl

@[simp] theorem instantiate_source (function : GeneralizedClosure)
    (substitution : Substitution) (evidence : EvidenceEnvironment) :
    (function.instantiate substitution evidence).source =
      function.source.applySubstitution substitution :=
  rfl

@[simp] theorem instantiate_captured (function : GeneralizedClosure)
    (substitution : Substitution) (evidence : EvidenceEnvironment) :
    (function.instantiate substitution evidence).captured = function.captured :=
  rfl

@[simp] theorem instantiate_context (function : GeneralizedClosure)
    (substitution : Substitution) (evidence : EvidenceEnvironment) :
    (function.instantiate substitution evidence).context =
      FlexibleSubstitution.closeContext substitution
        (localSchemeInitializerContext function.definitionContext
          function.binder) :=
  rfl

@[simp] theorem instantiate_evidence (function : GeneralizedClosure)
    (substitution : Substitution) (evidence : EvidenceEnvironment) :
    (function.instantiate substitution evidence).evidence = evidence :=
  rfl

end GeneralizedClosure

/-- One principal generalized closure is the exact descriptor captured from a
direct lambda initializer.  The retained occurrence has no initializer-level
requirements or output coercions: dictionaries and instantiation are deferred
to each local-reference use. -/
inductive GeneralizedClosureCaptures
    (context : Context) (source : TypedSource) (environment : Environment)
    (binder : TypedBinder) (initializer : ExpressionId) :
    GeneralizedClosure → Prop where
  | directLambda
      {node : ExpressionNode} {parameters : List TypedBinder}
      {resultType : Ty} {body : List StatementId}
      (contains : ContainsExpression source initializer node)
      (form_eq : node.form = .lambda parameters resultType body)
      (raw_type_eq : node.rawType = binder.scheme.body)
      (type_eq : node.type = binder.scheme.body)
      (requirements_empty : node.requirements = [])
      (coercions_empty : node.coercions = []) :
      GeneralizedClosureCaptures context source environment binder initializer
        (GeneralizedClosure.ofDirectLambda context source environment binder
          initializer parameters resultType body)

namespace GeneralizedClosureCaptures

/-- Invert a capture witness to the direct-lambda occurrence and the exact
canonical descriptor assembled from it. -/
theorem canonical
    {context : Context} {source : TypedSource} {environment : Environment}
    {binder : TypedBinder} {initializer : ExpressionId}
    {function : GeneralizedClosure}
    (captures : GeneralizedClosureCaptures context source environment binder
      initializer function) :
    ∃ node parameters resultType body,
      ContainsExpression source initializer node ∧
      node.form = .lambda parameters resultType body ∧
      node.rawType = binder.scheme.body ∧
      node.type = binder.scheme.body ∧
      node.requirements = [] ∧
      node.coercions = [] ∧
      function = GeneralizedClosure.ofDirectLambda context source environment
        binder initializer parameters resultType body := by
  cases captures with
  | directLambda contains form_eq raw_type_eq type_eq requirements_empty
      coercions_empty =>
      exact ⟨_, _, _, _, contains, form_eq, raw_type_eq, type_eq,
        requirements_empty, coercions_empty, rfl⟩

/-- The descriptor retains exactly the generalized binder supplied by the
binding occurrence. -/
@[simp] theorem binder_eq
    {context : Context} {source : TypedSource} {environment : Environment}
    {binder : TypedBinder} {initializer : ExpressionId}
    {function : GeneralizedClosure}
    (captures : GeneralizedClosureCaptures context source environment binder
      initializer function) :
    function.binder = binder := by
  cases captures
  rfl

/-- The descriptor retains the exact initializer identity. -/
@[simp] theorem initializer_eq
    {context : Context} {source : TypedSource} {environment : Environment}
    {binder : TypedBinder} {initializer : ExpressionId}
    {function : GeneralizedClosure}
    (captures : GeneralizedClosureCaptures context source environment binder
      initializer function) :
    function.initializer = initializer := by
  cases captures
  rfl

/-- The descriptor retains the source graph containing the lambda. -/
@[simp] theorem source_eq
    {context : Context} {source : TypedSource} {environment : Environment}
    {binder : TypedBinder} {initializer : ExpressionId}
    {function : GeneralizedClosure}
    (captures : GeneralizedClosureCaptures context source environment binder
      initializer function) :
    function.source = source := by
  cases captures
  rfl

/-- The descriptor captures the current runtime environment exactly. -/
@[simp] theorem captured_eq
    {context : Context} {source : TypedSource} {environment : Environment}
    {binder : TypedBinder} {initializer : ExpressionId}
    {function : GeneralizedClosure}
    (captures : GeneralizedClosureCaptures context source environment binder
      initializer function) :
    function.captured = environment := by
  cases captures
  rfl

/-- The descriptor records the lexical context at its definition site. -/
@[simp] theorem definitionContext_eq
    {context : Context} {source : TypedSource} {environment : Environment}
    {binder : TypedBinder} {initializer : ExpressionId}
    {function : GeneralizedClosure}
    (captures : GeneralizedClosureCaptures context source environment binder
      initializer function) :
    function.definitionContext = context := by
  cases captures
  rfl

/-- Capture inversion in the field-oriented form consumed by principal-code
typing. -/
theorem occurrence
    {context : Context} {source : TypedSource} {environment : Environment}
    {binder : TypedBinder} {initializer : ExpressionId}
    {function : GeneralizedClosure}
    (captures : GeneralizedClosureCaptures context source environment binder
      initializer function) :
    ∃ node,
      ContainsExpression function.source function.initializer node ∧
      node.form = .lambda function.parameters function.resultType
        function.body ∧
      node.rawType = function.binder.scheme.body ∧
      node.type = function.binder.scheme.body ∧
      node.requirements = [] ∧
      node.coercions = [] := by
  cases captures with
  | directLambda contains form_eq raw_type_eq type_eq requirements_empty
      coercions_empty =>
      exact ⟨_, contains, form_eq, raw_type_eq, type_eq, requirements_empty,
        coercions_empty⟩

end GeneralizedClosureCaptures

end Solcore.SourceSemantics.Dynamic

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

/-- Lexical extension changes only locals; these are the non-local fields used
by dynamic typing, evidence, and closure-code provenance.  The relation lives
with generalized closures because both evaluation and preservation need to
relate a definition site to a later materialization site. -/
structure RuntimeContextFields (source target : Context) : Prop where
  signatures : target.signatures = source.signatures
  currentDeclaration :
    target.currentDeclaration = source.currentDeclaration
  typeParameters : target.typeParameters = source.typeParameters
  typeVariables : target.typeVariables = source.typeVariables
  residualTypeVariables :
    target.residualTypeVariables = source.residualTypeVariables
  assumptions : target.assumptions = source.assumptions
  solvedRequirements :
    target.solvedRequirements = source.solvedRequirements

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

/-! ## Generalized-initializer runtime boundary -/

/-- Positive structural reasons why a generalized local initializer cannot
yet be retained as a principal direct-lambda closure.  Each constructor names
one concrete obstruction; failure to derive a successful evaluation is never
used as fault evidence. -/
inductive GeneralizedInitializerMalformed (source : TypedSource)
    (binder : TypedBinder) : Option ExpressionId → Prop where
  | noInitializer : GeneralizedInitializerMalformed source binder none
  | missing
      {initializer : ExpressionId}
      (lookup_eq : source.lookupExpression? initializer = none) :
      GeneralizedInitializerMalformed source binder (some initializer)
  | nonLambda
      {initializer : ExpressionId} {node : ExpressionNode}
      (lookup_eq : source.lookupExpression? initializer = some node)
      (form_ne : ∀ parameters resultType body,
        node.form ≠ .lambda parameters resultType body) :
      GeneralizedInitializerMalformed source binder (some initializer)
  | rawTypeMismatch
      {initializer : ExpressionId} {node : ExpressionNode}
      {parameters : List TypedBinder} {resultType : Ty}
      {body : List StatementId}
      (lookup_eq : source.lookupExpression? initializer = some node)
      (form_eq : node.form = .lambda parameters resultType body)
      (raw_type_ne : node.rawType ≠ binder.scheme.body) :
      GeneralizedInitializerMalformed source binder (some initializer)
  | typeMismatch
      {initializer : ExpressionId} {node : ExpressionNode}
      {parameters : List TypedBinder} {resultType : Ty}
      {body : List StatementId}
      (lookup_eq : source.lookupExpression? initializer = some node)
      (form_eq : node.form = .lambda parameters resultType body)
      (type_ne : node.type ≠ binder.scheme.body) :
      GeneralizedInitializerMalformed source binder (some initializer)
  | requirementsPresent
      {initializer : ExpressionId} {node : ExpressionNode}
      {parameters : List TypedBinder} {resultType : Ty}
      {body : List StatementId}
      (lookup_eq : source.lookupExpression? initializer = some node)
      (form_eq : node.form = .lambda parameters resultType body)
      (requirements_ne : node.requirements ≠ []) :
      GeneralizedInitializerMalformed source binder (some initializer)
  | coercionsPresent
      {initializer : ExpressionId} {node : ExpressionNode}
      {parameters : List TypedBinder} {resultType : Ty}
      {body : List StatementId}
      (lookup_eq : source.lookupExpression? initializer = some node)
      (form_eq : node.form = .lambda parameters resultType body)
      (coercions_ne : node.coercions ≠ []) :
      GeneralizedInitializerMalformed source binder (some initializer)

/-- A generalized initializer reaches the explicit unsupported-runtime
boundary only with a concrete malformed shape in an occurrence-unique source.
The uniqueness premise makes the classification deterministic even though the
declarative source carrier itself remains forgeable. -/
structure GeneralizedInitializerUnsupported (source : TypedSource)
    (binder : TypedBinder) (initializer : Option ExpressionId) : Prop where
  source_unique : NodeOccurrencesUnique source
  malformed : GeneralizedInitializerMalformed source binder initializer

namespace GeneralizedInitializerUnsupported

/-- Every initializer in an occurrence-unique source is either the canonical
direct-lambda capture currently supported by the runtime, or carries one of
the explicit unsupported-shape witnesses above. -/
theorem captures_or_unsupported
    (context : Context) (source : TypedSource) (environment : Environment)
    (binder : TypedBinder) (initializer : Option ExpressionId)
    (source_unique : NodeOccurrencesUnique source) :
    (∃ initializerId function,
      initializer = some initializerId ∧
      GeneralizedClosureCaptures context source environment binder
        initializerId function) ∨
    GeneralizedInitializerUnsupported source binder initializer := by
  cases initializer with
  | none => exact .inr ⟨source_unique, .noInitializer⟩
  | some initializer =>
      cases lookup_eq : source.lookupExpression? initializer with
      | none => exact .inr ⟨source_unique, .missing lookup_eq⟩
      | some node =>
          by_cases lambda_form : ∃ parameters resultType body,
              node.form = .lambda parameters resultType body
          · rcases lambda_form with ⟨parameters, resultType, body, form_eq⟩
            by_cases raw_type_eq : node.rawType = binder.scheme.body
            · by_cases type_eq : node.type = binder.scheme.body
              · by_cases requirements_empty : node.requirements = []
                · by_cases coercions_empty : node.coercions = []
                  · refine .inl ⟨initializer,
                      GeneralizedClosure.ofDirectLambda context source
                        environment binder initializer parameters resultType
                        body,
                      rfl, ?_⟩
                    exact .directLambda
                      (lookupExpression?_sound lookup_eq) form_eq raw_type_eq
                      type_eq requirements_empty coercions_empty
                  · exact .inr ⟨source_unique,
                      .coercionsPresent lookup_eq form_eq coercions_empty⟩
                · exact .inr ⟨source_unique,
                    .requirementsPresent lookup_eq form_eq requirements_empty⟩
              · exact .inr ⟨source_unique,
                  .typeMismatch lookup_eq form_eq type_eq⟩
            · exact .inr ⟨source_unique,
                .rawTypeMismatch lookup_eq form_eq raw_type_eq⟩
          · exact .inr ⟨source_unique,
              .nonLambda lookup_eq (by
                intro parameters resultType body form_eq
                exact lambda_form ⟨parameters, resultType, body, form_eq⟩)⟩

/-- A canonical direct-lambda capture and an unsupported-initializer witness
cannot describe the same generalized binding. -/
theorem not_captures
    {context : Context} {source : TypedSource} {environment : Environment}
    {binder : TypedBinder} {initializer : ExpressionId}
    {function : GeneralizedClosure}
    (unsupported : GeneralizedInitializerUnsupported source binder
      (some initializer))
    (captures : GeneralizedClosureCaptures context source environment binder
      initializer function) : False := by
  cases captures with
  | @directLambda node parameters resultType body contains form_eq raw_type_eq
      type_eq requirements_empty coercions_empty =>
      have found : source.lookupExpression? initializer = some node :=
        lookupExpression?_complete unsupported.source_unique contains
      cases unsupported.malformed with
      | missing lookup_eq => simp [found] at lookup_eq
      | @nonLambda _ candidate lookup_eq form_ne =>
          rw [found] at lookup_eq
          cases Option.some.inj lookup_eq
          exact form_ne parameters resultType body form_eq
      | @rawTypeMismatch _ candidate otherParameters otherResultType otherBody
          lookup_eq other_form_eq raw_type_ne =>
          rw [found] at lookup_eq
          cases Option.some.inj lookup_eq
          exact raw_type_ne raw_type_eq
      | @typeMismatch _ candidate otherParameters otherResultType otherBody
          lookup_eq other_form_eq type_ne =>
          rw [found] at lookup_eq
          cases Option.some.inj lookup_eq
          exact type_ne type_eq
      | @requirementsPresent _ candidate otherParameters otherResultType
          otherBody lookup_eq other_form_eq requirements_ne =>
          rw [found] at lookup_eq
          cases Option.some.inj lookup_eq
          exact requirements_ne requirements_empty
      | @coercionsPresent _ candidate otherParameters otherResultType otherBody
          lookup_eq other_form_eq coercions_ne =>
          rw [found] at lookup_eq
          cases Option.some.inj lookup_eq
          exact coercions_ne coercions_empty

end GeneralizedInitializerUnsupported

end Solcore.SourceSemantics.Dynamic

import Solcore.SourceSemantics.Dynamic.Value
import Solcore.SourceSemantics.Substitution
import Solcore.SourceSemantics.Binders

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

end Solcore.SourceSemantics.Dynamic

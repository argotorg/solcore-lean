import Solcore.SourceSemantics

set_option autoImplicit false

namespace Solcore.Test.SourceSemantics

open Frontend
open TypeSystem
open Solcore.SourceSemantics

/-- Extending a semantic context makes the new local available immediately. -/
example (context : Solcore.SourceSemantics.Context)
    (binder : Resolved.LocalId)
    (scheme : Scheme) :
    (context.withLocal binder scheme).LocalLookup binder scheme := by
  exact Context.localLookup_withLocal_self context binder scheme

/-- A quantified local scheme can be instantiated independently at each
reference occurrence. -/
theorem polymorphicLocalReference
    (context : Solcore.SourceSemantics.Context)
    (binder : Resolved.LocalId)
    (metavariable : TypeVarId) :
    ReferenceHasRawType
      (context.withLocal binder {
        quantified := [metavariable]
        body := .variable metavariable
      })
      (.local binder) .word := by
  let scheme : Scheme := {
    quantified := [metavariable]
    body := .variable metavariable
  }
  change ReferenceHasRawType (context.withLocal binder scheme)
    (.local binder) .word
  apply ReferenceHasRawType.local
  · exact Context.localLookup_withLocal_self _ _ _
  · refine SchemeInstantiates.intro [(metavariable, .word)] ?_ ?_
    · exact ExactSubstitution.singleton metavariable .word
    · simp [scheme, TypeSystem.Substitution.apply,
        TypeSystem.Substitution.lookup?]

/-- An exact rigid-parameter substitution validates the complete retained
top-level declaration instantiation. -/
theorem genericDeclarationReference
    (context : Solcore.SourceSemantics.Context)
    (signature : ProgramFunctionSignature)
    (signature_mem : signature ∈ context.signatures.functions)
    (substitution : ParameterSubstitution)
    (exact : Solcore.SourceSemantics.ParameterSubstitution.Exact substitution
      signature.scheme.parameters) :
    ReferenceHasRawType context
      (.declaration {
        declaration := signature.id
        parameterSubstitution := substitution
        type := substitution.apply signature.scheme.body
        predicates := signature.scheme.predicates.map
          (ProgramPredicate.applyParameters substitution)
        parameterComptime := signature.parameterComptime
        returnComptime := signature.returnComptime
      })
      (substitution.apply signature.scheme.body) := by
  apply ReferenceHasRawType.declaration
  exact .intro signature signature_mem rfl exact rfl rfl rfl rfl

/-- Declarative expression membership determines executable lookup only after
the occurrence-uniqueness invariant is supplied. -/
theorem expressionMembershipLookup
    (source : Frontend.SourceInference.TypedSource)
    (id : Frontend.SourceInference.ExpressionId)
    (node : Frontend.SourceInference.ExpressionNode)
    (unique : NodeOccurrencesUnique source)
    (contains : ContainsExpression source id node) :
    source.lookupExpression? id = some node :=
  lookupExpression?_complete unique contains

/-- Explicit assumption evidence validates without invoking trait search. -/
theorem assumptionEvidenceValid
    (context : Solcore.SourceSemantics.Context)
    (goal : ProgramPredicate) :
    EvidenceValid
      (context.withAssumption goal).assumptions
      (context.withAssumption goal).signatures.resolutionRules
      goal (.assumption goal) := by
  exact .assumption (Context.hasAssumption_withAssumption_self context goal)

/-- A monomorphic builtin implementation head is related to its goal by the
empty exact simultaneous substitution. -/
theorem builtinIntWordHeadInstantiates :
    ImplHeadInstantiates ProgramSignatures.builtinIntWordRule
      (ProgramSignatures.builtinIntPredicate .word) [] := by
  refine .intro { parameters := [], variables := [] } ?_ rfl rfl
  exact ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩

/-- An empty-premise semantic implementation tree is valid when its catalog
rule declaratively instantiates to the goal. -/
theorem emptyPremiseImplementationValid
    (rule : ProgramImplRule) (goal : ProgramPredicate)
    (headInstantiation : ImplHeadInstantiates rule goal []) :
    EvidenceValid [] [rule] goal
      (.implementation goal rule.id []) := by
  exact .implementation (by simp) rfl headInstantiation .nil

/-- The frontend's retained implementation carrier can be related explicitly
to the independently validated semantic evidence tree. -/
theorem builtinIntWordRetainedEvidenceValid :
    RetainedEvidenceValid [] [ProgramSignatures.builtinIntWordRule]
      (ProgramSignatures.builtinIntPredicate .word)
      (.implementation (.byImpl
        (ProgramSignatures.builtinIntPredicate .word)
        ProgramSignatures.builtinIntWordRule.id [])) := by
  apply RetainedEvidenceValid.intro
  · exact .implementation (.byImpl .nil)
  · exact emptyPremiseImplementationValid _ _
      builtinIntWordHeadInstantiates

/-- A contextual assumption can discharge a nested where premise, rather than
being restricted to the root of the evidence tree. -/
theorem assumedPremiseImplementationValid
    (rule : ProgramImplRule)
    (goal premise : ProgramPredicate)
    (headInstantiation : ImplHeadInstantiates rule goal [premise]) :
    EvidenceValid [premise] [rule] goal
      (.implementation goal rule.id [.assumption premise]) := by
  exact .implementation (by simp) rfl headInstantiation
    (.cons (.assumption (by simp)) .nil)

/-- A solved requirement carrying explicit assumption evidence is validated by
the independent source judgment. -/
example (context : Solcore.SourceSemantics.Context)
    (goal : ProgramPredicate)
    (requirementId : Frontend.SourceInference.RequirementId) :
    SolvedRequirementValid (context.withAssumption goal) {
      id := requirementId
      predicate := goal
      evidence := .assumption goal
    } := by
  apply SolvedRequirementValid.intro
  exact RetainedEvidenceValid.intro (.assumption goal)
    (assumptionEvidenceValid context goal)

/-- Entailment exposes evidence whose stored goal is the requested goal. -/
example (context : Solcore.SourceSemantics.Context)
    (goal : ProgramPredicate) :
    ∃ evidence,
      EvidenceValid
        (context.withAssumption goal).assumptions
        (context.withAssumption goal).signatures.resolutionRules
        goal evidence ∧
      evidence.goal = goal := by
  let valid := assumptionEvidenceValid context goal
  exact ⟨.assumption goal, valid, valid.evidence_goal_eq⟩

end Solcore.Test.SourceSemantics

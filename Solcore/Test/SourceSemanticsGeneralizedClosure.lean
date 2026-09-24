import Solcore.SourceSemantics.Dynamic.GeneralizedClosure

/-! Focused checks for proof-facing generalized-closure materialization. -/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsGeneralizedClosure

open Frontend
open Frontend.SourceInference
open SourceSemantics
open SourceSemantics.Dynamic
open TypeSystem

private def predicate (metavariable : TypeVarId) : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate (.variable metavariable)

private def requirement (id : RequirementId) (metavariable : TypeVarId) :
    LocalSchemeRequirement := {
  templateRequirement := id
  predicate := predicate metavariable
}

private def generalizedBinder (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) (requirementId : RequirementId) : TypedBinder := {
  id := ⟨owner, 20⟩
  name := "generalized"
  scheme := {
    quantified := [metavariable]
    body := .function (.variable metavariable) (.variable metavariable)
  }
  schemeRequirements := [requirement requirementId metavariable]
}

private def lambdaParameter (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) : TypedBinder := {
  id := ⟨owner, 21⟩
  name := "argument"
  scheme := .mono (.variable metavariable)
}

private def protectedBinder (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) : TypedBinder := {
  id := ⟨owner, 22⟩
  name := "protected"
  scheme := {
    quantified := [metavariable]
    body := .variable metavariable
  }
}

private def principalSource (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) : TypedSource := {
  owner
  inputs := [lambdaParameter owner metavariable,
    protectedBinder owner metavariable]
  roots := []
  nodes := []
}

private def definitionContext (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (metavariable : TypeVarId)
    (protectedRequirement : RequirementId) : SourceSemantics.Context :=
  ((Context.ofSignatures signatures).withAssumptions
      [predicate metavariable]).withLocal
    (protectedBinder owner metavariable).id
    (protectedBinder owner metavariable).scheme
    [requirement protectedRequirement metavariable]

private def principalClosure (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (metavariable : TypeVarId)
    (initializer : ExpressionId) (body : StatementId)
    (templateRequirement protectedRequirement : RequirementId) :
    GeneralizedClosure := {
  binder := generalizedBinder owner metavariable templateRequirement
  initializer
  parameters := [lambdaParameter owner metavariable]
  resultType := .variable metavariable
  body := [body]
  source := principalSource owner metavariable
  captured := [((protectedBinder owner metavariable).id, ⟨7⟩)]
  definitionContext := definitionContext signatures owner metavariable
    protectedRequirement
}

/-- Materialization closes direct-lambda types and initializer assumptions,
while the quantified variable of an existing lexical scheme (and its paired
requirement metadata) remains capture-protected.  Code identities, captured
locations, and use-site dictionaries are retained exactly. -/
example (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (metavariable : TypeVarId) (initializer : ExpressionId)
    (body : StatementId) (templateRequirement protectedRequirement : RequirementId)
    (evidence : EvidenceEnvironment) :
    let function := principalClosure signatures owner metavariable initializer
      body templateRequirement protectedRequirement
    let materialized := function.instantiate [(metavariable, .word)] evidence
    materialized.parameters = [{
        lambdaParameter owner metavariable with scheme := .mono .word
      }] ∧
      materialized.resultType = .word ∧
      materialized.body = [body] ∧
      materialized.source.inputs = [
        { lambdaParameter owner metavariable with scheme := .mono .word },
        protectedBinder owner metavariable
      ] ∧
      materialized.captured =
        [((protectedBinder owner metavariable).id, ⟨7⟩)] ∧
      materialized.context.typeVariables = [] ∧
      materialized.context.locals = [
        ((protectedBinder owner metavariable).id,
          (protectedBinder owner metavariable).scheme)
      ] ∧
      materialized.context.localSchemeRequirements = [
        ((protectedBinder owner metavariable).id,
          [requirement protectedRequirement metavariable])
      ] ∧
      materialized.context.assumptions = [
        ProgramSignatures.builtinIntPredicate .word,
        ProgramSignatures.builtinIntPredicate .word
      ] ∧
      materialized.evidence = evidence := by
  simp [principalClosure, GeneralizedClosure.instantiate, principalSource,
    definitionContext, generalizedBinder, lambdaParameter, protectedBinder,
    requirement, predicate, Context.ofSignatures, Context.withAssumptions,
    Context.withLocal, localSchemeInitializerContext,
    Context.withTypeVariables, FlexibleSubstitution.closeContext,
    FlexibleSubstitution.applyLocals,
    FlexibleSubstitution.applyLocalSchemeRequirements,
    FlexibleSubstitution.forLocal, Resolved.LocalScope.lookup?,
    TypedSource.applySubstitution, TypedBinder.applySubstitution,
    Scheme.mono, Scheme.apply,
    LocalSchemeRequirement.applySubstitution,
    TypedTraitResolution.applySubstitution,
    ProgramSignatures.builtinIntPredicate, TypeSystem.Substitution.without,
    TypeSystem.Substitution.erase, TypeSystem.Substitution.apply,
    TypeSystem.Substitution.lookup?]

end Solcore.Test.SourceSemanticsGeneralizedClosure

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
    (metavariable : TypeVarId)
    (context_binders : TypeParameterBindersWellFormed context) :
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
  · refine SchemeInstantiatesAt.intro ?_
      [(metavariable, .word)] ?_ ?_ ?_
    · exact {
        binders := context_binders.withLocal binder scheme
        quantified_nodup := by simp [scheme]
        body := by
          apply TypeWellScoped.variable
          simp [scheme]
      }
    · exact ExactSubstitution.singleton metavariable .word
    · intro candidate replacement member
      simp only [List.mem_cons, List.mem_nil_iff, or_false,
        Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact {
        binders := context_binders.withLocal binder scheme
        typeWellScoped := .builtin .word
      }
    · simp [scheme, TypeSystem.Substitution.apply,
        TypeSystem.Substitution.lookup?]

/-- A quantified local can be instantiated at a flexible variable explicitly
scoped by an enclosing generalized initializer.  This is the compositional
case which a closed-only substitution range would reject. -/
theorem polymorphicLocalReferenceAtAmbientVariable
    (context : Solcore.SourceSemantics.Context)
    (binder : Resolved.LocalId)
    (quantified ambient : TypeVarId)
    (context_binders : TypeParameterBindersWellFormed context) :
    ReferenceHasRawType
      ((context.withTypeVariables [ambient]).withLocal binder {
        quantified := [quantified]
        body := .variable quantified
      })
      (.local binder) (.variable ambient) := by
  let scheme : Scheme := {
    quantified := [quantified]
    body := .variable quantified
  }
  let ambientContext :=
    (context.withTypeVariables [ambient]).withLocal binder scheme
  change ReferenceHasRawType ambientContext (.local binder) (.variable ambient)
  apply ReferenceHasRawType.local
  · exact Context.localLookup_withLocal_self _ _ _
  · refine SchemeInstantiatesAt.intro ?_
      [(quantified, .variable ambient)] ?_ ?_ ?_
    · exact {
        binders := (context_binders.withTypeVariables [ambient]).withLocal
          binder scheme
        quantified_nodup := by simp [scheme]
        body := by
          apply TypeWellScoped.variable
          simp [ambientContext, scheme, Context.withTypeVariables,
            Context.withLocal]
      }
    · exact ExactSubstitution.singleton quantified (.variable ambient)
    · intro candidate replacement member
      simp only [List.mem_cons, List.mem_nil_iff, or_false,
        Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact {
        binders := (context_binders.withTypeVariables [ambient]).withLocal
          binder scheme
        typeWellScoped := by
          apply TypeWellScoped.variable
          simp [ambientContext, admissibleTypeVariables,
            Context.withTypeVariables, Context.withLocal,
            TypeSystem.Ty.freeVariables]
      }
    · simp [scheme, TypeSystem.Substitution.apply,
        TypeSystem.Substitution.lookup?]

/-- Opening residual scope admits a retained occurrence metavariable but does
not turn it into a closed source type. -/
theorem residualVariableAdmissible
    (context : Solcore.SourceSemantics.Context) (residual : TypeVarId)
    (context_binders : TypeParameterBindersWellFormed context) :
    TypeAdmissible context.withResidualTypeVariables (.variable residual) := {
  binders := context_binders.withResidualTypeVariables
  typeWellScoped := by
    apply TypeWellScoped.variable
    simp [admissibleTypeVariables, Context.withResidualTypeVariables,
      TypeSystem.Ty.freeVariables]
}

theorem residualVariableNotClosed
    (context : Solcore.SourceSemantics.Context) (residual : TypeVarId) :
    ¬ TypeWellFormed context.withResidualTypeVariables (.variable residual) := by
  intro wellFormed
  exact TypeWellFormed.variable_impossible residual wellFormed

/-- A residual rigid-parameter replacement is accepted by the static
occurrence judgment but cannot cross the closed runtime-instantiation
boundary. -/
theorem residualDeclarationInstantiationIsStaticOnly
    (context : Solcore.SourceSemantics.Context)
    (signature : ProgramFunctionSignature)
    (signature_mem : signature ∈ context.signatures.functions)
    (parameter : TypeParameterId) (residual : TypeVarId)
    (parameters_eq : signature.scheme.parameters = [parameter])
    (body_eq : signature.scheme.body = .parameter parameter)
    (context_binders : TypeParameterBindersWellFormed context) :
    ∃ instantiation,
      DeclarationInstantiation.Admissible
        context.withResidualTypeVariables instantiation ∧
      ¬ DeclarationInstantiation.Valid
        context.withResidualTypeVariables instantiation := by
  let substitution : ParameterSubstitution :=
    [(parameter, .variable residual)]
  let instantiation : Frontend.SourceInference.DeclarationInstantiation := {
    declaration := signature.id
    parameterSubstitution := substitution
    type := .variable residual
    predicates := signature.scheme.predicates.map
      (ProgramPredicate.applyParameters substitution)
    parameterComptime := signature.parameterComptime
    returnComptime := signature.returnComptime
  }
  refine ⟨instantiation, ?_, ?_⟩
  · apply DeclarationInstantiation.Admissible.intro signature
    · simpa [Context.withResidualTypeVariables] using signature_mem
    · rfl
    · simpa [instantiation, substitution, parameters_eq] using
        ParameterSubstitution.exact_singleton parameter (.variable residual)
    · intro candidate replacement member
      simp only [instantiation, substitution, List.mem_cons,
        List.mem_nil_iff, or_false, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact residualVariableAdmissible context residual context_binders
    · simp [instantiation, substitution, body_eq,
        TypeSystem.ParameterSubstitution.apply,
        TypeSystem.ParameterSubstitution.lookup?]
    · rfl
    · rfl
    · rfl
  · intro valid
    cases valid with
    | intro selected selected_mem declaration_eq exact range type_eq
        predicates_eq parameterComptime_eq returnComptime_eq =>
        have member :
            (parameter, .variable residual) ∈
              instantiation.parameterSubstitution := by
          simp [instantiation, substitution]
        exact TypeWellFormed.variable_impossible residual
          (range parameter (.variable residual) member)

/-- A quantified local may be instantiated at an unconstrained occurrence
metavariable retained anywhere in a resolved body.  This is distinct from the
lexical flexible scope used inside generalized initializers. -/
theorem polymorphicLocalReferenceAtResidualVariable
    (context : Solcore.SourceSemantics.Context)
    (binder : Resolved.LocalId)
    (quantified residual : TypeVarId)
    (context_binders : TypeParameterBindersWellFormed context) :
    ReferenceHasRawType
      (context.withResidualTypeVariables.withLocal binder {
        quantified := [quantified]
        body := .variable quantified
      })
      (.local binder) (.variable residual) := by
  let scheme : Scheme := {
    quantified := [quantified]
    body := .variable quantified
  }
  let residualContext :=
    context.withResidualTypeVariables.withLocal binder scheme
  change ReferenceHasRawType residualContext (.local binder)
    (.variable residual)
  apply ReferenceHasRawType.local
  · exact Context.localLookup_withLocal_self _ _ _
  · refine SchemeInstantiatesAt.intro ?_
      [(quantified, .variable residual)] ?_ ?_ ?_
    · exact {
        binders := context_binders.withLocal binder scheme
        quantified_nodup := by simp [scheme]
        body := by
          apply TypeWellScoped.variable
          simp [residualContext, scheme, admissibleTypeVariables,
            Context.withResidualTypeVariables, Context.withLocal]
      }
    · exact ExactSubstitution.singleton quantified (.variable residual)
    · intro candidate replacement member
      simp only [List.mem_cons, List.mem_nil_iff, or_false,
        Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact {
        binders := context_binders.withLocal binder scheme
        typeWellScoped := by
          apply TypeWellScoped.variable
          simp [residualContext, admissibleTypeVariables,
            Context.withResidualTypeVariables, Context.withLocal,
            TypeSystem.Ty.freeVariables]
      }
    · simp [scheme, TypeSystem.Substitution.apply,
        TypeSystem.Substitution.lookup?]

/-- Opening residual occurrence scope does not change the lexical
generalization barrier. -/
theorem residualScopeDoesNotBlockGeneralization
    (context : Solcore.SourceSemantics.Context) :
    GeneralizationBlockedVariables context.withResidualTypeVariables =
      GeneralizationBlockedVariables context := by
  rfl

/-- Free variables of preceding local schemes participate in the
generalization barrier. -/
theorem precedingLocalVariableBlocksGeneralization
    (context : Solcore.SourceSemantics.Context)
    (binder : Resolved.LocalId) (blocked : TypeVarId) :
    blocked ∈ GeneralizationBlockedVariables
      (context.withLocal binder {
        quantified := []
        body := .variable blocked
      }) := by
  simp [GeneralizationBlockedVariables, GeneralizationBlockedVariablesExcept,
    Context.withLocal,
    TypeSystem.Scheme.freeVariables, TypeSystem.Ty.freeVariables]

/-- Variables retained by solved predicates also participate in the
generalization barrier. -/
theorem solvedRequirementVariableBlocksGeneralization
    (context : Solcore.SourceSemantics.Context) (blocked : TypeVarId) :
    let predicate : ProgramPredicate := {
      trait := .builtin .int
      subject := .variable blocked
      arguments := []
    }
    let requirement : Frontend.SourceInference.SolvedRequirement := {
      id := ⟨0⟩
      predicate
      evidence := .assumption predicate
    }
    blocked ∈ GeneralizationBlockedVariables
      (context.withSolvedRequirements [requirement]) := by
  simp [GeneralizationBlockedVariables, GeneralizationBlockedVariablesExcept,
    Context.withSolvedRequirements,
    Frontend.TypedTraitResolution.predicateVariables,
    TypeSystem.Ty.freeVariables]

/-- Rigid substitution preserves the body-wide residual scope exactly. -/
theorem rigidSubstitutionPreservesResidualScope
    (context : Solcore.SourceSemantics.Context)
    (substitution : ParameterSubstitution) :
    StructuralSubstitution.applyContext substitution
        (context.withResidualTypeVariables) =
      Context.withResidualTypeVariables
        (StructuralSubstitution.applyContext substitution context) := by
  rfl

/-- Generalization retains an ambient flexible variable while quantifying the
fresh variable of the initialized value. -/
theorem generalizesOnlyFreshVariable
    (context : Solcore.SourceSemantics.Context)
    (ambient fresh : TypeVarId)
    (different : fresh ≠ ambient)
    (blocked : GeneralizationBlockedVariables context = [ambient]) :
    SchemeGeneralizes context {
      quantified := [fresh]
      body := .product (.variable ambient) (.variable fresh)
    } := by
  unfold SchemeGeneralizes
  unfold SchemeGeneralizesExcept
  rw [GeneralizationBlockedVariablesExcept_nil, blocked]
  change [fresh] =
    (if fresh ∈ [ambient] then [ambient] else [ambient] ++ [fresh]).filter
      (fun metavariable => ![ambient].contains metavariable)
  simp [different]

private def qualifiedLocalTemplateId :
    Frontend.SourceInference.RequirementId :=
  ⟨100⟩

private def qualifiedLocalPredicate (fresh : TypeVarId) :
    ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate (.variable fresh)

private def qualifiedLocalTemplate (fresh : TypeVarId) :
    Frontend.SourceInference.SolvedRequirement := {
  id := qualifiedLocalTemplateId
  predicate := qualifiedLocalPredicate fresh
  evidence := .assumption (qualifiedLocalPredicate fresh)
}

private def qualifiedLocalRequirement (fresh : TypeVarId) :
    Frontend.SourceInference.LocalSchemeRequirement := {
  templateRequirement := qualifiedLocalTemplateId
  predicate := qualifiedLocalPredicate fresh
}

private def qualifiedLocalBinder
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    Frontend.SourceInference.TypedBinder := {
  id := ⟨owner, 100⟩
  name := "qualified"
  scheme := {
    quantified := [fresh]
    body := .function (.variable fresh) (.variable fresh)
  }
  schemeRequirements := [qualifiedLocalRequirement fresh]
}

private def qualifiedLocalContext
    (signatures : ProgramSignatures) (fresh : TypeVarId) :
    Solcore.SourceSemantics.Context :=
  (Context.ofSignatures signatures).withSolvedRequirements
    [qualifiedLocalTemplate fresh]

private def duplicateQualifiedLocalContext
    (signatures : ProgramSignatures) (fresh : TypeVarId) :
    Solcore.SourceSemantics.Context :=
  (Context.ofSignatures signatures).withSolvedRequirements
    [qualifiedLocalTemplate fresh, qualifiedLocalTemplate fresh]

/-- A qualified local predicate is formed in the initializer scope, where
the scheme variable is admissible and the exact retained assumption row is
identified by its stable template requirement ID. -/
theorem qualifiedLocalRequirementFormation
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    LocalSchemeRequirementWellFormed
      (qualifiedLocalContext signatures fresh)
      (qualifiedLocalBinder owner fresh)
      (qualifiedLocalRequirement fresh) := by
  constructor
  · constructor
    · constructor
      · constructor
        · simp [qualifiedLocalContext, localSchemeInitializerContext,
            qualifiedLocalBinder, Context.ofSignatures,
            Context.withSolvedRequirements, Context.withTypeVariables,
            Context.withAssumptions]
        · intro parameter member
          simp [qualifiedLocalContext, localSchemeInitializerContext,
            qualifiedLocalBinder, Context.ofSignatures,
            Context.withSolvedRequirements, Context.withTypeVariables,
            Context.withAssumptions] at member
      · apply TypeWellScoped.variable
        simp [admissibleTypeVariables, qualifiedLocalContext,
          localSchemeInitializerContext, qualifiedLocalBinder,
          Context.ofSignatures, Context.withSolvedRequirements,
          Context.withTypeVariables, Context.withAssumptions]
    · intro argument member
      simp [qualifiedLocalRequirement, qualifiedLocalPredicate,
        ProgramSignatures.builtinIntPredicate] at member
    · rfl
  · refine ⟨fresh, by simp [qualifiedLocalBinder], ?_⟩
    simp [qualifiedLocalRequirement, qualifiedLocalPredicate,
      ProgramSignatures.builtinIntPredicate,
      Frontend.TypedTraitResolution.predicateVariables,
      TypeSystem.Ty.freeVariables]
  · refine ⟨qualifiedLocalTemplate fresh, ?_, rfl, rfl, rfl⟩
    change [qualifiedLocalTemplate fresh].filter (fun candidate =>
      candidate.id == (qualifiedLocalTemplate fresh).id) =
        [qualifiedLocalTemplate fresh]
    have selected :
        ((qualifiedLocalTemplate fresh).id ==
          (qualifiedLocalTemplate fresh).id) = true :=
      by rfl
    rw [List.filter_cons, if_pos selected]
    rfl

/-- The source-ordered singleton set of qualified predicates satisfies the
binder-level uniqueness and pointwise-formation judgment. -/
theorem qualifiedLocalRequirementsFormation
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    LocalSchemeRequirementsWellFormed
      (qualifiedLocalContext signatures fresh)
      (qualifiedLocalBinder owner fresh) := by
  constructor
  · simp [localSchemeTemplateIds, qualifiedLocalBinder,
      qualifiedLocalRequirement]
  · intro requirement member
    simp [qualifiedLocalBinder] at member
    subst requirement
    exact qualifiedLocalRequirementFormation signatures owner fresh

/-- Abstracting a template requirement removes only that row from the exact
generalization barrier, so its predicate variable can be quantified. -/
theorem qualifiedLocalTemplateIsExemptFromGeneralization
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    SchemeGeneralizesExcept (qualifiedLocalContext signatures fresh)
      (localSchemeTemplateIds (qualifiedLocalBinder owner fresh))
      (qualifiedLocalBinder owner fresh).scheme := by
  have filtered :
      (qualifiedLocalContext signatures fresh).solvedRequirements.filter
          (fun requirement =>
            !(localSchemeTemplateIds
              (qualifiedLocalBinder owner fresh)).contains requirement.id) =
        [] := by
    change [qualifiedLocalTemplate fresh].filter _ = []
    simp only [List.filter_cons, List.filter_nil]
    have contained :
        (localSchemeTemplateIds (qualifiedLocalBinder owner fresh)).contains
            (qualifiedLocalTemplate fresh).id = true := by
      simp [localSchemeTemplateIds, qualifiedLocalBinder,
        qualifiedLocalRequirement, qualifiedLocalTemplate,
        qualifiedLocalTemplateId]
      exact beq_self_eq_true' (qualifiedLocalTemplate fresh).id
    rw [contained]
    rfl
  have blocked :
      GeneralizationBlockedVariablesExcept
          (qualifiedLocalContext signatures fresh)
          (localSchemeTemplateIds (qualifiedLocalBinder owner fresh)) = [] := by
    unfold GeneralizationBlockedVariablesExcept
    rw [filtered]
    simp [qualifiedLocalContext, Context.ofSignatures,
      Context.withSolvedRequirements]
  unfold SchemeGeneralizesExcept
  rw [blocked]
  change [fresh] =
    (if fresh ∈ [fresh] then [fresh] else [fresh] ++ [fresh]).filter
      (fun _ => true)
  simp

/-- The initializer-only assumption scope validates the retained template.
This deliberately does not claim whole-body `RequirementLedgerWellFormed`:
open template rows are integrated with that global judgment in a later step. -/
theorem qualifiedLocalInitializerProvesTemplate
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    RequirementProves
      (localSchemeInitializerContext (qualifiedLocalContext signatures fresh)
        (qualifiedLocalBinder owner fresh))
      qualifiedLocalTemplateId (qualifiedLocalPredicate fresh) := by
  refine ⟨qualifiedLocalTemplate fresh, ?_⟩
  constructor
  · constructor
    · simp [qualifiedLocalContext, localSchemeInitializerContext,
        qualifiedLocalBinder, Context.withSolvedRequirements,
        Context.withTypeVariables, Context.withAssumptions]
    · rfl
  · constructor
    · simp [qualifiedLocalTemplate]
    · unfold qualifiedLocalTemplate
      apply SolvedRequirementValid.intro
      apply RetainedEvidenceValid.intro (.assumption _)
      apply EvidenceValid.assumption
      simp [qualifiedLocalContext, localSchemeInitializerContext,
        qualifiedLocalBinder, qualifiedLocalRequirement,
        Context.ofSignatures, Context.withSolvedRequirements,
        Context.withTypeVariables, Context.withAssumptions]

/-- Duplicate template identities are rejected before use-site
instantiation. -/
theorem duplicateQualifiedLocalTemplatesRejected
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    ¬ LocalSchemeRequirementsWellFormed
      (qualifiedLocalContext signatures fresh)
      { (qualifiedLocalBinder owner fresh) with
        schemeRequirements :=
          [qualifiedLocalRequirement fresh, qualifiedLocalRequirement fresh] } := by
  intro wellFormed
  simpa [localSchemeTemplateIds, qualifiedLocalBinder,
    qualifiedLocalRequirement] using wellFormed.ids_unique

/-- A qualified predicate cannot cite a template row absent from the source
requirement ledger. -/
theorem missingQualifiedLocalTemplateRejected
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    ¬ LocalSchemeRequirementWellFormed
      (Context.ofSignatures signatures)
      (qualifiedLocalBinder owner fresh)
      (qualifiedLocalRequirement fresh) := by
  intro wellFormed
  rcases wellFormed.template with ⟨solved, member, _⟩
  simp [Context.ofSignatures] at member

/-- A template identity denotes exactly one ledger occurrence; duplicating
even an otherwise identical retained row is rejected. -/
theorem duplicateQualifiedLocalLedgerRowsRejected
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    ¬ LocalSchemeRequirementWellFormed
      (duplicateQualifiedLocalContext signatures fresh)
      (qualifiedLocalBinder owner fresh)
      (qualifiedLocalRequirement fresh) := by
  intro wellFormed
  rcases wellFormed.template with ⟨solved, exactOne, _⟩
  change
    [qualifiedLocalTemplate fresh, qualifiedLocalTemplate fresh].filter
      (fun candidate => candidate.id ==
        (qualifiedLocalTemplate fresh).id) = [solved] at exactOne
  have selected :
      ((qualifiedLocalTemplate fresh).id ==
        (qualifiedLocalTemplate fresh).id) = true :=
    by rfl
  rw [List.filter_cons, if_pos selected, List.filter_cons,
    if_pos selected] at exactOne
  have lengths := congrArg List.length exactOne
  simp at lengths

/-- Monomorphic binders cannot smuggle qualified-scheme metadata into
parameter, pattern, or ordinary-let positions. -/
theorem monomorphicQualifiedMetadataRejected
    (context : Solcore.SourceSemantics.Context)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    ¬ BinderWellFormed context owner
      { (qualifiedLocalBinder owner fresh) with scheme := .mono .word } := by
  intro wellFormed
  have empty := wellFormed.monomorphic_requirements_empty (by
    simp [TypeSystem.Scheme.mono])
  simp [qualifiedLocalBinder] at empty

private def generalizedLetExpressionId
    (owner : Resolved.DeclarationId) :
    Frontend.SourceInference.ExpressionId :=
  ⟨⟨owner, 0⟩⟩

private def generalizedLetStatementId
    (owner : Resolved.DeclarationId) :
    Frontend.SourceInference.StatementId :=
  ⟨⟨owner, 1⟩⟩

private def generalizedLetBinder
    (owner : Resolved.DeclarationId) (fresh : TypeVarId)
    (span : Syntax.SourceSpan) : Frontend.SourceInference.TypedBinder := {
  id := ⟨owner, 0⟩
  name := "generalized"
  scheme := {
    quantified := [fresh]
    body := .proxy (.variable fresh)
  }
  span := some span
}

private def generalizedLetSource
    (owner : Resolved.DeclarationId) (fresh : TypeVarId)
    (span : Syntax.SourceSpan) : Frontend.SourceInference.TypedSource := {
  owner
  inputs := []
  roots := [.statement (generalizedLetStatementId owner)]
  nodes := [
    .expression {
      id := generalizedLetExpressionId owner
      span
      type := .proxy (.variable fresh)
      form := .proxy (.variable fresh)
    },
    .statement {
      id := generalizedLetStatementId owner
      span
      type := .unit
      form := .letDecl (generalizedLetBinder owner fresh span)
        (some (generalizedLetExpressionId owner))
    }
  ]
}

/-- A concrete occurrence table containing a polymorphic initialized `let`
is admitted by the dedicated static rule.  The initializer is checked with
the scheme's quantified variable in lexical scope, while the resulting local
is installed in the surrounding context with its rank-1 scheme intact. -/
theorem generalizedInitializedLetHasType
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) (span : Syntax.SourceSpan) :
    StatementHasType (generalizedLetSource owner fresh span)
      { returnType := .unit }
      (Context.ofSignatures signatures)
      (generalizedLetStatementId owner)
      ((Context.ofSignatures signatures).withLocal
        (generalizedLetBinder owner fresh span).id
        (generalizedLetBinder owner fresh span).scheme) {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } := by
  let context := Context.ofSignatures signatures
  let binder := generalizedLetBinder owner fresh span
  let initializer := generalizedLetExpressionId owner
  let statement := generalizedLetStatementId owner
  let source := generalizedLetSource owner fresh span
  have binders : TypeParameterBindersWellFormed context :=
    TypeParameterBindersWellFormed.ofSignatures signatures
  have variableAdmissible :
      TypeAdmissible (context.withTypeVariables [fresh])
        (.variable fresh) := {
    binders := binders.withTypeVariables [fresh]
    typeWellScoped := by
      apply TypeWellScoped.variable
      simp [admissibleTypeVariables, Context.withTypeVariables, context,
        Context.ofSignatures]
  }
  have proxyAdmissible :
      TypeAdmissible (context.withTypeVariables [fresh])
        (.proxy (.variable fresh)) := {
    binders := binders.withTypeVariables [fresh]
    typeWellScoped := .proxy variableAdmissible.typeWellScoped
  }
  have initializerType : ExpressionHasType source
      (context.withTypeVariables [fresh]) initializer
      (.proxy (.variable fresh)) := by
    apply ExpressionHasType.intro
        (node := {
          id := initializer
          span := span
          type := .proxy (.variable fresh)
          form := .proxy (.variable fresh)
        })
        (rawType := .proxy (.variable fresh))
        (plan := .ordinary [])
    · simp [ContainsExpression, source, generalizedLetSource, initializer,
        generalizedLetExpressionId]
    · exact .proxy variableAdmissible
    · rfl
    · exact proxyAdmissible
    · exact proxyAdmissible
    · apply ExpressionRequirementPlan.Valid.ordinary
      · simp [RequirementIdsValid]
      · exact .nil _
      · rfl
  have generalizes : SchemeGeneralizesExcept context
      (localSchemeTemplateIds binder) binder.scheme := by
    simp [SchemeGeneralizesExcept, GeneralizationBlockedVariablesExcept,
      localSchemeTemplateIds, context,
      Context.ofSignatures, binder, generalizedLetBinder,
      TypeSystem.Ty.freeVariables]
  have extension : BinderExtends owner context binder
      (context.withLocal binder.id binder.scheme) := by
    apply BinderExtends.intro
    · refine {
        owned := by simp [binder, generalizedLetBinder]
        scheme := ?_
        monomorphic_requirements_empty := ?_
      }
      · refine {
          binders
          quantified_nodup := by simp [binder, generalizedLetBinder]
          body := ?_
        }
        apply TypeWellScoped.proxy
        apply TypeWellScoped.variable
        simp [admissibleTypeVariables, context, Context.ofSignatures, binder,
          generalizedLetBinder]
      · intro quantifiedEmpty
        simp [binder, generalizedLetBinder] at quantifiedEmpty
    · simp [LocalFresh, context, Context.ofSignatures]
  change StatementHasType source { returnType := .unit } context statement
    (context.withLocal binder.id binder.scheme) _
  apply StatementHasType.letInitializedGeneralized
      (node := {
        id := statement
        span := span
        type := .unit
        form := .letDecl binder (some initializer)
      })
      (binder := binder) (initializer := initializer)
  · simp [ContainsStatement, source, generalizedLetSource, statement,
      generalizedLetStatementId, binder, generalizedLetBinder, initializer,
      generalizedLetExpressionId]
  · rfl
  · simp [binder, generalizedLetBinder]
  · exact LocalSchemeRequirementsWellFormed.empty context binder (by
      simp [binder, generalizedLetBinder])
  · exact generalizes
  · simpa [localSchemeInitializerContext, context, binder,
      generalizedLetBinder, Context.withTypeVariables,
      Context.withAssumptions] using initializerType
  · exact extension
  · rfl

/-- The same concrete generalized binding is admitted as a complete unit
body, so the regression also covers root extraction and statement-sequence
typing rather than only the isolated statement constructor. -/
theorem generalizedInitializedLetBodyHasType
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) (span : Syntax.SourceSpan) :
    BodyHasType (generalizedLetSource owner fresh span)
      (Context.ofSignatures signatures) .unit
      (.singleton {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .ordinary .unit
      }) := by
  let source := generalizedLetSource owner fresh span
  let context := Context.ofSignatures signatures
  let statement := generalizedLetStatementId owner
  let final := context.withLocal
    (generalizedLetBinder owner fresh span).id
    (generalizedLetBinder owner fresh span).scheme
  refine ⟨final, ?_, ?_, ?_⟩
  · change StatementsHaveType source { returnType := .unit } context
      [statement] final _
    apply StatementsHaveType.singleton
    exact generalizedInitializedLetHasType signatures owner fresh span
  · intro expression member
    simp [generalizedLetSource] at member
  · simp [BodyCompletes, BodyFacts.singleton, ControlSummary.ordinary]

/-- An exact rigid-parameter substitution validates the complete retained
top-level declaration instantiation. -/
theorem genericDeclarationReference
    (context : Solcore.SourceSemantics.Context)
    (signature : ProgramFunctionSignature)
    (signature_mem : signature ∈ context.signatures.functions)
    (substitution : ParameterSubstitution)
    (exact : Solcore.SourceSemantics.ParameterSubstitution.Exact substitution
      signature.scheme.parameters)
    (range : Solcore.SourceSemantics.ParameterSubstitution.RangeWellFormed
      context substitution) :
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
  exact .intro signature signature_mem rfl exact range.toAdmissible
    rfl rfl rfl rfl

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

private def qualifiedLocalActualId :
    Frontend.SourceInference.RequirementId :=
  ⟨101⟩

private def qualifiedLocalActualWord :
    Frontend.SourceInference.SolvedRequirement := {
  id := qualifiedLocalActualId
  predicate := ProgramSignatures.builtinIntPredicate .word
  evidence := .implementation (.byImpl
    (ProgramSignatures.builtinIntPredicate .word)
    ProgramSignatures.builtinIntWordRule.id [])
}

private def qualifiedLocalUseContext
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) : Solcore.SourceSemantics.Context :=
  ((Context.ofSignatures signatures).withSolvedRequirements
      [qualifiedLocalTemplate fresh, qualifiedLocalActualWord]).withLocal
    (qualifiedLocalBinder owner fresh).id
    (qualifiedLocalBinder owner fresh).scheme
    (qualifiedLocalBinder owner fresh).schemeRequirements

private theorem qualifiedLocalUseFormation
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    LocalSchemeRequirementsWellFormed
      (qualifiedLocalUseContext signatures owner fresh)
      (qualifiedLocalBinder owner fresh) := by
  constructor
  · simp [localSchemeTemplateIds, qualifiedLocalBinder,
      qualifiedLocalRequirement]
  · intro requirement member
    simp [qualifiedLocalBinder] at member
    subst requirement
    constructor
    · constructor
      · constructor
        · constructor
          · simp [qualifiedLocalUseContext, localSchemeInitializerContext,
              qualifiedLocalBinder, Context.ofSignatures,
              Context.withSolvedRequirements, Context.withLocal,
              Context.withTypeVariables, Context.withAssumptions]
          · intro parameter parameterMember
            simp [qualifiedLocalUseContext, localSchemeInitializerContext,
              qualifiedLocalBinder, Context.ofSignatures,
              Context.withSolvedRequirements, Context.withLocal,
              Context.withTypeVariables, Context.withAssumptions] at parameterMember
        · apply TypeWellScoped.variable
          simp [admissibleTypeVariables, qualifiedLocalUseContext,
            localSchemeInitializerContext, qualifiedLocalBinder,
            Context.ofSignatures, Context.withSolvedRequirements,
            Context.withLocal, Context.withTypeVariables,
            Context.withAssumptions]
      · intro argument argumentMember
        simp [qualifiedLocalRequirement, qualifiedLocalPredicate,
          ProgramSignatures.builtinIntPredicate] at argumentMember
      · rfl
    · refine ⟨fresh, by simp [qualifiedLocalBinder], ?_⟩
      simp [qualifiedLocalRequirement, qualifiedLocalPredicate,
        ProgramSignatures.builtinIntPredicate,
        Frontend.TypedTraitResolution.predicateVariables,
        TypeSystem.Ty.freeVariables]
    · refine ⟨qualifiedLocalTemplate fresh, ?_, rfl, rfl, rfl⟩
      change
        [qualifiedLocalTemplate fresh, qualifiedLocalActualWord].filter
            (fun candidate => candidate.id ==
              (qualifiedLocalTemplate fresh).id) =
          [qualifiedLocalTemplate fresh]
      rfl

private theorem qualifiedLocalUseSchemeWellFormed
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    SchemeWellFormed (qualifiedLocalUseContext signatures owner fresh)
      (qualifiedLocalBinder owner fresh).scheme := by
  constructor
  · simp [TypeParameterBindersWellFormed, qualifiedLocalUseContext,
      Context.ofSignatures, Context.withSolvedRequirements, Context.withLocal]
  · simp [qualifiedLocalBinder]
  · apply TypeWellScoped.function
    · apply TypeWellScoped.variable
      simp [qualifiedLocalBinder, admissibleTypeVariables,
        qualifiedLocalUseContext, Context.ofSignatures,
        Context.withSolvedRequirements, Context.withLocal]
    · apply TypeWellScoped.variable
      simp [qualifiedLocalBinder, admissibleTypeVariables,
        qualifiedLocalUseContext, Context.ofSignatures,
        Context.withSolvedRequirements, Context.withLocal]

private theorem qualifiedLocalActualWordProves
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    RequirementProves (qualifiedLocalUseContext signatures owner fresh)
      qualifiedLocalActualId
      (ProgramSignatures.builtinIntPredicate .word) := by
  refine ⟨qualifiedLocalActualWord, ?_⟩
  constructor
  · constructor
    · simp [qualifiedLocalUseContext, Context.withLocal,
        Context.withSolvedRequirements]
    · rfl
  · constructor
    · rfl
    · apply SolvedRequirementValid.intro
      apply RetainedEvidenceValid.intro
      · exact .implementation (.byImpl .nil)
      · exact .implementation
          (by simp [ProgramSignatures.resolutionRules,
            ProgramSignatures.builtinResolutionRules])
          rfl builtinIntWordHeadInstantiates .nil

/-- A qualified local reference uses one substitution for both `α → α` and
its ordered `Int<α>` predicate, producing `Word → Word` and `Int<Word>` at the
same occurrence. -/
theorem qualifiedLocalReferenceUseValid
    (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    ReferenceUseValid (qualifiedLocalUseContext signatures owner fresh)
      (.local (qualifiedLocalBinder owner fresh).id)
      (.function .word .word) [qualifiedLocalActualId] := by
  apply ReferenceUseValid.local
  · exact .head
  · exact .head
  · refine .intro
      (qualifiedLocalUseFormation signatures owner fresh)
      (qualifiedLocalUseSchemeWellFormed signatures owner fresh)
      [(fresh, .word)] (ExactSubstitution.singleton fresh .word) ?_ ?_ ?_ ?_ ?_
    · intro metavariable replacement member
      simp only [List.mem_cons, List.mem_nil_iff, or_false,
        Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩
      exact {
        binders := by
          simp [TypeParameterBindersWellFormed, qualifiedLocalUseContext,
            Context.ofSignatures, Context.withSolvedRequirements,
            Context.withLocal]
        typeWellScoped := .builtin .word
      }
    · simp [qualifiedLocalBinder, TypeSystem.Substitution.apply,
        TypeSystem.Substitution.lookup?]
    · simp [qualifiedLocalActualId]
    · intro id actualMember templateMember
      have actualEq : id = qualifiedLocalActualId := by
        simpa using actualMember
      have templateEq : id = qualifiedLocalTemplateId := by
        simpa [localSchemeTemplateIds, qualifiedLocalBinder,
          qualifiedLocalRequirement] using templateMember
      exact (show qualifiedLocalActualId ≠ qualifiedLocalTemplateId by decide)
        (actualEq.symm.trans templateEq)
    · exact .cons (by
        simpa [instantiateLocalSchemePredicates, qualifiedLocalBinder,
          qualifiedLocalRequirement, qualifiedLocalPredicate,
          ProgramSignatures.builtinIntPredicate,
          Frontend.TypedTraitResolution.applySubstitution,
          TypeSystem.Substitution.apply, TypeSystem.Substitution.lookup?] using
          (qualifiedLocalActualWordProves signatures owner fresh)) .nil

/-- Repeating one actual requirement identity cannot fabricate a two-item
qualified evidence spine. -/
theorem duplicateLocalActualRequirementsRejected
    (context : Solcore.SourceSemantics.Context)
    (binder : Frontend.SourceInference.TypedBinder)
    (type : Ty) (requirement : Frontend.SourceInference.RequirementId) :
    ¬ LocalSchemeInstantiationValid context binder type
      [requirement, requirement] := by
  intro valid
  simpa using valid.actual_requirements_nodup

/-- An initializer-only template identity cannot be recycled as evidence for
the corresponding local use. -/
theorem localTemplateCannotBeActualRequirement
    (context : Solcore.SourceSemantics.Context)
    (binder : Frontend.SourceInference.TypedBinder)
    (type : Ty) (template : Frontend.SourceInference.RequirementId)
    (templateMember : template ∈ localSchemeTemplateIds binder) :
    ¬ LocalSchemeInstantiationValid context binder type [template] := by
  intro valid
  exact valid.actual_templates_disjoint template (by simp) templateMember

/-- With a unique ledger, reversing two distinct actual evidence IDs cannot
validate an ordered two-predicate local-scheme instance. -/
theorem reversedLocalActualRequirementsRejected
    (context : Solcore.SourceSemantics.Context)
    (binder : Frontend.SourceInference.TypedBinder) (type : Ty)
    (firstId secondId : Frontend.SourceInference.RequirementId)
    (firstPredicate secondPredicate : ProgramPredicate)
    (ledger : RequirementLedgerWellFormed context)
    (different : firstPredicate ≠ secondPredicate)
    (ordered : ∀ substitution,
      ExactSubstitution substitution binder.scheme.quantified →
        instantiateLocalSchemePredicates substitution binder =
          [firstPredicate, secondPredicate])
    (_firstProves : RequirementProves context firstId firstPredicate)
    (secondProves : RequirementProves context secondId secondPredicate) :
    ¬ LocalSchemeInstantiationValid context binder type [secondId, firstId] := by
  intro valid
  rcases valid.has_shared_substitution with
    ⟨substitution, exact, _, _, proves⟩
  rw [ordered substitution exact] at proves
  have reversedHead : RequirementProves context secondId firstPredicate :=
    proves.head
  have predicatesEq :=
    ledger.proves_predicate_eq secondProves reversedHead
  exact different predicatesEq.symm

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

/-- Canonical defaults are source values with the exact declared type. -/
example :
    Dynamic.DefaultValue (.product .bool .integer)
      (.product (.bool false) (.integer 0)) := by
  exact .product .bool .integer

/-- Mathematical integer primitives include the operations which have no
fixed-width Core interpretation. -/
example :
    Dynamic.BinaryPrimitiveApplies .add
      (.integer 19) (.integer 23) (.integer 42) := by
  exact .integerAdd 19 23

/-- Lazy Boolean source operators need not evaluate an unselected operand. -/
example :
    Dynamic.ShortCircuits .logicalAnd (.bool false) (.bool false) := by
  exact .andFalse

/-- Multi-argument calls use the same right-associated product convention as
source types. -/
example :
    Dynamic.ValuesPack [.integer 1, .bool true]
      (.product (.integer 1) (.bool true)) := by
  exact .cons (.singleton (.bool true))

/-- A deferred input dominates a collection with no runtime input. -/
example :
    Staging.StagesJoin [.comptime, .deferred] .deferred := by
  exact .deferred (by simp) (by simp)

/-- Only the closed residual-data fragment crosses the materialization
boundary. -/
example :
    Staging.Materializes
      (.product (.bool true) (.word Core.Word.zero))
      (.product (.bool true) (.word Core.Word.zero)) := by
  exact .product (.bool true) (.word Core.Word.zero)

theorem integerDoesNotMaterialize (value : Int) :
    ¬ Staging.Materializable (.integer value) := by
  intro admitted
  cases admitted

/-- A retained, requirement-free literal occurrence executes directly under
the declarative big-step relation; no frontend evaluator result is a premise. -/
theorem literalExpressionEvaluates
    (program : Program) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment)
    (source : Frontend.SourceInference.TypedSource)
    (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) (id : Frontend.SourceInference.ExpressionId)
    (node : Frontend.SourceInference.ExpressionNode)
    (literal : Syntax.CoreLiteralValue) (value : Dynamic.Value)
    (contains : ContainsExpression source id node)
    (form_eq : node.form =
      Frontend.SourceInference.ExpressionForm.literal literal)
    (requirements_eq : node.requirements = [])
    (coercions_eq : node.coercions = [])
    (constructs : Dynamic.LiteralConstructs literal value) :
    Dynamic.ExpressionEvaluates program context evidence source environment
      heap id value heap := by
  apply Dynamic.ExpressionEvaluates.intro contains
  · rw [form_eq, requirements_eq, coercions_eq]
    exact .literal rfl constructs
  · rw [coercions_eq]
    exact .nil

end Solcore.Test.SourceSemantics

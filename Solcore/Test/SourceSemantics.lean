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
  simp [GeneralizationBlockedVariables, Context.withLocal,
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
  simp [GeneralizationBlockedVariables, Context.withSolvedRequirements,
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
  rw [blocked]
  change [fresh] =
    (if fresh ∈ [ambient] then [ambient] else [ambient] ++ [fresh]).filter
      (fun metavariable => ![ambient].contains metavariable)
  simp [different]

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
  have generalizes : SchemeGeneralizes context binder.scheme := by
    simp [SchemeGeneralizes, GeneralizationBlockedVariables, context,
      Context.ofSignatures, binder, generalizedLetBinder,
      TypeSystem.Ty.freeVariables]
  have extension : BinderExtends owner context binder
      (context.withLocal binder.id binder.scheme) := by
    apply BinderExtends.intro
    · refine {
        owned := by simp [binder, generalizedLetBinder]
        scheme := ?_
      }
      refine {
        binders
        quantified_nodup := by simp [binder, generalizedLetBinder]
        body := ?_
      }
      apply TypeWellScoped.proxy
      apply TypeWellScoped.variable
      simp [admissibleTypeVariables, context, Context.ofSignatures, binder,
        generalizedLetBinder]
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
  · exact generalizes
  · exact initializerType
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

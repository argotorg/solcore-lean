import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.Dynamic.Control
import Solcore.SourceSemantics.Dynamic.ControlTransferFacts

/-!
# Constructive whole-language preservation

This module discharges the mutually recursive preservation proof for every
successful source-dynamic judgment.  It constructs `WholeLanguagePreservation`
from `ProgramWellFormed` alone and exposes the companion control-soundness
theorems used by function-body sequencing and exhaustive matches.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference
open TypeSystem

private theorem containsExpression_unique
    {source : TypedSource} {id : ExpressionId}
    {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (left_contains : ContainsExpression source id left)
    (right_contains : ContainsExpression source id right) :
    left = right := by
  have left_lookup := lookupExpression?_complete unique left_contains
  have right_lookup := lookupExpression?_complete unique right_contains
  rw [left_lookup] at right_lookup
  exact Option.some.inj right_lookup

private theorem containsStatement_unique
    {source : TypedSource} {id : StatementId}
    {left right : StatementNode}
    (unique : NodeOccurrencesUnique source)
    (left_contains : ContainsStatement source id left)
    (right_contains : ContainsStatement source id right) :
    left = right := by
  have left_lookup := lookupStatement?_complete unique left_contains
  have right_lookup := lookupStatement?_complete unique right_contains
  rw [left_lookup] at right_lookup
  exact Option.some.inj right_lookup

private theorem ordinaryRequirementLayout_eq
    {context : Context} {rawType finalType : Ty}
    {requirements owned staticOwned : List RequirementId}
    {coercions : List CoercionStep}
    (valid : ExpressionRequirementPlan.Valid context rawType finalType
      (.ordinary staticOwned) requirements coercions)
    (layout : OrdinaryRequirementLayout requirements coercions owned) :
    owned = staticOwned := by
  cases valid with
  | ordinary _ _ requirements_eq =>
      unfold OrdinaryRequirementLayout at layout
      rw [requirements_eq] at layout
      exact List.append_cancel_right layout.symm

private theorem selected_covers
    {program : Program} {context : Context}
    {callerEvidence calleeEvidence : EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    {bodyInstance : BodyInstance}
    (selected : OperatorMethodSelected program context callerEvidence traitName
      methodName requirements bodyInstance calleeEvidence) :
    calleeEvidence.Covers bodyInstance.context := by
  cases selected with
  | intro _ _ _ _ _ _ _ _ _ _ _ _ _ covers =>
      exact covers

private theorem unaryDispatch_functional
    {operator : Syntax.UnaryOp} {leftTrait leftMethod rightTrait rightMethod : String}
    (left : UnaryTraitDispatch operator leftTrait leftMethod)
    (right : UnaryTraitDispatch operator rightTrait rightMethod) :
    leftTrait = rightTrait /\ leftMethod = rightMethod := by
  cases left <;> cases right
  exact ⟨rfl, rfl⟩

private theorem binaryDispatch_functional
    {operator : Syntax.BinaryOp} {leftTrait leftMethod rightTrait rightMethod : String}
    (left : BinaryTraitDispatch operator leftTrait leftMethod)
    (right : BinaryTraitDispatch operator rightTrait rightMethod) :
    leftTrait = rightTrait /\ leftMethod = rightMethod := by
  cases left <;> cases right <;> exact ⟨rfl, rfl⟩

private theorem statementFinalContext_eq
    {program : Program} {context staticFinalContext runtimeFinalContext : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap}
    {statement : StatementId} {outcome : ControlOutcome}
    {control : ControlContext} {facts : StatementFacts}
    (graph : OccurrenceGraphWellFormed source)
    (typing : StatementHasType source control context statement
      staticFinalContext facts)
    (execution : StatementExecutes program context evidence source environment
      before statement runtimeFinalContext outcome after) :
    runtimeFinalContext = staticFinalContext := by
  rcases Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
    ⟨typedNode, typed_contains, form_typing⟩
  cases execution with
  | letUninitialized contains form_eq runtime_monomorphic extension allocate =>
      have node_eq := containsStatement_unique
        graph.nodeOccurrencesUnique typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | letUninitialized monomorphic static_extension =>
          exact Solcore.SourceSemantics.Dynamic.BinderExtends.functional extension
            static_extension
  | letInitialized contains form_eq evaluate runtime_monomorphic extension allocate =>
      have node_eq := containsStatement_unique
        graph.nodeOccurrencesUnique typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | letInitialized initializer_type monomorphic static_extension =>
          exact Solcore.SourceSemantics.Dynamic.BinderExtends.functional extension
            static_extension
      | letInitializedGeneralized polymorphic _requirements_well_formed
          _generalizes initializer_type static_extension =>
          exact (polymorphic runtime_monomorphic).elim
  | letInitializedGeneralized contains form_eq captures runtime_polymorphic
      extension allocate =>
      have node_eq := containsStatement_unique
        graph.nodeOccurrencesUnique typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing with
      | letInitialized initializer_type static_monomorphic static_extension =>
          exact (runtime_polymorphic static_monomorphic).elim
      | letInitializedGeneralized static_polymorphic
          requirements_well_formed generalizes initializer_type
          static_extension =>
          exact Solcore.SourceSemantics.Dynamic.BinderExtends.functional
            extension static_extension
  | returnUnit contains form_eq | returnValue contains form_eq evaluate
    | expression contains form_eq evaluate
    | assignValue contains form_eq assignment_executes
    | assignBitNot contains form_eq assignment_executes
    | ifTrue contains form_eq condition_evaluates body_executes
    | ifFalseWithoutElse contains form_eq condition_evaluates
    | ifFalseWithElse contains form_eq condition_evaluates body_executes
    | block contains form_eq body_executes
    | matchArm contains form_eq scrutinee_contains scrutinee_evaluates
        allocate_hidden select binders_eq values_eq binders_extend
        allocate_bindings execute
    | matchDefault contains form_eq scrutinee_contains scrutinee_evaluates
        allocate_hidden select execute
    | matchNoBranch contains form_eq scrutinee_contains scrutinee_evaluates
        allocate_hidden select
    | forLoop contains form_eq initializer_executes iterate
    | whileLoop contains form_eq iterate
    | breakStmt contains form_eq
    | continueStmt contains form_eq =>
      have node_eq := containsStatement_unique
        graph.nodeOccurrencesUnique typed_contains contains
      subst typedNode
      rw [form_eq] at form_typing
      cases form_typing <;> rfl

private theorem monoBinders_toBinders
    {owner : Resolved.DeclarationId} {context final : Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner context binders types final) :
    BindersExtend owner context binders final := by
  induction extension with
  | nil => exact .nil _
  | cons scheme_eq head tail induction => exact .cons head induction

private theorem monoBinders_monomorphic
    {owner : Resolved.DeclarationId} {context final : Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner context binders types final) :
    ∀ binder, binder ∈ binders → binder.scheme.quantified = [] := by
  induction extension with
  | nil => simp
  | @cons _ _ _ binder binders type types scheme_eq head tail induction =>
      intro selected member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp [scheme_eq, TypeSystem.Scheme.mono]
      · exact induction selected member

private theorem bodyArguments_length
    {program : Program} {bodyInstance : BodyInstance}
    {evidence : EvidenceEnvironment} {before after : Heap}
    {arguments : List Value} {result : Value}
    (evaluation : BodyInvokes program bodyInstance evidence before arguments
      result after) :
    arguments.length = bodyInstance.source.inputs.length := by
  cases evaluation with
  | returned covers roots_eq inputs_extend allocate execute returned =>
      exact allocate.length_eq.symm
  | unit covers result_unit roots_eq inputs_extend allocate execute fell_through =>
      exact allocate.length_eq.symm

private theorem tailExpressionTyping
    {source : TypedSource} {control : ControlContext} {context final : Context}
    {statement : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (graph : OccurrenceGraphWellFormed source)
    (typing : StatementHasType source control context statement final facts)
    (contains : ContainsStatement source statement node)
    (form_eq : node.form = .expression expression false) :
    ∃ type,
      ExpressionHasType source context expression type ∧
      facts = {
        type, hasValue := true, sawReturn := false
        control := .ordinary type
      } := by
  cases typing with
  | letUninitialized static_contains static_form monomorphic generalizes extension
      type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | letInitialized static_contains static_form initializer_type monomorphic
      generalizes extension type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | letInitializedGeneralized static_contains static_form polymorphic generalizes
      initializer_type extension type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | returnUnit static_contains static_form return_type_eq type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | returnValue static_contains static_form value_type type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | expressionValue static_contains static_form expression_type type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
      exact ⟨_, expression_type, rfl, rfl⟩
  | expressionDiscard static_contains static_form expression_type type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | assignValue static_contains static_form assignment_type type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | assignBitNot static_contains static_form assignment_type type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | ifWithoutElse static_contains static_form condition_type then_type type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | ifWithElse static_contains static_form condition_type then_type else_type
      type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | block static_contains static_form body_type type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | matchWithoutDefault static_contains static_form default_eq scrutinee_type
      cases_type requirements_eq exhaustive merged type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | matchWithDefault static_contains static_form default_eq scrutinee_type
      cases_type default_type requirements_eq merged type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | forLoop static_contains static_form initializer_type condition_type body_type
      post_type type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | whileLoop static_contains static_form condition_type body_type type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | breakStmt static_contains static_form allowed type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all
  | continueStmt static_contains static_form allowed type_eq =>
      have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
        static_contains contains
      subst_vars
      simp_all

private theorem whileFinalContext_eq
    {program : Program} {context finalContext : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap}
    {condition : ExpressionId} {body : List StatementId}
    {outcome : ControlOutcome}
    (evaluation : WhileExecutes program context evidence source environment
      before condition body finalContext outcome after) :
    finalContext = context := by
  cases evaluation <;> rfl

private theorem forLoopFinalContext_eq
    {program : Program} {context finalContext : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap}
    {condition : ExpressionId} {post : List ForItemForm}
    {body : List StatementId} {outcome : ControlOutcome}
    (evaluation : ForLoopExecutes program context evidence source environment
      before condition post body finalContext outcome after) :
    finalContext = context := by
  cases evaluation <;> rfl

private theorem statementControlFormTyping
    {source : TypedSource} {control : ControlContext}
    {context finalContext : Context} {statement : StatementId}
    {node : StatementNode} {form : StatementForm} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (typing : StatementHasType source control context statement finalContext facts)
    (contains : ContainsStatement source statement node)
    (form_eq : node.form = form) :
    StatementControlFormTyping source control context form facts := by
  rcases
      Solcore.SourceSemantics.Dynamic.StatementHasType.controlFormTyping typing with
    ⟨typedNode, typed_contains, control_typing⟩
  have node_eq := containsStatement_unique unique typed_contains contains
  subst typedNode
  exact form_eq ▸ control_typing

set_option maxHeartbeats 2400000 in
mutual

  private theorem preserveExpressionRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment}
      {before after : Heap} {id : ExpressionId} {value : Value} {type : Ty}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : ExpressionHasType source context id type)
      (evaluation : ExpressionEvaluates program context evidence source environment
        before id value after) :
      ExpressionEvaluationPreserved context before after value type :=
    match evaluation with
    | @ExpressionEvaluates.intro _ _ _ _ _ _ middle _ _ evaluatedNode raw result
        evaluated_contains form_evaluation coercion_evaluation => by
        cases typing with
        | @intro _ _ typedNode rawType plan typed_contains form_type raw_type_eq
            raw_well_formed type_well_formed requirements =>
            have node_eq := containsExpression_unique
              runtime.graph.nodeOccurrencesUnique typed_contains
              evaluated_contains
            subst typedNode
            rcases preserveFormRec program_well_formed runtime
                evidence_covers environment_agrees before_typed
                ⟨_, evaluatedNode, typed_contains, rfl, raw_type_eq⟩ form_type requirements
                form_evaluation with
              ⟨raw_typed, middle_typed, raw_extension⟩
            rcases preservePathRec program_well_formed runtime
                middle_typed raw_typed
                (ExpressionRequirementPlan.Valid.outputPath requirements)
                coercion_evaluation with
              ⟨result_typed, after_typed, coercion_extension⟩
            exact {
              value_typed := result_typed
              heap_typed := after_typed
              heap_extends := raw_extension.trans coercion_extension
            }
    | @ExpressionEvaluates.generalizedLocal _ _ _ _ _ _ _ _ evaluatedNode name
        binder owned location cell function substitution produced result
        evaluated_contains form_eq layout lookup read descriptor context_fields
        instantiation coercion_evaluation => by
        cases typing with
        | @intro _ _ typedNode rawType plan typed_contains form_type raw_type_eq
            raw_well_formed type_well_formed requirements =>
            have node_eq := containsExpression_unique
              runtime.graph.nodeOccurrencesUnique typed_contains
              evaluated_contains
            subst typedNode
            rw [form_eq] at form_type
            cases form_type with
            | reference reference_use =>
                cases reference_use with
                | @«local» staticBinder _ actualRequirements scheme_lookup
                    requirements_lookup static_instantiation =>
                    have owned_eq := ordinaryRequirementLayout_eq requirements layout
                    subst owned
                    have binder_identity := environment_agrees.lookup_generalized
                      scheme_lookup lookup read descriptor
                    have cell_typed : CellWellTyped context before cell :=
                      before_typed cell read.member
                    have function_typed :=
                      (cell_typed.generalized_inv descriptor).2
                    have raw_typed := function_typed.instantiateHasType
                      (by
                        simpa only [← runtime.signatures,
                          context_fields.signatures] using
                          program_well_formed.signatures)
                      context_fields evidence_covers instantiation
                    have raw_typed' : ValueHasType context before
                        (.closure (function.instantiate substitution
                          (produced ++
                            evidence.applySubstitution substitution))) rawType := by
                      simpa only [raw_type_eq] using raw_typed
                    rcases preservePathRec program_well_formed runtime
                        before_typed raw_typed'
                        (ExpressionRequirementPlan.Valid.outputPath requirements)
                        coercion_evaluation with
                      ⟨result_typed, after_typed, coercion_extension⟩
                    exact {
                      value_typed := result_typed
                      heap_typed := after_typed
                      heap_extends := coercion_extension
                    }
    termination_by structural evaluation

  private theorem preserveFormRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment}
      {before after : Heap} {form : ExpressionForm}
      {requirements : List RequirementId} {coercions : List CoercionStep}
      {raw : Value} {rawType finalType : Ty} {plan : ExpressionRequirementPlan}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (occurrence : exists id node,
        ContainsExpression source id node /\ node.form = form /\
          node.rawType = rawType)
      (typing : ExpressionFormHasRawType source context form rawType plan)
      (requirements_valid : ExpressionRequirementPlan.Valid context rawType
        finalType plan requirements coercions)
      (evaluation : ExpressionFormEvaluates program context evidence source
        environment before form requirements coercions raw after) :
      ValueHasType context after raw rawType /\
        HeapWellTyped context after /\ HeapTypesExtend before after :=
    match evaluation with
    | .literal layout constructs => by
        cases typing with
        | literal valid =>
            exact ⟨constructs.hasType, before_typed, .refl before⟩
    | .integerLiteral layout constructs => by
        cases typing with
        | integerLiteral valid =>
            exact ⟨constructs.hasType, before_typed, .refl before⟩
    | evaluated@(.local layout lookup read descriptor_empty initialized) => by
        cases typing with
        | reference reference_use =>
            exact evaluated.referencePreserves environment_agrees before_typed
              (.reference reference_use)
    | evaluated@(.localEmptyMapping layout lookup read descriptor_empty type_eq
        empty write) => by
        cases typing with
        | reference reference_use =>
            exact evaluated.referencePreserves environment_agrees before_typed
              (.reference reference_use)
    | evaluated@(.declaration layout dynamic_valid requirements_close) => by
        cases typing with
        | reference reference_use =>
            exact evaluated.referencePreserves environment_agrees before_typed
              (.reference reference_use)
    | evaluated@(.builtinFunction layout) => by
        cases typing with
        | reference reference_use =>
            exact evaluated.referencePreserves environment_agrees before_typed
              (.reference reference_use)
    | evaluated@(.builtinBoolean layout) => by
        cases typing with
        | reference reference_use =>
            exact evaluated.referencePreserves environment_agrees before_typed
              (.reference reference_use)
    | .group layout inner_evaluates => by
        cases typing with
        | group inner_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed inner_type
                inner_evaluates with
              ⟨value_typed, after_typed, extension⟩
            exact ⟨value_typed, after_typed, extension⟩
    | .tuple layout elements_evaluate pack => by
        cases typing with
        | tuple elements_type =>
            rcases preserveExpressionsRec program_well_formed runtime
                evidence_covers environment_agrees before_typed elements_type
                elements_evaluate with
              ⟨values_typed, after_typed, extension⟩
            exact ⟨pack.hasType values_typed, after_typed, extension⟩
    | .unary layout operand_evaluates applies => by
        cases typing with
        | unary operand_type operator_type =>
            have owned_eq := ordinaryRequirementLayout_eq
              requirements_valid layout
            subst owned_eq
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed operand_type
                operand_evaluates with
              ⟨operand_typed, middle_typed, operand_extension⟩
            rcases preserveUnaryRec program_well_formed runtime
                middle_typed operand_typed operator_type applies with
              ⟨result_typed, after_typed, operation_extension⟩
            exact ⟨result_typed, after_typed,
              operand_extension.trans operation_extension⟩
    | .binaryShortCircuit layout left_evaluates circuit owned_empty => by
        cases typing with
        | binary left_type right_type operator_type =>
            have owned_eq := ordinaryRequirementLayout_eq
              requirements_valid layout
            subst owned_eq
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed left_type
                left_evaluates with
              ⟨left_typed, after_typed, extension⟩
            cases circuit <;> cases operator_type
            all_goals try { rename_i kind; cases kind }
            all_goals try { rename_i dispatch profile proof; cases dispatch }
            all_goals exact ⟨.bool _, after_typed, extension⟩
    | .binaryEvaluateRight layout left_evaluates evaluate_right right_evaluates
        applies => by
        cases typing with
        | binary left_type right_type operator_type =>
            have owned_eq := ordinaryRequirementLayout_eq
              requirements_valid layout
            subst owned_eq
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed left_type
                left_evaluates with
              ⟨left_typed, left_heap_typed, left_extension⟩
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers (environment_agrees.mono left_extension)
                left_heap_typed right_type right_evaluates with
              ⟨right_typed, right_heap_typed, right_extension⟩
            rcases preserveBinaryRec program_well_formed runtime
                right_heap_typed (left_typed.mono right_extension) right_typed
                operator_type applies with
              ⟨result_typed, after_typed, operation_extension⟩
            exact ⟨result_typed, after_typed,
              (left_extension.trans right_extension).trans operation_extension⟩
    | .conditionalTrue layout condition_evaluates branch_evaluates => by
        cases typing with
        | conditional condition_type then_type else_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed condition_type
                condition_evaluates with
              ⟨condition_typed, middle_typed, condition_extension⟩
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers (environment_agrees.mono condition_extension)
                middle_typed then_type branch_evaluates with
              ⟨value_typed, after_typed, branch_extension⟩
            exact ⟨value_typed, after_typed,
              condition_extension.trans branch_extension⟩
    | .conditionalFalse layout condition_evaluates branch_evaluates => by
        cases typing with
        | conditional condition_type then_type else_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed condition_type
                condition_evaluates with
              ⟨condition_typed, middle_typed, condition_extension⟩
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers (environment_agrees.mono condition_extension)
                middle_typed else_type branch_evaluates with
              ⟨value_typed, after_typed, branch_extension⟩
            exact ⟨value_typed, after_typed,
              condition_extension.trans branch_extension⟩
    | @ExpressionFormEvaluates.lambda _ _ _ _ _ _ parameters returnType body _ _
        layout => by
        cases typing with
        | @lambda _ lambdaContext finalContext parameters parameterTypes returnType
            body bodyFacts names_unique parameters_extend body_type body_completes =>
            rcases occurrence with ⟨id, node, contains, node_form, node_raw⟩
            have body_types :=
              Solcore.SourceSemantics.Dynamic.MonoBindersExtend.bodyTypes_eq
                parameters_extend
            have form_typed := ExpressionFormHasRawType.lambda names_unique
              parameters_extend body_type body_completes
            have code : ClosureCodeValid context {
                parameters := parameters
                resultType := returnType
                body := body
                source := source
                captured := environment
                context := context
                evidence := evidence
              } := {
              owner := runtime.owner
              closed := runtime.closed
              variables_closed := runtime.variables_closed
              residual_variables_open := runtime.residual_variables_open
              graph := runtime.graph
              requirement_ledger := runtime.requirements
              occurrence := ⟨id, node, contains, node_form, by
                  simpa [body_types] using node_raw, by
                  rw [node_form]
                  simpa [body_types] using form_typed⟩
            }
            exact ⟨by
                simpa [body_types] using
                  (ValueHasType.closure (context := context) (heap := before)
                    (function := {
                      parameters := parameters
                      resultType := returnType
                      body := body
                      source := source
                      captured := environment
                      context := context
                      evidence := evidence
                    }) rfl code evidence_covers environment_agrees),
              before_typed, .refl before⟩
    | @ExpressionFormEvaluates.directCall _ _ _ _ _ _ argumentsHeap _ _ _
        instantiation _ _ argumentValues
        calleeEvidence _ _ _ callee_contains callee_form callee_requirements
        callee_coercions dynamic_valid arguments_evaluate call_evidence applies => by
        cases typing with
        | @directCall _ callee arguments instantiation parameterTypes resultType
            predicates callee_valid application arguments_type =>
            rcases preserveExpressionsRec program_well_formed runtime
                evidence_covers environment_agrees before_typed arguments_type
                arguments_evaluate with
              ⟨arguments_typed, arguments_heap_typed, arguments_extension⟩
            cases application with
            | intro signature_mem valid declaration_eq parameter_types_eq
                result_type_eq function_type_eq predicates_eq =>
                cases call_evidence with
                | intro coercions_eq requirements_eq produces =>
                    have callee_typed : ValueHasType context argumentsHeap
                        (.global ⟨instantiation, calleeEvidence⟩)
                        (.function (Ty.productMany parameterTypes) rawType) := by
                      rw [← function_type_eq]
                      exact .global dynamic_valid
                        ⟨produces.valid, by
                        intro predicate member
                        exact produces.supplies predicate member⟩
                    rcases ValuesPack.exists_pack argumentValues with
                      ⟨packed, pack⟩
                    have packed_typed := pack.hasType arguments_typed
                    rcases preserveCallableRec program_well_formed
                        runtime arguments_heap_typed callee_typed pack packed_typed
                        applies with
                      ⟨result_typed, after_typed, call_extension⟩
                    exact ⟨result_typed, after_typed,
                      arguments_extension.trans call_extension⟩
    | @ExpressionFormEvaluates.builtinCall _ _ _ _ _ _ argumentsHeap _ _ _
        function _ _ argumentValues _ layout
        arguments_evaluate applies => by
        cases typing with
        | @builtinCall _ callee arguments function callee_valid arguments_type =>
            rcases preserveExpressionsRec program_well_formed runtime
                evidence_covers environment_agrees before_typed arguments_type
                arguments_evaluate with
              ⟨arguments_typed, arguments_heap_typed, arguments_extension⟩
            have callee_typed : ValueHasType context argumentsHeap
                (.builtin ⟨function⟩)
                (.function (Ty.productMany function.parameterTypes)
                  function.returnType) := by
              simpa [BuiltinFunctionId.type] using
                (ValueHasType.builtin (context := context)
                  (heap := argumentsHeap) ⟨function⟩)
            rcases ValuesPack.exists_pack argumentValues with ⟨packed, pack⟩
            have packed_typed := pack.hasType arguments_typed
            rcases preserveCallableRec program_well_formed runtime
                arguments_heap_typed callee_typed pack packed_typed applies with
              ⟨result_typed, after_typed, call_extension⟩
            exact ⟨result_typed, after_typed,
              arguments_extension.trans call_extension⟩
    | .indirectCall requirements_eq callee_evaluates arguments_evaluate
        pack_before argument_coercions pack_after source_arity applied_arity
        applies => by
        cases typing with
        | indirectCall callee_type arguments_type application =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed callee_type
                callee_evaluates with
              ⟨callee_typed, callee_heap_typed, callee_extension⟩
            rcases preserveExpressionsRec program_well_formed runtime
                evidence_covers (environment_agrees.mono callee_extension)
                callee_heap_typed arguments_type arguments_evaluate with
              ⟨arguments_typed, argument_heap_typed, argument_extension⟩
            cases application with
            | intro count_eq before_eq after_eq path_valid =>
                have packed_typed := pack_before.hasType arguments_typed
                rw [← before_eq] at packed_typed
                rcases preservePathRec program_well_formed runtime
                    argument_heap_typed packed_typed path_valid
                    argument_coercions with
                  ⟨coerced_typed, coerced_heap_typed, coercion_extension⟩
                have callable_typed := callee_typed.mono
                  (argument_extension.trans coercion_extension)
                rcases preserveCallableRec program_well_formed runtime
                    coerced_heap_typed callable_typed pack_after coerced_typed
                    applies with
                  ⟨result_typed, after_typed, call_extension⟩
                exact ⟨result_typed, after_typed,
                  ((callee_extension.trans argument_extension).trans
                    coercion_extension).trans call_extension⟩
    | .constructor layout dynamic_valid arguments_evaluate => by
        cases typing with
        | constructor valid arguments_type =>
            rcases preserveExpressionsRec program_well_formed runtime
                evidence_covers environment_agrees before_typed arguments_type
                arguments_evaluate with
              ⟨arguments_typed, after_typed, extension⟩
            exact ⟨.constructed dynamic_valid arguments_typed, after_typed,
              extension⟩
    | .member layout base_evaluates selected_at => by
        cases typing with
        | member base_type member_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed base_type
                base_evaluates with
              ⟨base_typed, after_typed, extension⟩
            exact ⟨
              (Solcore.SourceSemantics.Dynamic.UniformMemberProjection.preservesType
                member_type).read _ _ _ base_typed selected_at,
              after_typed, extension⟩
    | .proxy layout => by
        cases typing with
        | proxy inner_well_formed =>
            exact ⟨.proxy _, before_typed, .refl before⟩
    | .indexFound layout base_evaluates index_evaluates lookup => by
        cases typing with
        | @index _ base key keyType valueType base_type key_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed base_type
                base_evaluates with
              ⟨base_typed, middle_typed, base_extension⟩
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers (environment_agrees.mono base_extension)
                middle_typed key_type index_evaluates with
              ⟨key_typed, after_typed, index_extension⟩
            rcases (base_typed.mono index_extension).mappingComponents with
              ⟨rfl, rfl, entries_typed⟩
            exact ⟨lookup.preserves entries_typed, after_typed,
              base_extension.trans index_extension⟩
    | .indexDefault layout base_evaluates index_evaluates absent defaulted => by
        cases typing with
        | @index _ base key keyType valueType base_type key_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed base_type
                base_evaluates with
              ⟨base_typed, middle_typed, base_extension⟩
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers (environment_agrees.mono base_extension)
                middle_typed key_type index_evaluates with
              ⟨key_typed, after_typed, index_extension⟩
            rcases (base_typed.mono index_extension).mappingComponents with
              ⟨rfl, rfl, entries_typed⟩
            exact ⟨defaulted.hasType, after_typed,
              base_extension.trans index_extension⟩
    termination_by structural evaluation

  private theorem preserveExpressionsRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment}
      {before after : Heap} {ids : List ExpressionId} {values : List Value}
      {types : List Ty}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : ExpressionsHaveTypes source context ids types)
      (evaluation : ExpressionsEvaluate program context evidence source environment
        before ids values after) :
      ValuesHaveTypes context after values types /\
        HeapWellTyped context after /\ HeapTypesExtend before after :=
    match evaluation with
    | .nil => by
        cases typing
        exact ⟨.nil, before_typed, .refl before⟩
    | .cons head tail => by
        cases typing with
        | cons head_type tail_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed head_type head with
              ⟨head_typed, middle_typed, head_extension⟩
            rcases preserveExpressionsRec (program := program)
                (context := context) (evidence := evidence) (source := source)
                (environment := environment) program_well_formed runtime
                evidence_covers (environment_agrees.mono head_extension)
                middle_typed tail_type tail with
              ⟨tail_typed, after_typed, tail_extension⟩
            exact ⟨.cons (head_typed.mono tail_extension) tail_typed,
              after_typed, head_extension.trans tail_extension⟩
    termination_by structural evaluation

  private theorem preserveProjectionsRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment}
      {before after : Heap} {projections : List PlaceProjection}
      {evaluated : List EvaluatedProjection} {sourceType finalType : Ty}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : SourceProjectionsHaveType source context sourceType projections
        finalType)
      (evaluation : SourceProjectionsEvaluate program context evidence source
        environment before projections evaluated after) :
      EvaluatedProjectionsHaveType context after sourceType evaluated finalType /\
        HeapWellTyped context after /\ HeapTypesExtend before after :=
    match evaluation with
    | .nil => by
        cases typing
        exact ⟨.nil _, before_typed, .refl before⟩
    | .member tail => by
        cases typing with
        | member selected rest_type =>
            rcases preserveProjectionsRec (program := program)
                (context := context) (evidence := evidence) (source := source)
                (environment := environment) program_well_formed runtime
                evidence_covers environment_agrees before_typed rest_type tail with
              ⟨path_typed, after_typed, extension⟩
            exact ⟨.member selected
                (UniformMemberProjection.preservesType selected) path_typed,
              after_typed, extension⟩
    | .index head tail => by
        cases typing with
        | index key_type rest_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed key_type head with
              ⟨key_typed, middle_typed, head_extension⟩
            rcases preserveProjectionsRec (program := program)
                (context := context) (evidence := evidence) (source := source)
                (environment := environment) program_well_formed runtime
                evidence_covers (environment_agrees.mono head_extension)
                middle_typed rest_type tail with
              ⟨path_typed, after_typed, tail_extension⟩
            exact ⟨.index (key_typed.mono tail_extension) path_typed,
              after_typed, head_extension.trans tail_extension⟩
    termination_by structural evaluation

  private theorem preservePlaceRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment}
      {before after : Heap} {place : PlaceResolution} {target : ResolvedPlace}
      {type : Ty}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : SourcePlaceHasType source context place type)
      (evaluation : SourcePlaceResolves program context evidence source environment
        before place target after) :
      exists rootType,
        ResolvedPlaceHasType context after target rootType type /\
          HeapWellTyped context after /\ HeapTypesExtend before after :=
    match evaluation with
    | @SourcePlaceResolves.intro _ _ _ _ _ _ _ _ location initialCell
        currentCell evaluated initial selected dynamic_lookup initial_read evaluate
        current_read initial_value selection => by
      cases typing with
      | @intro _ _ rootType finalType writable projections_type stored_type_eq =>
        rcases writable.scheme with
          ⟨scheme, static_lookup, scheme_well_formed, monomorphic, body_eq⟩
        rcases preserveProjectionsRec program_well_formed runtime
            evidence_covers environment_agrees before_typed projections_type
            evaluate with
          ⟨evaluated_typed, after_typed, extension⟩
        rcases environment_agrees.lookup static_lookup with
          ⟨staticLocation, staticCell, static_lookup_runtime, static_read,
            static_cell_type, _storage⟩
        have location_eq := dynamic_lookup.functional static_lookup_runtime
        subst staticLocation
        have initial_cell_eq := initial_read.functional static_read
        subst staticCell
        rcases extension _ _ initial_read with
          ⟨updatedCell, updated_read, updated_type, _⟩
        have updated_cell_eq := current_read.functional updated_read
        subst updatedCell
        have root_type : currentCell.type = rootType :=
          updated_type.trans (static_cell_type.trans body_eq)
        have initial_typed :=
          initial_value.preserves (after_typed _ current_read.member)
        have initial_at_root :
            OptionalValueHasType context after initial rootType := by
          rw [← root_type]
          exact initial_typed
        have selected_typed :=
          selection.preserves evaluated_typed initial_at_root
        refine ⟨rootType, ?_, after_typed, extension⟩
        exact {
          root_type := root_type
          value_type := stored_type_eq
          projections := evaluated_typed
          selected := by simpa [stored_type_eq] using selected_typed
        }
    termination_by structural evaluation

  private theorem preserveAssignmentRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment}
      {before after : Heap} {assignment : AssignmentResolution}
      {operator : Syntax.ValueAssignOp} {right : ExpressionId}
      {combine : Option Value → Value → Value → Prop}
      {place : PlaceResolution} {rightExpression : ExpressionId}
      {updatedRoot : Value}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : SourceAssignmentHasType source context assignment operator right)
      (combine_eq : combine = AssignmentValueApplies operator)
      (place_eq : place = assignment.target)
      (right_eq : rightExpression = right)
      (evaluation : SourcePlaceAssignment program context evidence source
        combine environment before place rightExpression updatedRoot after) :
      HeapWellTyped context after /\ HeapTypesExtend before after :=
    match evaluation with
    | @SourcePlaceAssignment.intro _ _ _ _ _ _ _ targetHeap rhsHeap _ _ target
        _ rightValue _ resolve evaluate_right write => by
      cases typing with
      | @equal _ _ _ type target_type value_type requirements_eq =>
            have aligned_target_type : SourcePlaceHasType source context place type :=
              place_eq.symm ▸ target_type
            have aligned_value_type :
                ExpressionHasType source context rightExpression type :=
              right_eq.symm ▸ value_type
            rcases preservePlaceRec program_well_formed runtime
                evidence_covers environment_agrees before_typed aligned_target_type
                resolve with
              ⟨rootType, target_typed, target_heap_typed, target_extension⟩
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers (environment_agrees.mono target_extension)
                target_heap_typed aligned_value_type evaluate_right with
              ⟨right_typed, rhs_heap_typed, rhs_extension⟩
            have target_rhs_typed := target_typed.mono rhs_extension
            cases write with
            | intro current_read root_type_eq initial_value update heap_write =>
                rename_i currentCell initial
                have initial_typed :=
                  initial_value.preserves (rhs_heap_typed _ current_read.member)
                have initial_root_typed :
                    OptionalValueHasType context rhsHeap initial rootType := by
                  rw [← target_rhs_typed.root_type, ← root_type_eq]
                  exact initial_typed
                have modify_typed : LeafModificationPreservesType context rhsHeap
                    (fun _ updated => combine target.selected rightValue updated)
                    type := by
                  intro current updated current_typed applies
                  rw [combine_eq] at applies
                  exact applies.equalPreserves right_typed
                have updated_typed := update.preserves
                  target_rhs_typed.projections initial_root_typed modify_typed
                have updated_cell_typed :
                    ValueHasType context rhsHeap updatedRoot currentCell.type := by
                  rw [root_type_eq, target_rhs_typed.root_type]
                  exact updated_typed
                have final_typed := rhs_heap_typed.write current_read
                  (.some updated_cell_typed) heap_write
                exact ⟨final_typed,
                  (target_extension.trans rhs_extension).trans
                    (HeapTypesExtend.of_write heap_write)⟩
      | wordCompound kind target_type value_type requirements_eq =>
            have aligned_target_type : SourcePlaceHasType source context place .word :=
              place_eq.symm ▸ target_type
            have aligned_value_type :
                ExpressionHasType source context rightExpression .word :=
              right_eq.symm ▸ value_type
            rcases preservePlaceRec program_well_formed runtime
                evidence_covers environment_agrees before_typed aligned_target_type
                resolve with
              ⟨rootType, target_typed, target_heap_typed, target_extension⟩
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers (environment_agrees.mono target_extension)
                target_heap_typed aligned_value_type evaluate_right with
              ⟨right_typed, rhs_heap_typed, rhs_extension⟩
            have target_rhs_typed := target_typed.mono rhs_extension
            cases write with
            | intro current_read root_type_eq initial_value update heap_write =>
                rename_i currentCell initial
                have initial_typed :=
                  initial_value.preserves (rhs_heap_typed _ current_read.member)
                have initial_root_typed :
                    OptionalValueHasType context rhsHeap initial rootType := by
                  rw [← target_rhs_typed.root_type, ← root_type_eq]
                  exact initial_typed
                have modify_typed : LeafModificationPreservesType context rhsHeap
                    (fun _ updated => combine target.selected rightValue updated)
                    .word := by
                  intro current updated current_typed applies
                  rw [combine_eq] at applies
                  exact applies.wordCompoundPreserves kind
                    target_rhs_typed.selected right_typed
                have updated_typed := update.preserves
                  target_rhs_typed.projections initial_root_typed modify_typed
                have updated_cell_typed :
                    ValueHasType context rhsHeap updatedRoot currentCell.type := by
                  rw [root_type_eq, target_rhs_typed.root_type]
                  exact updated_typed
                have final_typed := rhs_heap_typed.write current_read
                  (.some updated_cell_typed) heap_write
                exact ⟨final_typed,
                  (target_extension.trans rhs_extension).trans
                    (HeapTypesExtend.of_write heap_write)⟩
  private theorem preserveSnapshotRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment}
      {before after : Heap} {assignment : AssignmentResolution}
      {modify : Option Value → Value → Prop} {place : PlaceResolution}
      {updatedRoot : Value}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : SourceBitNotAssignmentValid source context assignment)
      (modify_eq : modify = BitNotSnapshot)
      (place_eq : place = assignment.target)
      (evaluation : SourcePlaceSnapshotUpdate program context evidence source
        modify environment before place updatedRoot after) :
      HeapWellTyped context after /\ HeapTypesExtend before after :=
    match evaluation with
    | @SourcePlaceSnapshotUpdate.intro _ _ _ _ _ _ _ selectedHeap _ _ target _
        resolve write => by
      cases typing with
      | intro target_type requirements_eq =>
            have aligned_target_type : SourcePlaceHasType source context place .word :=
              place_eq.symm ▸ target_type
            rcases preservePlaceRec program_well_formed runtime
                evidence_covers environment_agrees before_typed aligned_target_type
                resolve with
              ⟨rootType, target_typed, selected_heap_typed, target_extension⟩
            cases write with
            | intro current_read root_type_eq initial_value update heap_write =>
                rename_i currentCell initial
                have initial_typed := initial_value.preserves
                  (selected_heap_typed _ current_read.member)
                have initial_root_typed :
                    OptionalValueHasType context selectedHeap initial rootType := by
                  rw [← target_typed.root_type, ← root_type_eq]
                  exact initial_typed
                have modify_typed : LeafModificationPreservesType context
                    selectedHeap
                    (fun _ updated => modify target.selected updated) .word := by
                  intro current updated current_typed modifies
                  rw [modify_eq] at modifies
                  exact modifies.preserves target_typed.selected
                have updated_typed := update.preserves target_typed.projections
                  initial_root_typed modify_typed
                have updated_cell_typed : ValueHasType context selectedHeap
                    updatedRoot currentCell.type := by
                  rw [root_type_eq, target_typed.root_type]
                  exact updated_typed
                have final_typed := selected_heap_typed.write current_read
                  (.some updated_cell_typed) heap_write
                exact ⟨final_typed,
                  target_extension.trans (HeapTypesExtend.of_write heap_write)⟩
  private theorem preserveUnaryRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {before after : Heap}
      {operator : Syntax.UnaryOp} {requirements : List RequirementId}
      {input output : Value} {operandType resultType : Ty}
      (runtime : SourceRuntimeValid program context source)
      (before_typed : HeapWellTyped context before)
      (input_typed : ValueHasType context before input operandType)
      (typing : UnaryOperatorHasType context operator operandType resultType
        requirements)
      (evaluation : UnaryOperationApplies program context evidence before operator
        requirements input output after) :
      ValueHasType context after output resultType /\
        HeapWellTyped context after /\ HeapTypesExtend before after :=
    match evaluation with
    | .primitive applies => by
        cases typing with
        | logicalNot =>
            exact ⟨applies.preserves .logicalNot input_typed, before_typed,
              .refl before⟩
        | wordBitNot =>
            exact ⟨applies.preserves .wordBitNot input_typed, before_typed,
              .refl before⟩
        | integerBitNot =>
            exact ⟨applies.preserves .integerBitNot input_typed, before_typed,
              .refl before⟩
        | trait dispatch profile requirements_prove =>
            cases requirements_prove
            cases profile
    | .method dispatch selected invokes => by
        cases typing with
        | logicalNot => cases selected
        | wordBitNot => cases selected
        | integerBitNot => cases selected
        | trait static_dispatch profile requirements_prove =>
            rcases unaryDispatch_functional static_dispatch dispatch with
              ⟨rfl, rfl⟩
            obtain ⟨lexicalContext, facts, certificate, result_eq⟩ :=
              selected.certificateOfProfile program_well_formed
                runtime.signatures runtime.requirements.idsUnique profile
                  requirements_prove
            have signatures_eq :=
              certificate.signatures_eq.trans runtime.signatures.symm
            have body_heap_typed := before_typed.transportClosed signatures_eq
              runtime.closed certificate.type_parameters_empty
              runtime.variables_closed certificate.residual_type_variables_open
            have body_input_typed := input_typed.transportClosed signatures_eq
              runtime.closed certificate.type_parameters_empty
              runtime.variables_closed certificate.residual_type_variables_open
            have body_arguments_typed : ValuesHaveTypes _ before
                [input] [operandType] := .cons body_input_typed .nil
            have invocation := preserveBodyRec program_well_formed
              certificate (selected_covers selected) body_heap_typed
              body_arguments_typed invokes
            have result_at_caller := invocation.result_typed.transportClosed
              signatures_eq.symm certificate.type_parameters_empty runtime.closed
              certificate.type_variables_empty runtime.residual_variables_open
            have heap_at_caller := invocation.heap_typed.transportClosed
              signatures_eq.symm certificate.type_parameters_empty runtime.closed
              certificate.type_variables_empty runtime.residual_variables_open
            rw [result_eq] at result_at_caller
            exact ⟨result_at_caller, heap_at_caller, invocation.heap_extends⟩
    termination_by structural evaluation

  private theorem preserveBinaryRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {before after : Heap}
      {operator : Syntax.BinaryOp} {requirements : List RequirementId}
      {left right output : Value} {operandType resultType : Ty}
      (runtime : SourceRuntimeValid program context source)
      (before_typed : HeapWellTyped context before)
      (left_typed : ValueHasType context before left operandType)
      (right_typed : ValueHasType context before right operandType)
      (typing : BinaryOperatorHasType context operator operandType operandType
        resultType requirements)
      (evaluation : BinaryOperationApplies program context evidence before operator
        requirements left right output after) :
      ValueHasType context after output resultType /\
        HeapWellTyped context after /\ HeapTypesExtend before after :=
    match evaluation with
    | .primitive applies => by
        cases typing with
        | wordArithmetic kind =>
            exact ⟨applies.preserves (.wordArithmetic kind) left_typed right_typed,
              before_typed, .refl before⟩
        | integerArithmetic kind =>
            exact ⟨applies.preserves (.integerArithmetic kind) left_typed right_typed,
              before_typed, .refl before⟩
        | wordComparison kind =>
            exact ⟨applies.preserves (.wordComparison kind) left_typed right_typed,
              before_typed, .refl before⟩
        | integerComparison kind =>
            exact ⟨applies.preserves (.integerComparison kind) left_typed right_typed,
              before_typed, .refl before⟩
        | booleanAnd =>
            exact ⟨applies.preserves .booleanAnd left_typed right_typed,
              before_typed, .refl before⟩
        | booleanOr =>
            exact ⟨applies.preserves .booleanOr left_typed right_typed,
              before_typed, .refl before⟩
        | trait dispatch profile requirements_prove =>
            cases requirements_prove
            cases profile
    | .method dispatch selected invokes => by
        cases typing with
        | wordArithmetic kind => cases selected
        | integerArithmetic kind => cases selected
        | wordComparison kind => cases selected
        | integerComparison kind => cases selected
        | booleanAnd => cases selected
        | booleanOr => cases selected
        | trait static_dispatch profile requirements_prove =>
            rcases binaryDispatch_functional static_dispatch dispatch with
              ⟨rfl, rfl⟩
            obtain ⟨lexicalContext, facts, certificate, result_eq⟩ :=
              selected.certificateOfProfile program_well_formed
                runtime.signatures runtime.requirements.idsUnique profile
                  requirements_prove
            have signatures_eq :=
              certificate.signatures_eq.trans runtime.signatures.symm
            have body_heap_typed := before_typed.transportClosed signatures_eq
              runtime.closed certificate.type_parameters_empty
              runtime.variables_closed certificate.residual_type_variables_open
            have body_left_typed := left_typed.transportClosed signatures_eq
              runtime.closed certificate.type_parameters_empty
              runtime.variables_closed certificate.residual_type_variables_open
            have body_right_typed := right_typed.transportClosed signatures_eq
              runtime.closed certificate.type_parameters_empty
              runtime.variables_closed certificate.residual_type_variables_open
            have body_arguments_typed : ValuesHaveTypes _ before
                [left, right] [operandType, operandType] :=
              .cons body_left_typed (.cons body_right_typed .nil)
            have invocation := preserveBodyRec program_well_formed
              certificate (selected_covers selected) body_heap_typed
              body_arguments_typed invokes
            have result_at_caller := invocation.result_typed.transportClosed
              signatures_eq.symm certificate.type_parameters_empty runtime.closed
              certificate.type_variables_empty runtime.residual_variables_open
            have heap_at_caller := invocation.heap_typed.transportClosed
              signatures_eq.symm certificate.type_parameters_empty runtime.closed
              certificate.type_variables_empty runtime.residual_variables_open
            rw [result_eq] at result_at_caller
            exact ⟨result_at_caller, heap_at_caller, invocation.heap_extends⟩
    termination_by structural evaluation

  private theorem preserveStepRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {before after : Heap} {step : CoercionStep}
      {input output : Value}
      (runtime : SourceRuntimeValid program context source)
      (before_typed : HeapWellTyped context before)
      (input_typed : ValueHasType context before input step.source)
      (typing : CoercionStepValid context step)
      (evaluation : CoercionStepExecutes program context evidence before step input
        output after) :
      ValueHasType context after output step.target /\
        HeapWellTyped context after /\ HeapTypesExtend before after :=
    match evaluation with
    | .primitive no_source_method applies => by
        exact CoercionStepExecutes.primitivePreserves before_typed input_typed
          applies
    | .method selected invokes => by
        cases typing with
        | intro profile requirements_prove =>
            obtain ⟨lexicalContext, facts, certificate, result_eq⟩ :=
              selected.coercionCertificateOfProfile program_well_formed
                runtime.signatures runtime.requirements.idsUnique profile
                  requirements_prove
            have signatures_eq :=
              certificate.signatures_eq.trans runtime.signatures.symm
            have body_heap_typed := before_typed.transportClosed signatures_eq
              runtime.closed certificate.type_parameters_empty
              runtime.variables_closed certificate.residual_type_variables_open
            have body_input_typed := input_typed.transportClosed signatures_eq
              runtime.closed certificate.type_parameters_empty
              runtime.variables_closed certificate.residual_type_variables_open
            have body_arguments_typed : ValuesHaveTypes _ before
                [input] [step.source] := .cons body_input_typed .nil
            have invocation := preserveBodyRec program_well_formed
              certificate (selected_covers selected) body_heap_typed
              body_arguments_typed invokes
            have result_at_caller := invocation.result_typed.transportClosed
              signatures_eq.symm certificate.type_parameters_empty runtime.closed
              certificate.type_variables_empty runtime.residual_variables_open
            have heap_at_caller := invocation.heap_typed.transportClosed
              signatures_eq.symm certificate.type_parameters_empty runtime.closed
              certificate.type_variables_empty runtime.residual_variables_open
            rw [result_eq] at result_at_caller
            exact ⟨result_at_caller, heap_at_caller, invocation.heap_extends⟩
    termination_by structural evaluation

  private theorem preservePathRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {before after : Heap} {sourceType targetType : Ty}
      {steps : List CoercionStep} {input output : Value}
      (runtime : SourceRuntimeValid program context source)
      (before_typed : HeapWellTyped context before)
      (input_typed : ValueHasType context before input sourceType)
      (typing : CoercionPathValid context sourceType targetType steps)
      (evaluation : CoercionPathExecutes program context evidence before steps input
        output after) :
      ValueHasType context after output targetType /\
        HeapWellTyped context after /\ HeapTypesExtend before after :=
    match evaluation with
    | .nil => by
        cases typing
        exact ⟨input_typed, before_typed, .refl before⟩
    | .cons head tail => by
        cases typing with
        | cons head_type tail_type =>
            rcases preserveStepRec program_well_formed runtime
                before_typed input_typed head_type head with
              ⟨middle_value_typed, middle_heap_typed, head_extension⟩
            rcases preservePathRec (program := program) (context := context)
                (evidence := evidence) (source := source)
                program_well_formed runtime middle_heap_typed middle_value_typed
                tail_type tail with
              ⟨output_typed, after_heap_typed, tail_extension⟩
            exact ⟨output_typed, after_heap_typed,
              head_extension.trans tail_extension⟩
    termination_by structural evaluation

  private theorem preserveCallableRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context : Context} {callerEvidence invocationEvidence : EvidenceEnvironment}
      {source : TypedSource} {before after : Heap} {callable : Value}
      {arguments : List Value} {result packed : Value}
      {parameterType resultType : Ty}
      (runtime : SourceRuntimeValid program context source)
      (before_typed : HeapWellTyped context before)
      (callable_typed : ValueHasType context before callable
        (.function parameterType resultType))
      (packing : ValuesPack arguments packed)
      (packed_typed : ValueHasType context before packed parameterType)
      (evaluation : CallableApplies program context callerEvidence
        invocationEvidence before callable arguments result after) :
      ValueHasType context after result resultType /\
        HeapWellTyped context after /\ HeapTypesExtend before after :=
    match evaluation with
    | .builtin applies => by
        rcases applies.preserves with ⟨arguments_typed, result_typed⟩
        rcases callable_typed.builtin_inv with type_eq | staged
        · rw [BuiltinFunctionId.type] at type_eq
          cases type_eq
          exact ⟨result_typed, before_typed, .refl before⟩
        · rcases staged with ⟨inner, impossible, inner_typed⟩
          cases impossible
    | @CallableApplies.global _ _ _ _ _ _ function _ _ bodyInstance instantiates
        invocation_eq covers invokes => by
        rcases callable_typed.global_inv with ordinary | staged
        · rcases ordinary with ⟨type_eq, valid, function_evidence⟩
          obtain ⟨inputTypes, lexicalContext, facts, certificate⟩ :=
            instantiates.certificate program_well_formed
          have function_eq :
              Ty.function parameterType resultType =
                .function (Ty.productMany inputTypes) bodyInstance.resultType :=
            type_eq.trans certificate.callable_type
          cases function_eq
          have signatures_eq :
              bodyInstance.context.signatures = context.signatures :=
            certificate.signatures_eq.trans runtime.signatures.symm
          have body_before_typed := before_typed.transportClosed signatures_eq
            runtime.closed certificate.type_parameters_empty
            runtime.variables_closed certificate.residual_type_variables_open
          have body_packed_typed := packed_typed.transportClosed signatures_eq
            runtime.closed certificate.type_parameters_empty
            runtime.variables_closed certificate.residual_type_variables_open
          have arguments_length : arguments.length = inputTypes.length :=
            (bodyArguments_length invokes).trans
              certificate.typing.inputs_extend.length_eq
          have arguments_typed := packing.unpackTypes body_packed_typed
            arguments_length
          have invocation := preserveBodyRec program_well_formed
            certificate.toBodyInstanceTypingCertificate covers body_before_typed
            arguments_typed invokes
          exact ⟨
            invocation.result_typed.transportClosed signatures_eq.symm
              certificate.type_parameters_empty runtime.closed
              certificate.type_variables_empty runtime.residual_variables_open,
            invocation.heap_typed.transportClosed signatures_eq.symm
              certificate.type_parameters_empty runtime.closed
              certificate.type_variables_empty runtime.residual_variables_open,
            invocation.heap_extends⟩
        · rcases staged with ⟨inner, impossible, inner_typed⟩
          cases impossible
    | @CallableApplies.closure _ _ _ _ _ _ _ function _ environment outcome _ parameterTypes
        callContext finalContext invocation_eq frame parameters_extend allocate
        execute returned => by
        rcases callable_typed.closure_function_inv with
          ⟨parameter_eq, result_eq, signatures_eq, code, closure_evidence,
            captures⟩
        subst parameterType
        subst resultType
        rcases code.occurrence with
          ⟨id, node, contains, node_form, node_raw, form_typing⟩
        rw [node_form] at form_typing
        generalize raw_type_eq :
          Ty.function
            (Ty.productMany
              (function.parameters.map fun binder => binder.scheme.body))
            function.resultType = rawType at form_typing
        generalize plan_eq :
          ExpressionRequirementPlan.ordinary [] = plan at form_typing
        cases form_typing with
        | @lambda _ staticCallContext staticFinalContext _ staticParameterTypes _
            _ bodyFacts names_unique static_parameters_extend body_type
            body_completes =>
            have call_context_eq :=
              Solcore.SourceSemantics.Dynamic.MonoBindersExtend.functional
                parameters_extend static_parameters_extend
            subst call_context_eq
            have closure_before_typed := before_typed.transportClosed signatures_eq
              runtime.closed code.closed runtime.variables_closed
              code.residual_variables_open
            have closure_packed_typed := packed_typed.transportClosed signatures_eq
              runtime.closed code.closed runtime.variables_closed
              code.residual_variables_open
            have arguments_length :
                arguments.length =
                  (function.parameters.map
                    fun binder => binder.scheme.body).length := by
              simpa using allocate.length_eq.symm
            have arguments_typed := packing.unpackTypes closure_packed_typed
              arguments_length
            have bound_typed := allocate.preservesHeapTyping closure_before_typed
              arguments_typed
            have allocation_extension := allocate.extendsHeapTypes
            have bound_environment := allocate.preservesEnvironmentAgreement
              (monoBinders_toBinders static_parameters_extend)
              (monoBinders_monomorphic static_parameters_extend) captures
            have fields :=
              Solcore.SourceSemantics.Dynamic.MonoBindersExtend.runtimeContextFields
                static_parameters_extend
            have call_closed := fields.targetClosed code.closed
            have bound_at_call := bound_typed.transportClosed fields.signatures
              code.closed call_closed code.variables_closed
              (fields.targetResidualVariablesOpen code.residual_variables_open)
            have call_evidence := fields.covers closure_evidence
            have closure_runtime :
                SourceRuntimeValid program function.context function.source := {
              signatures := frame.signatures
              graph := code.graph
              owner := code.owner
              closed := code.closed
              variables_closed := code.variables_closed
              residual_variables_open := code.residual_variables_open
              requirements := code.requirement_ledger
            }
            rcases (preserveFunctionStatementsRecWithControl program_well_formed
                (closure_runtime.transport fields) call_evidence bound_environment
                bound_at_call body_type body_completes execute).1 with
              ⟨after_typed, execution_extension, outcome_typed⟩
            rw [returned] at outcome_typed
            cases outcome_typed with
            | returned result_typed =>
                have outer_signatures :=
                  signatures_eq.symm.trans fields.signatures.symm
                exact ⟨
                  result_typed.transportClosed outer_signatures call_closed
                    runtime.closed
                    (fields.targetVariablesClosed code.variables_closed)
                    runtime.residual_variables_open,
                  after_typed.transportClosed outer_signatures call_closed
                    runtime.closed
                    (fields.targetVariablesClosed code.variables_closed)
                    runtime.residual_variables_open,
                  allocation_extension.trans execution_extension⟩
    | @CallableApplies.closureUnit _ _ _ _ _ _ _ function _ environment outcome parameterTypes
        callContext finalContext invocation_eq frame result_unit parameters_extend
        allocate execute fell_through => by
        rcases callable_typed.closure_function_inv with
          ⟨parameter_eq, result_eq, signatures_eq, code, closure_evidence,
            captures⟩
        subst parameterType
        subst resultType
        rcases code.occurrence with
          ⟨id, node, contains, node_form, node_raw, form_typing⟩
        rw [node_form] at form_typing
        generalize raw_type_eq :
          Ty.function
            (Ty.productMany
              (function.parameters.map fun binder => binder.scheme.body))
            function.resultType = rawType at form_typing
        generalize plan_eq :
          ExpressionRequirementPlan.ordinary [] = plan at form_typing
        cases form_typing with
        | @lambda _ staticCallContext staticFinalContext _ staticParameterTypes _
            _ bodyFacts names_unique static_parameters_extend body_type
            body_completes =>
            have call_context_eq :=
              Solcore.SourceSemantics.Dynamic.MonoBindersExtend.functional
                parameters_extend static_parameters_extend
            subst call_context_eq
            have closure_before_typed := before_typed.transportClosed signatures_eq
              runtime.closed code.closed runtime.variables_closed
              code.residual_variables_open
            have closure_packed_typed := packed_typed.transportClosed signatures_eq
              runtime.closed code.closed runtime.variables_closed
              code.residual_variables_open
            have arguments_length :
                arguments.length =
                  (function.parameters.map
                    fun binder => binder.scheme.body).length := by
              simpa using allocate.length_eq.symm
            have arguments_typed := packing.unpackTypes closure_packed_typed
              arguments_length
            have bound_typed := allocate.preservesHeapTyping closure_before_typed
              arguments_typed
            have allocation_extension := allocate.extendsHeapTypes
            have bound_environment := allocate.preservesEnvironmentAgreement
              (monoBinders_toBinders static_parameters_extend)
              (monoBinders_monomorphic static_parameters_extend) captures
            have fields :=
              Solcore.SourceSemantics.Dynamic.MonoBindersExtend.runtimeContextFields
                static_parameters_extend
            have call_closed := fields.targetClosed code.closed
            have bound_at_call := bound_typed.transportClosed fields.signatures
              code.closed call_closed code.variables_closed
              (fields.targetResidualVariablesOpen code.residual_variables_open)
            have call_evidence := fields.covers closure_evidence
            have closure_runtime :
                SourceRuntimeValid program function.context function.source := {
              signatures := frame.signatures
              graph := code.graph
              owner := code.owner
              closed := code.closed
              variables_closed := code.variables_closed
              residual_variables_open := code.residual_variables_open
              requirements := code.requirement_ledger
            }
            rcases (preserveFunctionStatementsRecWithControl program_well_formed
                (closure_runtime.transport fields) call_evidence bound_environment
                bound_at_call body_type body_completes execute).1 with
              ⟨after_typed, execution_extension, outcome_typed⟩
            rcases fell_through with ⟨finalEnvironment, rfl⟩
            cases outcome_typed with
            | fallthrough final_agrees =>
                have outer_signatures :=
                  signatures_eq.symm.trans fields.signatures.symm
                exact ⟨by rw [result_unit]; exact .unit,
                  after_typed.transportClosed outer_signatures call_closed
                    runtime.closed
                    (fields.targetVariablesClosed code.variables_closed)
                    runtime.residual_variables_open,
                  allocation_extension.trans execution_extension⟩
    termination_by structural evaluation

  private theorem preserveBodyRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {bodyInstance : BodyInstance} {evidence : EvidenceEnvironment}
      {before after : Heap} {arguments : List Value} {result : Value}
      {inputTypes : List Ty} {lexicalContext : Context} {facts : BodyFacts}
      (certificate : BodyInstanceTypingCertificate program bodyInstance inputTypes
        lexicalContext facts)
      (evidence_covers : evidence.Covers bodyInstance.context)
      (before_typed : HeapWellTyped bodyInstance.context before)
      (arguments_typed : ValuesHaveTypes bodyInstance.context before arguments
        inputTypes)
      (evaluation : BodyInvokes program bodyInstance evidence before arguments
        result after) :
      BodyInvocationPreserved bodyInstance before after result :=
    match evaluation with
    | .returned covers roots_eq inputs_extend allocate execute returned => by
        rcases certificate.typing.body_typed with
          ⟨staticFinalContext, body_type, no_expression_roots, completes⟩
        have aligned_body_type := roots_eq.filterMap_eq ▸ body_type
        have lexical_context_eq :=
          Solcore.SourceSemantics.Dynamic.MonoBindersExtend.functional
            inputs_extend certificate.typing.inputs_extend
        subst lexical_context_eq
        have input_types_eq : _ = inputTypes :=
          (Solcore.SourceSemantics.Dynamic.MonoBindersExtend.bodyTypes_eq
            inputs_extend).symm.trans
            (Solcore.SourceSemantics.Dynamic.MonoBindersExtend.bodyTypes_eq
              certificate.typing.inputs_extend)
        subst input_types_eq
        have binder_arguments_typed : ValuesHaveTypes bodyInstance.context before
            arguments (bodyInstance.source.inputs.map
              fun binder => binder.scheme.body) := by
          rw [Solcore.SourceSemantics.Dynamic.MonoBindersExtend.bodyTypes_eq
            certificate.typing.inputs_extend]
          exact arguments_typed
        have bound_typed := allocate.preservesHeapTyping before_typed
          binder_arguments_typed
        have allocation_extension := allocate.extendsHeapTypes
        have base_environment : EnvironmentAgrees before
            bodyInstance.context.locals [] := by
          rw [certificate.locals_empty]
          exact .nil
        have bound_environment := allocate.preservesEnvironmentAgreement
          (monoBinders_toBinders certificate.typing.inputs_extend)
          (monoBinders_monomorphic certificate.typing.inputs_extend)
          base_environment
        have fields :=
          Solcore.SourceSemantics.Dynamic.MonoBindersExtend.runtimeContextFields
            certificate.typing.inputs_extend
        have lexical_closed := fields.targetClosed
          certificate.type_parameters_empty
        have bound_at_lexical := bound_typed.transportClosed fields.signatures
          certificate.type_parameters_empty lexical_closed
          certificate.type_variables_empty
          (fields.targetResidualVariablesOpen
            certificate.residual_type_variables_open)
        have lexical_evidence := fields.covers evidence_covers
        rcases (preserveFunctionStatementsRecWithControl program_well_formed
            (certificate.sourceRuntimeValid.transport fields) lexical_evidence
            bound_environment bound_at_lexical aligned_body_type completes
            execute).1 with
          ⟨after_typed, execution_extension, outcome_typed⟩
        rw [returned] at outcome_typed
        cases outcome_typed with
        | returned result_typed =>
            exact {
              result_typed := result_typed.transportClosed
                fields.signatures.symm lexical_closed
                certificate.type_parameters_empty
                (fields.targetVariablesClosed certificate.type_variables_empty)
                certificate.residual_type_variables_open
              heap_typed := after_typed.transportClosed fields.signatures.symm
                lexical_closed certificate.type_parameters_empty
                (fields.targetVariablesClosed certificate.type_variables_empty)
                certificate.residual_type_variables_open
              heap_extends := allocation_extension.trans execution_extension
            }
    | .unit covers result_unit roots_eq inputs_extend allocate execute
        fell_through => by
        rcases certificate.typing.body_typed with
          ⟨staticFinalContext, body_type, no_expression_roots, completes⟩
        have aligned_body_type := roots_eq.filterMap_eq ▸ body_type
        have lexical_context_eq :=
          Solcore.SourceSemantics.Dynamic.MonoBindersExtend.functional
            inputs_extend certificate.typing.inputs_extend
        subst lexical_context_eq
        have input_types_eq : _ = inputTypes :=
          (Solcore.SourceSemantics.Dynamic.MonoBindersExtend.bodyTypes_eq
            inputs_extend).symm.trans
            (Solcore.SourceSemantics.Dynamic.MonoBindersExtend.bodyTypes_eq
              certificate.typing.inputs_extend)
        subst input_types_eq
        have binder_arguments_typed : ValuesHaveTypes bodyInstance.context before
            arguments (bodyInstance.source.inputs.map
              fun binder => binder.scheme.body) := by
          rw [Solcore.SourceSemantics.Dynamic.MonoBindersExtend.bodyTypes_eq
            certificate.typing.inputs_extend]
          exact arguments_typed
        have bound_typed := allocate.preservesHeapTyping before_typed
          binder_arguments_typed
        have allocation_extension := allocate.extendsHeapTypes
        have base_environment : EnvironmentAgrees before
            bodyInstance.context.locals [] := by
          rw [certificate.locals_empty]
          exact .nil
        have bound_environment := allocate.preservesEnvironmentAgreement
          (monoBinders_toBinders certificate.typing.inputs_extend)
          (monoBinders_monomorphic certificate.typing.inputs_extend)
          base_environment
        have fields :=
          Solcore.SourceSemantics.Dynamic.MonoBindersExtend.runtimeContextFields
            certificate.typing.inputs_extend
        have lexical_closed := fields.targetClosed
          certificate.type_parameters_empty
        have bound_at_lexical := bound_typed.transportClosed fields.signatures
          certificate.type_parameters_empty lexical_closed
          certificate.type_variables_empty
          (fields.targetResidualVariablesOpen
            certificate.residual_type_variables_open)
        have lexical_evidence := fields.covers evidence_covers
        rcases (preserveFunctionStatementsRecWithControl program_well_formed
            (certificate.sourceRuntimeValid.transport fields) lexical_evidence
            bound_environment bound_at_lexical aligned_body_type completes
            execute).1 with
          ⟨after_typed, execution_extension, outcome_typed⟩
        rcases fell_through with ⟨finalEnvironment, rfl⟩
        cases outcome_typed with
        | fallthrough final_agrees =>
            exact {
              result_typed := by rw [result_unit]; exact .unit
              heap_typed := after_typed.transportClosed fields.signatures.symm
                lexical_closed certificate.type_parameters_empty
                (fields.targetVariablesClosed certificate.type_variables_empty)
                certificate.residual_type_variables_open
              heap_extends := allocation_extension.trans execution_extension
            }
    termination_by structural evaluation

  private theorem preserveStatementRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context staticFinalContext runtimeFinalContext : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment}
      {before after : Heap} {statement : StatementId} {outcome : ControlOutcome}
      {control : ControlContext} {facts : StatementFacts}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : StatementHasType source control context statement staticFinalContext
        facts)
      (evaluation : StatementExecutes program context evidence source environment
        before statement runtimeFinalContext outcome after) :
      StatementEvaluationPreserved context staticFinalContext control.returnType
        before after outcome :=
    match evaluation with
    | .letUninitialized contains form_eq runtime_monomorphic extension allocate => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique runtime.graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | letUninitialized monomorphic static_extension =>
            cases static_extension
            have allocation_extension := HeapTypesExtend.of_allocation allocate
            have after_typed := before_typed.allocate (.none _) allocate
            exact {
              heap_typed := after_typed
              heap_extends := allocation_extension
              outcome_typed := .fallthrough
                (.cons allocate.reads_new rfl
                  (.ordinary runtime_monomorphic rfl)
                  (environment_agrees.mono allocation_extension))
            }
    | .letInitialized contains form_eq evaluate runtime_monomorphic extension allocate => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | letInitialized initializer_type monomorphic static_extension =>
            cases static_extension
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers
                environment_agrees before_typed initializer_type evaluate with
              ⟨value_typed, middle_typed, evaluation_extension⟩
            have allocation_extension := HeapTypesExtend.of_allocation allocate
            have after_typed := middle_typed.allocate (.some value_typed) allocate
            exact {
              heap_typed := after_typed
              heap_extends := evaluation_extension.trans allocation_extension
              outcome_typed := .fallthrough
                (.cons allocate.reads_new rfl
                  (.ordinary runtime_monomorphic rfl)
                  ((environment_agrees.mono evaluation_extension).mono
                    allocation_extension))
            }
        | letInitializedGeneralized polymorphic _requirements_well_formed
            _generalizes initializer_type static_extension =>
            exact (polymorphic runtime_monomorphic).elim
    | .letInitializedGeneralized contains form_eq captures runtime_polymorphic
        extension allocate => by
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique
          runtime.graph.nodeOccurrencesUnique typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | letInitialized initializer_type static_monomorphic static_extension =>
            exact (runtime_polymorphic static_monomorphic).elim
        | letInitializedGeneralized static_polymorphic
            requirements_well_formed generalizes initializer_type
            static_extension =>
            have function_typed := captures.wellTyped runtime
              environment_agrees static_polymorphic requirements_well_formed
              generalizes initializer_type static_extension
            have allocation_extension :=
              HeapTypesExtend.of_generalized_allocation allocate
            have after_typed := before_typed.allocateGeneralized function_typed
              allocate
            cases static_extension
            exact {
              heap_typed := after_typed
              heap_extends := allocation_extension
              outcome_typed := .fallthrough
                (.cons allocate.reads_new
                  (by simpa only using (congrArg
                    (fun retained : TypedBinder => retained.scheme.body)
                    captures.binder_eq))
                  (.generalized rfl
                    (by simpa only using (congrArg TypedBinder.id
                      captures.binder_eq))
                    (by simpa only using (congrArg TypedBinder.scheme
                      captures.binder_eq)))
                  (environment_agrees.mono allocation_extension))
            }
    | .returnUnit contains form_eq => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | returnUnit return_type_eq =>
            exact {
              heap_typed := before_typed
              heap_extends := .refl before
              outcome_typed := .returned (return_type_eq ▸ ValueHasType.unit)
            }
    | .returnValue contains form_eq evaluate => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | returnValue value_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers
                environment_agrees before_typed value_type evaluate with
              ⟨value_typed, after_typed, extension⟩
            exact {
              heap_typed := after_typed
              heap_extends := extension
              outcome_typed := .returned value_typed
            }
    | .expression contains form_eq evaluate => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | expressionValue expression_type | expressionDiscard expression_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers
                environment_agrees before_typed expression_type evaluate with
              ⟨value_typed, after_typed, extension⟩
            exact {
              heap_typed := after_typed
              heap_extends := extension
              outcome_typed := .fallthrough (environment_agrees.mono extension)
            }
    | .assignValue contains form_eq assignment_executes => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | assignValue assignment_type =>
            rcases preserveAssignmentRec program_well_formed runtime
                evidence_covers environment_agrees before_typed assignment_type
                rfl rfl rfl assignment_executes with
              ⟨after_typed, extension⟩
            exact {
              heap_typed := after_typed
              heap_extends := extension
              outcome_typed := .fallthrough (environment_agrees.mono extension)
            }
    | .assignBitNot contains form_eq assignment_executes => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | assignBitNot assignment_type =>
            rcases preserveSnapshotRec program_well_formed runtime
                evidence_covers environment_agrees before_typed assignment_type
                rfl rfl assignment_executes with
              ⟨after_typed, extension⟩
            exact {
              heap_typed := after_typed
              heap_extends := extension
              outcome_typed := .fallthrough (environment_agrees.mono extension)
            }
    | .ifTrue contains form_eq condition_evaluates body_executes => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | ifWithoutElse condition_type then_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers
                environment_agrees before_typed condition_type condition_evaluates with
              ⟨condition_typed, middle_typed, condition_extension⟩
            rcases preserveStatementsRec program_well_formed runtime
                evidence_covers (environment_agrees.mono condition_extension)
                middle_typed then_type body_executes with
              body_preserved
            rcases body_preserved with
              ⟨body_heap_typed, body_extension, body_outcome⟩
            have extension := condition_extension.trans body_extension
            exact {
              heap_typed := body_heap_typed
              heap_extends := extension
              outcome_typed := body_outcome.restore (.refl context) closed
                runtime.variables_closed runtime.residual_variables_open
                (environment_agrees.mono extension)
            }
        | ifWithElse condition_type then_type else_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers
                environment_agrees before_typed condition_type condition_evaluates with
              ⟨condition_typed, middle_typed, condition_extension⟩
            rcases preserveStatementsRec program_well_formed runtime
                evidence_covers (environment_agrees.mono condition_extension)
                middle_typed then_type body_executes with
              body_preserved
            rcases body_preserved with
              ⟨body_heap_typed, body_extension, body_outcome⟩
            have extension := condition_extension.trans body_extension
            exact {
              heap_typed := body_heap_typed
              heap_extends := extension
              outcome_typed := body_outcome.restore (.refl context) closed
                runtime.variables_closed runtime.residual_variables_open
                (environment_agrees.mono extension)
            }
    | .ifFalseWithoutElse contains form_eq condition_evaluates => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | ifWithoutElse condition_type then_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers
                environment_agrees before_typed condition_type condition_evaluates with
              ⟨condition_typed, after_typed, extension⟩
            exact {
              heap_typed := after_typed
              heap_extends := extension
              outcome_typed := .fallthrough (environment_agrees.mono extension)
            }
    | .ifFalseWithElse contains form_eq condition_evaluates body_executes => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | ifWithElse condition_type then_type else_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers
                environment_agrees before_typed condition_type condition_evaluates with
              ⟨condition_typed, middle_typed, condition_extension⟩
            rcases preserveStatementsRec program_well_formed runtime
                evidence_covers (environment_agrees.mono condition_extension)
                middle_typed else_type body_executes with
              body_preserved
            rcases body_preserved with
              ⟨body_heap_typed, body_extension, body_outcome⟩
            have extension := condition_extension.trans body_extension
            exact {
              heap_typed := body_heap_typed
              heap_extends := extension
              outcome_typed := body_outcome.restore (.refl context) closed
                runtime.variables_closed runtime.residual_variables_open
                (environment_agrees.mono extension)
            }
    | .block contains form_eq body_executes => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | block body_type =>
            rcases preserveStatementsRec program_well_formed runtime
                evidence_covers environment_agrees before_typed body_type
                body_executes with
              body_preserved
            rcases body_preserved with
              ⟨body_heap_typed, extension, body_outcome⟩
            exact {
              heap_typed := body_heap_typed
              heap_extends := extension
              outcome_typed := body_outcome.restore (.refl context) closed
                runtime.variables_closed runtime.residual_variables_open
                (environment_agrees.mono extension)
            }
    | .matchArm contains form_eq scrutinee_contains scrutinee_evaluates
        allocate_hidden select binders_eq values_eq binders_extend
        allocate_bindings execute => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        rename_i scrutineeHeap hiddenHeap dynamicNode resolution scrutinee
          scrutineeNode location armBody bindings binders values armContext
          armFinalContext armEnvironment bound outcome
        have common_typing :
            ∃ scrutineeType caseFacts,
              staticFinalContext = context ∧
              ExpressionHasType source context resolution.scrutinee scrutineeType ∧
              MatchCasesHaveType source control context scrutineeType
                resolution.cases caseFacts := by
          cases form_typing with
          | matchWithoutDefault default_eq scrutinee_type cases_type =>
              exact ⟨_, _, rfl, scrutinee_type, cases_type⟩
          | matchWithDefault default_eq scrutinee_type cases_type default_type =>
              exact ⟨_, _, rfl, scrutinee_type, cases_type⟩
        rcases common_typing with
          ⟨scrutineeType, caseFacts, static_final_eq, scrutinee_type, cases_type⟩
        subst staticFinalContext
        ·
          rcases preserveExpressionRec program_well_formed runtime
                evidence_covers
              environment_agrees before_typed scrutinee_type
              scrutinee_evaluates with
            ⟨scrutinee_typed, scrutinee_heap_typed, scrutinee_extension⟩
          rcases scrutinee_type.stored_type with
            ⟨staticScrutineeNode, static_contains, static_type_eq⟩
          have scrutinee_node_eq := containsExpression_unique
            graph.nodeOccurrencesUnique static_contains scrutinee_contains
          subst staticScrutineeNode
          have hidden_value_typed : ValueHasType context scrutineeHeap scrutinee
              scrutineeNode.type := static_type_eq ▸ scrutinee_typed
          have hidden_heap_typed := scrutinee_heap_typed.allocate
            (.some hidden_value_typed) allocate_hidden
          have hidden_extension := HeapTypesExtend.of_allocation allocate_hidden
          have scrutinee_hidden_typed := scrutinee_typed.mono hidden_extension
          rcases select.armPreserves cases_type scrutinee_hidden_typed with
            ⟨staticBinders, staticArmContext, staticArmFinalContext, armFacts,
              bindings_typed, static_binders_eq, static_binders_extend,
              arm_type, binders_monomorphic⟩
          have dynamic_static_binders : binders = staticBinders :=
            binders_eq.trans static_binders_eq
          have static_binders_extend' :
              BindersExtend source.owner context binders staticArmContext := by
            rw [dynamic_static_binders]
            exact static_binders_extend
          have arm_context_eq :=
            Solcore.SourceSemantics.Dynamic.BindersExtend.functional
              binders_extend static_binders_extend'
          have values_typed : ValuesHaveTypes context hiddenHeap values
              (staticBinders.map fun binder => binder.scheme.body) := by
            rw [values_eq, ← static_binders_eq, List.map_map]
            change ValuesHaveTypes context hiddenHeap (bindings.map Prod.snd)
              (bindings.map fun binding => binding.1.scheme.body)
            exact bindings_typed.unzip
          have values_typed_dynamic : ValuesHaveTypes context hiddenHeap values
              (binders.map fun binder => binder.scheme.body) := by
            simpa [dynamic_static_binders] using values_typed
          have bound_heap_typed :=
            Solcore.SourceSemantics.Dynamic.BindersAllocate.preservesHeapTyping
              hidden_heap_typed values_typed_dynamic allocate_bindings
          have bound_extension := allocate_bindings.extendsHeapTypes
          have arm_environment_agrees :=
            allocate_bindings.preservesEnvironmentAgreement
              static_binders_extend'
              (by
                intro binder member
                exact binders_monomorphic binder
                  (by simpa [dynamic_static_binders] using member))
              (environment_agrees.mono
                (scrutinee_extension.trans hidden_extension))
          have aligned_arm_environment_agrees :
              EnvironmentAgrees bound armContext.locals armEnvironment :=
            arm_context_eq.symm ▸ arm_environment_agrees
          have aligned_arm_type :
              StatementsHaveType source control armContext armBody
                staticArmFinalContext armFacts :=
            arm_context_eq.symm ▸ arm_type
          have arm_fields :=
            Solcore.SourceSemantics.Dynamic.BindersExtend.runtimeContextFields
              binders_extend
          have arm_closed := arm_fields.targetClosed closed
          have arm_evidence := arm_fields.covers evidence_covers
          have bound_heap_at_arm := bound_heap_typed.transportClosed
            arm_fields.signatures closed arm_closed runtime.variables_closed
            (arm_fields.targetResidualVariablesOpen
              runtime.residual_variables_open)
          rcases preserveStatementsRec program_well_formed
              (runtime.transport arm_fields) arm_evidence
              aligned_arm_environment_agrees bound_heap_at_arm aligned_arm_type
              execute with
            arm_preserved
          rcases arm_preserved with
            ⟨arm_heap_typed, arm_extension, arm_outcome⟩
          have arm_heap_at_outer := arm_heap_typed.transportClosed
            arm_fields.signatures.symm arm_closed closed
            (arm_fields.targetVariablesClosed runtime.variables_closed)
            runtime.residual_variables_open
          have extension := ((scrutinee_extension.trans hidden_extension).trans
            bound_extension).trans arm_extension
          exact {
            heap_typed := arm_heap_at_outer
            heap_extends := extension
            outcome_typed := arm_outcome.restore arm_fields closed
              runtime.variables_closed runtime.residual_variables_open
              (environment_agrees.mono extension)
          }
    | .matchDefault contains form_eq scrutinee_contains scrutinee_evaluates
        allocate_hidden select execute => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        rename_i scrutineeHeap hiddenHeap dynamicNode resolution scrutinee
          scrutineeNode location defaultBody runtimeDefaultFinal outcome
        cases form_typing with
        | matchWithoutDefault default_eq scrutinee_type cases_type =>
            have selected_default := select.defaultBody_eq
            rw [default_eq] at selected_default
            contradiction
        | matchWithDefault default_eq scrutinee_type cases_type default_type =>
            have selected_default := select.defaultBody_eq
            rw [selected_default] at default_eq
            cases default_eq
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers
                environment_agrees before_typed scrutinee_type
                scrutinee_evaluates with
              ⟨scrutinee_typed, scrutinee_heap_typed, scrutinee_extension⟩
            rcases scrutinee_type.stored_type with
              ⟨staticScrutineeNode, static_contains, static_type_eq⟩
            have scrutinee_node_eq := containsExpression_unique
              graph.nodeOccurrencesUnique static_contains scrutinee_contains
            subst staticScrutineeNode
            have hidden_value_typed : ValueHasType context scrutineeHeap scrutinee
                scrutineeNode.type := static_type_eq ▸ scrutinee_typed
            have hidden_heap_typed := scrutinee_heap_typed.allocate
              (.some hidden_value_typed) allocate_hidden
            have hidden_extension := HeapTypesExtend.of_allocation allocate_hidden
            rcases preserveStatementsRec program_well_formed runtime
                evidence_covers
                (environment_agrees.mono
                  (scrutinee_extension.trans hidden_extension))
                hidden_heap_typed default_type execute with
              body_preserved
            rcases body_preserved with
              ⟨body_heap_typed, body_extension, body_outcome⟩
            have extension := (scrutinee_extension.trans hidden_extension).trans
              body_extension
            exact {
              heap_typed := body_heap_typed
              heap_extends := extension
              outcome_typed := body_outcome.restore (.refl context) closed
                runtime.variables_closed runtime.residual_variables_open
                (environment_agrees.mono extension)
            }
    | .matchNoBranch contains form_eq scrutinee_contains scrutinee_evaluates
        allocate_hidden select => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        rename_i scrutineeHeap dynamicNode resolution scrutinee scrutineeNode
          location
        cases form_typing with
        | matchWithoutDefault default_eq scrutinee_type cases_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers
                environment_agrees before_typed scrutinee_type
                scrutinee_evaluates with
              ⟨scrutinee_typed, scrutinee_heap_typed, scrutinee_extension⟩
            rcases scrutinee_type.stored_type with
              ⟨staticScrutineeNode, static_contains, static_type_eq⟩
            have scrutinee_node_eq := containsExpression_unique
              graph.nodeOccurrencesUnique static_contains scrutinee_contains
            subst staticScrutineeNode
            have hidden_value_typed : ValueHasType context scrutineeHeap scrutinee
                scrutineeNode.type := static_type_eq ▸ scrutinee_typed
            have hidden_heap_typed := scrutinee_heap_typed.allocate
              (.some hidden_value_typed) allocate_hidden
            have hidden_extension := HeapTypesExtend.of_allocation allocate_hidden
            have extension := scrutinee_extension.trans hidden_extension
            exact {
              heap_typed := hidden_heap_typed
              heap_extends := extension
              outcome_typed := .fallthrough (environment_agrees.mono extension)
            }
        | matchWithDefault default_eq scrutinee_type cases_type default_type =>
            have selected_default := select.noBranch_defaultBody_eq
            rw [default_eq] at selected_default
            contradiction
    | .forLoop contains form_eq initializer_executes iterate => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        rename_i initialized dynamicNode initializer condition post body
          runtimeLoopContext loopFinalContext loopEnvironment outcome
        cases form_typing with
        | forLoop initializer_type condition_type body_type post_type =>
            rcases preserveForItemsRec program_well_formed runtime
                evidence_covers environment_agrees before_typed initializer_type
                initializer_executes with
              ⟨loop_context_eq, initialized_typed, initializer_extension,
                loop_environment_agrees⟩
            have loop_fields :=
              Solcore.SourceSemantics.Dynamic.ForItemsHaveType.runtimeContextFields
                initializer_type
            have aligned_loop_fields :
                RuntimeContextFields context runtimeLoopContext :=
              loop_context_eq.symm ▸ loop_fields
            have aligned_loop_environment_agrees :
                EnvironmentAgrees initialized runtimeLoopContext.locals
                  loopEnvironment :=
              loop_context_eq.symm ▸ loop_environment_agrees
            have aligned_condition_type :
                ExpressionHasType source runtimeLoopContext condition .bool :=
              loop_context_eq.symm ▸ condition_type
            have aligned_post_type := loop_context_eq.symm ▸ post_type
            have aligned_body_type := loop_context_eq.symm ▸ body_type
            have loop_closed := aligned_loop_fields.targetClosed closed
            have loop_evidence := aligned_loop_fields.covers evidence_covers
            have initialized_at_loop := initialized_typed.transportClosed
              aligned_loop_fields.signatures closed loop_closed
              runtime.variables_closed
              (aligned_loop_fields.targetResidualVariablesOpen
                runtime.residual_variables_open)
            rcases (preserveForLoopRecWithControl program_well_formed
                (runtime.transport aligned_loop_fields) loop_evidence
                aligned_loop_environment_agrees initialized_at_loop
                aligned_condition_type aligned_post_type aligned_body_type iterate).1 with
              ⟨loop_heap_typed, loop_extension, loop_outcome⟩
            have loop_heap_at_outer := loop_heap_typed.transportClosed
              aligned_loop_fields.signatures.symm loop_closed closed
              (aligned_loop_fields.targetVariablesClosed runtime.variables_closed)
              runtime.residual_variables_open
            have extension := initializer_extension.trans loop_extension
            exact {
              heap_typed := loop_heap_at_outer
              heap_extends := extension
              outcome_typed := loop_outcome.restore aligned_loop_fields closed
                runtime.variables_closed runtime.residual_variables_open
                (environment_agrees.mono extension)
            }
    | .whileLoop contains form_eq iterate => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | whileLoop condition_type body_type =>
            rcases (preserveWhileRecWithControl program_well_formed runtime
                evidence_covers environment_agrees before_typed condition_type
                body_type iterate).1 with
              ⟨loop_heap_typed, extension, loop_outcome⟩
            exact {
              heap_typed := loop_heap_typed
              heap_extends := extension
              outcome_typed := loop_outcome.restore (.refl context) closed
                runtime.variables_closed runtime.residual_variables_open
                (environment_agrees.mono extension)
            }
    | .breakStmt contains form_eq => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | breakStmt allowed =>
            exact {
              heap_typed := before_typed
              heap_extends := .refl before
              outcome_typed := .breaking
            }
    | .continueStmt contains form_eq => by
        have graph : OccurrenceGraphWellFormed source := runtime.graph
        have owner : context.currentDeclaration = some source.owner := runtime.owner
        have closed : context.typeParameters = [] := runtime.closed
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | continueStmt allowed =>
            exact {
              heap_typed := before_typed
              heap_extends := .refl before
              outcome_typed := .continuing
            }
    termination_by structural evaluation

  private theorem preserveStatementsRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context staticFinalContext runtimeFinalContext : Context}
      {evidence : EvidenceEnvironment} {source : TypedSource}
      {environment : Environment} {before after : Heap}
      {statements : List StatementId} {outcome : ControlOutcome}
      {control : ControlContext} {facts : BodyFacts}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : StatementsHaveType source control context statements
        staticFinalContext facts)
      (evaluation : StatementsExecute program context evidence source environment
        before statements runtimeFinalContext outcome after) :
      StatementEvaluationPreserved context staticFinalContext control.returnType
        before after outcome :=
    match evaluation with
    | .nil => by
        cases typing
        exact {
          heap_typed := before_typed
          heap_extends := .refl before
          outcome_typed := .fallthrough environment_agrees
        }
    | @StatementsExecute.cons program context middleContext finalContext evidence
        source environment before middle after statement statements nextEnvironment
        outcome head tail => by
        have preserve_head :
            ∀ {staticHeadFinal headFacts},
              StatementHasType source control context statement staticHeadFinal
                headFacts →
              StatementEvaluationPreserved context staticHeadFinal
                control.returnType before middle (.fallthrough nextEnvironment) :=
          fun head_type =>
            preserveStatementRec program_well_formed runtime
              evidence_covers environment_agrees before_typed head_type head
        have preserve_tail :
            ∀ {staticTailFinal tailFacts},
              SourceRuntimeValid program middleContext source →
              evidence.Covers middleContext →
              EnvironmentAgrees middle middleContext.locals nextEnvironment →
              HeapWellTyped middleContext middle →
              StatementsHaveType source control middleContext statements
                staticTailFinal tailFacts →
              StatementEvaluationPreserved middleContext staticTailFinal
                control.returnType middle after outcome :=
          fun tail_runtime tail_evidence tail_environment tail_heap tail_type =>
            preserveStatementsRec program_well_formed tail_runtime
              tail_evidence tail_environment tail_heap tail_type tail
        cases typing with
        | singleton head_type =>
            cases tail
            exact preserve_head head_type
        | cons head_type tail_type =>
            have middle_context_eq := statementFinalContext_eq
              runtime.graph head_type head
            have aligned_tail_type := middle_context_eq.symm ▸ tail_type
            rcases preserve_head head_type with
              ⟨middle_typed, head_extension, head_outcome⟩
            cases head_outcome with
            | fallthrough middle_environment_agrees =>
                have fields :=
                  Solcore.SourceSemantics.Dynamic.StatementHasType.runtimeContextFields
                    head_type
                have aligned_fields :
                    RuntimeContextFields context middleContext :=
                  middle_context_eq.symm ▸ fields
                have aligned_middle_environment_agrees :
                    EnvironmentAgrees middle middleContext.locals
                      nextEnvironment :=
                  middle_context_eq.symm ▸ middle_environment_agrees
                have middle_closed := aligned_fields.targetClosed runtime.closed
                have middle_evidence := aligned_fields.covers evidence_covers
                have middle_typed' := middle_typed.transportClosed
                  aligned_fields.signatures runtime.closed middle_closed
                  runtime.variables_closed
                  (aligned_fields.targetResidualVariablesOpen
                    runtime.residual_variables_open)
                rcases preserve_tail (runtime.transport aligned_fields)
                    middle_evidence aligned_middle_environment_agrees middle_typed'
                    aligned_tail_type with
                  ⟨after_typed, tail_extension, tail_outcome⟩
                exact {
                  heap_typed := after_typed.transportClosed
                    aligned_fields.signatures.symm middle_closed runtime.closed
                    (aligned_fields.targetVariablesClosed runtime.variables_closed)
                    runtime.residual_variables_open
                  heap_extends := head_extension.trans tail_extension
                  outcome_typed := tail_outcome.transportEntry aligned_fields
                    runtime.closed runtime.variables_closed
                    runtime.residual_variables_open
                }
    | @StatementsExecute.terminal program context finalContext evidence source
        environment before after statement statements outcome head terminal => by
        have preserve_head :
            ∀ {staticHeadFinal headFacts},
              StatementHasType source control context statement staticHeadFinal
                headFacts →
              StatementEvaluationPreserved context staticHeadFinal
                control.returnType before after outcome :=
          fun head_type =>
            preserveStatementRec program_well_formed runtime
              evidence_covers environment_agrees before_typed head_type head
        cases typing with
        | singleton head_type =>
            rcases preserve_head head_type with
              ⟨after_typed, extension, head_outcome⟩
            exact {
              heap_typed := after_typed
              heap_extends := extension
              outcome_typed := head_outcome.retargetTerminal terminal
            }
        | cons head_type tail_type =>
            rcases preserve_head head_type with
              ⟨after_typed, extension, head_outcome⟩
            exact {
              heap_typed := after_typed
              heap_extends := extension
              outcome_typed := head_outcome.retargetTerminal terminal
            }
    termination_by structural evaluation

  private theorem preserveStatementControlSummaryRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context staticFinalContext runtimeFinalContext : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment}
      {before after : Heap} {statement : StatementId} {outcome : ControlOutcome}
      {control : ControlContext} {facts : StatementFacts}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : StatementHasType source control context statement staticFinalContext
        facts)
      (evaluation : StatementExecutes program context evidence source environment
        before statement runtimeFinalContext outcome after) :
      ControlSummary.AllowsTransfers facts.control outcome :=
    match evaluation with
    | .letUninitialized contains form_eq runtime_monomorphic extension allocate => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing
        rfl
    | .letInitialized contains form_eq evaluate runtime_monomorphic extension allocate => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing
        rfl
    | .letInitializedGeneralized contains form_eq captures runtime_polymorphic
        extension allocate => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing
        rfl
    | .returnUnit contains form_eq => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing
        exact True.intro
    | .returnValue contains form_eq evaluate => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing
        exact True.intro
    | .expression contains form_eq evaluate => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing <;> rfl
    | .assignValue contains form_eq assignment_executes => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing
        rfl
    | .assignBitNot contains form_eq assignment_executes => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing
        rfl
    | .ifTrue contains form_eq condition_evaluates body_executes => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing with
        | ifWithoutElse condition_type then_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed condition_type
                condition_evaluates with
              ⟨condition_typed, middle_typed, condition_extension⟩
            have body_allowed := preserveStatementsControlSummaryRec
              program_well_formed runtime evidence_covers
              (environment_agrees.mono condition_extension) middle_typed then_type
              body_executes
            exact body_allowed.branches_left.restore _
        | ifWithElse condition_type then_type else_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed condition_type
                condition_evaluates with
              ⟨condition_typed, middle_typed, condition_extension⟩
            have body_allowed := preserveStatementsControlSummaryRec
              program_well_formed runtime evidence_covers
              (environment_agrees.mono condition_extension) middle_typed then_type
              body_executes
            exact body_allowed.branches_left.restore _
    | .ifFalseWithoutElse contains form_eq condition_evaluates => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing with
        | ifWithoutElse condition_type then_type =>
            exact (show ControlSummary.AllowsTransfers (.ordinary .unit)
              (.fallthrough environment) from rfl).branches_right
    | .ifFalseWithElse contains form_eq condition_evaluates body_executes => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing with
        | ifWithElse condition_type then_type else_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed condition_type
                condition_evaluates with
              ⟨condition_typed, middle_typed, condition_extension⟩
            have body_allowed := preserveStatementsControlSummaryRec
              program_well_formed runtime evidence_covers
              (environment_agrees.mono condition_extension) middle_typed else_type
              body_executes
            exact body_allowed.branches_right.restore _
    | .block contains form_eq body_executes => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing with
        | block body_type =>
            have body_allowed := preserveStatementsControlSummaryRec
              program_well_formed runtime evidence_covers environment_agrees
              before_typed body_type body_executes
            exact body_allowed.eraseValue.restore _
    | .matchArm contains form_eq scrutinee_contains scrutinee_evaluates
        allocate_hidden select binders_eq values_eq binders_extend
        allocate_bindings execute => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        rename_i scrutineeHeap hiddenHeap dynamicNode resolution scrutinee
          scrutineeNode location armBody bindings binders values armContext
          armFinalContext armEnvironment bound outcome
        have common_control :
            ∃ scrutineeType caseFacts fallbackFacts summary,
              facts.control = summary.eraseValue ∧
              ExpressionHasType source context resolution.scrutinee
                scrutineeType ∧
              MatchCasesHaveType source control context scrutineeType
                resolution.cases caseFacts ∧
              mergeBodyControls caseFacts fallbackFacts = some summary := by
          cases control_typing with
          | matchWithoutDefault default_eq scrutinee_type cases_type exhaustive
              merged =>
              exact ⟨_, _, none, _, rfl, scrutinee_type, cases_type, merged⟩
          | matchWithDefault default_eq scrutinee_type cases_type default_type
              merged =>
              exact ⟨_, _, some _, _, rfl, scrutinee_type, cases_type, merged⟩
        rcases common_control with
          ⟨scrutineeType, caseFacts, fallbackFacts, summary, control_eq,
            scrutinee_type, cases_type, merged⟩
        rcases preserveExpressionRec program_well_formed runtime
              evidence_covers environment_agrees before_typed scrutinee_type
              scrutinee_evaluates with
          ⟨scrutinee_typed, scrutinee_heap_typed, scrutinee_extension⟩
        rcases scrutinee_type.stored_type with
          ⟨staticScrutineeNode, static_contains, static_type_eq⟩
        have scrutinee_node_eq := containsExpression_unique
          runtime.graph.nodeOccurrencesUnique static_contains scrutinee_contains
        subst staticScrutineeNode
        have hidden_value_typed : ValueHasType context scrutineeHeap scrutinee
            scrutineeNode.type := static_type_eq ▸ scrutinee_typed
        have hidden_heap_typed := scrutinee_heap_typed.allocate
          (.some hidden_value_typed) allocate_hidden
        have hidden_extension := HeapTypesExtend.of_allocation allocate_hidden
        have scrutinee_hidden_typed := scrutinee_typed.mono hidden_extension
        rcases
            MatchCasesSelect.arm_preserves_typing cases_type
              scrutinee_hidden_typed select with
          ⟨staticBinders, staticArmContext, staticArmFinalContext, armFacts,
            bindings_typed, static_binders_eq, static_binders_extend, arm_type,
            arm_member, binders_monomorphic⟩
        have dynamic_static_binders : binders = staticBinders :=
          binders_eq.trans static_binders_eq
        have static_binders_extend' :
            BindersExtend source.owner context binders staticArmContext := by
          rw [dynamic_static_binders]
          exact static_binders_extend
        have arm_context_eq :=
          Solcore.SourceSemantics.Dynamic.BindersExtend.functional
            binders_extend static_binders_extend'
        have values_typed : ValuesHaveTypes context hiddenHeap values
            (staticBinders.map fun binder => binder.scheme.body) := by
          rw [values_eq, ← static_binders_eq, List.map_map]
          change ValuesHaveTypes context hiddenHeap (bindings.map Prod.snd)
            (bindings.map fun binding => binding.1.scheme.body)
          exact bindings_typed.unzip
        have values_typed_dynamic : ValuesHaveTypes context hiddenHeap values
            (binders.map fun binder => binder.scheme.body) := by
          simpa [dynamic_static_binders] using values_typed
        have bound_heap_typed :=
          Solcore.SourceSemantics.Dynamic.BindersAllocate.preservesHeapTyping
            hidden_heap_typed values_typed_dynamic allocate_bindings
        have bound_extension := allocate_bindings.extendsHeapTypes
        have arm_environment_agrees :=
          allocate_bindings.preservesEnvironmentAgreement
            static_binders_extend'
            (by
              intro binder member
              exact binders_monomorphic binder
                (by simpa [dynamic_static_binders] using member))
            (environment_agrees.mono
              (scrutinee_extension.trans hidden_extension))
        have aligned_arm_environment_agrees :
            EnvironmentAgrees bound armContext.locals armEnvironment :=
          arm_context_eq.symm ▸ arm_environment_agrees
        have aligned_arm_type :
            StatementsHaveType source control armContext armBody
              staticArmFinalContext armFacts :=
          arm_context_eq.symm ▸ arm_type
        have arm_fields :=
          Solcore.SourceSemantics.Dynamic.BindersExtend.runtimeContextFields
            binders_extend
        have arm_closed := arm_fields.targetClosed runtime.closed
        have arm_evidence := arm_fields.covers evidence_covers
        have bound_heap_at_arm := bound_heap_typed.transportClosed
          arm_fields.signatures runtime.closed arm_closed runtime.variables_closed
          (arm_fields.targetResidualVariablesOpen runtime.residual_variables_open)
        have arm_allowed := preserveStatementsControlSummaryRec
          program_well_formed (runtime.transport arm_fields) arm_evidence
          aligned_arm_environment_agrees bound_heap_at_arm aligned_arm_type execute
        rw [control_eq]
        exact (MergeBodyControls.allows_of_mem merged arm_member
          arm_allowed).eraseValue.restore _
    | .matchDefault contains form_eq scrutinee_contains scrutinee_evaluates
        allocate_hidden select execute => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        rename_i scrutineeHeap hiddenHeap dynamicNode resolution scrutinee
          scrutineeNode location defaultBody runtimeDefaultFinal outcome
        cases control_typing with
        | matchWithoutDefault default_eq scrutinee_type cases_type exhaustive
            merged =>
            have selected_default := select.defaultBody_eq
            rw [default_eq] at selected_default
            contradiction
        | matchWithDefault default_eq scrutinee_type cases_type default_type
            merged =>
            have selected_default := select.defaultBody_eq
            rw [selected_default] at default_eq
            cases default_eq
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed scrutinee_type
                scrutinee_evaluates with
              ⟨scrutinee_typed, scrutinee_heap_typed, scrutinee_extension⟩
            rcases scrutinee_type.stored_type with
              ⟨staticScrutineeNode, static_contains, static_type_eq⟩
            have scrutinee_node_eq := containsExpression_unique
              runtime.graph.nodeOccurrencesUnique static_contains
                scrutinee_contains
            subst staticScrutineeNode
            have hidden_value_typed : ValueHasType context scrutineeHeap scrutinee
                scrutineeNode.type := static_type_eq ▸ scrutinee_typed
            have hidden_heap_typed := scrutinee_heap_typed.allocate
              (.some hidden_value_typed) allocate_hidden
            have hidden_extension := HeapTypesExtend.of_allocation allocate_hidden
            have body_allowed := preserveStatementsControlSummaryRec
              program_well_formed runtime evidence_covers
              (environment_agrees.mono
                (scrutinee_extension.trans hidden_extension))
              hidden_heap_typed default_type execute
            exact (MergeBodyControls.allows_of_fallback merged
              body_allowed).eraseValue.restore _
    | .matchNoBranch contains form_eq scrutinee_contains scrutinee_evaluates
        allocate_hidden select => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing with
        | matchWithoutDefault default_eq scrutinee_type cases_type exhaustive
            merged =>
            rw [default_eq] at select
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed scrutinee_type
                scrutinee_evaluates with
              ⟨scrutinee_typed, scrutinee_heap_typed, scrutinee_extension⟩
            have catalog : SignatureCatalogWellFormed context.signatures := by
              simpa [runtime.signatures] using program_well_formed.signatures
            exact (select.noBranch_impossible_of_exhaustive catalog cases_type
              scrutinee_typed exhaustive).elim
        | matchWithDefault default_eq scrutinee_type cases_type default_type
            merged =>
            have selected_default := select.noBranch_defaultBody_eq
            rw [default_eq] at selected_default
            contradiction
    | .forLoop contains form_eq initializer_executes iterate => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique runtime.graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        rename_i initialized dynamicNode initializer condition post body
          runtimeLoopContext loopFinalContext loopEnvironment outcome
        cases form_typing with
        | forLoop initializer_type condition_type body_type post_type =>
            rcases preserveForItemsRec program_well_formed runtime
                evidence_covers environment_agrees before_typed initializer_type
                initializer_executes with
              ⟨loop_context_eq, initialized_typed, initializer_extension,
                loop_environment_agrees⟩
            have loop_fields :=
              Solcore.SourceSemantics.Dynamic.ForItemsHaveType.runtimeContextFields
                initializer_type
            have aligned_loop_fields :
                RuntimeContextFields context runtimeLoopContext :=
              loop_context_eq.symm ▸ loop_fields
            have aligned_loop_environment_agrees :
                EnvironmentAgrees initialized runtimeLoopContext.locals
                  loopEnvironment :=
              loop_context_eq.symm ▸ loop_environment_agrees
            have aligned_condition_type :
                ExpressionHasType source runtimeLoopContext condition .bool :=
              loop_context_eq.symm ▸ condition_type
            have aligned_post_type := loop_context_eq.symm ▸ post_type
            have aligned_body_type := loop_context_eq.symm ▸ body_type
            have loop_closed := aligned_loop_fields.targetClosed runtime.closed
            have loop_evidence := aligned_loop_fields.covers evidence_covers
            have initialized_at_loop := initialized_typed.transportClosed
              aligned_loop_fields.signatures runtime.closed loop_closed
              runtime.variables_closed
              (aligned_loop_fields.targetResidualVariablesOpen
                runtime.residual_variables_open)
            have loop_closed_control :=
              (preserveForLoopRecWithControl program_well_formed
                (runtime.transport aligned_loop_fields) loop_evidence
                aligned_loop_environment_agrees initialized_at_loop
                aligned_condition_type aligned_post_type aligned_body_type iterate).2
            cases control_typing
            exact ControlSummary.allows_of_noEscape
              (loop_closed_control.restore _) (fun _ => rfl)
    | .whileLoop contains form_eq iterate => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        rcases
            Solcore.SourceSemantics.Dynamic.StatementHasType.formTyping typing with
          ⟨typedNode, typed_contains, form_typing⟩
        have node_eq := containsStatement_unique runtime.graph.nodeOccurrencesUnique
          typed_contains contains
        subst typedNode
        rw [form_eq] at form_typing
        cases form_typing with
        | whileLoop condition_type body_type =>
            have loop_closed_control :=
              (preserveWhileRecWithControl program_well_formed runtime
                evidence_covers environment_agrees before_typed condition_type
                body_type iterate).2
            cases control_typing
            exact ControlSummary.allows_of_noEscape
              (loop_closed_control.restore _) (fun _ => rfl)
    | .breakStmt contains form_eq => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing
        rfl
    | .continueStmt contains form_eq => by
        have control_typing := statementControlFormTyping
          runtime.graph.nodeOccurrencesUnique typing contains form_eq
        cases control_typing
        rfl
    termination_by structural evaluation

  private theorem preserveStatementsControlSummaryRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context staticFinalContext runtimeFinalContext : Context}
      {evidence : EvidenceEnvironment} {source : TypedSource}
      {environment : Environment} {before after : Heap}
      {statements : List StatementId} {outcome : ControlOutcome}
      {control : ControlContext} {facts : BodyFacts}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : StatementsHaveType source control context statements
        staticFinalContext facts)
      (evaluation : StatementsExecute program context evidence source environment
        before statements runtimeFinalContext outcome after) :
      ControlSummary.AllowsTransfers facts.control outcome :=
    match evaluation with
    | .nil => by
        cases typing
        rfl
    | @StatementsExecute.cons program context middleContext finalContext evidence
        source environment before middle after statement statements nextEnvironment
        outcome head tail => by
        have preserve_head :
            ∀ {staticHeadFinal headFacts},
              StatementHasType source control context statement staticHeadFinal
                headFacts →
              StatementEvaluationPreserved context staticHeadFinal
                control.returnType before middle (.fallthrough nextEnvironment) :=
          fun head_type =>
            preserveStatementRec program_well_formed runtime
              evidence_covers environment_agrees before_typed head_type head
        have control_head_summary :
            ∀ {staticHeadFinal headFacts},
              StatementHasType source control context statement staticHeadFinal
                headFacts →
              ControlSummary.AllowsTransfers headFacts.control (.fallthrough nextEnvironment) :=
          fun head_type =>
            preserveStatementControlSummaryRec program_well_formed runtime
              evidence_covers environment_agrees before_typed head_type head
        have control_head :
            ∀ {staticHeadFinal headFacts},
              StatementHasType source control context statement staticHeadFinal
                headFacts →
              headFacts.control.canFallthrough = true :=
          fun head_type =>
            (control_head_summary head_type).canFallthrough (.intro nextEnvironment)
        have control_tail :
            ∀ {staticTailFinal tailFacts},
              SourceRuntimeValid program middleContext source →
              evidence.Covers middleContext →
              EnvironmentAgrees middle middleContext.locals nextEnvironment →
              HeapWellTyped middleContext middle →
              StatementsHaveType source control middleContext statements
                staticTailFinal tailFacts →
              ControlSummary.AllowsTransfers tailFacts.control outcome :=
          fun tail_runtime tail_evidence tail_environment tail_heap tail_type =>
            preserveStatementsControlSummaryRec program_well_formed tail_runtime
              tail_evidence tail_environment tail_heap tail_type tail
        cases typing with
        | singleton head_type =>
            cases tail
            exact control_head_summary head_type
        | cons head_type tail_type =>
            have middle_context_eq := statementFinalContext_eq
              runtime.graph head_type head
            have aligned_tail_type := middle_context_eq.symm ▸ tail_type
            rcases preserve_head head_type with
              ⟨middle_typed, head_extension, head_outcome⟩
            cases head_outcome with
            | fallthrough middle_environment_agrees =>
                have fields :=
                  Solcore.SourceSemantics.Dynamic.StatementHasType.runtimeContextFields
                    head_type
                have aligned_fields :
                    RuntimeContextFields context middleContext :=
                  middle_context_eq.symm ▸ fields
                have aligned_middle_environment_agrees :
                    EnvironmentAgrees middle middleContext.locals
                      nextEnvironment :=
                  middle_context_eq.symm ▸ middle_environment_agrees
                have middle_closed := aligned_fields.targetClosed runtime.closed
                have middle_evidence := aligned_fields.covers evidence_covers
                have middle_typed' := middle_typed.transportClosed
                  aligned_fields.signatures runtime.closed middle_closed
                  runtime.variables_closed
                  (aligned_fields.targetResidualVariablesOpen
                    runtime.residual_variables_open)
                exact (control_tail (runtime.transport aligned_fields)
                  middle_evidence aligned_middle_environment_agrees middle_typed'
                  aligned_tail_type).sequence (control_head head_type)
    | @StatementsExecute.terminal program context finalContext evidence source
        environment before after statement statements outcome head terminal => by
        have control_head :
            ∀ {staticHeadFinal headFacts},
              StatementHasType source control context statement staticHeadFinal
                headFacts → ControlSummary.AllowsTransfers headFacts.control outcome :=
          fun head_type => preserveStatementControlSummaryRec program_well_formed runtime
            evidence_covers environment_agrees before_typed head_type head
        cases typing with
        | singleton head_type =>
            exact control_head head_type
        | cons head_type tail_type =>
            exact (control_head head_type).sequence_terminal terminal
    termination_by structural evaluation

  private theorem preserveFunctionStatementsRecWithControl
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context staticFinalContext runtimeFinalContext : Context}
      {evidence : EvidenceEnvironment} {source : TypedSource}
      {environment : Environment} {before after : Heap}
      {statements : List StatementId} {outcome : ControlOutcome}
      {control : ControlContext} {facts : BodyFacts}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : StatementsHaveType source control context statements
        staticFinalContext facts)
      (completes : BodyCompletes control.returnType facts)
      (evaluation : FunctionStatementsExecute program context evidence source
        environment before statements runtimeFinalContext outcome after) :
      StatementEvaluationPreserved context staticFinalContext control.returnType
        before after outcome ∧ outcome.NoEscapedControl :=
    match evaluation with
    | .nil => by
        cases typing
        exact ⟨{
          heap_typed := before_typed
          heap_extends := .refl before
          outcome_typed := .fallthrough environment_agrees
        }, .fallthrough _⟩
    | .tailExpression contains form_eq evaluate => by
        cases typing with
        | singleton head_type =>
            rcases tailExpressionTyping runtime.graph head_type contains
                form_eq with
              ⟨expressionType, expression_type, facts_eq⟩
            rw [facts_eq] at completes
            simp [BodyCompletes, BodyFacts.singleton,
              ControlSummary.ordinary] at completes
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed expression_type
                evaluate with
              ⟨value_typed, after_typed, extension⟩
            exact ⟨{
              heap_typed := after_typed
              heap_extends := extension
              outcome_typed := .returned (completes ▸ value_typed)
            }, .returned _⟩
    | .singleton contains not_tail execute => by
        have control_head :
            ∀ {staticHeadFinal headFacts},
              StatementHasType source control context _ staticHeadFinal headFacts →
              ControlSummary.AllowsTransfers headFacts.control outcome :=
          fun head_type => preserveStatementControlSummaryRec program_well_formed runtime
            evidence_covers environment_agrees before_typed head_type execute
        cases typing with
        | singleton head_type =>
            refine ⟨preserveStatementRec program_well_formed runtime
              evidence_covers environment_agrees before_typed head_type execute, ?_⟩
            exact (control_head head_type).noEscape_of_complete completes
    | @FunctionStatementsExecute.cons program context middleContext finalContext
        evidence source environment before middle after statement next rest
        nextEnvironment outcome head tail => by
        have preserve_head :
            ∀ {staticHeadFinal headFacts},
              StatementHasType source control context statement staticHeadFinal
                headFacts →
              StatementEvaluationPreserved context staticHeadFinal
                control.returnType before middle (.fallthrough nextEnvironment) :=
          fun head_type =>
            preserveStatementRec program_well_formed runtime
              evidence_covers environment_agrees before_typed head_type head
        have control_head :
            ∀ {staticHeadFinal headFacts},
              StatementHasType source control context statement staticHeadFinal
                headFacts →
              headFacts.control.canFallthrough = true :=
          fun head_type =>
            (preserveStatementControlSummaryRec program_well_formed runtime
              evidence_covers environment_agrees before_typed head_type head).canFallthrough
              (.intro nextEnvironment)
        have preserve_tail :
            ∀ {staticTailFinal tailFacts},
              SourceRuntimeValid program middleContext source →
              evidence.Covers middleContext →
              EnvironmentAgrees middle middleContext.locals nextEnvironment →
              HeapWellTyped middleContext middle →
              StatementsHaveType source control middleContext (next :: rest)
                staticTailFinal tailFacts →
              BodyCompletes control.returnType tailFacts →
              StatementEvaluationPreserved middleContext staticTailFinal
                control.returnType middle after outcome ∧ outcome.NoEscapedControl :=
          fun tail_runtime tail_evidence tail_environment tail_heap tail_type
              tail_completes =>
            preserveFunctionStatementsRecWithControl program_well_formed
              tail_runtime tail_evidence tail_environment tail_heap tail_type
              tail_completes tail
        cases typing with
        | cons head_type tail_type =>
            have middle_context_eq := statementFinalContext_eq
              runtime.graph head_type head
            have aligned_tail_type := middle_context_eq.symm ▸ tail_type
            rcases preserve_head head_type with
              ⟨middle_typed, head_extension, head_outcome⟩
            cases head_outcome with
            | fallthrough middle_environment_agrees =>
                have fields :=
                  Solcore.SourceSemantics.Dynamic.StatementHasType.runtimeContextFields
                    head_type
                have aligned_fields : RuntimeContextFields context middleContext :=
                  middle_context_eq.symm ▸ fields
                have aligned_middle_environment_agrees :
                    EnvironmentAgrees middle middleContext.locals
                      nextEnvironment :=
                  middle_context_eq.symm ▸ middle_environment_agrees
                have middle_closed := aligned_fields.targetClosed runtime.closed
                have middle_evidence := aligned_fields.covers evidence_covers
                have middle_typed' := middle_typed.transportClosed
                  aligned_fields.signatures runtime.closed middle_closed
                  runtime.variables_closed
                  (aligned_fields.targetResidualVariablesOpen
                    runtime.residual_variables_open)
                have tail_completes :=
                  BodyCompletes.tail_of_cons_of_hasOutcome
                    (control_head head_type)
                    aligned_tail_type.controlHasOutcome completes
                rcases preserve_tail (runtime.transport aligned_fields)
                    middle_evidence aligned_middle_environment_agrees middle_typed'
                    aligned_tail_type tail_completes with
                  ⟨⟨after_typed, tail_extension, tail_outcome⟩, tail_noEscape⟩
                exact ⟨{
                  heap_typed := after_typed.transportClosed
                    aligned_fields.signatures.symm middle_closed runtime.closed
                    (aligned_fields.targetVariablesClosed runtime.variables_closed)
                    runtime.residual_variables_open
                  heap_extends := head_extension.trans tail_extension
                  outcome_typed := tail_outcome.transportEntry aligned_fields
                    runtime.closed runtime.variables_closed
                    runtime.residual_variables_open
                }, tail_noEscape⟩
    | .terminal head terminal => by
        have control_head :
            ∀ {staticHeadFinal headFacts},
              StatementHasType source control context _ staticHeadFinal headFacts →
              ControlSummary.AllowsTransfers headFacts.control outcome :=
          fun head_type => preserveStatementControlSummaryRec program_well_formed runtime
            evidence_covers environment_agrees before_typed head_type head
        cases typing with
        | cons head_type tail_type =>
            rcases preserveStatementRec program_well_formed runtime
                evidence_covers environment_agrees before_typed head_type head with
              ⟨after_typed, extension, head_outcome⟩
            exact ⟨{
              heap_typed := after_typed
              heap_extends := extension
              outcome_typed := head_outcome.retargetTerminal terminal
            }, (control_head head_type).noEscape_of_cons_complete completes⟩
    termination_by structural evaluation

  private theorem preserveForItemRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context staticFinalContext runtimeFinalContext : Context}
      {evidence : EvidenceEnvironment} {source : TypedSource}
      {environment finalEnvironment : Environment} {before after : Heap}
      {item : ForItemForm} {control : ControlContext}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : ForItemHasType source control context item staticFinalContext)
      (evaluation : ForItemExecutes program context evidence source environment
        before item runtimeFinalContext finalEnvironment after) :
      runtimeFinalContext = staticFinalContext /\
        HeapWellTyped context after /\ HeapTypesExtend before after /\
          EnvironmentAgrees after staticFinalContext.locals finalEnvironment :=
    match evaluation with
    | .letUninitialized runtime_monomorphic extension allocate => by
        cases typing with
        | letUninitialized monomorphic _generalizes static_extension =>
            cases static_extension
            cases extension
            have heap_extension := HeapTypesExtend.of_allocation allocate
            exact ⟨rfl, before_typed.allocate (.none _) allocate, heap_extension,
              .cons allocate.reads_new rfl (.ordinary runtime_monomorphic rfl)
                (environment_agrees.mono heap_extension)⟩
    | .letInitialized evaluate runtime_monomorphic extension allocate => by
        cases typing with
        | letInitialized initializer_type monomorphic _generalizes
            static_extension =>
            cases static_extension
            cases extension
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed initializer_type
                evaluate with
              ⟨value_typed, middle_typed, evaluation_extension⟩
            have allocation_extension := HeapTypesExtend.of_allocation allocate
            exact ⟨rfl, middle_typed.allocate (.some value_typed) allocate,
              evaluation_extension.trans allocation_extension,
              .cons allocate.reads_new rfl (.ordinary runtime_monomorphic rfl)
                ((environment_agrees.mono evaluation_extension).mono
                  allocation_extension)⟩
        | letInitializedGeneralized polymorphic _generalizes initializer_type
            static_extension =>
            exact (polymorphic runtime_monomorphic).elim
    | .letInitializedGeneralized captures runtime_polymorphic extension
        allocate => by
        cases typing with
        | letInitialized initializer_type static_monomorphic _generalizes
            static_extension =>
            exact (runtime_polymorphic static_monomorphic).elim
        | letInitializedGeneralized static_polymorphic
            requirements_well_formed generalizes initializer_type
            static_extension =>
            have function_typed := captures.wellTyped runtime
              environment_agrees static_polymorphic requirements_well_formed
              generalizes initializer_type static_extension
            have allocation_extension :=
              HeapTypesExtend.of_generalized_allocation allocate
            have after_typed := before_typed.allocateGeneralized function_typed
              allocate
            cases static_extension
            cases extension
            exact ⟨rfl, after_typed, allocation_extension,
              .cons allocate.reads_new
                (by simpa only using (congrArg
                  (fun retained : TypedBinder => retained.scheme.body)
                  captures.binder_eq))
                (.generalized rfl
                  (by simpa only using (congrArg TypedBinder.id
                    captures.binder_eq))
                  (by simpa only using (congrArg TypedBinder.scheme
                    captures.binder_eq)))
                (environment_agrees.mono allocation_extension)⟩
    | .expression evaluate => by
        cases typing with
        | expression expression_type =>
            rcases preserveExpressionRec program_well_formed runtime
                evidence_covers environment_agrees before_typed expression_type
                evaluate with
              ⟨value_typed, after_typed, extension⟩
            exact ⟨rfl, after_typed, extension,
              environment_agrees.mono extension⟩
    | .assignValue execute => by
        cases typing with
        | assignValue assignment_type =>
            rcases preserveAssignmentRec program_well_formed runtime
                evidence_covers environment_agrees before_typed assignment_type
                rfl rfl rfl execute with
              ⟨after_typed, extension⟩
            exact ⟨rfl, after_typed, extension,
              environment_agrees.mono extension⟩
    | .assignBitNot execute => by
        cases typing with
        | assignBitNot assignment_type =>
            rcases preserveSnapshotRec program_well_formed runtime
                evidence_covers environment_agrees before_typed assignment_type
                rfl rfl execute with
              ⟨after_typed, extension⟩
            exact ⟨rfl, after_typed, extension,
              environment_agrees.mono extension⟩
    termination_by structural evaluation

  private theorem preserveForItemsRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context staticFinalContext runtimeFinalContext : Context}
      {evidence : EvidenceEnvironment} {source : TypedSource}
      {environment finalEnvironment : Environment} {before after : Heap}
      {items : List ForItemForm} {control : ControlContext}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : ForItemsHaveType source control context items staticFinalContext)
      (evaluation : ForItemsExecute program context evidence source environment
        before items runtimeFinalContext finalEnvironment after) :
      runtimeFinalContext = staticFinalContext /\
        HeapWellTyped context after /\ HeapTypesExtend before after /\
          EnvironmentAgrees after staticFinalContext.locals finalEnvironment :=
    match evaluation with
    | .nil => by
        cases typing
        exact ⟨rfl, before_typed, .refl before, environment_agrees⟩
    | .cons head tail => by
        cases typing with
        | cons head_type tail_type =>
            rcases preserveForItemRec program_well_formed runtime
                evidence_covers environment_agrees before_typed head_type head with
              ⟨middle_context_eq, middle_typed, head_extension,
                middle_environment_agrees⟩
            subst middle_context_eq
            have fields :=
              Solcore.SourceSemantics.Dynamic.ForItemHasType.runtimeContextFields
                head_type
            have middle_closed := fields.targetClosed runtime.closed
            have middle_evidence := fields.covers evidence_covers
            have middle_typed' := middle_typed.transportClosed fields.signatures
              runtime.closed middle_closed runtime.variables_closed
              (fields.targetResidualVariablesOpen runtime.residual_variables_open)
            rcases preserveForItemsRec (control := control)
                (staticFinalContext := staticFinalContext)
                program_well_formed
                (runtime.transport fields) middle_evidence
                middle_environment_agrees middle_typed' tail_type tail with
              ⟨final_context_eq, after_typed, tail_extension,
                final_environment_agrees⟩
            subst final_context_eq
            have after_typed' := after_typed.transportClosed
              fields.signatures.symm middle_closed runtime.closed
              (fields.targetVariablesClosed runtime.variables_closed)
              runtime.residual_variables_open
            exact ⟨rfl, after_typed', head_extension.trans tail_extension,
              final_environment_agrees⟩
    termination_by structural evaluation

  private theorem preserveWhileRecWithControl
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context runtimeFinalContext : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment} {before after : Heap}
      {condition : ExpressionId} {body : List StatementId}
      {outcome : ControlOutcome} {control : ControlContext}
      {bodyFinal : Context} {bodyFacts : BodyFacts}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (condition_type : ExpressionHasType source context condition .bool)
      (body_type : StatementsHaveType source control.enterLoop context body
        bodyFinal bodyFacts)
      (evaluation : WhileExecutes program context evidence source environment before
        condition body runtimeFinalContext outcome after) :
      StatementEvaluationPreserved context context control.returnType before after
        outcome ∧ outcome.NoEscapedControl :=
    match evaluation with
    | .done condition_evaluates => by
        rcases preserveExpressionRec program_well_formed runtime
            evidence_covers environment_agrees before_typed condition_type
            condition_evaluates with
          ⟨condition_typed, after_typed, extension⟩
        exact ⟨{
          heap_typed := after_typed
          heap_extends := extension
          outcome_typed := .fallthrough (environment_agrees.mono extension)
        }, .fallthrough _⟩
    | .nextFallthrough condition_evaluates body_executes next => by
        rcases preserveExpressionRec program_well_formed runtime
            evidence_covers environment_agrees before_typed condition_type
            condition_evaluates with
          ⟨condition_typed, condition_heap_typed, condition_extension⟩
        rcases preserveStatementsRec program_well_formed runtime
            evidence_covers (environment_agrees.mono condition_extension)
            condition_heap_typed body_type body_executes with
          ⟨body_heap_typed, body_extension, body_outcome⟩
        have prefix_extension := condition_extension.trans body_extension
        rcases preserveWhileRecWithControl program_well_formed runtime
            evidence_covers (environment_agrees.mono prefix_extension)
            body_heap_typed condition_type body_type next with
          ⟨⟨after_typed, next_extension, next_outcome⟩, next_noEscape⟩
        exact ⟨{
          heap_typed := after_typed
          heap_extends := prefix_extension.trans next_extension
          outcome_typed := next_outcome
        }, next_noEscape⟩
    | .nextContinue condition_evaluates body_executes next => by
        rcases preserveExpressionRec program_well_formed runtime
            evidence_covers environment_agrees before_typed condition_type
            condition_evaluates with
          ⟨condition_typed, condition_heap_typed, condition_extension⟩
        rcases preserveStatementsRec program_well_formed runtime
            evidence_covers (environment_agrees.mono condition_extension)
            condition_heap_typed body_type body_executes with
          ⟨body_heap_typed, body_extension, body_outcome⟩
        have prefix_extension := condition_extension.trans body_extension
        rcases preserveWhileRecWithControl program_well_formed runtime
            evidence_covers (environment_agrees.mono prefix_extension)
            body_heap_typed condition_type body_type next with
          ⟨⟨after_typed, next_extension, next_outcome⟩, next_noEscape⟩
        exact ⟨{
          heap_typed := after_typed
          heap_extends := prefix_extension.trans next_extension
          outcome_typed := next_outcome
        }, next_noEscape⟩
    | .breaks condition_evaluates body_executes => by
        rcases preserveExpressionRec program_well_formed runtime
            evidence_covers environment_agrees before_typed condition_type
            condition_evaluates with
          ⟨condition_typed, condition_heap_typed, condition_extension⟩
        rcases preserveStatementsRec program_well_formed runtime
            evidence_covers (environment_agrees.mono condition_extension)
            condition_heap_typed body_type body_executes with
          ⟨after_typed, body_extension, body_outcome⟩
        have extension := condition_extension.trans body_extension
        exact ⟨{
          heap_typed := after_typed
          heap_extends := extension
          outcome_typed := .fallthrough (environment_agrees.mono extension)
        }, .fallthrough _⟩
    | .returns condition_evaluates body_executes => by
        rcases preserveExpressionRec program_well_formed runtime
            evidence_covers environment_agrees before_typed condition_type
            condition_evaluates with
          ⟨condition_typed, condition_heap_typed, condition_extension⟩
        rcases preserveStatementsRec program_well_formed runtime
            evidence_covers (environment_agrees.mono condition_extension)
            condition_heap_typed body_type body_executes with
          ⟨after_typed, body_extension, body_outcome⟩
        have extension := condition_extension.trans body_extension
        cases body_outcome with
        | returned result_typed =>
            exact ⟨{
              heap_typed := after_typed
              heap_extends := extension
              outcome_typed := .returned result_typed
            }, .returned _⟩
    termination_by structural evaluation

  private theorem preserveForLoopRecWithControl
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context runtimeFinalContext : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment} {before after : Heap}
      {condition : ExpressionId} {post : List ForItemForm}
      {body : List StatementId} {outcome : ControlOutcome}
      {control : ControlContext} {postContext bodyFinal : Context}
      {bodyFacts : BodyFacts}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (condition_type : ExpressionHasType source context condition .bool)
      (post_type : ForItemsHaveType source control.enterLoop context post postContext)
      (body_type : StatementsHaveType source control.enterLoop context body bodyFinal
        bodyFacts)
      (evaluation : ForLoopExecutes program context evidence source environment
        before condition post body runtimeFinalContext outcome after) :
      StatementEvaluationPreserved context context control.returnType before after
        outcome ∧ outcome.NoEscapedControl :=
    match evaluation with
    | .done condition_evaluates => by
        rcases preserveExpressionRec program_well_formed runtime
            evidence_covers environment_agrees before_typed condition_type
            condition_evaluates with
          ⟨condition_typed, after_typed, extension⟩
        exact ⟨{
          heap_typed := after_typed
          heap_extends := extension
          outcome_typed := .fallthrough (environment_agrees.mono extension)
        }, .fallthrough _⟩
    | .nextFallthrough condition_evaluates body_executes post_executes next => by
        rcases preserveExpressionRec program_well_formed runtime
            evidence_covers environment_agrees before_typed condition_type
            condition_evaluates with
          ⟨condition_typed, condition_heap_typed, condition_extension⟩
        rcases preserveStatementsRec program_well_formed runtime
            evidence_covers (environment_agrees.mono condition_extension)
            condition_heap_typed body_type body_executes with
          ⟨body_heap_typed, body_extension, body_outcome⟩
        have body_prefix := condition_extension.trans body_extension
        rcases preserveForItemsRec program_well_formed runtime
            evidence_covers (environment_agrees.mono body_prefix)
            body_heap_typed post_type post_executes with
          ⟨post_context_eq, post_heap_typed, post_extension,
            post_environment_agrees⟩
        have iteration_extension := body_prefix.trans post_extension
        rcases preserveForLoopRecWithControl program_well_formed runtime
            evidence_covers (environment_agrees.mono iteration_extension)
            post_heap_typed condition_type post_type body_type next with
          ⟨⟨after_typed, next_extension, next_outcome⟩, next_noEscape⟩
        exact ⟨{
          heap_typed := after_typed
          heap_extends := iteration_extension.trans next_extension
          outcome_typed := next_outcome
        }, next_noEscape⟩
    | .nextContinue condition_evaluates body_executes post_executes next => by
        rcases preserveExpressionRec program_well_formed runtime
            evidence_covers environment_agrees before_typed condition_type
            condition_evaluates with
          ⟨condition_typed, condition_heap_typed, condition_extension⟩
        rcases preserveStatementsRec program_well_formed runtime
            evidence_covers (environment_agrees.mono condition_extension)
            condition_heap_typed body_type body_executes with
          ⟨body_heap_typed, body_extension, body_outcome⟩
        have body_prefix := condition_extension.trans body_extension
        rcases preserveForItemsRec program_well_formed runtime
            evidence_covers (environment_agrees.mono body_prefix)
            body_heap_typed post_type post_executes with
          ⟨post_context_eq, post_heap_typed, post_extension,
            post_environment_agrees⟩
        have iteration_extension := body_prefix.trans post_extension
        rcases preserveForLoopRecWithControl program_well_formed runtime
            evidence_covers (environment_agrees.mono iteration_extension)
            post_heap_typed condition_type post_type body_type next with
          ⟨⟨after_typed, next_extension, next_outcome⟩, next_noEscape⟩
        exact ⟨{
          heap_typed := after_typed
          heap_extends := iteration_extension.trans next_extension
          outcome_typed := next_outcome
        }, next_noEscape⟩
    | .breaks condition_evaluates body_executes => by
        rcases preserveExpressionRec program_well_formed runtime
            evidence_covers environment_agrees before_typed condition_type
            condition_evaluates with
          ⟨condition_typed, condition_heap_typed, condition_extension⟩
        rcases preserveStatementsRec program_well_formed runtime
            evidence_covers (environment_agrees.mono condition_extension)
            condition_heap_typed body_type body_executes with
          ⟨after_typed, body_extension, body_outcome⟩
        have extension := condition_extension.trans body_extension
        exact ⟨{
          heap_typed := after_typed
          heap_extends := extension
          outcome_typed := .fallthrough (environment_agrees.mono extension)
        }, .fallthrough _⟩
    | .returns condition_evaluates body_executes => by
        rcases preserveExpressionRec program_well_formed runtime
            evidence_covers environment_agrees before_typed condition_type
            condition_evaluates with
          ⟨condition_typed, condition_heap_typed, condition_extension⟩
        rcases preserveStatementsRec program_well_formed runtime
            evidence_covers (environment_agrees.mono condition_extension)
            condition_heap_typed body_type body_executes with
          ⟨after_typed, body_extension, body_outcome⟩
        have extension := condition_extension.trans body_extension
        cases body_outcome with
        | returned result_typed =>
            exact ⟨{
              heap_typed := after_typed
              heap_extends := extension
              outcome_typed := .returned result_typed
            }, .returned _⟩
    termination_by structural evaluation

end

  private theorem preserveStatementControlRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context staticFinalContext runtimeFinalContext : Context}
      {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment}
      {before after : Heap} {statement : StatementId} {outcome : ControlOutcome}
      {control : ControlContext} {facts : StatementFacts}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : StatementHasType source control context statement staticFinalContext
        facts)
      (evaluation : StatementExecutes program context evidence source environment
        before statement runtimeFinalContext outcome after) :
      outcome.IsFallthrough → facts.control.canFallthrough = true :=
  (preserveStatementControlSummaryRec program_well_formed runtime evidence_covers
    environment_agrees before_typed typing evaluation).canFallthrough

  private theorem preserveStatementsControlRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context staticFinalContext runtimeFinalContext : Context}
      {evidence : EvidenceEnvironment} {source : TypedSource}
      {environment : Environment} {before after : Heap}
      {statements : List StatementId} {outcome : ControlOutcome}
      {control : ControlContext} {facts : BodyFacts}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : StatementsHaveType source control context statements
        staticFinalContext facts)
      (evaluation : StatementsExecute program context evidence source environment
        before statements runtimeFinalContext outcome after) :
      outcome.IsFallthrough → facts.control.canFallthrough = true :=
  (preserveStatementsControlSummaryRec program_well_formed runtime evidence_covers
    environment_agrees before_typed typing evaluation).canFallthrough

  private theorem preserveFunctionStatementsRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context staticFinalContext runtimeFinalContext : Context}
      {evidence : EvidenceEnvironment} {source : TypedSource}
      {environment : Environment} {before after : Heap}
      {statements : List StatementId} {outcome : ControlOutcome}
      {control : ControlContext} {facts : BodyFacts}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (typing : StatementsHaveType source control context statements
        staticFinalContext facts)
      (completes : BodyCompletes control.returnType facts)
      (evaluation : FunctionStatementsExecute program context evidence source
        environment before statements runtimeFinalContext outcome after) :
      StatementEvaluationPreserved context staticFinalContext control.returnType
        before after outcome :=
  (preserveFunctionStatementsRecWithControl program_well_formed runtime evidence_covers
    environment_agrees before_typed typing completes evaluation).1

  private theorem preserveWhileRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context runtimeFinalContext : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment} {before after : Heap}
      {condition : ExpressionId} {body : List StatementId}
      {outcome : ControlOutcome} {control : ControlContext}
      {bodyFinal : Context} {bodyFacts : BodyFacts}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (condition_type : ExpressionHasType source context condition .bool)
      (body_type : StatementsHaveType source control.enterLoop context body
        bodyFinal bodyFacts)
      (evaluation : WhileExecutes program context evidence source environment before
        condition body runtimeFinalContext outcome after) :
      StatementEvaluationPreserved context context control.returnType before after
        outcome :=
  (preserveWhileRecWithControl program_well_formed runtime evidence_covers
    environment_agrees before_typed condition_type body_type evaluation).1

  private theorem preserveForLoopRec
      {program : Program}
      (program_well_formed : ProgramWellFormed program)
      {context runtimeFinalContext : Context} {evidence : EvidenceEnvironment}
      {source : TypedSource} {environment : Environment} {before after : Heap}
      {condition : ExpressionId} {post : List ForItemForm}
      {body : List StatementId} {outcome : ControlOutcome}
      {control : ControlContext} {postContext bodyFinal : Context}
      {bodyFacts : BodyFacts}
      (runtime : SourceRuntimeValid program context source)
      (evidence_covers : evidence.Covers context)
      (environment_agrees : EnvironmentAgrees before context.locals environment)
      (before_typed : HeapWellTyped context before)
      (condition_type : ExpressionHasType source context condition .bool)
      (post_type : ForItemsHaveType source control.enterLoop context post postContext)
      (body_type : StatementsHaveType source control.enterLoop context body bodyFinal
        bodyFacts)
      (evaluation : ForLoopExecutes program context evidence source environment
        before condition post body runtimeFinalContext outcome after) :
      StatementEvaluationPreserved context context control.returnType before after
        outcome :=
  (preserveForLoopRecWithControl program_well_formed runtime evidence_covers
    environment_agrees before_typed condition_type post_type body_type evaluation).1

namespace StatementExecutes

/-- A dynamically observed ordinary statement outcome is represented by the
statement's static control summary. -/
theorem controlCanFallthrough
    {program : Program} (program_well_formed : ProgramWellFormed program)
    {context staticFinalContext runtimeFinalContext : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap}
    {statement : StatementId} {outcome : ControlOutcome}
    {control : ControlContext} {facts : StatementFacts}
    (runtime : SourceRuntimeValid program context source)
    (evidence_covers : evidence.Covers context)
    (environment_agrees : EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (typing : StatementHasType source control context statement
      staticFinalContext facts)
    (evaluation : StatementExecutes program context evidence source environment
      before statement runtimeFinalContext outcome after) :
    outcome.IsFallthrough → facts.control.canFallthrough = true :=
  preserveStatementControlRec program_well_formed runtime evidence_covers
    environment_agrees before_typed typing evaluation

end StatementExecutes

namespace StatementsExecute

/-- Ordinary completion of a dynamic statement list is admitted by its static
body-control summary. -/
theorem controlCanFallthrough
    {program : Program} (program_well_formed : ProgramWellFormed program)
    {context staticFinalContext runtimeFinalContext : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap}
    {statements : List StatementId} {outcome : ControlOutcome}
    {control : ControlContext} {facts : BodyFacts}
    (runtime : SourceRuntimeValid program context source)
    (evidence_covers : evidence.Covers context)
    (environment_agrees : EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (typing : StatementsHaveType source control context statements
      staticFinalContext facts)
    (evaluation : StatementsExecute program context evidence source environment
      before statements runtimeFinalContext outcome after) :
    outcome.IsFallthrough → facts.control.canFallthrough = true :=
  preserveStatementsControlRec program_well_formed runtime evidence_covers
    environment_agrees before_typed typing evaluation

end StatementsExecute

/-- A well-formed program supplies the complete mutually recursive dynamic
preservation package for the source language. -/
theorem _root_.Solcore.SourceSemantics.ProgramWellFormed.wholeLanguagePreservation
    {program : Program} (program_well_formed : ProgramWellFormed program) :
    WholeLanguagePreservation program := {
  program_well_formed
  expression := by
    intro context evidence source environment before after id value type runtime
      evidence_covers environment_agrees before_typed typing evaluation
    exact preserveExpressionRec program_well_formed runtime evidence_covers
      environment_agrees before_typed typing evaluation
  statements := by
    intro context evidence source environment before after statements outcome
      control staticFinalContext runtimeFinalContext facts runtime evidence_covers
      environment_agrees before_typed typing evaluation
    exact preserveStatementsRec program_well_formed runtime evidence_covers
      environment_agrees before_typed typing evaluation
  invoke := by
    intro bodyInstance evidence before after arguments result inputTypes
      lexicalContext facts certificate evidence_covers before_typed
      arguments_typed evaluation
    exact preserveBodyRec program_well_formed certificate evidence_covers
      before_typed arguments_typed evaluation
}

end Solcore.SourceSemantics.Dynamic

namespace Solcore.SourceSemantics.Dynamic
open Frontend SourceInference TypeSystem

namespace FunctionStatementsExecute

/-- The original function-statement preservation core applies to this exact
Source execution, including its implicit final expression. -/
theorem preserved
    {program : Program} (wellFormed : ProgramWellFormed program)
    {context staticFinalContext runtimeFinalContext : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap}
    {statements : List StatementId} {outcome : ControlOutcome}
    {control : ControlContext} {facts : BodyFacts}
    (runtime : SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context before)
    (typing : StatementsHaveType source control context statements staticFinalContext facts)
    (completes : BodyCompletes control.returnType facts)
    (execution : FunctionStatementsExecute program context evidence source environment
      before statements runtimeFinalContext outcome after) :
    StatementEvaluationPreserved context staticFinalContext control.returnType before after outcome :=
  preserveFunctionStatementsRec wellFormed runtime covers locals heap typing completes execution

/-- A complete typed function body cannot leave a break or continue transfer.
The original mutual preservation core supplies this observation at the actual
Source heap and environment; implicit tail-expression returns remain valid. -/
theorem noEscapedControl
    {program : Program} (wellFormed : ProgramWellFormed program)
    {context staticFinalContext runtimeFinalContext : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap}
    {statements : List StatementId} {outcome : ControlOutcome}
    {control : ControlContext} {facts : BodyFacts}
    (runtime : SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context before)
    (typing : StatementsHaveType source control context statements staticFinalContext facts)
    (completes : BodyCompletes control.returnType facts)
    (execution : FunctionStatementsExecute program context evidence source environment
      before statements runtimeFinalContext outcome after) :
    outcome.NoEscapedControl :=
  (preserveFunctionStatementsRecWithControl wellFormed runtime covers locals heap
    typing completes execution).2

end FunctionStatementsExecute

namespace StatementExecutes

/-- The original context proof applies to this actual Source statement and its
independent static typing receipt. -/
theorem final_context_of_typing
    {program : Program} {context staticFinalContext runtimeFinalContext : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap}
    {statement : StatementId} {outcome : ControlOutcome}
    {control : ControlContext} {facts : StatementFacts}
    (graph : OccurrenceGraphWellFormed source)
    (typing : StatementHasType source control context statement staticFinalContext facts)
    (execution : StatementExecutes program context evidence source environment
      before statement runtimeFinalContext outcome after) :
    runtimeFinalContext = staticFinalContext :=
  statementFinalContext_eq graph typing execution

end StatementExecutes

end Solcore.SourceSemantics.Dynamic

namespace Solcore.SourceSemantics.Dynamic
open Frontend SourceInference TypeSystem

namespace ForItemsExecute

/-- The original for-item preservation core applies to this exact Source
prefix, including its final context and allocated local environment. -/
theorem preserved
    {program : Program} (wellFormed : ProgramWellFormed program)
    {context staticFinalContext runtimeFinalContext : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment finalEnvironment : Environment} {before after : Heap}
    {items : List ForItemForm} {control : ControlContext}
    (runtime : SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context before)
    (typing : ForItemsHaveType source control context items staticFinalContext)
    (execution : ForItemsExecute program context evidence source environment
      before items runtimeFinalContext finalEnvironment after) :
    runtimeFinalContext = staticFinalContext ∧ HeapWellTyped context after ∧
      HeapTypesExtend before after ∧
        EnvironmentAgrees after staticFinalContext.locals finalEnvironment :=
  preserveForItemsRec wellFormed runtime covers locals heap typing execution

end ForItemsExecute

end Solcore.SourceSemantics.Dynamic

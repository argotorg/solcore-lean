import Solcore.SourceSemantics.Staging.RecursiveTypedControlBoundary
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservationSupport

/-! Faulting calls preserve the caller's heap typing through their actual
parameter allocation and faulting body. The caller's typing source is independent
of its staged invocation scope; body source and evidence come from selection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.Staging.Recursive.FaultPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

variable {program : Program} {registry : Registry}

private theorem monoBinders_toBinders
    {owner : Resolved.DeclarationId} {context final : Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner context binders types final) :
    BindersExtend owner context binders final := by
  induction extension with
  | nil => exact .nil _
  | cons _ head _ ih => exact .cons head ih

private theorem monoBinders_monomorphic
    {owner : Resolved.DeclarationId} {context final : Context}
    {binders : List TypedBinder} {types : List Ty}
    (extension : MonoBindersExtend owner context binders types final) :
    ∀ binder, binder ∈ binders → binder.scheme.quantified = [] := by
  induction extension with
  | nil => simp
  | @cons _ _ _ binder binders type types schemeEq _ _ ih =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | member
      · simp [schemeEq, Scheme.mono]
      · exact ih selected member

/-- A selected method enters its independently typed body with an empty capture
and the actual operand values; its recursive fault retains the allocated heap. -/
theorem method_body_fault {size : Nat}
    (statementsIH : StatementsAt program registry size)
    {context : Context} {source : TypedSource} {child : Scope}
    {bodyInstance : BodyInstance} {dictionary : EvidenceEnvironment}
    {before bound after : Heap} {arguments : List Value} {inputTypes parameterTypes : List Ty}
    {lexicalContext bodyContext finalContext : Context} {facts : BodyFacts}
    {roots : List StatementId} {environment : Dynamic.Environment} {outcome : BodyOutcome} {failure : Failure}
    (runtime : SourceRuntimeValid program context source)
    (certificate : BodyInstanceTypingCertificate program bodyInstance inputTypes lexicalContext facts)
    (covers : dictionary.Covers bodyInstance.context)
    (beforeTyped : HeapWellTyped context before)
    (argumentsTyped : ValuesHaveTypes context before arguments inputTypes)
    (rootsEq : StatementRoots bodyInstance.source.roots roots)
    (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
    (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
    (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments environment bound)
    (body : Size.StatementsIn program registry true size child bodyContext environment bound roots finalContext outcome after)
    (resultRule : BodyResult bodyInstance.resultType outcome (.fault failure)) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  have signaturesEq : bodyInstance.context.signatures = context.signatures :=
    certificate.signatures_eq.trans runtime.signatures.symm
  have bodyBeforeTyped := beforeTyped.transportClosed signaturesEq runtime.closed
    certificate.type_parameters_empty runtime.variables_closed certificate.residual_type_variables_open
  have bodyArgumentsTyped := argumentsTyped.transportClosed signaturesEq runtime.closed
    certificate.type_parameters_empty runtime.variables_closed certificate.residual_type_variables_open
  rcases certificate.typing.body_typed with
    ⟨staticFinalContext, bodyType, _noExpressionRoots, _completes⟩
  have alignedBodyType := rootsEq.filterMap_eq ▸ bodyType
  have inputTypesEq : parameterTypes = inputTypes :=
    (MonoBindersExtend.bodyTypes_eq parameters).symm.trans
      (MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend)
  subst parameterTypes
  have lexicalEq := MonoBindersExtend.functional parameters certificate.typing.inputs_extend
  subst lexicalEq
  have binderArgumentsTyped : ValuesHaveTypes bodyInstance.context before arguments
      (bodyInstance.source.inputs.map fun binder => binder.scheme.body) := by
    rw [MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend]
    exact bodyArgumentsTyped
  have boundTyped := allocate.preservesHeapTyping bodyBeforeTyped binderArgumentsTyped
  have baseEnvironment : EnvironmentAgrees before bodyInstance.context.locals [] := by
    rw [certificate.locals_empty]
    exact .nil
  have boundEnvironment := allocate.preservesEnvironmentAgreement
    (monoBinders_toBinders certificate.typing.inputs_extend)
    (monoBinders_monomorphic certificate.typing.inputs_extend) baseEnvironment
  have fields := MonoBindersExtend.runtimeContextFields certificate.typing.inputs_extend
  have lexicalClosed := fields.targetClosed certificate.type_parameters_empty
  have boundAtLexical := boundTyped.transportClosed fields.signatures
    certificate.type_parameters_empty lexicalClosed certificate.type_variables_empty
    (fields.targetResidualVariablesOpen certificate.residual_type_variables_open)
  have childRuntime : SourceRuntimeValid program bodyContext child.source := by
    rw [registry.source selected]
    exact certificate.sourceRuntimeValid.transport fields
  have childCovers : child.evidence.Covers bodyContext := by
    rw [registry.evidence selected]
    exact fields.covers covers
  have childType := alignedBodyType
  have sourceEq : child.source = bodyInstance.source := registry.source selected
  rw [← sourceEq] at childType
  have outcomeEq := TypedControlBoundary.body_fault
    (TypedControlBoundary.function childRuntime.graph.nodeOccurrencesUnique childType rfl body.sound) resultRule
  subst outcome
  obtain ⟨afterTyped, bodyExtends⟩ := statementsIH childRuntime childCovers
    boundEnvironment boundAtLexical childType body
  exact ⟨afterTyped.transportClosed (signaturesEq.symm.trans fields.signatures.symm)
    lexicalClosed runtime.closed (fields.targetVariablesClosed certificate.type_variables_empty)
    runtime.residual_variables_open, allocate.extendsHeapTypes.trans bodyExtends⟩

/-- The strict body hypothesis is used only after the real parameter allocation.
Both semantic faults and nested staging faults keep the resulting heap. -/
theorem applies_step (wellFormed : ProgramWellFormed program) (size : Nat)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    AppliesAt program registry size := by
  intro scope context source before after callable arguments packed failure parameter result
    runtime beforeTyped callableTyped packing packedTyped trace
  cases trace with
  | builtinArity _ | builtinType _ _ | closureArity _ | globalArity _ _ =>
      exact ⟨beforeTyped, .refl _⟩
  | @global bodySize scope context before bound after function arguments environment
      parameterTypes bodyContext finalContext bodyInstance roots child outcome result
      instantiates covers rootsEq selected parameters allocate body resultRule =>
      rcases callableTyped.global_inv with ordinary | staged
      · rcases ordinary with ⟨typeEq, _valid, _functionEvidence⟩
        obtain ⟨inputTypes, lexicalContext, facts, certificate⟩ := instantiates.certificate wellFormed
        have functionEq : Ty.function parameter result =
            .function (Ty.productMany inputTypes) bodyInstance.resultType :=
          typeEq.trans certificate.callable_type
        cases functionEq
        have signaturesEq : bodyInstance.context.signatures = context.signatures :=
          certificate.signatures_eq.trans runtime.signatures.symm
        have bodyBeforeTyped := beforeTyped.transportClosed signaturesEq runtime.closed
          certificate.type_parameters_empty runtime.variables_closed certificate.residual_type_variables_open
        have bodyPackedTyped := packedTyped.transportClosed signaturesEq runtime.closed
          certificate.type_parameters_empty runtime.variables_closed certificate.residual_type_variables_open
        have argumentsLength : arguments.length = inputTypes.length :=
          allocate.length_eq.symm.trans certificate.typing.inputs_extend.length_eq
        have argumentsTyped := packing.unpackTypes bodyPackedTyped argumentsLength
        rcases certificate.typing.body_typed with
          ⟨staticFinalContext, bodyType, _noExpressionRoots, _completes⟩
        have alignedBodyType := rootsEq.filterMap_eq ▸ bodyType
        have inputTypesEq : parameterTypes = inputTypes :=
          (MonoBindersExtend.bodyTypes_eq parameters).symm.trans
            (MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend)
        subst parameterTypes
        have lexicalEq := MonoBindersExtend.functional parameters certificate.typing.inputs_extend
        subst lexicalEq
        have binderArgumentsTyped : ValuesHaveTypes bodyInstance.context before arguments
            (bodyInstance.source.inputs.map fun binder => binder.scheme.body) := by
          rw [MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend]
          exact argumentsTyped
        have boundTyped := allocate.preservesHeapTyping bodyBeforeTyped binderArgumentsTyped
        have baseEnvironment : EnvironmentAgrees before bodyInstance.context.locals [] := by
          rw [certificate.locals_empty]
          exact .nil
        have boundEnvironment := allocate.preservesEnvironmentAgreement
          (monoBinders_toBinders certificate.typing.inputs_extend)
          (monoBinders_monomorphic certificate.typing.inputs_extend) baseEnvironment
        have fields := MonoBindersExtend.runtimeContextFields certificate.typing.inputs_extend
        have lexicalClosed := fields.targetClosed certificate.type_parameters_empty
        have boundAtLexical := boundTyped.transportClosed fields.signatures
          certificate.type_parameters_empty lexicalClosed certificate.type_variables_empty
          (fields.targetResidualVariablesOpen certificate.residual_type_variables_open)
        have childRuntime : SourceRuntimeValid program bodyContext child.source := by
          rw [registry.source selected]
          exact certificate.sourceRuntimeValid.transport fields
        have childCovers : child.evidence.Covers bodyContext := by
          rw [registry.evidence selected]
          exact fields.covers covers
        have childType := alignedBodyType
        have sourceEq : child.source = bodyInstance.source := registry.source selected
        rw [← sourceEq] at childType
        have outcomeEq := TypedControlBoundary.body_fault
          (TypedControlBoundary.function childRuntime.graph.nodeOccurrencesUnique childType rfl body.sound) resultRule
        subst outcome
        obtain ⟨afterTyped, bodyExtends⟩ := statementsIH bodySize
          (Size.child_lt_stepSize (by simp)) childRuntime childCovers boundEnvironment boundAtLexical childType body
        exact ⟨afterTyped.transportClosed (signaturesEq.symm.trans fields.signatures.symm)
          lexicalClosed runtime.closed (fields.targetVariablesClosed certificate.type_variables_empty)
          runtime.residual_variables_open, allocate.extendsHeapTypes.trans bodyExtends⟩
      · rcases staged with ⟨_inner, impossible, _innerTyped⟩
        cases impossible
  | @closure bodySize scope context before bound after function arguments environment
      parameterTypes bodyContext finalContext child outcome result selected valid parameters allocate body resultRule =>
      rcases callableTyped.closure_function_inv with
        ⟨parameterEq, resultEq, signaturesEq, code, closureEvidence, captures⟩
      subst parameter
      subst result
      rcases code.occurrence with ⟨id, node, contains, nodeForm, _nodeRaw, formTyping⟩
      rw [nodeForm] at formTyping
      generalize rawTypeEq : Ty.function
        (Ty.productMany (function.parameters.map fun binder => binder.scheme.body))
        function.resultType = rawType at formTyping
      generalize planEq : ExpressionRequirementPlan.ordinary [] = plan at formTyping
      cases formTyping with
      | @lambda _ staticCallContext staticFinalContext _ staticParameterTypes _
          _ bodyFacts _namesUnique staticParameters bodyType _bodyCompletes =>
          have parameterTypesEq : parameterTypes = staticParameterTypes :=
            (MonoBindersExtend.bodyTypes_eq parameters).symm.trans
              (MonoBindersExtend.bodyTypes_eq staticParameters)
          subst parameterTypes
          have callContextEq := MonoBindersExtend.functional parameters staticParameters
          subst callContextEq
          have closureBeforeTyped := beforeTyped.transportClosed signaturesEq runtime.closed
            code.closed runtime.variables_closed code.residual_variables_open
          have closurePackedTyped := packedTyped.transportClosed signaturesEq runtime.closed
            code.closed runtime.variables_closed code.residual_variables_open
          have argumentsLength : arguments.length =
              (function.parameters.map fun binder => binder.scheme.body).length := by
            simpa using allocate.length_eq.symm
          have argumentsTyped := packing.unpackTypes closurePackedTyped argumentsLength
          have boundTyped := allocate.preservesHeapTyping closureBeforeTyped argumentsTyped
          have boundEnvironment := allocate.preservesEnvironmentAgreement
            (monoBinders_toBinders staticParameters) (monoBinders_monomorphic staticParameters) captures
          have fields := MonoBindersExtend.runtimeContextFields staticParameters
          have callClosed := fields.targetClosed code.closed
          have boundAtCall := boundTyped.transportClosed fields.signatures code.closed callClosed
            code.variables_closed (fields.targetResidualVariablesOpen code.residual_variables_open)
          have closureRuntime : SourceRuntimeValid program function.context function.source := {
            signatures := valid.signatures
            graph := code.graph
            owner := code.owner
            closed := code.closed
            variables_closed := code.variables_closed
            residual_variables_open := code.residual_variables_open
            requirements := code.requirement_ledger
          }
          have childRuntime : SourceRuntimeValid program bodyContext child.source := by
            rw [registry.source selected]
            exact closureRuntime.transport fields
          have childCovers : child.evidence.Covers bodyContext := by
            rw [registry.evidence selected]
            exact fields.covers closureEvidence
          have childType := bodyType
          rw [← registry.source selected] at childType
          have outcomeEq := TypedControlBoundary.body_fault
            (TypedControlBoundary.function childRuntime.graph.nodeOccurrencesUnique childType rfl body.sound) resultRule
          subst outcome
          obtain ⟨afterTyped, bodyExtends⟩ := statementsIH bodySize
            (Size.child_lt_stepSize (by simp)) childRuntime childCovers boundEnvironment boundAtCall childType body
          exact ⟨afterTyped.transportClosed (signaturesEq.symm.trans fields.signatures.symm)
            callClosed runtime.closed (fields.targetVariablesClosed code.variables_closed)
            runtime.residual_variables_open, allocate.extendsHeapTypes.trans bodyExtends⟩

end Solcore.SourceSemantics.Staging.Recursive.FaultPreservation

import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.Dynamic.Preservation

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

variable {program : Program} {registry : Registry}

/-- The recursive premise concerns the actual selected body and its exact heap.
It is consumed after parameter allocation, with the selected source and dictionary. -/
def BodySuccessAt (program : Program) (registry : Registry) (size : Nat) : Prop :=
  ∀ {scope : Scope} {context staticFinal runtimeFinal : Context}
    {environment : Dynamic.Environment} {before after : Heap}
    {roots : List StatementId} {facts : BodyFacts} {type : Ty}
    {outcome : BodyOutcome} {value : Dynamic.Value},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    StatementsHaveType scope.source ⟨type, 0⟩ context roots staticFinal facts →
    BodyCompletes type facts →
    Size.StatementsIn program registry true size scope context environment before roots
      runtimeFinal outcome after →
    BodyResult type outcome (.value value) →
    ExpressionEvaluationPreserved context before after value type

/-- Only global bodies selected by this registry need an instance certificate. -/
def GlobalBodiesTyped (program : Program) (registry : Registry) : Prop :=
  ∀ {instantiation : DeclarationInstantiation} {body : BodyInstance}
    {evidence : EvidenceEnvironment} {roots : List StatementId} {scope : Scope},
    FunctionInstantiates program instantiation body →
    StatementRoots body.source.roots roots →
    registry.Closure (globalView body evidence roots) scope →
    ∃ inputTypes lexicalContext facts,
      FunctionInstanceTypingCertificate program instantiation body inputTypes lexicalContext facts

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

/-- Ordinary and method bodies share this allocation and result transport.
The selected view retains the full original source and invocation dictionary. -/
theorem body_success {size : Nat}
    (statementsIH : BodySuccessAt program registry size)
    {context : Context} {source : TypedSource} {child : Scope}
    {bodyInstance : BodyInstance} {dictionary : EvidenceEnvironment}
    {before bound after : Heap} {arguments : List Dynamic.Value}
    {inputTypes parameterTypes : List Ty}
    {lexicalContext bodyContext finalContext : Context} {facts : BodyFacts}
    {roots : List StatementId} {environment : Dynamic.Environment}
    {outcome : BodyOutcome} {value : Dynamic.Value}
    (runtime : SourceRuntimeValid program context source)
    (certificate : BodyInstanceTypingCertificate program bodyInstance inputTypes lexicalContext facts)
    (covers : dictionary.Covers bodyInstance.context)
    (beforeTyped : HeapWellTyped context before)
    (argumentsTyped : ValuesHaveTypes context before arguments inputTypes)
    (rootsEq : StatementRoots bodyInstance.source.roots roots)
    (selected : registry.Closure (globalView bodyInstance dictionary roots) child)
    (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context
      bodyInstance.source.inputs parameterTypes bodyContext)
    (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments environment bound)
    (body : Size.StatementsIn program registry true size child bodyContext environment bound
      roots finalContext outcome after)
    (resultRule : BodyResult bodyInstance.resultType outcome (.value value)) :
    ExpressionEvaluationPreserved context before after value bodyInstance.resultType := by
  have signaturesEq : bodyInstance.context.signatures = context.signatures :=
    certificate.signatures_eq.trans runtime.signatures.symm
  have bodyBeforeTyped := beforeTyped.transportClosed signaturesEq runtime.closed
    certificate.type_parameters_empty runtime.variables_closed certificate.residual_type_variables_open
  have bodyArgumentsTyped := argumentsTyped.transportClosed signaturesEq runtime.closed
    certificate.type_parameters_empty runtime.variables_closed certificate.residual_type_variables_open
  rcases certificate.typing.body_typed with
    ⟨staticFinalContext, bodyType, _noExpressionRoots, completes⟩
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
  have preserved := statementsIH childRuntime childCovers boundEnvironment boundAtLexical
    childType completes body resultRule
  have outerSignatures := signaturesEq.symm.trans fields.signatures.symm
  exact {
    value_typed := preserved.value_typed.transportClosed outerSignatures lexicalClosed
      runtime.closed (fields.targetVariablesClosed certificate.type_variables_empty)
      runtime.residual_variables_open
    heap_typed := preserved.heap_typed.transportClosed outerSignatures lexicalClosed
      runtime.closed (fields.targetVariablesClosed certificate.type_variables_empty)
      runtime.residual_variables_open
    heap_extends := allocate.extendsHeapTypes.trans preserved.heap_extends
  }

/-- Closure invocation keeps every captured cell and the complete code and evidence
receipt obtained from the typed callable. -/
theorem closure_success {size : Nat}
    (statementsIH : BodySuccessAt program registry size)
    {context : Context} {source : TypedSource} {child : Scope} {function : Dynamic.Closure}
    {before bound after : Heap} {arguments : List Dynamic.Value} {packed value : Dynamic.Value}
    {parameterType resultType : Ty} {parameterTypes : List Ty}
    {bodyContext finalContext : Context} {environment : Dynamic.Environment} {outcome : BodyOutcome}
    (runtime : SourceRuntimeValid program context source)
    (beforeTyped : HeapWellTyped context before)
    (callableTyped : ValueHasType context before (.closure function) (.function parameterType resultType))
    (packing : ValuesPack arguments packed) (packedTyped : ValueHasType context before packed parameterType)
    (selected : registry.Closure function child) (frame : ClosureFrame program function)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters
      parameterTypes bodyContext)
    (allocate : BindersAllocate function.captured before function.parameters arguments environment bound)
    (body : Size.StatementsIn program registry true size child bodyContext environment bound
      function.body finalContext outcome after)
    (resultRule : BodyResult function.resultType outcome (.value value)) :
    ExpressionEvaluationPreserved context before after value resultType := by
  rcases callableTyped.closure_function_inv with
    ⟨parameterEq, resultEq, signaturesEq, code, closureEvidence, captures⟩
  subst parameterType
  subst resultType
  rcases code.occurrence with ⟨id, node, contains, nodeForm, nodeRaw, formTyping⟩
  rw [nodeForm] at formTyping
  generalize rawTypeEq : Ty.function
    (Ty.productMany (function.parameters.map fun binder => binder.scheme.body))
    function.resultType = rawType at formTyping
  generalize planEq : ExpressionRequirementPlan.ordinary [] = plan at formTyping
  cases formTyping with
  | @lambda _ staticCallContext staticFinalContext _ staticParameterTypes _
      _ bodyFacts namesUnique staticParameters bodyType completes =>
    have callContextEq := Solcore.SourceSemantics.Dynamic.MonoBindersExtend.functional parameters staticParameters
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
      signatures := frame.signatures
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
    have preserved := statementsIH childRuntime childCovers boundEnvironment boundAtCall
      childType completes body resultRule
    have outerSignatures := signaturesEq.symm.trans fields.signatures.symm
    exact {
      value_typed := preserved.value_typed.transportClosed outerSignatures callClosed
        runtime.closed (fields.targetVariablesClosed code.variables_closed) runtime.residual_variables_open
      heap_typed := preserved.heap_typed.transportClosed outerSignatures callClosed
        runtime.closed (fields.targetVariablesClosed code.variables_closed) runtime.residual_variables_open
      heap_extends := allocate.extendsHeapTypes.trans preserved.heap_extends
    }

/-- The strict child is the actual selected body. Unselected original functions
are outside this premise, and the original program remains the trace index. -/
theorem applies_step (selectedBodies : GlobalBodiesTyped program registry) (size : Nat)
    (statementsIH : ∀ smaller, smaller < size → BodySuccessAt program registry smaller)
    {scope : Scope} {context : Context} {source : TypedSource}
    {before after : Heap} {callable : Dynamic.Value} {arguments : List Dynamic.Value}
    {packed value : Dynamic.Value} {parameterType resultType : Ty}
    (runtime : SourceRuntimeValid program context source)
    (beforeTyped : HeapWellTyped context before)
    (callableTyped : ValueHasType context before callable (.function parameterType resultType))
    (packing : ValuesPack arguments packed) (packedTyped : ValueHasType context before packed parameterType)
    (trace : Size.Applies program registry size scope context before callable arguments (.value value) after) :
    ExpressionEvaluationPreserved context before after value resultType := by
  cases trace with
  | builtin primitive =>
    rcases primitive.preserves with ⟨argumentsTyped, resultTyped⟩
    rcases callableTyped.builtin_inv with typeEq | staged
    · rw [BuiltinFunctionId.type] at typeEq
      cases typeEq
      exact ⟨resultTyped, beforeTyped, .refl _⟩
    · rcases staged with ⟨inner, impossible, innerTyped⟩
      cases impossible
  | @global bodySize scope context before bound after function arguments environment
      parameterTypes bodyContext finalContext bodyInstance roots child outcome result
      instantiates covers rootsEq selected parameters allocate body resultRule =>
    rcases callableTyped.global_inv with ordinary | staged
    · rcases ordinary with ⟨typeEq, valid, evidence⟩
      obtain ⟨inputTypes, lexicalContext, facts, certificate⟩ :=
        selectedBodies instantiates rootsEq selected
      have functionEq : Ty.function parameterType resultType =
          .function (Ty.productMany inputTypes) bodyInstance.resultType :=
        typeEq.trans certificate.callable_type
      cases functionEq
      have argumentsLength : arguments.length = inputTypes.length :=
        allocate.length_eq.symm.trans certificate.typing.inputs_extend.length_eq
      have argumentsTyped := packing.unpackTypes packedTyped argumentsLength
      exact body_success (statementsIH bodySize (Size.child_lt_stepSize (by simp)))
        runtime certificate.toBodyInstanceTypingCertificate covers beforeTyped argumentsTyped
        rootsEq selected parameters allocate body resultRule
    · rcases staged with ⟨inner, impossible, innerTyped⟩
      cases impossible
  | @closure bodySize scope context before bound after function arguments environment
      parameterTypes bodyContext finalContext child outcome result
      selected frame parameters allocate body resultRule =>
    exact closure_success (statementsIH bodySize (Size.child_lt_stepSize (by simp)))
      runtime beforeTyped callableTyped packing packedTyped selected frame parameters allocate body resultRule

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation

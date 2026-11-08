import Solcore.SourceSemantics.Staging.Internal.TraceSize
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.Internal.Checking.TypingCertificates
import Solcore.SourceSemantics.Staging.RecursiveProfile

/-!
# Contracts of selected preservation

The registry of selected bodies, and the atomic, body and projected-write cases that need no
recursion.
-/

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedBodyPreservation
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

/-- Closure invocation copies every captured cell and keeps the complete code and
evidence receipt obtained from the typed callable. -/
theorem closure_success {size : Nat}
    (statementsIH : BodySuccessAt program registry size)
    {context : Context} {source : TypedSource} {child : Scope} {function : Dynamic.Closure}
    {before copied bound after : Heap} {arguments : List Dynamic.Value} {packed value : Dynamic.Value}
    {parameterType resultType : Ty} {parameterTypes : List Ty}
    {bodyContext finalContext : Context} {entry environment : Dynamic.Environment}
    {outcome : BodyOutcome}
    (runtime : SourceRuntimeValid program context source)
    (beforeTyped : HeapWellTyped context before)
    (callableTyped : ValueHasType context before (.closure function) (.function parameterType resultType))
    (packing : ValuesPack arguments packed) (packedTyped : ValueHasType context before packed parameterType)
    (selected : registry.Closure function child) (frame : ClosureFrame program function)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters
      parameterTypes bodyContext)
    (copy : EnvironmentCopies function.source function.captured before entry copied)
    (allocate : BindersAllocate entry copied function.parameters arguments environment bound)
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
    have argumentsTyped := (packing.unpackTypes closurePackedTyped argumentsLength).mono
      copy.metadata_extends
    have boundTyped := allocate.preservesHeapTyping (closureBeforeTyped.copy copy) argumentsTyped
    have boundEnvironment := allocate.preservesEnvironmentAgreement
      (monoBinders_toBinders staticParameters) (monoBinders_monomorphic staticParameters)
      (copy.agrees captures)
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
      heap_extends := copy.metadata_extends.trans
        (allocate.extendsHeapTypes.trans preserved.heap_extends)
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
  | @closure bodySize scope context before copied bound after function arguments entry environment
      parameterTypes bodyContext finalContext child outcome result
      selected frame parameters copy allocate body resultRule =>
    exact closure_success (statementsIH bodySize (Size.child_lt_stepSize (by simp)))
      runtime beforeTyped callableTyped packing packedTyped selected frame parameters copy allocate
      body resultRule

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedPreservationContracts
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

/-- Typing belongs to the exact method selection whose body the registry enters. -/
def MethodBodiesTyped (program : Program) (registry : Registry) : Prop :=
  ∀ {context : Context} {evidence dictionary : EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    {body : BodyInstance} {roots : List StatementId} {child : Scope},
    OperatorMethodSelected program context evidence traitName methodName requirements body dictionary →
    StatementRoots body.source.roots roots →
    registry.Closure (methodView body dictionary roots) child →
    TypedOperatorMethodSelected program context evidence traitName methodName requirements body dictionary

structure SelectedBodies (program : Program) (registry : Registry) : Prop where
  signatures : SignatureCatalogWellFormed program.signatures
  globals : GlobalBodiesTyped program registry
  methods : MethodBodiesTyped program registry

/-- Every outcome retains deep heap typing. Only success adds a value judgment. -/
structure OutcomePreserved (context : Context) (before after : Heap)
    (type : Ty) (outcome : Outcome) : Prop where
  heap_typed : HeapWellTyped context after
  heap_extends : HeapTypesExtend before after
  value_typed : ∀ value, outcome = .value value → ValueHasType context after value type

structure ValuesPreserved (context : Context) (before after : Heap)
    (types : List Ty) (outcome : ValuesOutcome) : Prop where
  heap_typed : HeapWellTyped context after
  heap_extends : HeapTypesExtend before after
  values_typed : ∀ values, outcome = .values values → ValuesHaveTypes context after values types

structure StatementsPreserved (context staticFinal runtimeFinal : Context)
    (before after : Heap) (type : Ty) (outcome : BodyOutcome) (completion : Prop := True) (allowed : Prop := True) : Prop where
  heap_typed : HeapWellTyped context after
  heap_extends : HeapTypesExtend before after
  returned : completion → ∀ value, outcome = .returned value → ValueHasType context after value type
  fallthrough : ∀ environment, outcome = .fallthrough environment →
    runtimeFinal = staticFinal ∧ EnvironmentAgrees after staticFinal.locals environment ∧ allowed

structure ItemsPreserved (context staticFinal runtimeFinal : Context)
    (before after : Heap) (outcome : ForItemsOutcome) : Prop where
  heap_typed : HeapWellTyped context after
  heap_extends : HeapTypesExtend before after
  done : ∀ environment, outcome = .done environment →
    runtimeFinal = staticFinal ∧ EnvironmentAgrees after staticFinal.locals environment

variable (program : Program) (registry : Registry)

def ExpressionAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {id : ExpressionId} {outcome : Outcome} {type : Ty},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionHasType scope.source context id type →
    Size.Expression program registry size scope context environment before id outcome after →
    OutcomePreserved context before after type outcome

def ExpressionsAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {ids : List ExpressionId} {outcome : ValuesOutcome} {types : List Ty},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    ExpressionsHaveTypes scope.source context ids types →
    Size.Expressions program registry size scope context environment before ids outcome after →
    ValuesPreserved context before after types outcome

def AppliesAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {source : TypedSource}
    {before after : Heap} {callable : Value} {arguments : List Value} {packed : Value}
    {outcome : Outcome} {parameter result : Ty},
    SourceRuntimeValid program context source → HeapWellTyped context before →
    ValueHasType context before callable (.function parameter result) →
    ValuesPack arguments packed → ValueHasType context before packed parameter →
    Size.Applies program registry size scope context before callable arguments outcome after →
    OutcomePreserved context before after result outcome

def StatementsAt (size : Nat) : Prop :=
  ∀ {mode : Bool} {scope : Scope} {context staticFinal runtimeFinal : Context}
    {environment : Dynamic.Environment} {before after : Heap} {ids : List StatementId}
    {outcome : BodyOutcome} {control : ControlContext} {facts : BodyFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    StatementsHaveType scope.source control context ids staticFinal facts →
    Size.StatementsIn program registry mode size scope context environment before ids runtimeFinal outcome after →
    StatementsPreserved context staticFinal runtimeFinal before after control.returnType outcome
      (mode = true → BodyCompletes control.returnType facts) (facts.control.canFallthrough = true)

def RawFormAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {form : ExpressionForm} {requirements : List RequirementId}
    {coercions : List SourceInference.CoercionStep} {outcome : Outcome}
    {rawType finalType : Ty} {plan : ExpressionRequirementPlan},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    (∃ id node, ContainsExpression scope.source id node ∧ node.form = form ∧ node.rawType = rawType) →
    ExpressionFormHasRawType scope.source context form rawType plan →
    ExpressionRequirementPlan.Valid context rawType finalType plan requirements coercions →
    Size.RawForm program registry size scope context environment before form requirements coercions outcome after →
    OutcomePreserved context before after rawType outcome

def CoercionStepAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {before after : Heap}
    {step : SourceInference.CoercionStep} {input : Value} {outcome : Outcome},
    SourceRuntimeValid program context scope.source → HeapWellTyped context before →
    ValueHasType context before input step.source → CoercionStepValid context step →
    Size.CoercionStep program registry size scope context before step input outcome after →
    OutcomePreserved context before after step.target outcome

def CoercionPathAt (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {before after : Heap}
    {steps : List SourceInference.CoercionStep} {input : Value} {outcome : Outcome}
    {sourceType targetType : Ty},
    SourceRuntimeValid program context scope.source → HeapWellTyped context before →
    ValueHasType context before input sourceType → CoercionPathValid context sourceType targetType steps →
    Size.CoercionPath program registry size scope context before steps input outcome after →
    OutcomePreserved context before after targetType outcome

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedAtomicPreservation
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

/-- Atomic evaluation performs no nested call. Captures use the original source and environment. -/
theorem atomic_value
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Heap} {form : ExpressionForm} {requirements : List RequirementId}
    {coercions : List SourceInference.CoercionStep} {value : Value}
    {rawType : Ty} {plan : ExpressionRequirementPlan}
    (runtime : SourceRuntimeValid program context source)
    (evidence_covers : evidence.Covers context)
    (environment_agrees : EnvironmentAgrees before context.locals environment)
    (before_typed : HeapWellTyped context before)
    (occurrence : ∃ id node, ContainsExpression source id node ∧ node.form = form ∧ node.rawType = rawType)
    (typing : ExpressionFormHasRawType source context form rawType plan)
    (atomic : AtomicForm form)
    (evaluation : ExpressionFormEvaluates program context evidence source environment before
      form requirements coercions value after) :
    ExpressionEvaluationPreserved context before after value rawType := by
  cases atomic with
  | unit =>
    cases evaluation with
    | tuple layout elements pack =>
      cases elements
      cases pack
      cases typing with
      | tuple types => cases types; exact ⟨.unit, before_typed, .refl _⟩
  | literal literal =>
    cases evaluation with
    | literal layout constructs =>
      cases typing with
      | literal valid => exact ⟨constructs.hasType, before_typed, .refl _⟩
  | integerLiteral source resolution =>
    cases evaluation with
    | integerLiteral layout constructs =>
      cases typing with
      | integerLiteral valid => exact ⟨constructs.hasType, before_typed, .refl _⟩
  | reference name resolution =>
    obtain ⟨valueTyped, heapTyped, extended⟩ := evaluation.referencePreserves environment_agrees before_typed typing
    exact ⟨valueTyped, heapTyped, extended⟩
  | proxy inner =>
    cases evaluation with
    | proxy layout =>
      cases typing with
      | proxy valid => exact ⟨.proxy _, before_typed, .refl _⟩
  | lambda parameters returnType body =>
    cases evaluation with
    | @lambda _ _ _ _ _ after captured _ _ _ _ _ layout snapshot =>
      cases typing with
      | @lambda _ lambdaContext finalContext parameters parameterTypes returnType
          body bodyFacts names_unique parameters_extend body_type body_completes =>
        rcases occurrence with ⟨id, node, contains, node_form, node_raw⟩
        have body_types := MonoBindersExtend.bodyTypes_eq parameters_extend
        have form_typed := ExpressionFormHasRawType.lambda names_unique parameters_extend body_type body_completes
        have code : ClosureCodeValid context {
            parameters := parameters, resultType := returnType, body := body,
            source := source, captured := captured, context := context, evidence := evidence } := {
          owner := runtime.owner
          closed := runtime.closed
          variables_closed := runtime.variables_closed
          residual_variables_open := runtime.residual_variables_open
          graph := runtime.graph
          requirement_ledger := runtime.requirements
          occurrence := ⟨id, node, contains, node_form, by simpa [body_types] using node_raw, by
            rw [node_form]; simpa [body_types] using form_typed⟩ }
        exact ⟨by
          simpa [body_types] using (ValueHasType.closure (context := context) (heap := after)
            (function := {
              parameters := parameters
              resultType := returnType
              body := body
              source := source
              captured := captured
              context := context
              evidence := evidence })
            rfl code evidence_covers (snapshot.agrees environment_agrees)),
          before_typed.copy snapshot, snapshot.metadata_extends⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.Staging.SelectedProjectedWritePreservation
/-! Actual typed key values determine the saved projection path. Its getter
heap and the successful RHS heap supply exactly the typing needed by a real
write, without a whole-program execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem Solcore.SourceSemantics.Dynamic

private theorem expression_type_unique {source : TypedSource} {context : Context}
    {id : ExpressionId} {first second : Ty} (unique : NodeOccurrencesUnique source)
    (left : ExpressionHasType source context id first) (right : ExpressionHasType source context id second) :
    first = second := by
  obtain ⟨leftNode, leftFound, leftType⟩ := left.stored_type
  obtain ⟨rightNode, rightFound, rightType⟩ := right.stored_type
  have same := Option.some.inj ((lookupExpression?_complete unique leftFound).symm.trans
    (lookupExpression?_complete unique rightFound))
  cases same
  exact leftType.symm.trans rightType

/-- Source typing itself supplies the complete ordered row of key types. -/
theorem projected_keys_typed {source : TypedSource} {context : Context}
    {root leaf : Ty} {projections : List PlaceProjection}
    (typing : SourceProjectionsHaveType source context root projections leaf) :
    ∃ types, ExpressionsHaveTypes source context (ProjectedTarget.keys projections) types := by
  induction projections generalizing root leaf with
  | nil => cases typing; exact ⟨[], .nil _⟩
  | cons projection rest ih =>
      cases projection with
      | member name index =>
          cases typing with
          | member _ path => exact ih path
      | index key =>
          cases typing with
          | index typed path =>
              obtain ⟨types, tail⟩ := ih path
              exact ⟨_ :: types, .cons typed tail⟩

theorem projected_place_keys_typed {source : TypedSource} {context : Context}
    {place : PlaceResolution} {leaf : Ty}
    (typing : SourcePlaceHasType source context place leaf) :
    ∃ types, ExpressionsHaveTypes source context (ProjectedTarget.keys place.projections) types := by
  cases typing with
  | intro _ path _ => exact projected_keys_typed path

/-- The row has the original Source types, independent of native layout types. -/
theorem projected_values_typed {source : TypedSource} {context : Context} {heap : Heap}
    {projections : List PlaceProjection} {values : List Dynamic.Value}
    {evaluated : List EvaluatedProjection} {root leaf : Ty} {types : List Ty}
    (unique : NodeOccurrencesUnique source)
    (typing : SourceProjectionsHaveType source context root projections leaf)
    (row : ExpressionsHaveTypes source context (ProjectedTarget.keys projections) types)
    (typedValues : ValuesHaveTypes context heap values types)
    (ordered : ProjectedTarget.Values projections values evaluated) :
    EvaluatedProjectionsHaveType context heap root evaluated leaf := by
  induction ordered generalizing root leaf types with
  | nil => cases typing; exact .nil _
  | member tail ih =>
      cases typing with
      | member selected restTyped =>
          exact .member selected (Dynamic.UniformMemberProjection.preservesType selected)
            (ih restTyped row typedValues)
  | index tail ih =>
      cases typing with
      | index keyTyped restTyped =>
          cases row with
          | cons headType tailType =>
              cases typedValues with
              | cons headValue tailValues =>
                  have same := expression_type_unique unique keyTyped headType
                  exact .index (same.symm ▸ headValue) (ih restTyped tailType tailValues)

/-- The getter reads the root at the actual successful key endpoint. -/
theorem projected_target_typed {source : TypedSource} {context : Context}
    {environment : Dynamic.Environment} {before after : Heap} {place : PlaceResolution}
    {values : List Dynamic.Value} {target : ResolvedPlace} {leaf : Ty} {types : List Ty}
    (unique : NodeOccurrencesUnique source)
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context after) (extension : HeapTypesExtend before after)
    (typed : SourcePlaceHasType source context place leaf)
    (row : ExpressionsHaveTypes source context (ProjectedTarget.keys place.projections) types)
    (typedValues : ValuesHaveTypes context after values types)
    (snapshot : ProjectedTarget.Snapshot environment before after place values target) :
    ∃ root, ResolvedPlaceHasType context after target root leaf := by
  cases typed with
  | @intro _ _ root final writable projections stored =>
      cases snapshot with
      | intro lookup initialRead ordered currentRead initialValue selection =>
          have path := projected_values_typed unique projections row typedValues ordered
          obtain ⟨scheme, staticLookup, _wellFormed, _monomorphic, bodyType⟩ := writable.scheme
          obtain ⟨location, cell, actualLookup, actualRead, cellType, _storage⟩ := locals.lookup staticLookup
          cases lookup.functional actualLookup
          cases initialRead.functional actualRead
          obtain ⟨reached, reachedRead, sameType, _⟩ := extension _ _ initialRead
          cases currentRead.functional reachedRead
          have rootType := sameType.trans (cellType.trans bodyType)
          have initialTyped := initialValue.preserves (heap _ currentRead.member)
          have selectedTyped := selection.preserves path (rootType ▸ initialTyped)
          exact ⟨root, ⟨rootType, stored, path, by simpa [stored] using selectedTyped⟩⟩

/-- Reconstruct the path from the latest root while retaining its earlier snapshot. -/
theorem projected_write_equal {context : Context} {before middle after : Heap}
    {target : ResolvedPlace} {root leaf : Ty} {value updated : Dynamic.Value}
    (targetTyped : ResolvedPlaceHasType context before target root leaf)
    (rhs : ExpressionEvaluationPreserved context before middle value leaf)
    (write : ResolvedPlaceWrites
      (fun _ replacement => AssignmentValueApplies .equal target.selected value replacement)
      middle target updated after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  have currentTarget := targetTyped.mono rhs.heap_extends
  cases write with
  | intro currentRead rootType initialValue update heapWrite =>
      rename_i currentCell initial
      have initialTyped := initialValue.preserves (rhs.heap_typed _ currentRead.member)
      have initialRoot : OptionalValueHasType context middle initial root := by
        rw [← currentTarget.root_type, ← rootType]
        exact initialTyped
      have modification : LeafModificationPreservesType context middle
          (fun _ replacement => AssignmentValueApplies .equal target.selected value replacement) leaf := by
        intro current replacement _ applies
        exact applies.equalPreserves rhs.value_typed
      have updatedTyped := update.preserves currentTarget.projections initialRoot modification
      have updatedCell : ValueHasType context middle updated currentCell.type := by
        rw [rootType, currentTarget.root_type]
        exact updatedTyped
      exact ⟨rhs.heap_typed.write currentRead (.some updatedCell) heapWrite,
        rhs.heap_extends.trans (HeapTypesExtend.of_write heapWrite)⟩

theorem projected_write_compound {context : Context} {before middle after : Heap}
    {target : ResolvedPlace} {root : Ty} {value updated : Dynamic.Value} {operator : Syntax.ValueAssignOp}
    (kind : WordCompoundAssignmentOperator operator)
    (targetTyped : ResolvedPlaceHasType context before target root .word)
    (rhs : ExpressionEvaluationPreserved context before middle value .word)
    (write : ResolvedPlaceWrites
      (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
      middle target updated after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  have currentTarget := targetTyped.mono rhs.heap_extends
  cases write with
  | intro currentRead rootType initialValue update heapWrite =>
      rename_i currentCell initial
      have initialTyped := initialValue.preserves (rhs.heap_typed _ currentRead.member)
      have initialRoot : OptionalValueHasType context middle initial root := by
        rw [← currentTarget.root_type, ← rootType]
        exact initialTyped
      have modification : LeafModificationPreservesType context middle
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement) .word := by
        intro current replacement _ applies
        exact applies.wordCompoundPreserves kind currentTarget.selected rhs.value_typed
      have updatedTyped := update.preserves currentTarget.projections initialRoot modification
      have updatedCell : ValueHasType context middle updated currentCell.type := by
        rw [rootType, currentTarget.root_type]
        exact updatedTyped
      exact ⟨rhs.heap_typed.write currentRead (.some updatedCell) heapWrite,
        rhs.heap_extends.trans (HeapTypesExtend.of_write heapWrite)⟩

/-- Unary assignment writes at the actual getter heap without an RHS phase. -/
theorem projected_write_bitNot {context : Context} {before after : Heap}
    {target : ResolvedPlace} {root : Ty} {updated : Dynamic.Value}
    (targetTyped : ResolvedPlaceHasType context before target root .word)
    (heap : HeapWellTyped context before)
    (write : ResolvedPlaceWrites (fun _ replacement => BitNotSnapshot target.selected replacement)
      before target updated after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  cases write with
  | intro currentRead rootEq initialValue update heapWrite =>
      rename_i currentCell initial
      have initialTyped := initialValue.preserves (heap _ currentRead.member)
      have initialRoot : OptionalValueHasType context before initial root := by
        rw [← targetTyped.root_type, ← rootEq]
        exact initialTyped
      have modification : LeafModificationPreservesType context before
          (fun _ replacement => BitNotSnapshot target.selected replacement) .word := by
        intro current replacement _ applies
        exact applies.preserves targetTyped.selected
      have updatedTyped := update.preserves targetTyped.projections initialRoot modification
      have updatedCell : ValueHasType context before updated currentCell.type := by
        rw [rootEq, targetTyped.root_type]
        exact updatedTyped
      exact ⟨heap.write currentRead (.some updatedCell) heapWrite, HeapTypesExtend.of_write heapWrite⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
end

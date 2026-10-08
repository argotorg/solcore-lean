import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedReadyMethodInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceMeaning

/-! Prepared operators retain the independently selected Source dictionary.
These finite static views preserve the same accepted method code, tree and
parameter receipts. Genuine operator typing supplies raw callee heap/argument
admission; no native projection or body execution law is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOperatorSourceAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogHookMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)

/-- Actual dictionary coverage strengthens only the static validity domain. -/
def EvidenceValidity (dictionary : Dynamic.EvidenceEnvironment) (context : SourceSemantics.Context) : Prop :=
  validity context ∧ dictionary.Covers context

/-- Reindex the genuine same-code compiler receipt at its actual Source selector. -/
def with_dictionary (dictionary : Dynamic.EvidenceEnvironment)
    (covers : dictionary.Covers principal.sourceBody.context) :
    ProfileFor principal.cached.compilation (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody dictionary administrative registry faults
      expressionSyntax certificates (EvidenceValidity (validity := validity) dictionary) diagnosticPolicy := {
  sameSource := profile.sameSource, parameters := profile.parameters
  sourceFrame := { profile.sourceFrame with covers := covers }
  context := profile.context, types := profile.types, extended := profile.extended
  body := { profile.body with
    initialValid := ⟨profile.body.initialValid, (Dynamic.MonoBindersExtend.runtimeContextFields profile.extended).covers covers⟩ }
  definitions := profile.definitions, registered := profile.registered, parameterType := profile.parameterType }

/-- A real binder extension transports only genuine static fields and coverage. -/
theorem evidence_extend (dictionary : Dynamic.EvidenceEnvironment)
    (extend : ∀ {context next binder}, validity context → BinderExtends principal.sourceBody.source.owner context binder next → validity next)
    {context next : SourceSemantics.Context} {binder : TypedBinder}
    (valid : EvidenceValidity (validity := validity) dictionary context)
    (extended : BinderExtends principal.sourceBody.source.owner context binder next) :
    EvidenceValidity (validity := validity) dictionary next :=
  ⟨extend valid.1 extended, (Dynamic.RuntimeContextFields.ofBinderExtends extended).covers valid.2⟩

/-- Original ledger/runtime fields and the actual dictionary remain separate. -/
theorem evidence_runtime (dictionary : Dynamic.EvidenceEnvironment)
    (runtimeOf : ∀ {context}, validity context →
      CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context principal.dictionary)
    {context : SourceSemantics.Context} (valid : EvidenceValidity (validity := validity) dictionary context) :
    CompatibleRuntimeContextValidity.Valid principal.named.specialized.function.solvedRequirements context dictionary :=
  ⟨(runtimeOf valid.1).ledger, (runtimeOf valid.1).runtime, valid.2⟩

/-- The actual trait profile and selector authenticate the raw parameter vector
and Source context at the successful operand heap, before Core erasure. -/
theorem at_selected_arguments
    {context : SourceSemantics.Context} {source : TypedSource}
    {callerEvidence dictionary : Dynamic.EvidenceEnvironment} {traitName methodName : String}
    {operand : TypeSystem.Ty} {parameterTypes returnTypes : List TypeSystem.Ty}
    {predicates : List ProgramPredicate} {requirements : List RequirementId}
    {heap : Dynamic.Heap} {arguments : List Dynamic.Value}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (operatorProfile : OperatorProfileInstantiates context traitName methodName operand parameterTypes returnTypes predicates)
    (requirementsProve : RequirementSequenceProves context requirements predicates)
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      traitName methodName requirements principal.sourceBody dictionary)
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context heap arguments parameterTypes) :
    Dynamic.HeapWellTyped principal.sourceFunction.context heap ∧
      Dynamic.ValuesHaveTypes principal.sourceFunction.context heap arguments profile.types ∧
      principal.sourceBody.resultType = TypeSystem.Ty.productMany returnTypes := by
  obtain ⟨lexicalContext, facts, certificate, resultEq⟩ := selected.certificateOfProfile wellFormed
    runtime.signatures runtime.requirements.idsUnique operatorProfile requirementsProve
  have signatures := certificate.signatures_eq.trans runtime.signatures.symm
  have bodyHeap := heapTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have bodyArguments := argumentsTyped.transportClosed signatures runtime.closed certificate.type_parameters_empty
    runtime.variables_closed certificate.residual_type_variables_open
  have typesEq : parameterTypes = profile.types :=
    (Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend).symm.trans
      (Dynamic.MonoBindersExtend.bodyTypes_eq profile.extended)
  exact ⟨principal.source_frame.context.symm ▸ bodyHeap,
    principal.source_frame.context.symm ▸ (typesEq ▸ bodyArguments), resultEq⟩

section ParentFacts
open CallablePreparedMethodSelection CallableCoercionExpressionCertificates
open CallablePreparedOperatorSourceBounds
variable {checkedProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  {receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output}
  (selected : OperatorSource receipt)
  {context : SourceSemantics.Context}

/-- Genuine parent typing exposes its original operands, operator profile and
raw result. These facts concern the complete original Source judgment. -/
theorem source_facts (unique : NodeOccurrencesUnique source)
    (coercions : node.coercions = []) (typed : ExpressionHasType source context id node.type) :
    ∃ operand parameterTypes returnTypes predicates,
      ExpressionsHaveTypes source context receipt.arguments parameterTypes ∧
      OperatorProfileInstantiates context selected.traitName selected.methodName operand parameterTypes returnTypes predicates ∧
      RequirementSequenceProves context receipt.requirements predicates ∧
      node.type = TypeSystem.Ty.productMany returnTypes := by
  generalize _typeEq : node.type = annotation at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw rawEq _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.found)
    subst actualNode
    have layout := CallableCallRequirementLayouts.ordinary_owned receipt.ordinary
    have dispatch := selected.dispatch
    rcases receipt.form with ⟨operator, operandId, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
    · simp only [form] at dispatch
      rw [form] at raw
      cases raw with
      | unary child operatorTyped =>
        cases valid with
        | ordinary _ path requirements =>
          have ownedEq := List.append_cancel_right (layout.symm.trans requirements)
          rw [coercions] at path
          generalize targetEq : node.type = target at path
          cases path
          cases operatorTyped with
          | logicalNot | wordBitNot | integerBitNot => exact False.elim (receipt.nonempty ownedEq)
          | trait staticDispatch operatorProfile proves =>
            obtain ⟨rfl, rfl⟩ := unary_dispatch_unique dispatch staticDispatch
            exact ⟨_, _, _, _, arguments ▸ .cons child (.nil context), operatorProfile, ownedEq.symm ▸ proves, rfl⟩
    · simp only [form] at dispatch
      rw [form] at raw
      cases raw with
      | binary first second operatorTyped =>
        cases valid with
        | ordinary _ path requirements =>
          have ownedEq := List.append_cancel_right (layout.symm.trans requirements)
          rw [coercions] at path
          generalize targetEq : node.type = target at path
          cases path
          cases operatorTyped with
          | wordArithmetic _ | integerArithmetic _ | wordComparison _ | integerComparison _ | booleanAnd | booleanOr =>
            exact False.elim (receipt.nonempty ownedEq)
          | trait staticDispatch operatorProfile proves =>
            obtain ⟨rfl, rfl⟩ := binary_dispatch_unique dispatch staticDispatch
            exact ⟨_, _, _, _, arguments ▸ .cons first (.cons second (.nil context)), operatorProfile, ownedEq.symm ▸ proves, rfl⟩
end ParentFacts

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOperatorSourceAdmission

import Solcore.SourceSemantics.CoreLowering.NamedCallArgumentCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleSourceInstantiationClosure
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallSelectionCertificates

/-! Ordinary declaration calls retain the actual compiler-selected signature,
physical slot, complete specialization and ordered child actions. Raw Source
callee and argument typing is recovered independently from the original node.
No inventory membership, called-body execution or native result is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallCertificates
open Core Frontend SourceInference

structure Monomorphic (instantiation : DeclarationInstantiation) : Prop where
  substitution : instantiation.parameterSubstitution = []
  predicates : instantiation.predicates = []

/-- Ordinary calls keep every raw replacement and the order retained by Source
inference. The selected compiler row still authenticates the other metadata. -/
structure Ordinary (plan : SourceCompilationPlan.Plan)
    (instantiation : DeclarationInstantiation) : Prop where
  predicates : instantiation.predicates = []
  ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution
  ordered : RecursiveNamedCallSelectionCertificates.Ordered plan instantiation

/-- Empty substitutions are a special case of ordinary selection. The actual
matcher excludes a nonempty selected row even when the plan contains others. -/
theorem Monomorphic.ordinary {instantiation : DeclarationInstantiation}
    (monomorphic : Monomorphic instantiation) (plan : SourceCompilationPlan.Plan) :
    Ordinary plan instantiation := by
  refine ⟨monomorphic.predicates, ?_, ?_⟩
  · intro parameter replacement member
    rw [monomorphic.substitution] at member
    cases member
  · intro key specialized target record
    have matched := CallableNamedMetadata.matches_of_exact target record
    have equivalent := matched.substitution
    simp only [SourceCompilationPlan.parameterSubstitutionsEquivalent,
      Bool.and_eq_true, beq_iff_eq] at equivalent
    have empty : specialized.parameterSubstitution = [] := List.length_eq_zero_iff.mp (by
      simpa only [monomorphic.substitution, List.length_nil] using equivalent.1.1)
    simp only [monomorphic.substitution, empty, List.map_nil, List.reverse_nil]

structure Receipt (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (compilation : SourceCoreFunctions.Context)
    (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id callee : ExpressionId)
    (ids : List ExpressionId) (instantiation : DeclarationInstantiation)
    (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  node : ExpressionNode
  metadata : CompatibleExpressionReads.Metadata values.checked source id node lowered.type
  form : node.form = .call callee ids (.declaration instantiation)
  ordinary : Ordinary compilation.plan instantiation
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
    compilation source scope id reasonAt = .ok lowered
  signature : SourceCoreCalls.Signature
  index : Nat
  specialized : SourceSpecialization.SpecializedFunction
  selected : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false =
    .ok (index, signature)
  record : SourceCompilationPlan.exactSpecialization compilation.plan signature.key = .ok specialized
  arity : ids.length = specialized.function.typedBody.inputs.length
  codes : List SourceCoreBasic.LoweredExpr
  generated : ids.mapM (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
    compilation source scope child reasonAt) = .ok codes
  parameter : signature.parameterType = (SourceCoreCalls.packArguments codes).type
  result : signature.resultType = lowered.type
  emitted : lowered.expression = SourceCoreCalls.call signature
    (scope.length + compilation.administrativePrefix + index)
    (SourceCoreCalls.packArguments codes).expression compilation.internalReason

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The original compatible reader and accepted real lowering supply the
complete direct-call record before any recursive child certificate is built. -/
theorem of_ordinary
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (ordinary : Ordinary compilation.plan instantiation)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt policy body fuel compilation values source scope id callee ids instantiation reasonAt lowered) := by
  have original := accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
        compilation childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form] at accepted
      obtain ⟨pair, read, _remaining⟩ := bind_ok accepted
      rcases pair with ⟨other, type⟩
      have metadata := CompatibleExpressionReads.metadata_of_read (readPolicy.symm ▸ read)
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst other
      obtain ⟨index, signature, specialized, codes, selected, record, arity, generated,
        parameter, result, emitted, output⟩ := NamedCalls.Arguments.call_of_accepted
          owner found read form (special _ _) original
      exact ⟨⟨node, output.symm ▸ metadata, form, ordinary, original, signature,
        index, specialized, selected, record, arity, codes, generated, parameter,
        result.trans output.symm, emitted⟩⟩
  · simp [owner, bind, Except.bind] at accepted

/-- Existing monomorphic callers use the same ordinary extraction. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (monomorphic : Monomorphic instantiation)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt policy body fuel compilation values source scope id callee ids instantiation reasonAt lowered) := by
  exact of_ordinary found form (monomorphic.ordinary compilation.plan) special readPolicy accepted

/-- Source argument types and declaration evidence precede compiler-child
extraction. The complete Source application record is retained, including the
raw function type and the exact declaration signature. -/
theorem source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ types, DirectDeclarationCalleeValid context source callee instantiation ∧
      DeclarationApplicationValid context instantiation types node.type instantiation.predicates ∧
      ExpressionsHaveTypes source context ids types := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    cases raw with
    | directCall calleeValid application argumentsTyped =>
      cases application with
      | intro signatureMember admissible declaration parameters result functionType predicates =>
        exact ⟨_, calleeValid, .intro signatureMember admissible declaration parameters result functionType rfl,
          argumentsTyped⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallCertificates

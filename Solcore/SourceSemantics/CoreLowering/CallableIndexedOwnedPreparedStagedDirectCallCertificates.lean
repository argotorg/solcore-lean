import Solcore.SourceSemantics.CoreLowering.NamedCallArgumentCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleSourceInstantiationClosure
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallSelectionCertificates
import Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionCertificates

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

/-- Every direct call retains its full closed raw replacement range and the
original Source parameter order in the actual compilation plan. -/
structure Supported (plan : SourceCompilationPlan.Plan)
    (instantiation : DeclarationInstantiation) : Prop where
  ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution
  ordered : RecursiveNamedCallSelectionCertificates.Ordered plan instantiation

/-- Ordinary calls keep every raw replacement and the order retained by Source
inference. The selected compiler row still authenticates the other metadata. -/
structure Ordinary (plan : SourceCompilationPlan.Plan)
    (instantiation : DeclarationInstantiation) : Prop where
  predicates : instantiation.predicates = []
  ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution
  ordered : RecursiveNamedCallSelectionCertificates.Ordered plan instantiation

theorem Ordinary.supported {plan : SourceCompilationPlan.Plan} {instantiation : DeclarationInstantiation}
    (ordinary : Ordinary plan instantiation) : Supported plan instantiation :=
  ⟨ordinary.ranges, ordinary.ordered⟩

/-- A direct node can retain declaration requirements. Its result projection
and empty output coercions are common to both compiler branches. -/
structure Metadata (checked : SourceCoreCompatibleCatalog.Checked) (source : TypedSource)
    (id : ExpressionId) (node : ExpressionNode) (type : Core.Ty) : Prop where
  found : source.lookupExpression? id = some node
  owner : id.occurrence.owner = source.owner
  coercions : node.coercions = []
  projected : checked.catalog.project node.type = .ok type

theorem Metadata.of_read {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : ExpressionId} {node : ExpressionNode} {type : Core.Ty}
    (metadata : CompatibleExpressionReads.Metadata checked source id node type) :
    Metadata checked source id node type :=
  ⟨metadata.found, metadata.owner, metadata.coercions, metadata.projected⟩

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
  metadata : Metadata values.checked source id node lowered.type
  form : node.form = .call callee ids (.declaration instantiation)
  supported : Supported compilation.plan instantiation
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
    compilation source scope id reasonAt = .ok lowered
  signature : SourceCoreCalls.Signature
  index : Nat
  specialized : SourceSpecialization.SpecializedFunction
  target : SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok signature.key
  global : compilation.globals[index]? = some signature
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
theorem of_supported
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (ordinary : Supported compilation.plan instantiation)
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
      exact ⟨⟨node, output.symm ▸ Metadata.of_read metadata, form, ordinary, original, signature,
        index, specialized, (NamedCalls.selected_signature_target selected).1,
        (NamedCalls.selected_signature_target selected).2, record, arity, codes, generated, parameter,
        result.trans output.symm, emitted⟩⟩
  · simp [owner, bind, Except.bind] at accepted

/-- Ordinary sites use the common successful fast-path extraction. -/
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
  exact of_supported found form ordinary.supported special readPolicy accepted

/-- The real fast-path read establishes empty requirements at this exact
reached node, even when the common receipt also admits authenticated calls. -/
theorem Receipt.ordinary_facts
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt policy body fuel compilation values source scope id callee ids instantiation reasonAt lowered)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id) :
    Ordinary compilation.plan instantiation ∧ receipt.node.requirements = [] := by
  have accepted := receipt.accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [receipt.metadata.owner, ne_eq, not_true_eq_false, ↓reduceIte,
    receipt.metadata.found, bind, Except.bind, pure, Except.pure] at accepted
  have bypass := special (fun budget childSource childScope childId childReasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
      compilation childSource childScope childId childReasonAt) (fuel + 1)
  cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
  all_goals try rw [bypass] at accepted
  all_goals
    simp only [receipt.form] at accepted
    obtain ⟨pair, read, _remaining⟩ := bind_ok accepted
    rcases pair with ⟨other, type⟩
    have metadata := CompatibleExpressionReads.metadata_of_read (readPolicy.symm ▸ read)
    have same := Option.some.inj (metadata.found.symm.trans receipt.metadata.found)
    subst other
    obtain ⟨index, signature, specialized, codes, selected, _rest⟩ :=
      NamedCalls.Arguments.call_of_accepted receipt.metadata.owner receipt.metadata.found read
        receipt.form (special _ _) receipt.accepted
    obtain ⟨_, _, matched, empty, _⟩ := CallableNamedMetadata.metadata_of_selected_signature selected
    exact ⟨⟨matched.predicates.symm.trans empty, receipt.supported.ranges,
      receipt.supported.ordered⟩, metadata.requirements⟩

/-- Existing profiles recover the exact ordinary restriction from the real
fast-path selector, including its full Source predicates. -/
theorem Receipt.ordinary
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt policy body fuel compilation values source scope id callee ids instantiation reasonAt lowered)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id) :
    Ordinary compilation.plan instantiation :=
  (receipt.ordinary_facts special readPolicy).1

theorem Receipt.ordinary_requirements
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt policy body fuel compilation values source scope id callee ids instantiation reasonAt lowered)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id) :
    receipt.node.requirements = [] :=
  (receipt.ordinary_facts special readPolicy).2

/-- Delegation of a direct occurrence retains both empty requirements and
an empty caller assumption list, as checked by the actual evidence hook. -/
theorem evidence_none_direct
    {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
    {child : SourceCoreEvidence.Child} {budget : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
    {callables : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector program project caller compilation child budget
      source scope id reasonAt callables = .ok none) :
    node.requirements = [] ∧ caller.assumptions = [] := by
  unfold SourceCoreEvidence.lowerWithProjector at accepted
  simp only [found, form, bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · rename_i ordinary
    simp only [Bool.and_eq_true, Bool.or_false, Bool.not_false, Bool.and_true,
      Bool.not_not] at ordinary
    exact ⟨List.isEmpty_iff.mp ordinary.1.2, List.isEmpty_iff.mp ordinary.2⟩
  · repeat first | cases accepted | split at accepted | contradiction

/-- The evidence branch receives the same recursive child callback and actual
budget as the enclosing expression compiler. -/
abbrev Child (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (compilation : SourceCoreFunctions.Context) : SourceCoreEvidence.Child :=
  fun budget childSource childScope childId childReasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
      compilation childSource childScope childId childReasonAt

/-- Accepted ordinary and authenticated calls expose the same static call
shape. The authenticated receipt keeps the real compiler branch and all its
ordered child actions; no dictionary or body meaning is supplied here. -/
theorem of_evidence
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {node : ExpressionNode} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {program : CheckedProgram} {project : SourceCoreEvidence.Projector}
    {caller : SourceSpecialization.SpecializedFunction}
    (supported : Supported compilation.plan instantiation)
    (coercions : node.coercions = [])
    (projected : values.checked.catalog.project node.type = .ok lowered.type)
    (evidence : CallableCoercionExpressionCertificates.Direct program project caller compilation
      (Child policy body fuel compilation) (fuel + 1) source scope id callee ids instantiation
      reasonAt policy.callables node lowered)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt policy body fuel compilation values source scope id callee ids instantiation reasonAt lowered) := by
  have owner : id.occurrence.owner = source.owner := by
    apply Classical.byContradiction
    intro mismatch
    simp [SourceCoreFunctions.lowerExpressionWithPolicy, mismatch, bind, Except.bind] at accepted
  have member : (evidence.native.signature, evidence.native.index) ∈
      compilation.globals.zipIdx.filter (fun row => decide (row.1.key = evidence.selection.key)) := by
    rw [evidence.native.global]
    exact List.mem_singleton.mpr rfl
  have selected := List.mem_filter.mp member
  have key : evidence.native.signature.key = evidence.selection.key := by
    simpa only [decide_eq_true_eq] using selected.2
  have target : SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation =
      .ok evidence.native.signature.key := by
    rw [evidence.selection.targetSelected]
    exact congrArg Except.ok (evidence.selection.key_eq.symm.trans key.symm)
  have record : SourceCompilationPlan.exactSpecialization compilation.plan evidence.native.signature.key =
      .ok evidence.selection.specialized := by
    rw [key]
    exact evidence.selection.selected
  have unchanged : evidence.operand = lowered := by
    have suffix := evidence.suffix.accepted
    simpa only [coercions, SourceCoreEvidence.applyCoercions, pure, Except.pure, Except.ok.injEq] using suffix
  have emitted := unchanged.symm.trans evidence.native.emitted
  refine ⟨⟨node, ⟨evidence.found, owner, coercions, projected⟩, evidence.form, supported, accepted,
    evidence.native.signature, evidence.native.index, evidence.selection.specialized, target,
    List.mk_mem_zipIdx_iff_getElem?.mp selected.1, record, evidence.arity,
    evidence.loweredArguments, ?_, evidence.native.inputType, ?_, ?_⟩⟩
  · simpa only [Child, Nat.min_eq_right (Nat.le_succ fuel)] using evidence.argumentsAccepted
  · exact (congrArg SourceCoreBasic.LoweredExpr.type emitted).symm
  · exact congrArg SourceCoreBasic.LoweredExpr.expression emitted

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

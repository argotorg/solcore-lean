import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.Staging.Erasure
import Solcore.SourceSemantics.Staging.Internal.TraceSize
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.TerminalStatementOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.WellFormed

/-!
# Staged bounds: terminal bodies

Bodies with one terminal statement: typing, meaning and trace bounds, with the direct-call authority, closure invocation bounds and lambda formation heads they use.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallCertificates
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping
/-! Successful staged arguments retain their original raw Source typing at
the reached heap. Each actual value child uses its ordinary value projection;
the same heap extension then admits the selected closure and its captures.
No statement or application meaning is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {program : Program} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {ids : List ExpressionId} {types : List TypeSystem.Ty} {values : List Dynamic.Value}

/-- Actual successful children retain both ordered types and the independent
Source heap extension. No stage failure is projected to a semantic fault. -/
theorem values_at (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heap : Dynamic.HeapWellTyped context before)
    (typing : ExpressionsHaveTypes invocation.source context ids types) {size : Nat}
    (trace : Staging.Recursive.Size.Expressions program stages size invocation context
      environment before ids (.values values) after) :
    Dynamic.ValuesHaveTypes context after values types ∧
      Dynamic.HeapWellTyped context after ∧ Dynamic.HeapTypesExtend before after := by
  induction ids generalizing types before after size values with
  | nil =>
      cases trace
      cases typing
      exact ⟨.nil, heap, .refl before⟩
  | cons id ids ih =>
      cases typing with
      | cons headTyping tailTyping =>
          cases trace with
          | cons head tail =>
              have first := wellFormed.wholeLanguagePreservation.expression
                context invocation.evidence invocation.source environment _ _ _ _ _
                runtime covers locals heap headTyping head.sound.value_plain
              obtain ⟨rest, finalHeap, extension⟩ :=
                ih (locals.mono first.heap_extends) first.heap_typed tailTyping tail
              exact ⟨.cons (first.value_typed.mono extension) rest,
                finalHeap, first.heap_extends.trans extension⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)
  {function : Dynamic.Closure} {parameter result : TypeSystem.Ty}

/-- The successful trace and same reached admission construct raw closure
arguments and its authentic Source frame. Captures stay at that reached heap. -/
theorem closure_at (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heap : Dynamic.HeapWellTyped context before)
    (typing : ExpressionsHaveTypes invocation.source context ids types)
    (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : values.length = function.parameters.length)
    (admitted : Admission bridge context reached) {size : Nat}
    (trace : Staging.Recursive.Size.Expressions program stages size invocation context
      environment before ids (.values values) index.heap) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function index.heap values ∧
      Dynamic.ClosureFrame program function := by
  obtain ⟨argumentsTyped, _finalHeap, extension⟩ :=
    values_at wellFormed runtime covers locals heap typing trace
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack values
  obtain ⟨raw, _rows⟩ :=
    CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
      bridge reached runtime admitted calleeTyped extension argumentsTyped packing bundle arity
  obtain ⟨_parameters, _result, signatures, code, evidence, _captures⟩ := calleeTyped.closure_function_inv
  exact ⟨raw, signatures.trans runtime.signatures, code.owner, code,
    code.requirement_ledger.idsUnique, evidence⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureArgumentRows
/-! The actual selected closure and accepted physical row determine the two
ordered argument vectors independently. Raw Source typing follows the executed
successful argument trace at its reached heap. The positive contextual payload
retains the real closure Code; native bundle equality supplies no Source count.
No body or application meaning is part of this argument producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {environment : Dynamic.Environment}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {function : Dynamic.Closure} {carrier : Value} {parameter result : TypeSystem.Ty}
  {sourceTypes : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
  {calleeHeap : Dynamic.Heap} {index : ProtectedStateTransition.Index}
  (reached : callerProtocol.State index)
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
    site site.call ids (.closure function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar site callee ids originalMetadata originalNode dispatch.row)
  (count : dispatch.row.entry.parameterCount = ids.length)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include dispatch selected count in
/-- Original binding, actual Source list length and the same selected second
row fix physical closure arity before either packed type is used. -/
theorem source_arity {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment calleeHeap ids (.values sources) index.heap) :
    sources.length = function.parameters.length := by
  have retained := CallableIndexedOwnedStoredIndirectCallBounds.selected_contract dispatch selected
  have physical : dispatch.row.entry.parameterCount = function.parameters.length := by
    cases dispatch.bound with
    | closure parameters _ =>
      exact (selected.parameter_count retained).trans (congrArg List.length parameters)
  exact trace.sound.length.symm.trans (count.symm.trans physical)

include bridge profile compiler reached dispatch selected count in
/-- At the actual successful argument endpoint, the original Source trace
constructs raw closure admission and its frame. The same positive payload then
constructs the retained contextual member and exact native binder arguments. -/
theorem at_arguments
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
    (heap : Dynamic.HeapWellTyped context calleeHeap)
    (typing : ExpressionsHaveTypes invocation.source context ids sourceTypes)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (admitted : Admission bridge context reached)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (calleeRelated : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry semanticFaults profile index.mapping index.world
      (.function parameter result) (.closure function) carrier compiler.calleeCode.type)
    (represented : DataExpressionSequence.Values model index.mapping index.world
      sourceTypes (compiler.codes.map (·.type)) sources values)
    {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment calleeHeap ids (.values sources) index.heap) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function index.heap sources ∧
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function ∧
    ∃ bindings parameterCore resultCore,
      CallableIndexedOwnedContextualTypedClosureReceipts.StaticMember headers keys bodyRegistry semanticFaults
        index.mapping index.world function carrier bindings parameterCore resultCore ∧
      compiler.parameterType = parameterCore ∧ compiler.resultType = resultCore ∧
      CallableIndexedParameterMeaning.Arguments model index.mapping index.world bindings sources values := by
  have arity := source_arity dispatch selected count trace
  obtain ⟨raw, valid⟩ := CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping.closure_at
    bridge reached wellFormed runtime covers locals heap typing calleeTyped bundle arity admitted trace
  obtain ⟨bindings, parameterCore, resultCore, member, nativeType⟩ :=
    CallableIndexedOwnedContextualCellOrigins.PayloadOrigins.closure_member profile calleeRelated function rfl
  have sameTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    ((actualFunctionType ▸ compiler.callableType).trans nativeType)
  have nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
      (compiler.packedType.symm.trans (sameTypes.1.trans (member.parameter_core profile)))
  obtain ⟨parameters, _result, _signatures, _code, _evidence, _captures⟩ := calleeTyped.closure_function_inv
  have sourceBundle : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) := by
    rw [member.source_binders]
    exact bundle.trans parameters
  have bindingArity : sources.length = bindings.length := by
    have retainedBinders : bindings.length = function.parameters.length := by
      simpa only [List.length_map] using congrArg List.length member.source_binders
    exact arity.trans retainedBinders.symm
  exact ⟨raw, valid, bindings, parameterCore, resultCore, member, sameTypes.1, sameTypes.2,
    CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles bindings represented
      bindingArity sourceBundle nativeBundle⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureArgumentRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTyping
/-! Original body typing selects the retained terminal expression and its
declared result type. This uses Source statement rules and full occurrence
identity, independently of erased native types or an execution outcome. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTyping
open Frontend SourceInference
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head)

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (same : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj
    ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))
  cases nodeEq
  exact same

private theorem returning_child {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt (some expression))
    (typed : StatementHasType source control context id final facts) :
    ExpressionHasType source context expression control.returnType := by
  have shape := statement_shape unique contains form
  clear contains form
  cases typed <;> have actualForm := shape _ (by assumption) <;> simp_all

private theorem tail_child {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression false)
    (typed : StatementHasType source control context id final facts) :
    ∃ type, ExpressionHasType source context expression type ∧
      facts = { type, hasValue := true, sawReturn := false, control := .ordinary type } := by
  have shape := statement_shape unique contains form
  clear contains form
  cases typed <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, by assumption, rfl, rfl⟩

/-- The supported terminal form and complete original body typing determine
its used expression type and actual lookup occurrence. -/
theorem child_typed {invocation : Staging.Recursive.Scope}
    {context final : SourceSemantics.Context} {expression : ExpressionId}
    {statements : List StatementId} {expected : TypeSystem.Ty} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : Head invocation expression statements)
    (typed : StatementsHaveType invocation.source { returnType := expected }
      context statements final facts)
    (completes : BodyCompletes expected facts) :
    ∃ node, invocation.source.lookupExpression? expression = some node ∧
      node.type = expected ∧ ExpressionHasType invocation.source context expression node.type := by
  have expressionTyped : ExpressionHasType invocation.source context expression expected := by
    cases head with
    | returning rest contains form =>
      cases typed with
      | singleton first => exact returning_child unique contains form first
      | cons first _tail => exact returning_child unique contains form first
    | tail contains form =>
      cases typed with
      | singleton first =>
        obtain ⟨type, child, sameFacts⟩ := tail_child unique contains form first
        rw [sameFacts] at completes
        have sameType : type = expected := by
          simpa [BodyCompletes, BodyFacts.singleton, ControlSummary.ordinary] using completes
        exact sameType ▸ child
  obtain ⟨node, contains, sameType⟩ := expressionTyped.stored_type
  exact ⟨node, lookupExpression?_complete unique contains, sameType, sameType ▸ expressionTyped⟩

/-- The real original lambda frame supplies complete body typing at the
actual parameter context before selecting the terminal child. -/
theorem at_parameters {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {invocation : Staging.Recursive.Scope} {expression : ExpressionId}
    (frame : Dynamic.ClosureFrame program function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (source : invocation.source = function.source)
    (head : Head invocation expression function.body) :
    ∃ node, invocation.source.lookupExpression? expression = some node ∧
      node.type = function.resultType ∧ ExpressionHasType invocation.source context expression node.type := by
  obtain ⟨final, facts, typed, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame extended
  have unique : NodeOccurrencesUnique invocation.source := by
    rw [source]
    exact frame.code.graph.nodeOccurrencesUnique
  rw [← source] at typed
  exact child_typed unique head typed completes

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion
/-! A supported terminal Head selects the actual expression child of a
staged Source statement trace. The real Source grade and both failure tags
are retained before applying the strict expression induction hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion
open Frontend SourceInference
open Staging.Recursive
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control)

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (same : node.form = form) :
    ∀ {other}, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj
    ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))
  cases nodeEq
  exact same

/-- Neither a completed body law nor a separate child trace is an input.
The literal Source constructor selects its one used child. -/
theorem child_of_body {program : Program} {registry : Registry} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {expression : ExpressionId} {statements : List StatementId}
    {size : Nat} {bodyOutcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : Head invocation expression statements)
    (trace : Size.Statements program registry size invocation context environment before
      statements finalContext bodyOutcome after) :
    ∃ childSize outcome,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ bodyOutcome = control outcome ∧
      Size.Expression program registry childSize invocation context environment before
        expression outcome after := by
  cases head with
  | returning rest contains form =>
    have shape := @statement_shape _ _ _ _ unique contains form
    cases trace with
    | breaking actual form | continuing actual form
    | blockBreaking actual form _ | blockContinuing actual form _
    | matchBreaking actual form _ | matchContinuing actual form _
    | ifBreaking actual form _ _ | ifContinuing actual form _ _
    | forInitializerFault actual form _ | forReturned actual form _ _ | forFault actual form _ _
    | forFallthrough actual form _ _ _
    | matchReturned actual form _ | matchFault actual form _ | matchFallthrough actual form _ _
    | blockReturned actual form _ | blockFault actual form _ | blockFallthrough actual form _ _
    | whileReturned actual form _ | whileFault actual form _ | whileFallthrough actual form _ _
    | ifConditionFault actual form _ | ifReturned actual form _ _ | ifFault actual form _ _
    | ifFallthrough actual form _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnUnit actual form =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnValue actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
      exact ⟨_, _, rfl, rfl, rfl, child⟩
    | returnFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
      exact ⟨_, _, rfl, rfl, rfl, child⟩
    | tail actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | discard actual form child next =>
      have same := shape actual
      rw [form] at same
      cases same
    | expressionFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | letGeneralized actual form _ _ _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | letUninitialized actual form mono extension allocated next =>
      have same := shape actual
      rw [form] at same
      cases same
    | letInitialized actual form child mono extension allocated next =>
      have same := shape actual
      rw [form] at same
      cases same
    | letFault actual form mono child =>
      have same := shape actual
      rw [form] at same
      cases same
    | bitNotProjected actual form _ _ _ _ _
    | bitNotProjectedRootFault actual form _ _
    | bitNotProjectedKeysFault actual form _ _ _
    | bitNotProjectedGetterFault actual form _ _ _
    | bitNotBare actual form _ _ _ | bitNotBareFault actual form _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignProjected actual form _ _ _ _ _ _
    | assignProjectedRootFault actual form _ _
    | assignProjectedKeysFault actual form _ _ _
    | assignProjectedGetterFault actual form _ _ _
    | assignProjectedRhsFault actual form _ _ _ _
    | assignProjectedWriteFault actual form _ _ _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBare actual form snapshot child write next =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareOperands actual form _ _ _ _ _ _ _ | assignBareFault actual form _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareUnbound actual form bare missing =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareDangling actual form bare lookup missing =>
      have same := shape actual
      rw [form] at same
      cases same
  | tail contains form =>
    have shape := @statement_shape _ _ _ _ unique contains form
    cases trace with
    | breaking actual form | continuing actual form
    | blockBreaking actual form _ | blockContinuing actual form _
    | matchBreaking actual form _ | matchContinuing actual form _
    | ifBreaking actual form _ _ | ifContinuing actual form _ _
    | forInitializerFault actual form _ | forReturned actual form _ _ | forFault actual form _ _
    | forFallthrough actual form _ _ _
    | matchReturned actual form _ | matchFault actual form _ | matchFallthrough actual form _ _
    | blockReturned actual form _ | blockFault actual form _ | blockFallthrough actual form _ _
    | whileReturned actual form _ | whileFault actual form _ | whileFallthrough actual form _ _
    | ifConditionFault actual form _ | ifReturned actual form _ _ | ifFault actual form _ _
    | ifFallthrough actual form _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnUnit actual form =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnValue actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | tail actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
      exact ⟨_, _, rfl, rfl, rfl, child⟩
    | discard actual form child next =>
      have same := shape actual
      rw [form] at same
      cases same
    | expressionFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
      exact ⟨_, _, rfl, rfl, rfl, child⟩
    | letGeneralized actual form _ _ _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | letUninitialized actual form mono extension allocated next =>
      have same := shape actual
      rw [form] at same
      cases same
    | letInitialized actual form child mono extension allocated next =>
      have same := shape actual
      rw [form] at same
      cases same
    | letFault actual form mono child =>
      have same := shape actual
      rw [form] at same
      cases same
    | bitNotProjected actual form _ _ _ _ _
    | bitNotProjectedRootFault actual form _ _
    | bitNotProjectedKeysFault actual form _ _ _
    | bitNotProjectedGetterFault actual form _ _ _
    | bitNotBare actual form _ _ _ | bitNotBareFault actual form _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignProjected actual form _ _ _ _ _ _
    | assignProjectedRootFault actual form _ _
    | assignProjectedKeysFault actual form _ _ _
    | assignProjectedGetterFault actual form _ _ _
    | assignProjectedRhsFault actual form _ _ _ _
    | assignProjectedWriteFault actual form _ _ _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBare actual form snapshot child write next =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareOperands actual form _ _ _ _ _ _ _ | assignBareFault actual form _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareUnbound actual form bare missing =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareDangling actual form bare lookup missing =>
      have same := shape actual
      rw [form] at same
      cases same

/-- A terminal body propagates the exact Source expression outcome. -/
theorem result_of_control {type : TypeSystem.Ty} {child result : Outcome}
    (matched : BodyResult type (control child) result) : result = child := by
  cases child <;> cases matched <;> rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyMeaning
/-! Actual accepted terminal compilation supplies its used expression and
footer. The original SourceView supplies the terminal occurrence. Strict
expression hypotheses then establish meaning for that exact emitted body,
including nested stage failures and the reached caller state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control)
universe u

def fallback (type : Ty) (fellThrough : Word) : Expr :=
  if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)

variable {policy : SourceCoreLoops.Policy} {fuel : Nat} {compilerSource : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
  {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}

/-- Substitution changes statement types, while preserving the original
terminal occurrence and expression identifier. -/
theorem source_head
    (receipt : Receipt policy fuel compilerSource scope expression statements result reasonAt fellThrough escaped code)
    {invocation : Staging.Recursive.Scope} (view : SourceView invocation.source compilerSource) :
    CallableIndexedOwnedAdmittedStagedTerminalStatements.Head invocation expression statements := by
  cases receipt.terminal with
  | returning rest found form =>
    exact CallableIndexedOwnedPreparedTerminalStatementOrigins.returning_head view rest found form
  | tail found form =>
    exact CallableIndexedOwnedPreparedTerminalStatementOrigins.tail_head view found form

/-- The actual used child type and footer determine the exact renamed body. -/
theorem emitted
    (receipt : Receipt policy fuel compilerSource scope expression statements result reasonAt fellThrough escaped code)
    (ξ : Renaming) :
    code.rename ξ = CallableIndexedOwnedAdmittedStagedTerminalBody.code receipt.child.type
      ((LocalLoop.returnValue receipt.child.type receipt.child.expression).rename ξ)
      escaped ((fallback receipt.child.type fellThrough).rename ξ) := by
  have footer := congrArg (fun generated : Expr => generated.rename ξ) receipt.emitted
  exact footer.trans (by
    simpa only [receipt.sameType, CompatibleStatements.finish,
      CallableIndexedOwnedAdmittedStagedTerminalBody.code, fallback] using
      (CallableIndexedOwnedAdmittedStagedTerminalBody.code_rename result
        (LocalLoop.returnValue result receipt.child.expression) escaped (fallback result fellThrough) ξ))

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (receipt : Receipt policy fuel compilerSource scope expression statements result reasonAt fellThrough escaped code)
  (view : SourceView invocation.source compilerSource)
  (certifies : ∀ child, policy.lowerExpression receipt.childFuel compilerSource scope expression reasonAt = .ok child →
    certificate scope expression child)
  {node : ExpressionNode}
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include view certifies found sourceTyped environments heaps locals agrees typed admitted in
/-- Preservation uses the actual accepted compiler child once. No body law
or independent terminal Head is supplied. -/
theorem preserves (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    Staging.Recursive.BodyResult node.type (control outcome) outcome ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type receipt.child.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  rw [emitted receipt ξ]
  exact CallableIndexedOwnedAdmittedStagedTerminalBody.preserves bridge (source_head receipt view)
    (certifies _ receipt.generated) found sourceTyped environments heaps locals agrees typed initial admitted
    budget children escaped ((fallback receipt.child.type fellThrough).rename ξ) child within

include view certifies found sourceTyped environments heaps locals agrees typed admitted in
/-- Reflection starts from the literal emitted body, obtains a strict native
child and reconstructs an independently measured original Source body. -/
theorem reflects (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment
        before statements context (control outcome) after ∧
      Staging.Recursive.BodyResult node.type (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type receipt.child.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  rw [emitted receipt ξ] at completed
  exact CallableIndexedOwnedAdmittedStagedTerminalBody.reflects bridge (source_head receipt view)
    (certifies _ receipt.generated) found sourceTyped environments heaps locals agrees typed initial admitted
    budget children escaped ((fallback receipt.child.type fellThrough).rename ξ) completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds
/-! Actual lambda metadata views preserve terminal statements literally.
Complete original body typing determines the used child and declared result;
strict expression hypotheses then construct both body directions at the same
reached parameter state. No execution law is part of the static input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control)
universe u

variable {policy : SourceCoreLoops.Policy} {fuel : Nat} {compilerSource : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
  {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
  (receipt : Receipt policy fuel compilerSource scope expression statements result reasonAt fellThrough escaped code)
  {invocation : Staging.Recursive.Scope}
  (view : LambdaMetadataViews.MetadataView invocation.source compilerSource)

include receipt view in
/-- The genuine metadata relation retains each complete statement node.
It does not identify arbitrary expression output types or coercion paths. -/
theorem source_head : Head invocation expression statements := by
  cases receipt.terminal with
  | returning rest found form =>
    exact .returning rest (lookupStatement?_sound (view.statement found)) form
  | tail found form =>
    exact .tail (lookupStatement?_sound (view.statement found)) form

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context staticFinal : SourceSemantics.Context} {expected : TypeSystem.Ty} {facts : BodyFacts}
  {registry : Staging.Recursive.Registry}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (bodyTyped : StatementsHaveType invocation.source { returnType := expected }
    context statements staticFinal facts)
  (complete : BodyCompletes expected facts)
  (certifies : ∀ child, policy.lowerExpression receipt.childFuel compilerSource scope expression reasonAt = .ok child →
    certificate scope expression child)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include view bodyTyped complete certifies environments heaps locals agrees typed admitted in
/-- Original whole-body trace, complete Source typing and the literal receipt
construct the used strict expression step and full body post internally. -/
theorem preserves_body (unique : NodeOccurrencesUnique invocation.source) (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements program registry size invocation context environment
      before statements finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult expected bodyOutcome outcome)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected result faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected outcome reached := by
  have head := source_head receipt view
  obtain ⟨node, found, sameType, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head bodyTyped complete
  obtain ⟨childSize, childOutcome, sameSize, _sameContext, sameBody, child⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body unique head trace
  have sameOutcome : outcome = childOutcome :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.result_of_control (sameBody ▸ matched)
  subst outcome
  rw [CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.emitted receipt ξ]
  obtain ⟨_sourceTrace, _sourceResult, meaning⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.preserves bridge head
      (certifies _ receipt.generated) found sourceTyped environments heaps locals agrees typed initial admitted
      budget children escaped
      ((CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback receipt.child.type fellThrough).rename ξ)
      child (sameSize ▸ within)
  simpa only [sameType, receipt.sameType] using meaning

include view bodyTyped complete certifies environments heaps locals agrees typed admitted in
/-- The literal emitted body exposes a strict native child. Its reflection
constructs a separately graded original body and the same reached full post. -/
theorem reflects_body (unique : NodeOccurrencesUnique invocation.source) (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment
        before statements context (control outcome) after ∧
      Staging.Recursive.BodyResult expected (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected result faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected outcome reached := by
  have head := source_head receipt view
  obtain ⟨node, found, sameType, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head bodyTyped complete
  rw [CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.emitted receipt ξ] at completed
  have meaning := CallableIndexedOwnedAdmittedStagedTerminalBody.reflects bridge head
    (certifies _ receipt.generated) found sourceTyped environments heaps locals agrees typed initial admitted
    budget children escaped
    ((CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback receipt.child.type fellThrough).rename ξ)
    completed within
  simpa only [sameType, receipt.sameType] using meaning

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds
/-! A staged user closure invokes its actual retained Code. The original
parameter installation and saved-caller restoration are independent of the
body outcome, so a nested stage failure keeps its Scope/call/tag. A strict
body hypothesis is used only at the real selected parameter entry. Its full
post returns through the saved physical caller; context support follows from
the genuine closure frame and caller runtime validity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open Staging.Recursive

private theorem binders_context_eq {owner : Resolved.DeclarationId}
    {before left right : SourceSemantics.Context} {parameters : List TypedBinder}
    {leftTypes rightTypes : List TypeSystem.Ty}
    (first : MonoBindersExtend owner before parameters leftTypes left)
    (second : MonoBindersExtend owner before parameters rightTypes right) : left = right := by
  have same := first.bodyTypes_eq.symm.trans second.bodyTypes_eq
  subst rightTypes
  exact first.functional second

/-- The Source application itself selects the genuine staged child Scope and
allocation. Physical arity excludes only the real closureArity alternative. -/
private theorem source_body {program : Program} {stages : Registry}
    {invocation : Scope} {function : Dynamic.Closure} {callContext bodyContext : SourceSemantics.Context}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {parameterTypes : List TypeSystem.Ty}
    {size : Nat} {outcome : Outcome}
    (parameters : MonoBindersExtend function.source.owner function.context
      function.parameters parameterTypes bodyContext)
    (arity : function.parameters.length = arguments.length)
    (trace : Size.Applies program stages size invocation callContext before
      (.closure function) arguments outcome after) :
    ∃ childSize child entry copied environment bound finalContext bodyOutcome,
      stages.Closure function child ∧ Dynamic.ClosureFrame program function ∧
      Dynamic.EnvironmentCopies function.source function.captured before entry copied ∧
      Dynamic.BindersAllocate entry copied function.parameters arguments environment bound ∧
      Size.Statements program stages childSize child bodyContext environment bound function.body
        finalContext bodyOutcome after ∧ BodyResult function.resultType bodyOutcome outcome ∧ childSize < size := by
  cases trace with
  | closureArity mismatch => exact False.elim (mismatch arity)
  | closure selected valid extended copy allocated body resultRule =>
      have same := binders_context_eq extended parameters
      subst same
      exact ⟨_, _, _, _, _, _, _, _, selected, valid, copy, allocated, body, resultRule,
        Size.child_lt_stepSize (by simp)⟩

section Invocation
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {stages : Registry} {faults : RecursiveStageMeaning.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid program callerContext callerSource)
  (savedRows : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

/-- A body induction hypothesis at one authentic parameter entry. The final
continuation will construct it from the terminal compiler receipt and strict
expression IH; no body execution law is stored in a static Code receipt. -/
def SourceBodyAt
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    (bodySize : Nat) : Prop :=
  ∀ {child : Scope} {finalContext : SourceSemantics.Context} {bodyOutcome : BodyOutcome}
    {outcome : Outcome} {after : Dynamic.Heap},
    stages.Closure function child → Dynamic.ClosureFrame program function →
    Size.Statements program stages bodySize child inputs.context entry.entry.environment entry.entry.heap
      function.body finalContext bodyOutcome after → BodyResult function.resultType bodyOutcome outcome →
    ∃ value bodyStore finalMap finalWorld,
      Evaluates entry.entry.actualBody entry.entry.store
        (code.receipt.body.rename entry.entry.embedding) value bodyStore ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after bodyStore ∧
      LocationMap.Extends entry.entry.mapping finalMap ∧ WorldExtends entry.entry.world finalWorld ∧
      AdministrativePreserved entry.entry.mapping entry.entry.store finalMap bodyStore ∧
      Dynamic.HeapMetadataExtend entry.entry.heap after ∧
      ∃ bodyState : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          finalMap, finalWorld, after, bodyStore, entry.entry.canonical⟩,
        Relates reached bodyState ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge inputs.context function.resultType outcome bodyState

def ResultAt (outcome : Outcome) (after : Dynamic.Heap) (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ returned : State headers keys
      ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩,
      Relates caller returned ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
        CallableIndexedOwnedBodyRestorationAdmission.bridge callerContext function.resultType outcome returned

include represented heaps locals reference currentCarried allowed callerRuntime savedRows in
/-- The strict staged body is selected by the actual Source closure rule.
Installation, marked parameter allocation and physical caller restoration
are the original producers, each used once at the argument-post pool. -/
theorem invocation_preserves (budget : Nat)
    (bodies : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor
        (values := .initial compiled.compatible.checked) captured code history inputs functions registry
        arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost),
      ∀ reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
      ∀ childSize, childSize < budget → SourceBodyAt (stages := stages) (faults := faults)
        captured code history inputs functions owner caller entry reached childSize)
    {invocation : Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Outcome} {after : Dynamic.Heap}
    (trace : Size.Applies program stages size invocation callContext before (.closure function)
      arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates (DataPatternValues.packValues nativeArguments ::
        encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
        store (code.body.rename captured.embedding.lift.lift) value finalStore ∧
      ResultAt (registry := registry) (faults := faults) (callerContext := callerContext) captured code functions caller
        outcome after value finalStore := by
  have arity : function.parameters.length = arguments.length := by
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code,
      List.length_map]
    exact represented.length.1
  obtain ⟨childSize, child, copies, copiedHeap, environment, bound, finalContext, bodyOutcome,
    selected, valid, copy, allocated, bodyTrace, resultRule, smaller⟩ := source_body inputs.extended arity trace
  obtain ⟨entry, _added, _copied, _length, _spine, _kept, parameterState, parameterRelated⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.parameters_with_state captured code history inputs
      functions represented owner caller heaps locals reference currentCarried allowed
  obtain ⟨sameCopies, sameCopied⟩ := Dynamic.EnvironmentCopies.functional entry.entry.copy copy
  rw [← sameCopies, ← sameCopied] at allocated
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyTransition⟩ :=
    bodies entry parameterState childSize (Nat.lt_of_lt_of_le smaller within)
      selected valid bodyTrace resultRule
  obtain ⟨bodyState, bodyRelated, bodyPost⟩ := bodyTransition
  have maps := entry.entry.maps.trans bodyMaps
  have worlds := entry.entry.worlds.trans bodyWorlds
  have frame := entry.entry.frame.trans bodyFrame
  have metadata := entry.entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, callerRelated, _records, _returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position
      (CallableIndexedAmbient.frame_registered compiled.indexed) finalHeaps worlds frame related
  have bodyRuntime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters valid inputs.extended).1
  have supports := Dynamic.TypeContextSupports.ofClosed
    (callerRuntime.signatures.trans bodyRuntime.signatures.symm)
    bodyRuntime.closed callerRuntime.closed bodyRuntime.variables_closed callerRuntime.residual_variables_open
  have callerPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position savedRows bodyPost supports restoredFrame
  exact ⟨value, _, entry.wrap bodyEvaluation, finalMap, finalWorld, result,
    restoredHeaps, maps, worlds, restoredFrame, metadata,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position, callerRelated, callerPost⟩


/-- The native body IH is indexed by the actual prefix and reached pool.
Its Source grade is independent of the native child's grade. -/
def NativeBodyAt
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (child : Scope) (nativeSize : Nat) : Prop :=
  ∀ {value : Value} {bodyStore : Store},
    EvaluationSize nativeSize entry.actual entry.store
      (code.receipt.body.rename entry.embedding) value bodyStore →
    ∃ sourceSize finalContext bodyOutcome outcome after finalMap finalWorld,
      Size.Statements program stages sourceSize child inputs.context entry.environment entry.heap
        function.body finalContext bodyOutcome after ∧ BodyResult function.resultType bodyOutcome outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after bodyStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap bodyStore ∧
      Dynamic.HeapMetadataExtend entry.heap after ∧
      ∃ bodyState : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          finalMap, finalWorld, after, bodyStore, entry.canonical⟩,
        Relates reached bodyState ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          CallableIndexedOwnedBodyRestorationAdmission.bridge inputs.context function.resultType outcome bodyState

include represented heaps locals reference currentCarried allowed callerRuntime savedRows in
/-- The original completion selects its strict native body child. The body
IH reconstructs an independently graded staged Source body, then the literal
closure rule and physical saved-caller restoration run once. -/
theorem invocation_reflects (child : Scope) (selected : stages.Closure function child)
    (valid : Dynamic.ClosureFrame program function) (budget : Nat)
    (bodies : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor
        (values := .initial compiled.compatible.checked) captured code history inputs functions registry
        arguments before store owner.key.frameLocation (caller.rows owner.position).authority.current),
      ∀ reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
      ∀ childSize, childSize < budget → NativeBodyAt (stages := stages) (faults := faults)
        captured code history inputs functions owner caller entry reached child childSize)
    {invocation : Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments ::
        encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Size.Applies program stages sourceSize invocation callContext before (.closure function)
        arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) (callerContext := callerContext) captured code functions caller
        outcome after value finalStore := by
  obtain ⟨entry, nativeChild, bodyStore, smaller, bodyCompleted, restored,
    parameterState, parameterRelated⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.body_prefix_with_state captured code history inputs
      functions represented owner caller heaps locals reference currentCarried allowed completed
  obtain ⟨sourceSize, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld,
    bodyTrace, resultRule, result, finalHeaps, bodyMaps, bodyWorlds,
    bodyFrame, bodyMetadata, bodyTransition⟩ :=
    bodies entry parameterState nativeChild (Nat.lt_of_lt_of_le smaller within) bodyCompleted
  obtain ⟨bodyState, bodyRelated, bodyPost⟩ := bodyTransition
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have metadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, callerRelated, _records, _returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position
      (CallableIndexedAmbient.frame_registered compiled.indexed) finalHeaps worlds frame related
  have bodyRuntime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters valid inputs.extended).1
  have supports := Dynamic.TypeContextSupports.ofClosed
    (callerRuntime.signatures.trans bodyRuntime.signatures.symm)
    bodyRuntime.closed callerRuntime.closed bodyRuntime.variables_closed callerRuntime.residual_variables_open
  have callerPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position savedRows bodyPost supports restoredFrame
  subst finalStore
  exact ⟨_, outcome, after, .closure selected valid inputs.extended entry.copy entry.allocation bodyTrace resultRule,
    finalMap, finalWorld, result, restoredHeaps, maps, worlds, restoredFrame, metadata,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position, callerRelated, callerPost⟩


include represented heaps locals reference currentCarried allowed callerRuntime savedRows in
/-- Applying the actual retained closure payload preserves the full staged
result. Its one native apply edge encloses the real invocation producer. -/
theorem application_preserves (budget : Nat)
    (bodies : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor
        (values := .initial compiled.compatible.checked) captured code history inputs functions registry
        arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost),
      ∀ reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
      ∀ childSize, childSize < budget → SourceBodyAt (stages := stages) (faults := faults)
        captured code history inputs functions owner caller entry reached childSize)
    {invocation : Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Outcome} {after : Dynamic.Heap}
    (trace : Size.Applies program stages size invocation callContext before (.closure function)
      arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) (callerContext := callerContext) captured code functions caller
        outcome after value finalStore := by
  obtain ⟨value, finalStore, evaluated, result⟩ :=
    invocation_preserves captured code history inputs functions represented owner caller heaps locals
      reference currentCarried allowed callerRuntime savedRows budget bodies trace within
  exact ⟨value, finalStore, .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result⟩

include represented heaps locals reference currentCarried allowed callerRuntime savedRows in
/-- The literal payload apply exposes a strict native invocation child.
Its Source closure application is reconstructed with an independent grade. -/
theorem application_reflects (child : Scope) (selected : stages.Closure function child)
    (valid : Dynamic.ClosureFrame program function) (budget : Nat)
    (bodies : ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor
        (values := .initial compiled.compatible.checked) captured code history inputs functions registry
        arguments before store owner.key.frameLocation (caller.rows owner.position).authority.current),
      ∀ reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
      ∀ childSize, childSize < budget → NativeBodyAt (stages := stages) (faults := faults)
        captured code history inputs functions owner caller entry reached child childSize)
    {invocation : Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Size.Applies program stages sourceSize invocation callContext before (.closure function)
        arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) (callerContext := callerContext) captured code functions caller
        outcome after value finalStore := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact invocation_reflects captured code history inputs functions represented owner caller heaps locals
    reference currentCarried allowed callerRuntime savedRows child selected valid budget bodies applied
    (Nat.le_trans (Nat.le_of_lt smaller) within)

end Invocation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds
/-! The original prepared named Header supplies the accepted terminal compiler
receipt. Independent Source program typing determines the used terminal child
at the Header's real parameter context. Strict expression hypotheses establish
both staged body directions at the same actual reached parameter state,
retaining nested stage failures and the full pool post. Native parameter entry
and caller restoration remain separate producers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt Terminal)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {expression : ExpressionId}

include aligned in
/-- The actual original body callback, its read policy and terminal Source
occurrence construct this receipt; a second body compilation is not assumed. -/
theorem compiler_receipt
    (terminal : Terminal header.function.source expression header.function.body) :
    Nonempty (Receipt header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body) :=
  CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) terminal aligned.accepted

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure header.function child)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (certifies : ∀ lowered,
    header.policy.lowerExpression terminal.childFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
    certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before header.context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State
    ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge header.context initial)

include selected wellFormed terminal certifies environments heaps locals agrees typed admitted in
/-- The original named body Source typing and genuine selected child scope
construct preservation from the used strict expression hypothesis. The body
trace and nested failure scope remain recursively staged. -/
theorem preserves_body (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge header.context model stages child certificate faults budget)
    {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages size child
      header.context environment before header.function.body finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult header.function.resultType bodyOutcome outcome)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (header.body.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge header.context header.function.resultType outcome reached := by
  have view : LambdaMetadataViews.MetadataView child.source header.function.source := by
    rw [stages.source selected]
    exact .refl _
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨staticFinal, facts, bodyTyped, complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  rw [← stages.source selected] at bodyTyped
  exact CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.preserves_body
    (receipt := terminal) (view := view) (bridge := bridge) (bodyTyped := bodyTyped) (complete := complete)
    (certifies := certifies) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    unique budget children trace matched within

include selected wellFormed terminal certifies environments heaps locals agrees typed admitted in
/-- Literal native body completion reflects to an independently graded staged
Source body, using the same accepted Header code and actual parameter state.
The complete returned pool and successful Source post are retained. -/
theorem reflects_body (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge header.context model stages child certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (header.body.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize child
        header.context environment before header.function.body header.context
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome) after ∧
      Staging.Recursive.BodyResult header.function.resultType
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge header.context header.function.resultType outcome reached := by
  have view : LambdaMetadataViews.MetadataView child.source header.function.source := by
    rw [stages.source selected]
    exact .refl _
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨staticFinal, facts, bodyTyped, complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  rw [← stages.source selected] at bodyTyped
  exact CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.reflects_body
    (receipt := terminal) (view := view) (bridge := bridge) (bodyTyped := bodyTyped) (complete := complete)
    (certifies := certifies) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    unique budget children completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
/-! Static direct-call authority is recovered from the exact compiler action
and actual finite inventory. Complete signatures identify physical slots;
accepted specialization records and full metadata identify Source functions.
No runtime global slot, capture, execution or body law is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

/-- A caller's exact executable resolver result and complete semantic dictionary.
This receipt does not require an ordinary Source declaration or Header. -/
structure ResolvedCaller (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction)
    (evidence : Dynamic.EvidenceEnvironment) where
  available : SourceTypedRuntime.RuntimeEvidenceEnvironment
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available
  dictionary : evidence = CallableNamedMetadata.environment available

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {program : Program}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id callee ids
    instantiation reasonAt lowered)

structure Ready (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled program)) where
  header : CallableIndexedOwnedFunctionValues.Header compiled program
  member : header ∈ catalog
  slot : header.slot = receipt.index
  signature : header.named.signature = receipt.signature
  specialized : header.named.specialized = receipt.specialized
  metadata : instantiation = header.instantiation

/-- The actual matching record and each authentic Header retain the Source
inference order. Their complete metadata then agrees, including nonempty
substitutions; declaration keys alone do not determine this equality. -/
theorem of_slot
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    (covered : ∃ header ∈ catalog,
      header.slot = receipt.index ∧ header.named.signature = receipt.signature)
    (plan : compilation.plan = compiled.indexed.base.plan)
    (ordered : ∀ header, header ∈ catalog →
      header.instantiation.parameterSubstitution.map Prod.fst =
        (header.named.specialized.parameterSubstitution.map Prod.fst).reverse) :
    Nonempty (Ready receipt catalog) := by
  obtain ⟨header, member, slot, signature⟩ := covered
  have record := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  rw [signature, ← plan] at record
  have specialized : header.named.specialized = receipt.specialized :=
    Except.ok.inj (record.symm.trans receipt.record)
  have occurrence := CallableNamedMetadata.matches_of_exact
    receipt.target receipt.record
  have headerTarget := header.target
  rw [signature, ← plan] at headerTarget
  have headerMatch := CallableNamedMetadata.matches_of_exact headerTarget receipt.record
  have occurrenceEq := occurrence.retained_canonical
    (receipt.supported.ordered _ _ receipt.target receipt.record)
  have headerEq := headerMatch.retained_canonical (by
    simpa only [← specialized] using ordered header member)
  exact ⟨⟨header, member, slot, signature, specialized, occurrenceEq.trans headerEq.symm⟩⟩

theorem of_complete
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) catalog)
    (plan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    (ordered : ∀ header, header ∈ catalog →
      header.instantiation.parameterSubstitution.map Prod.fst =
        (header.named.specialized.parameterSubstitution.map Prod.fst).reverse) :
    Nonempty (Ready receipt catalog) := by
  have selected := receipt.global
  rw [globals] at selected
  exact of_slot receipt (complete receipt.index receipt.signature selected) plan ordered

/-- Independently typed declaration application fixes the original parameter
row and return type of the selected Header. Native packed types are unused. -/
theorem Ready.source_types
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    (ready : Ready receipt catalog) {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty}
    (wellFormed : ProgramWellFormed program)
    (signatures : context.signatures = program.signatures)
    (application : DeclarationApplicationValid context instantiation types
      receipt.node.type instantiation.predicates) :
    types = ready.header.bindings.map (fun binding => binding.1.scheme.body) ∧
      receipt.node.type = ready.header.function.resultType := by
  cases application with
  | intro member admissible declaration parameters result functionType predicates =>
    have shape := RecursiveNamedSourceSignatureFacts.header_shape ready.header wellFormed
      (signatures ▸ member) (by rw [← ready.metadata]; exact declaration)
    rw [← ready.metadata] at shape
    exact ⟨parameters.symm.trans shape.1, result.symm.trans shape.2⟩

/-- A selected finite row retains its authentic preparation, reissued diagnostic
Header and complete Source dictionary. Runtime capture/slot authority remains
separate and must come from the actual caller packet. -/
structure Port (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram))) extends Ready receipt catalog where
  row : SourceSpecialization.SpecializedFunction
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation toReady.header
  rawDictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  function : Dynamic.GlobalFunction
  sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt toReady.header rawDictionary function
  sourceInstantiation : function.instantiation = instantiation
  dictionary : function.evidence = prepared.view.evidence

/-- The real retained Inventory supplies all preparation and Source provenance.
No new public execution premise or unrelated native run is needed. -/
theorem of_inventory_at {inputs : List (Input compiled)} (rows : Inventory inputs)
    (covered : ∃ header ∈ headers rows,
      header.slot = receipt.index ∧ header.named.signature = receipt.signature)
    (plan : compilation.plan = compiled.indexed.base.plan) :
    Nonempty (Port receipt (headers rows)) := by
  obtain ⟨ready⟩ := of_slot receipt covered plan
    (CallableIndexedOwnedPreparedFiniteNamedInventories.ordered rows)
  obtain ⟨input, packet, _retained, same⟩ := rows.mem_headers ready.header ready.member
  have aligned := packet.aligned
  have metadata : (CallableNamedCanonicalOrder.retainedInstantiation input.row) = instantiation :=
    aligned.metadata.symm.trans ((congrArg (·.instantiation) same).trans ready.metadata.symm)
  have aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt
      (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
      instantiation ready.header := by
    rw [← same, ← metadata]
    exact aligned
  have sourceAt := packet.sourceAt
  have sourceMetadata :
      (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized
        input.prepared.available)).instantiation = instantiation := by
    change CallableNamedCanonicalOrder.retainedInstantiation packet.header.named.specialized = instantiation
    rw [packet.aligned.named]
    change CallableNamedCanonicalOrder.retainedInstantiation input.prepared.named.specialized = instantiation
    rw [input.prepared.same]
    exact metadata
  refine ⟨{ toReady := ready
            row := input.row
            prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
            aligned := aligned
            rawDictionary := input.prepared.available
            function := CallableNamedReversal.global
              (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)
            sourceAt := same ▸ sourceAt
            sourceInstantiation := sourceMetadata
            dictionary := (same ▸ sourceAt).dictionary.symm.trans
              (congrArg Dynamic.Closure.evidence aligned.function) }⟩

theorem of_inventory {inputs : List (Input compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers rows))
    (plan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals) :
    Nonempty (Port receipt (headers rows)) := by
  have selected := receipt.global
  rw [globals] at selected
  exact of_inventory_at receipt rows (complete receipt.index receipt.signature selected) plan

/-- Full Source evidence is produced and identified at the actual caller
context. It contains no Source or native body execution premise. -/
structure EvidenceAt {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (port : Port receipt catalog) (context : SourceSemantics.Context)
    (caller : Dynamic.EvidenceEnvironment) : Prop where
  produces : Dynamic.DirectCallProducesEvidence context caller receipt.node.requirements []
    instantiation.predicates port.function.evidence
  agrees : ∀ evidence, Dynamic.DirectCallProducesEvidence context caller receipt.node.requirements []
    instantiation.predicates evidence → evidence = port.function.evidence

structure PortWithEvidence (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram)))
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment)
    extends Port receipt catalog where
  evidence : EvidenceAt receipt toPort context caller

/-- Empty predicates imply the actual prepared dictionary is empty. The full
selected metadata, issued Header and resolver establish this equality. -/
theorem ordinary_evidence
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (port : Port receipt catalog)
    (ordinary : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Ordinary compilation.plan instantiation)
    (requirements : receipt.node.requirements = [])
    (context : SourceSemantics.Context) (caller : Dynamic.EvidenceEnvironment) :
    EvidenceAt receipt port context caller := by
  have same : port.row = receipt.specialized :=
    port.prepared.same.symm.trans
      ((congrArg (fun named => named.specialized) port.aligned.named).symm.trans port.specialized)
  have metadata := CallableNamedMetadata.matches_of_exact receipt.target receipt.record
  have assumptions : port.row.assumptions = [] := by
    rw [same]
    exact metadata.predicates.trans ordinary.predicates
  have empty : port.function.evidence = [] :=
    port.dictionary.trans (RecursiveNamedPreparedHeaders.Prepared.evidence_empty port.prepared assumptions)
  constructor
  · rw [requirements, ordinary.predicates, empty]
    exact .intro (selected := []) (contextual := []) rfl rfl .nil
  · intro evidence produced
    cases produced with
    | intro _ _ produced =>
      have length := produced.length_eq.2
      rw [ordinary.predicates] at length
      exact (List.length_eq_zero_iff.mp length.symm).trans empty.symm

/-- The exact caller resolver and genuine selected callee identify the full
produced dictionary. Reached lexical fields retain the original ledger IDs. -/
theorem authenticated_evidence_of_resolved
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (port : Port receipt catalog)
    {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
    {child : SourceCoreEvidence.Child} {budget : Nat} {callables : SourceCoreFunctions.CallablePolicy}
    (actual : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
      child budget source scope id callee ids instantiation reasonAt callables receipt.node lowered)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (resolvedCaller : ResolvedCaller compiled.sourceProgram caller callerEvidence)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context) :
    EvidenceAt receipt port context callerEvidence := by
  have key : actual.selection.key = receipt.signature.key :=
    actual.selection.key_eq.trans (Except.ok.inj (actual.selection.targetSelected.symm.trans receipt.target))
  have record : SourceCompilationPlan.exactSpecialization compilation.plan receipt.signature.key =
      .ok actual.selection.specialized := by
    rw [← key]
    exact actual.selection.selected
  have same : port.row = actual.selection.specialized :=
    port.prepared.same.symm.trans
      ((congrArg (fun named => named.specialized) port.aligned.named).symm.trans
        (port.specialized.trans (Except.ok.inj (receipt.record.symm.trans record))))
  have actualKey := (CallableNamedMetadata.specialization_of_exact actual.selection.selected).2
  have calleeDictionary : actual.selection.actual = port.prepared.available := by
    apply port.prepared.authenticated_dictionary
    simpa only [same, actualKey] using actual.selection.authenticated
  have input : actual.selection.available = resolvedCaller.available :=
    Except.ok.inj (actual.selection.resolved.symm.trans resolvedCaller.resolved)
  have output : CallableNamedMetadata.environment actual.selection.actual = port.function.evidence := by
    rw [calleeDictionary, port.dictionary]
    rfl
  constructor
  · have produced := actual.selection.direct_produces signatures ledger assumptions
    simpa only [receipt.metadata.coercions, input, output, resolvedCaller.dictionary] using produced
  · intro evidence produced
    have produced : Dynamic.DirectCallProducesEvidence context
        (CallableNamedMetadata.environment actual.selection.available) receipt.node.requirements receipt.node.coercions
        instantiation.predicates evidence := by
      simpa only [receipt.metadata.coercions, input, resolvedCaller.dictionary] using produced
    exact (actual.selection.direct_agrees ledger
      (CallableCallRequirementLayouts.singletons_of_unique ledger unique) produced).trans output

/-- The ordinary prepared caller supplies the same general resolver receipt. -/
theorem authenticated_evidence
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (port : Port receipt catalog)
    {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
    {child : SourceCoreEvidence.Child} {budget : Nat} {callables : SourceCoreFunctions.CallablePolicy}
    (actual : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
      child budget source scope id callee ids instantiation reasonAt callables receipt.node lowered)
    (callerPrepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled caller)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (callerDictionary : callerEvidence = callerPrepared.view.evidence) :
    EvidenceAt receipt port context callerEvidence := by
  exact authenticated_evidence_of_resolved receipt port actual
    ⟨callerPrepared.available, callerPrepared.resolved, callerDictionary⟩
    signatures ledger assumptions unique

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaFormationHeads
/-! Ordinary lambda formation uses the actual named packet and keeps the
positive closure member of the formed closure, over the copies of its captured
cells, in the public receiving model. The retained Site and body are static
compiler receipts; captures come from this input. The reached packet is the
input packet transported to the formed state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open RecursiveNamedLambdaFormationHeads
open CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads (Formation)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry receiving : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (context : SourceSemantics.Context) {stages : Staging.Recursive.Registry}
  (invocation : Staging.Recursive.Scope)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (sameSource : invocation.source = CallableIndexedNamedGeneration.source caller.named)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "bridge" => CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller

abbrev Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
    caller context invocation.evidence scope id lowered)

private theorem no_stage
    {program : Program} {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {size : Nat}
    {parameters result body failedScope call reason}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result body)
    (coercions : node.coercions = [])
    (trace : Staging.Recursive.Size.Expression program registry size scope context environment
      before id (.fault (.stage failedScope call reason)) after) : False := by
  have actual : ∀ {shape requirements}, Staging.Recursive.Occurrence scope id shape requirements →
      shape = .lambda parameters result body := by
    intro shape requirements occurrence
    obtain ⟨actualNode, contains, sameForm, _requirements, _coercions⟩ := occurrence
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    exact sameForm.symm.trans form
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found coercions contains))
  | generalizedLocal contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | group occurrence _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _ | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _
  | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
      cases actual occurrence

include complete globals slots prefixZero in
/-- One actual formation copies the captured cells into the receiving heap and
forms the closure over the copies, with its positive static member; the input
packet is transported to the formed state. -/
private theorem forms {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : OrdinaryFormation (registry := bodyRegistry) (faults := semanticFaults)
      caller context invocation.evidence scope id lowered)
    {mapping world administrative environment canonical actual actualContext before store ξ}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (nativeTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨scope, mapping, world, before, store, canonical⟩) :
    ∃ payload copies after finalStore finalMap finalWorld,
      Dynamic.EnvironmentCopies (receipt.toFormation.function environment).source environment before copies after ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word payload) finalStore ∧
      ValueRep compiled.compatible.checked receiving functions finalMap finalWorld
        receipt.site.code.sourceNode.type (.closure { receipt.toFormation.function environment with captured := copies })
        payload lowered.type ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld
        after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
          ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        (CallableIndexedOwnedNestedCanonicalState.protocol owner caller).Relates initial reached := by
  let head := receipt.toFormation
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
    initial.property.observed initial.property.carried initial.property.bundle globals
  let captured := captures_for complete globals entry environments agrees nativeTyped
  have observed := capture_globals_for complete globals slots entry environments agrees nativeTyped
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical
      (initial.val.rows owner.position).authority.frameLocation at observed
    rw [(initial.val.rows owner.position).frame_eq] at observed
    exact observed
  let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
  let support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry semanticFaults := head.support environment
  let actualHistory : History code :=
    @CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at compiled headers keys bodyRegistry
      semanticFaults (head.function environment) scope mapping world before store actual canonical
      captured code support owner initial.val initial.property
  have origin := CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.source_origin
    (function := head.function environment) captured code support owner initial.val initial.property
  have referenceIndex := CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reference_index
    (function := head.function environment) captured code support
  obtain ⟨formed, _sourceTrace, native, related, _determined⟩ :=
    CallableIndexedOwnedGeneralLambdaValues.ordinary_lambda_of_formation (function := head.function environment)
      initial.val owner captured code actualHistory support origin rfl observed referenceIndex
      rfl profile heaps head.site.snapshots receipt.ordinary receipt.coercions
  have typed := (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry semanticFaults profile).runtime_hasType
    (registry := bodyRegistry) related
  have member : CallableIndexedOwnedContextualTypedClosureReceipts.StaticMember headers keys bodyRegistry semanticFaults
      formed.finalMap formed.finalWorld formed.closure
      (value code formed.embedding actualHistory.native formed.closureActual)
      code.receipt.loweredParameters code.receipt.parameterCore code.receipt.resultCore :=
    ⟨.ordinary (function := formed.closure) owner formed.captures formed.closureCode formed.closureHistory
      (support.recapture formed.captured) ⟨origin.metadata⟩ rfl (observed.of_slots formed.slots) referenceIndex typed
      (CallableIndexedOwnedAdmittedContextualOrdinaryLambdaFormation.provenance_recapture
        (receipt.at environment globals) formed.captured)⟩
  have payload := CallableIndexedOwnedContextualCellOrigins.payload_static_member (registry := receiving) profile member
  obtain ⟨reached, transported⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner caller)
    initial formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  refine ⟨value code formed.embedding actualHistory.native formed.closureActual, formed.captured, formed.finalHeap,
    formed.finalStore, formed.finalMap, formed.finalWorld, formed.copy, ?_, ?_, formed.heaps, formed.maps,
    formed.worlds, formed.frame, reached, transported⟩
  · simpa only [code, Formation.code, recaptureCode, head, receipt.emitted, captured, captures_for, actualHistory] using native
  have sourceType : receipt.site.code.sourceNode.type = FunctionValues.sourceType (head.function environment) := receipt.sourceType
  have nativeType := CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type
    (compiled := compiled) (function := head.function environment) captured code
  rw [sourceType]
  have emittedType : lowered.type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
    simpa only [code, Formation.code, recaptureCode, head, receipt.emitted] using nativeType
  rw [emittedType]
  exact payload

variable (unique : NodeOccurrencesUnique invocation.source)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (faults : RecursiveStageMeaning.FaultRep)

include complete globals slots prefixZero sameSource unique wellFormed runtime covers in
theorem preserves (size : Nat) :
    PreservesAt bridge context model stages invocation
      (Certificate (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) caller context invocation) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  obtain ⟨receipt⟩ := certified
  let head := receipt.toFormation
  let code := head.code environment
  have sourceFound : invocation.source.lookupExpression? id = some receipt.site.code.sourceNode := by
    simpa only [sameSource, receipt.identifier, CallableIndexedLambdaGeneration.closure] using receipt.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  have changed : ∃ copies, outcome = .value (.closure { head.function environment with captured := copies }) ∧
      Dynamic.EnvironmentCopies (head.function environment).source environment before copies after := by
    cases outcome with
    | value value =>
      have evaluated : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
          (head.function environment).context (head.function environment).evidence
          (head.function environment).source environment before code.id value after := by
        simpa only [sameSource, code, head, Formation.code, Formation.function,
          CallableIndexedLambdaGeneration.closure, recaptureCode, receipt.identifier] using trace.sound.value_plain
      obtain ⟨copies, rfl, copy⟩ := source_value_of_code (values := .initial compiled.compatible.checked) code
        (by simpa only [head, Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using unique)
        receipt.coercions evaluated
      exact ⟨copies, rfl, copy⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        apply False.elim
        apply excludes_fault_of_code (values := .initial compiled.compatible.checked) code
          (by simpa only [head, Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource] using unique)
          receipt.coercions
        simpa only [sameSource, code, head, Formation.code, Formation.function,
          CallableIndexedLambdaGeneration.closure, recaptureCode, receipt.identifier] using trace.sound.semanticFault_plain
      | stage failedScope call reason =>
        exact False.elim (no_stage unique sourceFound receipt.site.code.sourceForm receipt.coercions trace)
  obtain ⟨copies, rfl, copy⟩ := changed
  obtain ⟨payload, formedCopies, formedHeap, finalStore, finalMap, finalWorld, formedCopy, native, represented,
      finalHeaps, maps, worlds, frame, reached, related⟩ :=
    forms caller owner context invocation profile complete globals slots prefixZero receipt environments heaps agrees
      nativeTyped initial
  obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formedCopy
  refine ⟨.inRight .word payload, finalStore, finalMap, finalWorld, native, .value represented,
    finalHeaps, maps, worlds, frame, copy.metadata_extends, reached, related, ?_⟩
  exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed trace frame

include complete globals slots prefixZero sameSource wellFormed runtime covers in
theorem reflects (size : Nat) :
    ReflectsAt bridge context model stages invocation
      (Certificate (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) caller context invocation) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  obtain ⟨receipt⟩ := certified
  have sourceFound : invocation.source.lookupExpression? id = some receipt.site.code.sourceNode := by
    simpa only [sameSource, receipt.identifier, CallableIndexedLambdaGeneration.closure] using receipt.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  obtain ⟨payload, copies, after, formedStore, finalMap, finalWorld, copy, native, represented,
      finalHeaps, maps, worlds, frame, reached, related⟩ :=
    forms caller owner context invocation profile complete globals slots prefixZero receipt environments heaps agrees
      nativeTyped initial
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic native completed.sound
  have snapshot : Dynamic.EnvironmentCopies invocation.source environment before copies after := by
    rw [sameSource]
    exact copy
  have sourceTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize []) invocation context environment before id
      (.value (.closure { receipt.toFormation.function environment with captured := copies })) after := by
    apply Staging.Recursive.Size.Expression.atomicValue (lookupExpression?_sound sourceFound)
      (receipt.site.code.sourceForm ▸ Staging.Recursive.AtomicForm.lambda _ _ _) receipt.coercions
    rw [receipt.site.code.sourceForm]
    simpa only [Formation.function, CallableIndexedLambdaGeneration.closure, ← sameSource, receipt.coercions] using
      (Dynamic.ExpressionFormEvaluates.lambda (program := Program.ofChecked compiled.sourceProgram)
        (context := context) (evidence := invocation.evidence) (source := invocation.source)
        (environment := environment) (before := before) (after := after) (captured := copies)
        (parameters := receipt.parameters) (returnType := receipt.result) (body := receipt.statements)
        receipt.ordinary snapshot)
  refine ⟨Staging.Recursive.Size.stepSize [], _, after, finalMap, finalWorld, sourceTrace, .value represented,
    finalHeaps, maps, worlds, frame, copy.metadata_extends, reached, related, ?_⟩
  exact after_expression_sized initial reached admitted wellFormed runtime covers locals typed sourceTrace frame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaFormationHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectAuthority
/-! Actual direct-call output-coercion receipts identify the selected ordinary
Header before the suffix runs. The raw operand, final output and original
requirement partition remain distinct. No method is represented by a Header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectAuthority
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (ResolvedCaller)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {budget : Nat}
  {source : TypedSource} {scope : SourceCoreBasic.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (actual : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    child budget source scope id callee ids instantiation reasonAt callables node output)

/-- The physical slot comes from the actual unique lookup made by the compiler. -/
theorem native_selected :
    compilation.globals[actual.native.index]? = some actual.native.signature ∧
      actual.native.signature.key = actual.selection.key := by
  have member : (actual.native.signature, actual.native.index) ∈
      compilation.globals.zipIdx.filter (fun row => decide (row.1.key = actual.selection.key)) := by
    rw [actual.native.global]
    exact List.mem_singleton.mpr rfl
  have selected := List.mem_filter.mp member
  exact ⟨List.mk_mem_zipIdx_iff_getElem?.mp selected.1,
    by simpa only [decide_eq_true_eq] using selected.2⟩

theorem target : SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation =
    .ok actual.native.signature.key := by
  rw [actual.selection.targetSelected]
  exact congrArg Except.ok (actual.selection.key_eq.symm.trans (native_selected actual).2.symm)

theorem record : SourceCompilationPlan.exactSpecialization compilation.plan actual.native.signature.key =
    .ok actual.selection.specialized := by
  rw [(native_selected actual).2]
  exact actual.selection.selected

structure Ready (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram))) where
  supported : Supported compilation.plan instantiation
  header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)
  member : header ∈ catalog
  slot : header.slot = actual.native.index
  signature : header.named.signature = actual.native.signature
  specialized : header.named.specialized = actual.selection.specialized
  metadata : instantiation = header.instantiation

/-- Complete retained Source metadata, including its original parameter order,
identifies the selected Header at this one covered slot. -/
theorem of_slot {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (supported : Supported compilation.plan instantiation)
    (covered : ∃ header ∈ catalog,
      header.slot = actual.native.index ∧ header.named.signature = actual.native.signature)
    (plan : compilation.plan = compiled.indexed.base.plan)
    (ordered : ∀ header, header ∈ catalog →
      header.instantiation.parameterSubstitution.map Prod.fst =
        (header.named.specialized.parameterSubstitution.map Prod.fst).reverse) :
    Nonempty (Ready actual catalog) := by
  obtain ⟨header, member, slot, signature⟩ := covered
  have actualRecord := record actual
  have actualTarget := target actual
  have headerRecord := CallableIndexedActualNamedSourceReceipts.header_record compiled header
  rw [signature, ← plan] at headerRecord
  have specialized : header.named.specialized = actual.selection.specialized :=
    Except.ok.inj (headerRecord.symm.trans actualRecord)
  have occurrence := CallableNamedMetadata.matches_of_exact actualTarget actualRecord
  have headerTarget := header.target
  rw [signature, ← plan] at headerTarget
  have headerMatch := CallableNamedMetadata.matches_of_exact headerTarget actualRecord
  have occurrenceEq := occurrence.retained_canonical
    (supported.ordered _ _ actualTarget actualRecord)
  have headerEq := headerMatch.retained_canonical (by
    simpa only [← specialized] using ordered header member)
  exact ⟨⟨supported, header, member, slot, signature, specialized, occurrenceEq.trans headerEq.symm⟩⟩

theorem Ready.source_types
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (ready : Ready actual catalog) {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (application : DeclarationApplicationValid context instantiation types node.rawType instantiation.predicates) :
    types = ready.header.bindings.map (fun binding => binding.1.scheme.body) ∧
      node.rawType = ready.header.function.resultType := by
  cases application with
  | intro member admissible declaration parameters result functionType predicates =>
    have shape := RecursiveNamedSourceSignatureFacts.header_shape ready.header wellFormed
      (signatures ▸ member) (by rw [← ready.metadata]; exact declaration)
    rw [← ready.metadata] at shape
    exact ⟨parameters.symm.trans shape.1, result.symm.trans shape.2⟩

/-- The selected inventory row carries its real preparation and whole Source
dictionary. Capture authority remains the reached physical caller's receipt. -/
structure Port (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram))) extends Ready actual catalog where
  row : SourceSpecialization.SpecializedFunction
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation toReady.header
  rawDictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  function : Dynamic.GlobalFunction
  sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt toReady.header rawDictionary function
  sourceInstantiation : function.instantiation = instantiation
  dictionary : function.evidence = prepared.view.evidence

theorem of_inventory_at {inputs : List (Input compiled)} (rows : Inventory inputs)
    (supported : Supported compilation.plan instantiation)
    (covered : ∃ header ∈ headers rows,
      header.slot = actual.native.index ∧ header.named.signature = actual.native.signature)
    (plan : compilation.plan = compiled.indexed.base.plan) :
    Nonempty (Port actual (headers rows)) := by
  obtain ⟨ready⟩ := of_slot actual supported covered plan
    (CallableIndexedOwnedPreparedFiniteNamedInventories.ordered rows)
  obtain ⟨input, packet, _retained, same⟩ := rows.mem_headers ready.header ready.member
  have aligned := packet.aligned
  have metadata : CallableNamedCanonicalOrder.retainedInstantiation input.row = instantiation :=
    aligned.metadata.symm.trans ((congrArg (·.instantiation) same).trans ready.metadata.symm)
  have aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt
      (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
      instantiation ready.header := by
    rw [← same, ← metadata]
    exact aligned
  have sourceAt := packet.sourceAt
  have sourceMetadata :
      (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized
        input.prepared.available)).instantiation = instantiation := by
    change CallableNamedCanonicalOrder.retainedInstantiation packet.header.named.specialized = instantiation
    rw [packet.aligned.named]
    change CallableNamedCanonicalOrder.retainedInstantiation input.prepared.named.specialized = instantiation
    rw [input.prepared.same]
    exact metadata
  exact ⟨{ toReady := ready
           row := input.row
           prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
           aligned := aligned
           rawDictionary := input.prepared.available
           function := CallableNamedReversal.global
             (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)
           sourceAt := same ▸ sourceAt
           sourceInstantiation := sourceMetadata
           dictionary := (same ▸ sourceAt).dictionary.symm.trans
             (congrArg Dynamic.Closure.evidence aligned.function) }⟩

/-- Evidence belongs to the original call and its full output-coercion
partition, before the selected named invocation starts. -/
structure EvidenceAt {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (port : Port actual catalog) (context : SourceSemantics.Context)
    (callerEvidence : Dynamic.EvidenceEnvironment) : Prop where
  produces : Dynamic.DirectCallProducesEvidence context callerEvidence node.requirements node.coercions
    instantiation.predicates port.function.evidence
  agrees : ∀ evidence, Dynamic.DirectCallProducesEvidence context callerEvidence node.requirements node.coercions
    instantiation.predicates evidence → evidence = port.function.evidence

structure PortWithEvidence (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram)))
    (context : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment)
    extends Port actual catalog where
  evidence : EvidenceAt actual toPort context callerEvidence

/-- Both dictionaries are authenticated by the real resolver and complete
selected record; Source agreement retains the original requirement IDs. -/
theorem authenticated_evidence_of_resolved
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (port : Port actual catalog)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (resolvedCaller : ResolvedCaller compiled.sourceProgram caller callerEvidence)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context) :
    EvidenceAt actual port context callerEvidence := by
  have same : port.row = actual.selection.specialized :=
    port.prepared.same.symm.trans
      ((congrArg (fun named => named.specialized) port.aligned.named).symm.trans port.specialized)
  have actualKey := (CallableNamedMetadata.specialization_of_exact actual.selection.selected).2
  have calleeDictionary : actual.selection.actual = port.prepared.available := by
    apply port.prepared.authenticated_dictionary
    simpa only [same, actualKey] using actual.selection.authenticated
  have input : actual.selection.available = resolvedCaller.available :=
    Except.ok.inj (actual.selection.resolved.symm.trans resolvedCaller.resolved)
  have output : CallableNamedMetadata.environment actual.selection.actual = port.function.evidence := by
    rw [calleeDictionary, port.dictionary]
    rfl
  constructor
  · have produced := actual.selection.direct_produces signatures ledger assumptions
    simpa only [input, output, resolvedCaller.dictionary] using produced
  · intro evidence produced
    have produced : Dynamic.DirectCallProducesEvidence context
        (CallableNamedMetadata.environment actual.selection.available) node.requirements node.coercions
        instantiation.predicates evidence := by
      simpa only [input, resolvedCaller.dictionary] using produced
    exact (actual.selection.direct_agrees ledger
      (CallableCallRequirementLayouts.singletons_of_unique ledger unique) produced).trans output

theorem of_resolved {inputs : List (Input compiled)} (rows : Inventory inputs)
    (supported : Supported compilation.plan instantiation)
    (covered : ∃ header ∈ headers rows,
      header.slot = actual.native.index ∧ header.named.signature = actual.native.signature)
    (plan : compilation.plan = compiled.indexed.base.plan)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (resolvedCaller : ResolvedCaller compiled.sourceProgram caller callerEvidence)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context) :
    Nonempty (PortWithEvidence actual (headers rows) context callerEvidence) := by
  obtain ⟨port⟩ := of_inventory_at actual rows supported covered plan
  exact ⟨{
    toPort := port
    evidence := authenticated_evidence_of_resolved actual port resolvedCaller
      signatures ledger assumptions unique
  }⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectAuthority
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureInvocationSpineBounds
/-! A staged user closure invokes its actual retained Code. The original
parameter installation and saved-caller restoration are independent of the
body outcome, so a nested stage failure keeps its Scope/call/tag. A strict
body hypothesis is used only at the real selected parameter entry. Its full
post returns through the saved physical caller; context support follows from
the genuine closure frame and caller runtime validity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureInvocationSpineBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds
open Staging.Recursive

private theorem binders_context_eq {owner : Resolved.DeclarationId}
    {before left right : SourceSemantics.Context} {parameters : List TypedBinder}
    {leftTypes rightTypes : List TypeSystem.Ty}
    (first : MonoBindersExtend owner before parameters leftTypes left)
    (second : MonoBindersExtend owner before parameters rightTypes right) : left = right := by
  have same := first.bodyTypes_eq.symm.trans second.bodyTypes_eq
  subst rightTypes
  exact first.functional second

/-- The Source application itself selects the genuine staged child Scope and
allocation. Physical arity excludes only the real closureArity alternative. -/
private theorem source_body {program : Program} {stages : Registry}
    {invocation : Scope} {function : Dynamic.Closure} {callContext bodyContext : SourceSemantics.Context}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {parameterTypes : List TypeSystem.Ty}
    {size : Nat} {outcome : Outcome}
    (parameters : MonoBindersExtend function.source.owner function.context
      function.parameters parameterTypes bodyContext)
    (arity : function.parameters.length = arguments.length)
    (trace : Size.Applies program stages size invocation callContext before
      (.closure function) arguments outcome after) :
    ∃ childSize child entry copied environment bound finalContext bodyOutcome,
      stages.Closure function child ∧ Dynamic.ClosureFrame program function ∧
      Dynamic.EnvironmentCopies function.source function.captured before entry copied ∧
      Dynamic.BindersAllocate entry copied function.parameters arguments environment bound ∧
      Size.Statements program stages childSize child bodyContext environment bound function.body
        finalContext bodyOutcome after ∧ BodyResult function.resultType bodyOutcome outcome ∧ childSize < size := by
  cases trace with
  | closureArity mismatch => exact False.elim (mismatch arity)
  | closure selected valid extended copy allocated body resultRule =>
      have same := binders_context_eq extended parameters
      subst same
      exact ⟨_, _, _, _, _, _, _, _, selected, valid, copy, allocated, body, resultRule,
        Size.child_lt_stepSize (by simp)⟩

section Invocation
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {stages : Registry} {faults : RecursiveStageMeaning.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid program callerContext callerSource)
  (savedRows : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include represented heaps locals reference currentCarried allowed callerRuntime savedRows in
/-- The strict staged body is selected by the actual Source closure rule.
Installation, marked parameter allocation and physical caller restoration
are the original producers, each used once at the argument-post pool. -/
theorem invocation_preserves (budget : Nat)
    (bodies : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor
        (values := .initial compiled.compatible.checked) captured code history inputs functions registry
        arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost),
      ∀ (added : Environment) (_length : added.length = code.receipt.loweredParameters.length)
        (copied : Environment) (_spine : entry.entry.canonical = added ++ copied)
        (_kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?),
      ∀ reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
      ∀ childSize, childSize < budget → SourceBodyAt (stages := stages) (faults := faults)
        captured code history inputs functions owner caller entry reached childSize)
    {invocation : Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Outcome} {after : Dynamic.Heap}
    (trace : Size.Applies program stages size invocation callContext before (.closure function)
      arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates (DataPatternValues.packValues nativeArguments ::
        encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
        store (code.body.rename captured.embedding.lift.lift) value finalStore ∧
      ResultAt (registry := registry) (faults := faults) (callerContext := callerContext) captured code functions caller
        outcome after value finalStore := by
  have arity : function.parameters.length = arguments.length := by
    rw [CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code,
      List.length_map]
    exact represented.length.1
  obtain ⟨childSize, child, copies, copiedHeap, environment, bound, finalContext, bodyOutcome,
    selected, valid, copy, allocated, bodyTrace, resultRule, smaller⟩ := source_body inputs.extended arity trace
  obtain ⟨entry, added, copied, length, spine, kept, parameterState, parameterRelated⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.parameters_with_state captured code history inputs
      functions represented owner caller heaps locals reference currentCarried allowed
  obtain ⟨sameCopies, sameCopied⟩ := Dynamic.EnvironmentCopies.functional entry.entry.copy copy
  rw [← sameCopies, ← sameCopied] at allocated
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyTransition⟩ :=
    bodies entry added length copied spine kept parameterState childSize (Nat.lt_of_lt_of_le smaller within)
      selected valid bodyTrace resultRule
  obtain ⟨bodyState, bodyRelated, bodyPost⟩ := bodyTransition
  have maps := entry.entry.maps.trans bodyMaps
  have worlds := entry.entry.worlds.trans bodyWorlds
  have frame := entry.entry.frame.trans bodyFrame
  have metadata := entry.entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := parameterRelated.trans bodyRelated
  obtain ⟨restoredHeaps, restoredFrame, _cell, _bodyRelated, callerRelated, _records, _returned⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position
      (CallableIndexedAmbient.frame_registered compiled.indexed) finalHeaps worlds frame related
  have bodyRuntime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters valid inputs.extended).1
  have supports := Dynamic.TypeContextSupports.ofClosed
    (callerRuntime.signatures.trans bodyRuntime.signatures.symm)
    bodyRuntime.closed callerRuntime.closed bodyRuntime.variables_closed callerRuntime.residual_variables_open
  have callerPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position savedRows bodyPost supports restoredFrame
  exact ⟨value, _, entry.wrap bodyEvaluation, finalMap, finalWorld, result,
    restoredHeaps, maps, worlds, restoredFrame, metadata,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position, callerRelated, callerPost⟩


include represented heaps locals reference currentCarried allowed callerRuntime savedRows in
/-- Applying the actual retained closure payload preserves the full staged
result. Its one native apply edge encloses the real invocation producer. -/
theorem application_preserves (budget : Nat)
    (bodies : ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor
        (values := .initial compiled.compatible.checked) captured code history inputs functions registry
        arguments nativeArguments before store owner.key.frameLocation
        (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost),
      ∀ (added : Environment) (_length : added.length = code.receipt.loweredParameters.length)
        (copied : Environment) (_spine : entry.entry.canonical = added ++ copied)
        (_kept : ∀ slot, scope.length ≤ slot → copied[slot]? = captured.canonical[slot]?),
      ∀ reached : State headers keys
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
      ∀ childSize, childSize < budget → SourceBodyAt (stages := stages) (faults := faults)
        captured code history inputs functions owner caller entry reached childSize)
    {invocation : Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Outcome} {after : Dynamic.Heap}
    (trace : Size.Applies program stages size invocation callContext before (.closure function)
      arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) (callerContext := callerContext) captured code functions caller
        outcome after value finalStore := by
  obtain ⟨value, finalStore, evaluated, result⟩ :=
    invocation_preserves captured code history inputs functions represented owner caller heaps locals
      reference currentCarried allowed callerRuntime savedRows budget bodies trace within
  exact ⟨value, finalStore, .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result⟩

end Invocation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosureInvocationSpineBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectSourceInversion
/-! Direct calls evaluate their argument vector before entering the selected
named body. No runtime callee evaluation or indirect call guard is inserted. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectSourceInversion
open Frontend SourceInference Staging.Recursive

variable {program : Program} {registry : Registry} {invocation : Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id callee : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Outcome}
  {instantiation : DeclarationInstantiation} {arguments : List ExpressionId}

private theorem occurrence_form {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Occurrence invocation id actualForm requirements) : actualForm = node.form := by
  obtain ⟨actualNode, contains, actualFormEq, _, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact actualFormEq.symm.trans (congrArg ExpressionNode.form same)

private theorem occurrence_requirements {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Occurrence invocation id actualForm requirements) : node.requirements = requirements := by
  obtain ⟨actualNode, contains, _, actualRequirements, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact (congrArg ExpressionNode.requirements same).symm.trans actualRequirements

theorem children
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (coercions : node.coercions = [])
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    (∃ sequenceSize invocationSize argumentsHeap values name evidence,
      size = Size.stepSize [sequenceSize, invocationSize] ∧
      Occurrence invocation callee (.reference name (.declaration instantiation)) ∧
      SourceSemantics.DeclarationInstantiation.Valid context instantiation ∧
      Size.Expressions program registry sequenceSize invocation context environment before arguments (.values values) argumentsHeap ∧
      Dynamic.DirectCallProducesEvidence context invocation.evidence node.requirements [] instantiation.predicates evidence ∧
      Size.Applies program registry invocationSize invocation context argumentsHeap
        (.global ⟨instantiation, evidence⟩) values outcome after) ∨
    (∃ sequenceSize failure, size = Size.stepSize [sequenceSize] ∧
      outcome = .fault failure ∧
      Size.Expressions program registry sequenceSize invocation context environment before arguments (.fault failure) after) := by
  have actual : ∀ {actualForm requirements}, Occurrence invocation id actualForm requirements → actualForm = .call callee arguments (.declaration instantiation) :=
    fun occurrence => (occurrence_form unique found occurrence).trans form
  cases trace with
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found coercions contains))
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [same, form] at atomic
      cases atomic
  | directApplied occurrence calleeOccurrence valid children callEvidence applied =>
      obtain ⟨rfl, rfl, same⟩ := ExpressionForm.call.inj (actual occurrence)
      cases same
      rw [← occurrence_requirements unique found occurrence] at callEvidence
      exact .inl ⟨_, _, _, _, _, _, rfl, calleeOccurrence, valid, children, callEvidence, applied⟩
  | directArgumentsFault occurrence _calleeOccurrence children =>
      obtain ⟨rfl, rfl, same⟩ := ExpressionForm.call.inj (actual occurrence)
      cases same
      exact .inr ⟨_, _, rfl, rfl, children⟩
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | tupleValue occurrence _ _ | tupleFault occurrence _ | constructorValue occurrence _ _ | constructorFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _
  | unaryInvalid occurrence _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _
  | binaryInvalid occurrence _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _
  | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTraceBounds
/-! A literal terminal compiler receipt and an actual whole Source body trace
select its used expression internally. Strict expression preservation then
proves the emitted body and its full reached post, including both fault tags. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTraceBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
universe u

variable {policy : SourceCoreLoops.Policy} {fuel : Nat} {compilerSource : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
  {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (receipt : Receipt policy fuel compilerSource scope expression statements result reasonAt fellThrough escaped code)
  (view : SourceView invocation.source compilerSource)
  (certifies : ∀ child, policy.lowerExpression receipt.childFuel compilerSource scope expression reasonAt = .ok child →
    certificate scope expression child)
  {node : ExpressionNode}
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include view certifies found sourceTyped environments heaps locals agrees typed admitted in
/-- The supported Source statement constructor supplies the one used child;
no body execution law or separate expression trace is a premise. -/
theorem preserves_body (unique : NodeOccurrencesUnique invocation.source) (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements program registry size invocation context environment
      before statements finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult node.type bodyOutcome outcome)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type receipt.child.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  obtain ⟨childSize, childOutcome, sameSize, _sameContext, sameBody, child⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body unique
      (CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.source_head receipt view) trace
  have sameOutcome : outcome = childOutcome :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.result_of_control (sameBody ▸ matched)
  subst outcome
  obtain ⟨_sourceTrace, _sourceResult, meaning⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.preserves bridge receipt view certifies found
      sourceTyped environments heaps locals agrees typed initial admitted budget children child (sameSize ▸ within)
  exact meaning

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTraceBounds
end

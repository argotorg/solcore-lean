import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
import Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedInitialContextValidity

/-! The actual authenticated direct-call branch fixes both complete dictionaries
and the physical prepared callee. These are static receipts and independent
source evidence judgments. No closed Header, body execution, native authority,
or whole compiler admission is constructed here. Full raw substitution order,
unused ledger rows and recursive evidence remain unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedCallEvidence
open Core Frontend SourceInference
open RecursiveNamedPublicSpecializationMeaning CallableCoercionExpressionCertificates
open CallableNamedMetadata (environment)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) : ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

/-- Only the real successful preparation fixes this key. No signature or
native type is used to identify an arbitrary source record. -/
private theorem prepared_key {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {row : SourceSpecialization.SpecializedFunction} {named : SourceCoreGeneralFunctions.Function}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation row = .ok named) :
    named.signature.key = row.key := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (row.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged] at accepted
    cases shape : row.function.type <;>
      simp only [shape, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted <;>
      try contradiction
    rename_i parameter result
    by_cases mismatch : result ≠ row.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      cases accepted
      rfl

namespace Prepared
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : Specialized}
  (prepared : Prepared compiled row)

theorem signature_key : prepared.named.signature.key = row.key := by
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled prepared.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  exact (prepared_key accepted).trans (congrArg (·.key) (same.symm.trans prepared.same))

/-- Real parameter installation retains the exact source catalog, complete
ledger and declaration assumptions. -/
theorem context_fields {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend prepared.view.source.owner prepared.view.context prepared.view.parameters types context) :
    context.signatures = compiled.sourceProgram.signatures ∧
      context.solvedRequirements = row.function.solvedRequirements ∧ context.assumptions = row.assumptions := by
  have fields := RecursiveNamedInitialContextValidity.mono_fields extended
  simpa only [RecursiveNamedPublicSpecializationMeaning.Prepared.view, RecursiveNamedPreparedSourceFrames.view,
    RecursiveNamedSpecializationBodyFacts.bodyInstance, declarationContext, SourceSemantics.Context.withResidualTypeVariables,
    SourceSemantics.Context.withSolvedRequirements, SourceSemantics.Context.withAssumptions,
    SourceSemantics.Context.forDeclaration, SourceSemantics.Context.ofSignatures, prepared.same] using
    And.intro fields.signatures (And.intro fields.solvedRequirements fields.assumptions)
end Prepared

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {caller : Specialized}
  {project : Projector} {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child}
  {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
  {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compiled.sourceProgram project caller compilation child fuel caller.function.typedBody scope
    id callee arguments instantiation reasonAt policy node output)
  (callerPrepared : Prepared compiled caller)
  (calleePrepared : Prepared compiled receipt.selection.specialized)

/-- The actual caller resolver, including all ordered entries, agrees by the
same successful computation, rather than by its predicate keys. -/
theorem caller_dictionary : receipt.selection.available = callerPrepared.available :=
  Except.ok.inj (receipt.selection.resolved.symm.trans callerPrepared.resolved)

/-- Authentication compares every complete recursive evidence tree with the
same resolver used to prepare the actual callee view. -/
theorem callee_dictionary : receipt.selection.actual = calleePrepared.available := by
  have key := (CallableNamedMetadata.specialization_of_exact receipt.selection.selected).2
  apply calleePrepared.authenticated_dictionary
  simpa only [key] using receipt.selection.authenticated

/-- Full actual globals, the successful named preparer and the singleton
native selection identify the signature and physical cache slot together. -/
theorem native_target
    (globals : compilation.globals = compiled.indexed.base.globals) :
    receipt.native.signature = calleePrepared.named.signature ∧ receipt.native.index = calleePrepared.index := by
  have selected : compiled.indexed.base.globals[calleePrepared.index]? = some calleePrepared.named.signature := by
    rw [CallableIndexedPreparedInventories.cached_globals]
    simp only [List.getElem?_map, calleePrepared.selected, Option.map_some]
  have key : calleePrepared.named.signature.key = receipt.selection.key :=
    (Prepared.signature_key calleePrepared).trans (CallableNamedMetadata.specialization_of_exact receipt.selection.selected).2
  have member : (calleePrepared.named.signature, calleePrepared.index) ∈
      compilation.globals.zipIdx.filter (fun row => decide (row.1.key = receipt.selection.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr (globals ▸ selected), ?_⟩
    simp only [key, decide_true]
  rw [receipt.native.global] at member
  have same := List.mem_singleton.mp member
  exact ⟨(congrArg Prod.fst same).symm, (congrArg Prod.snd same).symm⟩

/-- The actual selected full metadata determines the retained record only with
its original reverse-domain receipt; order is not erased. -/
theorem retained_metadata
    (order : instantiation.parameterSubstitution.map Prod.fst =
      (receipt.selection.specialized.parameterSubstitution.map Prod.fst).reverse) :
    instantiation = CallableNamedCanonicalOrder.retainedInstantiation receipt.selection.specialized :=
  receipt.selection.metadata.retained_canonical order

/-- Source production uses exactly the two actual prepared dictionaries.
No unrelated source ledger row is required to be an ordinary assumption. -/
theorem produces {context : SourceSemantics.Context}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions) :
    Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
      instantiation.predicates calleePrepared.view.evidence := by
  have actual := receipt.selection.direct_produces signatures ledger assumptions
  simpa only [caller_dictionary receipt callerPrepared, callee_dictionary receipt calleePrepared,
    RecursiveNamedPublicSpecializationMeaning.Prepared.view] using actual

/-- Independent source production selects the same complete output. The
source ledger's identity invariant fixes reached rows, including after an
actual lexical extension; it does not discard unused rows. -/
theorem agrees {context : SourceSemantics.Context} {semantic : Dynamic.EvidenceEnvironment}
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (unique : RequirementIdsUnique context)
    (independent : Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence
      node.requirements node.coercions instantiation.predicates semantic) :
    semantic = calleePrepared.view.evidence := by
  have same := receipt.selection.direct_agrees ledger
    (CallableCallRequirementLayouts.singletons_of_unique ledger unique)
    (by simpa only [caller_dictionary receipt callerPrepared, RecursiveNamedPublicSpecializationMeaning.Prepared.view] using independent)
  simpa only [callee_dictionary receipt calleePrepared, RecursiveNamedPublicSpecializationMeaning.Prepared.view] using same

/-- The actual source frame supplies ledger identity and the real parameter
context. Independent program and full substitution-range validity remain
explicit; source typing is not inferred from native acceptance. -/
theorem at_frame {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) caller.parameterSubstitution)
    (extended : MonoBindersExtend callerPrepared.view.source.owner callerPrepared.view.context
      callerPrepared.view.parameters types context) :
    Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
      instantiation.predicates calleePrepared.view.evidence ∧
    ∀ semantic, Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
      instantiation.predicates semantic → semantic = calleePrepared.view.evidence := by
  obtain ⟨signatures, ledger, assumptions⟩ := Prepared.context_fields callerPrepared extended
  have runtime := RecursiveNamedInitialContextValidity.runtime (callerPrepared.source_frame wellFormed range) extended wellFormed
  exact ⟨produces receipt callerPrepared calleePrepared signatures ledger (by intro goal member; simpa only [assumptions] using member),
    fun _ independent => agrees receipt callerPrepared calleePrepared ledger runtime.idsUnique independent⟩

/-- The selected callee frame uses the same full retained source instantiation
and authenticated dictionary; this is not a native body execution theorem. -/
theorem callee_frame
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) receipt.selection.specialized.parameterSubstitution)
    (order : instantiation.parameterSubstitution.map Prod.fst =
      (receipt.selection.specialized.parameterSubstitution.map Prod.fst).reverse) :
    NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) instantiation
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram receipt.selection.specialized) calleePrepared.view := by
  exact Eq.mp (congrArg (fun selected => NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) selected
    (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram receipt.selection.specialized) calleePrepared.view)
    (retained_metadata receipt order).symm) (calleePrepared.retained_frame wellFormed range)

/-- Start at the actual authenticated `some` branch on the original caller
source. The returned receipt retains ordered callback results and full target
selection; no old ordinary Header or empty-callee premise is introduced. -/
theorem from_accepted {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (found : caller.function.typedBody.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (accepted : SourceCoreEvidence.lowerWithProjector compiled.sourceProgram project caller compilation child fuel
      caller.function.typedBody scope id reasonAt policy = .ok (some output))
    (globals : compilation.globals = compiled.indexed.base.globals)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) caller.parameterSubstitution)
    (extended : MonoBindersExtend callerPrepared.view.source.owner callerPrepared.view.context
      callerPrepared.view.parameters types context) :
    ∃ receipt : Direct compiled.sourceProgram project caller compilation child fuel caller.function.typedBody scope
        id callee arguments instantiation reasonAt policy node output,
      ∀ calleePrepared : Prepared compiled receipt.selection.specialized,
        receipt.native.signature = calleePrepared.named.signature ∧ receipt.native.index = calleePrepared.index ∧
        Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
          instantiation.predicates calleePrepared.view.evidence ∧
        ∀ semantic, Dynamic.DirectCallProducesEvidence context callerPrepared.view.evidence node.requirements node.coercions
          instantiation.predicates semantic → semantic = calleePrepared.view.evidence := by
  obtain ⟨actual⟩ := CallableCoercionExpressionCertificates.direct_of_accepted found form accepted
  refine ⟨actual, fun target => ?_⟩
  obtain ⟨signature, slot⟩ := native_target actual target globals
  obtain ⟨produced, same⟩ := at_frame actual callerPrepared target wellFormed range extended
  exact ⟨signature, slot, produced, same⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedCallEvidence

import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionLiftBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedArgumentTraceBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChain
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectAuthority

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageRawDirectSource
open Frontend SourceInference
open SelectedCompilationStageCoercionLiftBounds

private def Available (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (ids : List RequirementId) : Prop :=
  ∀ id, id ∈ ids → ¬ Dynamic.RequirementUnavailable context evidence id

private theorem produced_available {context : Context} {evidence produced : Dynamic.EvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate}
    (unique : RequirementIdsUnique context)
    (receipt : Dynamic.RequirementsProduceEnvironment context evidence ids predicates produced) :
    Available context evidence ids := by
  induction receipt with
  | nil => intro id member; cases member
  | cons head tail ih =>
    intro id member
    rcases List.mem_cons.mp member with same | member
    · subst id; exact head.excludes_unavailable unique
    · exact ih id member

private theorem selected_available {program : Program} {context : Context} {evidence dictionary : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {ids : List RequirementId} {body : Dynamic.BodyInstance}
    (unique : RequirementIdsUnique context)
    (selected : Dynamic.OperatorMethodSelected program context evidence traitName methodName ids body dictionary) :
    Available context evidence ids := by
  cases selected with
  | intro selects _ _ _ _ _ _ _ _ _ methods _ _ _ =>
    cases selects with
    | intro primary _ =>
      intro id member
      rcases List.mem_cons.mp member with same | member
      · subst id; exact primary.excludes_unavailable unique
      · exact produced_available unique methods id member

private theorem chain_available {compiled : SourceCoreUnifiedCompilation.Compiled}
    {project compilation caller available scope node policy context invocation stages source target input steps output calls}
    (chain : CallableIndexedOwnedPreparedStagedCoercionChain.Chain compiled project compilation caller available
      scope node policy context invocation stages source target input steps output calls)
    (unique : RequirementIdsUnique context) : Available context invocation.evidence (coercionRequirementIds steps) := by
  induction chain with
  | nil => intro id member; cases member
  | cons step port valid tail ih =>
    intro id member
    rcases List.mem_append.mp member with member | member
    · exact selected_available unique port.selected id member
    · exact ih id member

private theorem requirements_available {context : Context} {evidence dictionary : Dynamic.EvidenceEnvironment}
    {ids : List RequirementId} {steps : List CoercionStep} {predicates : List ProgramPredicate}
    (unique : RequirementIdsUnique context)
    (produced : Dynamic.DirectCallProducesEvidence context evidence ids steps predicates dictionary)
    (coercions : Available context evidence (coercionRequirementIds steps)) : Available context evidence ids := by
  cases produced with
  | intro stepsEq idsEq produced =>
    subst steps
    subst ids
    rw [coercionRequirementIds_append] at coercions
    intro id member
    rcases List.mem_append.mp member with member | member
    · exact coercions id (List.mem_append_left _ member)
    · rcases List.mem_append.mp member with member | member
      · exact produced_available unique produced id member
      · exact coercions id (List.mem_append_right _ member)

private theorem available_excludes {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate} {failed : RequirementId}
    (available : Available context evidence ids)
    (fault : Dynamic.RequirementsFault context evidence ids predicates failed) : False := by
  induction fault with
  | head missing => exact available _ (by simp) missing
  | tail _ _ ih => exact ih (fun id member => available id (by simp [member]))

/-- The exact selected conversion ports and declaration dictionary cover the
whole retained requirement partition, including the conversion requirements. -/
theorem requirements_safe {compiled : SourceCoreUnifiedCompilation.Compiled}
    {project compilation caller available scope node policy context invocation stages source target input steps output calls}
    (chain : CallableIndexedOwnedPreparedStagedCoercionChain.Chain compiled project compilation caller available
      scope node policy context invocation stages source target input steps output calls)
    {ids : List RequirementId} {predicates : List ProgramPredicate} {dictionary : Dynamic.EvidenceEnvironment}
    (unique : RequirementIdsUnique context)
    (produced : Dynamic.DirectCallProducesEvidence context invocation.evidence ids steps predicates dictionary)
    {failed : RequirementId} (fault : Dynamic.RequirementsFault context invocation.evidence ids predicates failed) : False :=
  available_excludes (requirements_available unique produced (chain_available chain unique)) fault

/-- Raw declaration calls keep their original coercion partition while
exposing the actual ordered argument prefix and exact invocation dictionary. -/
theorem raw_call {program : Program} {context : Context} {source : TypedSource}
    {caller invocation : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {callee : ExpressionId} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation} {requirements : List RequirementId} {coercions : List CoercionStep}
    {calleeNode : ExpressionNode} {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? callee = some calleeNode)
    (agrees : ∀ dictionary, Dynamic.DirectCallProducesEvidence context caller requirements coercions
      instantiation.predicates dictionary → dictionary = invocation)
    (safe : ∀ failed, ¬ Dynamic.RequirementsFault context caller requirements instantiation.predicates failed)
    (trace : RawOutcome program size context caller source environment before
      (.call callee ids (.declaration instantiation)) requirements coercions outcome after) :
    RecursiveNamedArgumentTraceBounds.TraceAt program context caller invocation source environment before
      ids instantiation size outcome after := by
  cases trace with
  | value evaluated =>
    cases evaluated with
    | directCall _ _ _ _ _ arguments produced applied =>
      have same := agrees _ produced
      subst same
      exact .apply arguments (.value applied) (SourceExecutionSize.child_lt_stepSize (by simp))
        (SourceExecutionSize.child_lt_stepSize (by simp))
  | fault failed =>
    cases failed with
    | directCalleeMissing missing => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains missing (lookupExpression?_sound found))
    | directArguments _ _ failed => exact .argumentFault failed (SourceExecutionSize.child_lt_stepSize (by simp))
    | directRequirements _ fault => exact False.elim (safe _ fault)
    | directApply arguments produced failed =>
      have same := agrees _ produced
      subst same
      exact .apply arguments (.fault failed) (SourceExecutionSize.child_lt_stepSize (by simp))
        (SourceExecutionSize.child_lt_stepSize (by simp))

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageRawDirectSource

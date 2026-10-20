import Solcore.SourceSemantics.SourceInferenceNormalizedLocalIssuance
import Solcore.Frontend.SourceInference.LocalHeaderRequirementTiming

/-! Actual initialized let and header receipts install their generalized
binder using normalized initializer/ledger formation. No current initializer
typing or retained-template evidence is required for this producer step. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation SourceInferenceSoundness

/-- Both optional annotation paths use the same real initializer return and
allocation. The no-capture certificate belongs to that exact emitted binder. -/
theorem initialized_statement_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : NormalizedStateFormation semantic outer receipt.ready)
    (value : TypeAdmissible semantic (outer.apply receipt.value.type))
    (continuation : outer.SemanticallyExtends receipt.ready.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer receipt.binding.1) :
    NormalizedBinderFormation semantic outer receipt.binding.1 ∧
      NormalizedStateFormation semantic outer result.state := by
  have localsFormed : NormalizedStateFormation semantic outer (receipt.ready.withLocals receipt.locals) :=
    ready.congr rfl rfl
  have valueFormed : TypeAdmissible semantic (outer.apply (receipt.ready.resolve receipt.value.type)) :=
    (continuation _).symm ▸ value
  have binderFormed : NormalizedBinderFormation semantic outer receipt.binding.1 :=
    NormalizedBinderFormation.generalized receipt.locals initial.nextRequirement receipt.name.value
      (some receipt.name.span) false continuation valueFormed ready.requirements noCapture
  have allocated := localsFormed.allocate receipt.name.value receipt.generalized.scheme
    (some receipt.name.span) false receipt.generalized.requirements binderFormed
  refine ⟨binderFormed, ?_⟩
  rw [receipt.completed]
  exact allocated.congr rfl rfl

/-- Header receipts return the actual binder as metadata before the enclosing
for statement records it. The same formation result enters the next item. -/
theorem initialized_header_normalized_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (receipt : LocalHeaderRequirementTiming.Receipt fuel context source initial result)
    (ready : NormalizedStateFormation semantic outer receipt.ready)
    (value : TypeAdmissible semantic (outer.apply receipt.value.type))
    (continuation : outer.SemanticallyExtends receipt.ready.inference.substitution)
    (noCapture : Detail.LocalBinderInstantiationNoCapture outer receipt.binding.1) :
    NormalizedBinderFormation semantic outer receipt.binding.1 ∧
      NormalizedStateFormation semantic outer result.2 := by
  have localsFormed : NormalizedStateFormation semantic outer (receipt.ready.withLocals receipt.locals) :=
    ready.congr rfl rfl
  have valueFormed : TypeAdmissible semantic (outer.apply (receipt.ready.resolve receipt.value.type)) :=
    (continuation _).symm ▸ value
  have binderFormed : NormalizedBinderFormation semantic outer receipt.binding.1 :=
    NormalizedBinderFormation.generalized receipt.locals initial.nextRequirement receipt.name.value
      (some receipt.name.span) false continuation valueFormed ready.requirements noCapture
  have allocated := localsFormed.allocate receipt.name.value receipt.generalized.scheme
    (some receipt.name.span) false receipt.generalized.requirements binderFormed
  refine ⟨binderFormed, ?_⟩
  rw [receipt.completed]
  exact allocated

/-- The real finalizer supplies no-capture for the receipt's actual recorded
statement binder. Node retention is the executable continuation's input. -/
theorem initialized_statement_normalized_from_finalizer
    {whole : SourceInference.Context} {wholeReturn : Ty} {evidence : State}
    {roots : List NodeId} {finalized : SourceInference.Result}
    (resources : FinalInferenceResources whole wholeReturn evidence roots finalized)
    {semantic : SourceSemantics.Context} {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Statement} {initial : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (ready : NormalizedStateFormation semantic finalized.substitution receipt.ready)
    (value : TypeAdmissible semantic (finalized.substitution.apply receipt.value.type))
    (continuation : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution)
    (retained : result.state.nodes ⊆ evidence.nodes) :
    NormalizedBinderFormation semantic finalized.substitution receipt.binding.1 ∧
      NormalizedStateFormation semantic finalized.substitution result.state := by
  apply initialized_statement_normalized_formation receipt ready value continuation
  apply resources.local_no_capture
  apply List.mem_flatMap.mpr
  refine ⟨.statement {
    id := initial.allocateStatementId.1, span := source.span, type := .unit,
    form := .letDecl receipt.binding.1 (some receipt.value.id) }, retained receipt.recorded, ?_⟩
  exact List.mem_singleton_self _

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation

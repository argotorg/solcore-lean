import Solcore.SourceSemantics.CoreLowering.ProtectedStateSequenceBridge

/-! Whole ordered sequence producers operate at one actual caller input.
Their outputs retain the full original result, effects and reached state.
Additional admission can be consumed before instantiation without changing
these neutral receipts or adding another sequence induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionSequenceProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open DataExpressionSequence
open ProtectedDataExpressionSequence
universe u v
variable {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u,v} Records}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr} {faults : GenericExpressionMeaning.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)

/-- Inclusive Source sequence grades retain success and fault posts. -/
def Preserves (budget : Nat) : Prop :=
  ∀ {size outcome after},
    TraceAt program size context evidence source environment before ids outcome after → size ≤ budget →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

/-- Native sequence grades are strict; the reconstructed Source grade is
independent, and its actual successful or fault witness is retained. -/
def Reflects (budget : Nat) : Prop :=
  ∀ {size value finalStore},
    EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore →
    size < budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      TraceAt program sourceSize context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

variable {model}

/-- The existing Source fold supplies this provider at the same real input. -/
theorem Preserves.of_uniform (budget : Nat)
    (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → Stateful.ExpressionPreservesAt protocol size model
      program context evidence source certificate faults)
    {administrative actualContext : Core.Context}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions) :
    Preserves (program := program) (context := context) (evidence := evidence) (source := source)
      (ids := ids) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
      (environment := environment) (actual := actual) (ξ := ξ) model initial budget := by
  intro size outcome after trace bounded
  exact Stateful.preserves_bounded protocol budget tree meaning environments heaps locals agrees typed initial trace bounded

/-- The existing native fold supplies the independently graded Source trace
and same reached witness at this exact input. -/
theorem Reflects.of_uniform (budget : Nat)
    (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → Stateful.ExpressionReflectsAt protocol size model
      program context evidence source certificate faults)
    {administrative actualContext : Core.Context}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions) :
    Reflects (program := program) (context := context) (evidence := evidence) (source := source)
      (ids := ids) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
      (environment := environment) (actual := actual) (ξ := ξ) model initial budget := by
  intro size value finalStore completed bounded
  exact Stateful.reflects_bounded protocol budget tree meaning environments heaps locals agrees typed initial completed bounded

end Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionSequenceProducer

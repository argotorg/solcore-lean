import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
import Solcore.SourceSemantics.CoreLowering.RecursiveStageMeaning
import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! Graded interfaces and concrete admission adapters for the supported
recursive staged Source profile. Compiler producers use actual static receipts
and strict child hypotheses. Ordinary outcomes retain the original caller
PostAdmission. Stage failures keep their exact tag and scope and stable rows
at the same reached state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

/-- The receipt is indexed by the actual reached state. A stage failure is
never projected to an ordinary Dynamic fault or given deep heap typing. -/
def PostAdmission (type : TypeSystem.Ty) (outcome : Staging.Recursive.Outcome)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop :=
  match outcome with
  | .value value =>
      CallableIndexedOwnedSourceAdmission.PostAdmission bridge context type (.value value) reached
  | .fault (.semantic reason) =>
      CallableIndexedOwnedSourceAdmission.PostAdmission bridge context type (.fault reason) reached
  | .fault (.stage _ _ _) => StableRows (bridge.pool reached)

variable {bridge context}

/-- Sequential successful children consume the original actual caller receipt
at precisely the reached heap and store. -/
theorem PostAdmission.at_value {type : TypeSystem.Ty} {value : Dynamic.Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge context type (.value value) reached) :
    Dynamic.ValueHasType context index.heap value type ∧ Admission bridge context reached :=
  CallableIndexedOwnedSourceAdmission.PostAdmission.at_value post

theorem PostAdmission.rows {type : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge context type outcome reached) : StableRows (bridge.pool reached) := by
  cases outcome with
  | value value => exact CallableIndexedOwnedSourceAdmission.PostAdmission.rows post
  | fault failure =>
    cases failure with
    | semantic reason => exact CallableIndexedOwnedSourceAdmission.PostAdmission.rows post
    | stage origin call reason => exact post

/-- A propagated fault keeps its exact tag and actual endpoint when the
enclosing expression has another type. Semantic success is impossible; stage
stability is the same receipt. Neither case adds deep heap typing. -/
theorem PostAdmission.at_fault_type {firstType lastType : TypeSystem.Ty}
    {failure : Staging.Recursive.Failure}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge context firstType (.fault failure) reached) :
    PostAdmission bridge context lastType (.fault failure) reached := by
  cases failure with
  | semantic reason =>
    change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context firstType (.fault reason) reached at post
    change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context lastType (.fault reason) reached
    exact ⟨post.rows, by intro value same; cases same⟩
  | stage origin call reason => exact post

/-- The concrete graded Source trace authenticates only its ordinary successful
branch. Stability comes from both genuine endpoint pools and the exact actual
administrative frame. This theorem neither constructs nor substitutes a state. -/
theorem after_expression_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Staging.Recursive.Outcome} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : ExpressionHasType invocation.source context id type)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      initial.heap id outcome reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    PostAdmission bridge context type outcome last := by
  cases outcome with
  | value value =>
    exact CallableIndexedOwnedSourceAdmission.after_expression first last admitted wellFormed runtime covers
      locals typed (.value trace.sound.value_plain) frame
  | fault failure =>
    cases failure with
    | semantic reason =>
      exact CallableIndexedOwnedSourceAdmission.after_expression first last admitted wellFormed runtime covers
        locals typed (.fault trace.sound.semanticFault_plain) frame
    | stage origin call reason =>
      exact StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame

/-- Retain the producer's exact reached witness and its concrete record
relation when adding admission. Transient callee/argument effects remain in
reached.heap/reached.store and in the same dependent caller state. -/
theorem after_related_expression_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (related : callerProtocol.Relates first last)
    (admitted : Admission bridge context first)
    {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Staging.Recursive.Outcome} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : ExpressionHasType invocation.source context id type)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      initial.heap id outcome reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    callerProtocol.Relates first last ∧ PostAdmission bridge context type outcome last :=
  ⟨related, after_expression_sized first last admitted wellFormed runtime covers locals typed trace frame⟩

section Expressions
variable (bridge) (context)
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (certificate : GenericExpressionMeaning.Certificate) (faults : RecursiveStageMeaning.FaultRep)

/-- Source size is the grade of the genuine staged trace. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    Staging.Recursive.Size.Expression program registry size invocation context environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

/-- Native size is measured independently; reflection returns the actual
Source grade and the exact staged outcome, including a nested failing scope. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

def PreservesAtMost (budget : Nat) : Prop :=
  ∀ size, size ≤ budget → PreservesAt bridge context model registry invocation certificate faults size

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt bridge context model registry invocation certificate faults size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt bridge context model registry invocation certificate faults size

end Expressions
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds

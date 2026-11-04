import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LexicalBodyFaults
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForControlShape
import Solcore.SourceSemantics.Staging.RecursiveProjectedTarget
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.Staging.RecursiveControlTransferFacts
import Solcore.SourceSemantics.SelectedBodyTypingCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSourceSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.OrdinaryCatalog
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.Frontend.SourceCoreUnifiedPreparationCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.Staging.SelectedBodyPreservation
import Solcore.SourceSemantics.Staging.RecursiveLiftOutcomes
import Solcore.SourceSemantics.CoreLowering.SourceExecutionSize
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies

/-!
# Selected compilations: catalog, headers and origins

The catalog and headers of a selected compilation, the origins of its callables and locals, and small staged facts about projected targets and coerced sources that later lifting needs.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationBuiltinFunctionOrigins
/-! Indirect builtin dispatch needs only the representation of an actual
builtin leaf. Prepared closure bodies remain in their own receiving model. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationBuiltinFunctionOrigins
open Core Frontend GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

class ErasesBuiltinsToContextual
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) : Prop where
  erase : ∀ {registry mapping world sourceType function native type},
    ValueRep compiled.compatible.checked registry functions mapping world sourceType (.builtin function) native type →
    ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      mapping world sourceType (.builtin function) native type

instance of_erasure (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    [CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual headers keys bodyRegistry faults profile functions] :
    ErasesBuiltinsToContextual headers keys bodyRegistry faults profile functions :=
  ⟨fun represented => represented.map_functions
    (CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual.erase (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (faults := faults) (profile := profile))⟩

theorem prepared_builtin
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Core.Ty}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile)
      mapping world sourceType source native type) :
    ∀ function, source = .builtin function →
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        mapping world sourceType (.builtin function) native type := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    cases related with
    | builtin related => intro function same; cases same; exact .function (.builtin related)
    | global related => intro function impossible; cases impossible
    | closure related => intro function impossible; cases impossible
  | compatible same _ ih =>
    intro function selected
    exact .compatible same (ih function selected)
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

instance prepared (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    ErasesBuiltinsToContextual headers keys bodyRegistry faults profile
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile) :=
  ⟨fun represented => prepared_builtin profile represented _ rfl⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationBuiltinFunctionOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCallableOrigins
/-! Callable stage gates inspect genuine artifact origins. Prepared closure
bodies keep their own model; only actual builtin leaves require a contextual
representation for builtin execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCallableOrigins
open Core Frontend GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

class Origins
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) : Prop
    extends SelectedCompilationBuiltinFunctionOrigins.ErasesBuiltinsToContextual
      headers keys bodyRegistry faults profile functions where
  origin : ∀ {registry mapping world sourceType source native type},
    ValueRep compiled.compatible.checked registry functions mapping world sourceType source native type →
    IsFunction source → CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table source native

instance of_erasure (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    [CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual headers keys bodyRegistry faults profile functions] :
    Origins headers keys bodyRegistry faults profile functions where
  toErasesBuiltinsToContextual := inferInstance
  origin := fun represented shape =>
    CallableIndexedOwnedContextualCalleeStageReceipts.callee_origin
      (CallableIndexedOwnedContextualCalleeOriginReadReceipts.callable_at profile
        (represented.map_functions
          (CallableIndexedOwnedPositiveFunctionModels.ErasesToContextual.erase
            (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
            (faults := faults) (profile := profile))) shape)

theorem prepared_origin
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Core.Ty}
    (represented : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile)
      mapping world sourceType source native type) :
    IsFunction source → CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table source native := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    intro _shape
    cases related with
    | closure member => exact member.stage_origin
    | global member =>
      exact CallableIndexedOwnedContextualCalleeStageReceipts.function_origin
        (bodyRegistry := bodyRegistry) (faults := faults)
        (CallableIndexedOwnedContextualCellOrigins.FunctionOrigins.global member.represents)
    | builtin member =>
      exact CallableIndexedOwnedContextualCalleeStageReceipts.function_origin
        (CallableIndexedOwnedContextualCellOrigins.FunctionOrigins.builtin member)
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

instance prepared (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    Origins headers keys bodyRegistry faults profile
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile) where
  toErasesBuiltinsToContextual := inferInstance
  origin := prepared_origin profile

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCallableOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationControlNoEscape
/-! Function-boundary control follows from the selected Source body's typing.
This argument depends only on syntax and control flow; calls and values do not
require typing of unrelated declarations in the original program. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationControlNoEscape
open Frontend SourceInference

private def StatementClosed (source : TypedSource) (id : StatementId) : Prop :=
  ∀ {program : Program} {context finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome},
    Dynamic.StatementExecutes program context evidence source environment before
      id finalContext outcome after → outcome.NoEscapedControl

private def StatementsClosed (source : TypedSource) (ids : List StatementId) : Prop :=
  ∀ id ∈ ids, StatementClosed source id

private theorem statements_closed {source : TypedSource} {ids : List StatementId}
    (closed : StatementsClosed source ids)
    {program : Program} {context finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.StatementsExecute program context evidence source environment
      before ids finalContext outcome after) : outcome.NoEscapedControl := by
  induction ids generalizing context environment before with
  | nil => cases execution; exact .fallthrough _
  | cons head tail induction =>
    cases execution with
    | cons head tail => exact induction (fun id member => closed id (.tail _ member)) tail
    | terminal head _ => exact closed _ (.head _) head

private structure CasesClosed (source : TypedSource) (cases : List TypedMatchCase) : Prop where
  bodies : ∀ matchCase ∈ cases, StatementsClosed source matchCase.body

private theorem execution_closed {source : TypedSource} {ids : List StatementId}
    {program : Program} {context finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.StatementsExecute program context evidence source environment
      before ids finalContext outcome after)
    (closed : StatementsClosed source ids) : outcome.NoEscapedControl :=
  statements_closed closed execution

private theorem selected_arm_closed {source : TypedSource}
    {context : Context} {value : Dynamic.Value} {cases : List TypedMatchCase}
    {fallback : Option (List StatementId)} {body : List StatementId}
    {bindings : List (TypedBinder × Dynamic.Value)}
    (closed : ∀ matchCase ∈ cases, StatementsClosed source matchCase.body)
    (selected : Dynamic.MatchCasesSelect context value cases fallback (.arm body bindings)) :
    StatementsClosed source body := by
  induction cases with
  | nil => cases selected
  | cons head tail induction =>
    cases selected with
    | head => exact closed head (.head _)
    | tail _ next => exact induction (fun item member => closed item (.tail _ member)) next

private theorem statement_shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

set_option linter.unusedSimpArgs false in
private theorem typed_statements_closed {source : TypedSource}
    (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context finalContext : Context}
    {ids : List StatementId} {facts : BodyFacts}
    (typing : StatementsHaveType source control context ids finalContext facts) :
    control.loopDepth = 0 → StatementsClosed source ids := by
  apply StatementsHaveType.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True)
    (motive_8 := fun control _ id _ _ _ => control.loopDepth = 0 → StatementClosed source id)
    (motive_9 := fun control _ ids _ _ _ => control.loopDepth = 0 → StatementsClosed source ids)
    (motive_10 := fun _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ => True)
    (motive_12 := fun control _ _ matchCase _ _ =>
      control.loopDepth = 0 → StatementsClosed source matchCase.body)
    (motive_13 := fun control _ _ cases _ _ =>
      control.loopDepth = 0 → ∀ matchCase ∈ cases, StatementsClosed source matchCase.body)
    (t := typing)
  all_goals intros
  all_goals try exact True.intro
  all_goals try solve | simp_all [StatementsClosed, ControlContext.loopAllowed]
  case cons =>
    rename_i head tail headIH tailIH zero selected member
    rcases List.mem_cons.mp member with same | member
    · subst selected; exact headIH zero
    · exact tailIH zero selected member
  case' matchWithoutDefault =>
    rename_i expressionIH casesIH zero
    have closedCases : CasesClosed source _ := ⟨casesIH zero⟩
    clear casesIH
  case' matchWithDefault =>
    rename_i expressionIH casesIH defaultIH zero
    have closedCases : CasesClosed source _ := ⟨casesIH zero⟩
    clear casesIH
  all_goals
    have shape := statement_shape unique (by assumption) (by assumption)
    intro program runtimeContext runtimeFinal evidence environment before after outcome execution
    cases execution <;> have actualForm := shape _ (by assumption) <;> simp_all only [reduceCtorEq, StatementForm.ifThen.injEq, StatementForm.block.injEq, StatementForm.matchWith.injEq, StatementForm.forLoop.injEq, StatementForm.whileLoop.injEq, Option.some.injEq, true_implies, and_true, true_and, and_self, and_false, false_and]
  all_goals first | exact .fallthrough _ | exact .returned _ | skip
  all_goals try exact (execution_closed (by assumption) (by assumption)).restore _
  all_goals try exact (execution_closed (by assumption) (selected_arm_closed (CasesClosed.bodies (by assumption)) (by assumption))).restore _
  case matchWithoutDefault.matchDefault =>
    have impossible := Dynamic.MatchCasesSelect.defaultBody_eq (by assumption)
    simp_all
  case matchWithDefault.matchDefault =>
    have same := Dynamic.MatchCasesSelect.defaultBody_eq (by assumption)
    simp_all only [Option.some.injEq]
    exact (execution_closed (by assumption) (by assumption)).restore _
  case forLoop.forLoop =>
    rcases GenericImperativeFor.for_control_shape (by assumption) with ⟨_, same⟩ | ⟨_, same⟩
    · simp_all [Dynamic.restoreControl, Dynamic.ControlOutcome.NoEscapedControl]
    · simp_all [Dynamic.restoreControl, Dynamic.ControlOutcome.NoEscapedControl]
  case whileLoop.whileLoop =>
    rcases TypedLexicalWhile.while_control_shape (by assumption) with ⟨_, same⟩ | ⟨_, same⟩
    · simp_all [Dynamic.restoreControl, Dynamic.ControlOutcome.NoEscapedControl]
    · simp_all [Dynamic.restoreControl, Dynamic.ControlOutcome.NoEscapedControl]


/-- A typed body at the original function depth cannot export a loop transfer.
No heap invariant or validity of another declaration is required. -/
theorem function {source : TypedSource} (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context staticFinal : Context}
    {ids : List StatementId} {facts : BodyFacts}
    (typing : StatementsHaveType source control context ids staticFinal facts)
    (depth : control.loopDepth = 0)
    {program : Program} {runtimeContext finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.FunctionStatementsExecute program runtimeContext evidence source
      environment before ids finalContext outcome after) : outcome.NoEscapedControl := by
  have closed := typed_statements_closed unique typing depth
  clear typing depth
  induction ids generalizing runtimeContext environment before with
  | nil => cases execution; exact .fallthrough _
  | cons head tail induction =>
    cases execution with
    | tailExpression => exact .returned _
    | singleton _ _ trace => exact closed _ (.head _) trace
    | cons _ trace => exact induction trace (fun id member => closed id (.tail _ member))
    | terminal trace _ => exact closed _ (.head _) trace

/-- Scoped sequencing shares the same control-only boundary argument. -/
theorem statements {source : TypedSource} (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context staticFinal : Context}
    {ids : List StatementId} {facts : BodyFacts}
    (typing : StatementsHaveType source control context ids staticFinal facts)
    (depth : control.loopDepth = 0)
    {program : Program} {runtimeContext finalContext : Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.StatementsExecute program runtimeContext evidence source
      environment before ids finalContext outcome after) : outcome.NoEscapedControl :=
  statements_closed (typed_statements_closed unique typing depth) execution

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationControlNoEscape
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedTarget
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive.ProjectedTarget
open Frontend SourceInference Solcore.SourceSemantics.Dynamic
open Solcore.SourceSemantics.CoreLowering

theorem keys_eq_sourceKeys (projections : List PlaceProjection) :
    keys projections = DataPlaceKeyOrder.sourceKeys projections := by
  induction projections with
  | nil => rfl
  | cons projection rest ih =>
      cases projection <;> simp only [keys, DataPlaceKeyOrder.sourceKeys, ih]

theorem Values.to_data {projections : List PlaceProjection} {values : List Dynamic.Value}
    {evaluated : List EvaluatedProjection} (ordered : Values projections values evaluated) :
    DataPlaceKeyOrder.Values projections values evaluated := by
  induction ordered with
  | nil => exact .nil
  | member _ ih => exact .member ih
  | index _ ih => exact .index ih

theorem Values.of_data {projections : List PlaceProjection} {values : List Dynamic.Value}
    {evaluated : List EvaluatedProjection} (ordered : DataPlaceKeyOrder.Values projections values evaluated) :
    Values projections values evaluated := by
  induction ordered with
  | nil => exact .nil
  | member _ ih => exact .member ih
  | index _ ih => exact .index ih

end Solcore.SourceSemantics.Staging.Recursive.ProjectedTarget
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLoopOutcomes
/-! The loop consumes body break and continue. Its final result keeps the
outer environment and cannot carry either control transfer beyond the loop. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLoopOutcomes
open Frontend SourceInference Staging.Recursive

variable {program : Program} {stages : Registry} {invocation : Scope}
  {context : SourceSemantics.Context} {environment inner : Dynamic.Environment}
  {before after : Dynamic.Heap} {test : ExpressionId} {post : List ForItemForm}
  {body : List StatementId} {size : Nat} {outcome : BodyOutcome}

theorem while_closed (trace : Size.While program stages size invocation context environment before test body outcome after) :
    outcome.NoEscapedControl := by
  induction size using Nat.strongRecOn generalizing before after outcome with
  | ind size ih =>
    cases trace with
    | done | breakFromBody => exact .fallthrough environment
    | returned => exact .returned _
    | conditionFault | bodyFault => exact .fault _
    | next test body next | continueNext test body next =>
      exact ih _ (Size.child_lt_stepSize (by simp)) next

theorem for_closed (trace : Size.ForLoop program stages size invocation context environment before test post body outcome after) :
    outcome.NoEscapedControl := by
  induction size using Nat.strongRecOn generalizing before after outcome with
  | ind size ih =>
    cases trace with
    | finished | forBreakFromBody => exact .fallthrough environment
    | returnedFromBody => exact .returned _
    | testFault | bodyFailure | postFailure | continuePostFailure => exact .fault _
    | iterate test body post next | continueIterate test body post next =>
      exact ih _ (Size.child_lt_stepSize (by simp)) next

theorem while_closed_of_trace
    (trace : While program stages invocation context environment before test body outcome after) :
    outcome.NoEscapedControl := by
  obtain ⟨size, measured⟩ := Size.While.of_trace trace
  exact while_closed measured

theorem for_closed_of_trace
    (trace : ForLoop program stages invocation context environment before test post body outcome after) :
    outcome.NoEscapedControl := by
  obtain ⟨size, measured⟩ := Size.ForLoop.of_trace trace
  exact for_closed measured

theorem while_environment
    (trace : Size.While program stages size invocation context environment before test body (.fallthrough inner) after) :
    inner = environment := by
  induction size using Nat.strongRecOn generalizing before after with
  | ind size ih =>
    cases trace with
    | done | breakFromBody => rfl
    | next test body next | continueNext test body next =>
      exact ih _ (Size.child_lt_stepSize (by simp)) next

theorem for_environment
    (trace : Size.ForLoop program stages size invocation context environment before test post body (.fallthrough inner) after) :
    inner = environment := by
  induction size using Nat.strongRecOn generalizing before after with
  | ind size ih =>
    cases trace with
    | finished | forBreakFromBody => rfl
    | iterate test body post next | continueIterate test body post next =>
      exact ih _ (Size.child_lt_stepSize (by simp)) next

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLoopOutcomes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping
open Frontend SourceInference TypeSystem

/-- The selected ordinary definition is identified by its actual cached row
and complete successful specialization, including unused replacement rows. -/
def OrdinarySource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (generic : CheckedFunction) : Prop :=
  ∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function)
      (signature : ProgramFunctionSignature) (supplied : ParameterSubstitution),
    compiled.indexed.base.functions[index]? = some named ∧
    signature ∈ compiled.sourceProgram.signatures.functions ∧
    generic ∈ compiled.sourceProgram.functions ∧
    SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized

/-- A selected method retains the real cache, original method identity and
complete checker carrier recovered by the original method coherence receipt. -/
def MethodSource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (retained : CheckedImplementationMethod) : Prop :=
  ∃ (index : Nat) (named : SourceCoreGeneralFunctions.Function)
      (method : ExecutableImplMethods.CheckedMethod),
    compiled.indexed.base.functions[index]? = some named ∧
    named.specialized = method.specialized ∧
    ∃ selection : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method,
      retained ∈ compiled.sourceProgram.methods ∧ retained.id = method.id ∧
        selection.generic = retained.checked

/-- Global identity facts and typing of only the original definitions selected
by the complete compiled cache. The original program and signature IDs stay fixed. -/
structure Bodies (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  signatures : SignatureCatalogWellFormed compiled.sourceProgram.signatures
  function_ids : ((Program.ofChecked compiled.sourceProgram).functions.map
    fun definition => definition.body.owner).Nodup
  method_ids : ((Program.ofChecked compiled.sourceProgram).methods.map
    fun definition => definition.id).Nodup
  ordinary : ∀ generic, OrdinarySource compiled generic →
    FunctionDefinition.Valid compiled.sourceProgram.signatures (FunctionDefinition.ofChecked generic)
  methods : ∀ retained, MethodSource compiled retained →
    MethodDefinition.Valid compiled.sourceProgram.signatures (MethodDefinition.ofChecked retained)

namespace Bodies
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Existing whole-program clients can use the narrower interface directly. -/
theorem of_program (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Bodies compiled := by
  refine ⟨wellFormed.signatures, wellFormed.function_ids, wellFormed.method_ids, ?_, ?_⟩
  · intro generic selected
    obtain ⟨index, named, signature, supplied, cached, signatureMember, member, accepted⟩ := selected
    exact wellFormed.functions_valid _ (List.mem_map.mpr ⟨generic, member, rfl⟩)
  · intro retained selected
    obtain ⟨index, named, method, cached, same, selection, member, identity, checked⟩ := selected
    exact wellFormed.methods_valid _ (List.mem_map.mpr ⟨retained, member, rfl⟩)

/-- An authentic prepared row supplies all membership facts for its original body. -/
theorem prepared_certificate (bodies : Bodies compiled)
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    ∃ types context facts,
      Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        (CallableNamedMetadata.instantiation row)
        (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
        types context facts := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, resolved, accepted⟩ := prepared.origin
  have valid := bodies.ordinary generic
    ⟨prepared.index, prepared.named, signature, request.parameterSubstitution, prepared.selected,
      signatureMember, genericMember, by simpa only [prepared.same] using accepted⟩
  have instantiated := RecursiveNamedSpecializationValidity.instantiated signatureMember genericMember
    accepted (bodies.signatures.function_parameters signature signatureMember).1 range
  have owner : (FunctionDefinition.ofChecked generic).body.owner =
      (CallableNamedMetadata.instantiation row).declaration := by
    exact ((RecursiveNamedSpecializationBodyFacts.identities accepted).2.2).symm
  exact instantiated.certificate_of_valid bodies.signatures bodies.function_ids
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩) owner valid

/-- A selected method instance uses the retained original definition authenticated
by its exact cache row and method-checking provenance. -/
theorem method_certificate (bodies : Bodies compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (cached : compiled.indexed.base.functions[index]? = some named)
    {method : ExecutableImplMethods.CheckedMethod}
    (same : named.specialized = method.specialized)
    (selection : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method)
    {retained : CheckedImplementationMethod}
    (member : retained ∈ compiled.sourceProgram.methods)
    (identity : retained.id = method.id) (original : selection.generic = retained.checked)
    {substitution : ParameterSubstitution} {bodyInstance : Dynamic.BodyInstance}
    (instantiates : Dynamic.TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
      selection.implementation selection.declaration selection.trait
      (MethodDefinition.ofChecked retained) substitution bodyInstance) :
    ∃ types context facts,
      Dynamic.TraitMethodInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        selection.declaration substitution (MethodDefinition.ofChecked retained) bodyInstance
        types context facts := by
  exact instantiates.certificate_of_valid bodies.signatures
    (bodies.methods retained ⟨index, named, method, cached, same, selection, member, identity, original⟩)

end Bodies
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaders
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaders
open Core Frontend SourceInference RecursiveNamedCatalog
open RecursiveNamedPublicSpecializationMeaning
open RecursiveNamedPreparedHeaders.Prepared (HeaderAt policy)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem project_productMany {catalog : SourceCoreCompatibleCatalog.Catalog}
    {types : List TypeSystem.Ty} {native : List Core.Ty}
    (projected : types.mapM catalog.project = .ok native) :
    catalog.project (TypeSystem.Ty.productMany types) = .ok (SourceCoreCompatibleCatalog.packTypes native) := by
  induction types generalizing native with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projected
    subst native
    rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at projected
    obtain ⟨first, projectedHead, projected⟩ := bind_ok projected
    obtain ⟨rest, projectedTail, projected⟩ := bind_ok projected
    cases projected
    cases tail with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projectedTail
      subst rest
      exact projectedHead
    | cons next suffix =>
      have remaining := ih projectedTail
      rw [List.mapM_cons] at projectedTail
      obtain ⟨nextNative, _, projectedTail⟩ := bind_ok projectedTail
      obtain ⟨suffixNative, _, projectedTail⟩ := bind_ok projectedTail
      cases projectedTail
      change (do pure (Ty.product (← catalog.project head)
        (← catalog.project (TypeSystem.Ty.productMany (next :: suffix))))) = _
      rw [projectedHead, remaining]
      rfl

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem prepared_outputs {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {specialized : SourceSpecialization.SpecializedFunction} {named : SourceCoreGeneralFunctions.Function}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named) :
    named.signature.key = specialized.key ∧
      representation.expressions.projectType (.declaration specialized.key.declaration)
        specialized.function.inferredBodyType = .ok named.signature.resultType := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (specialized.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged] at accepted
    cases shape : specialized.function.type <;>
      simp only [shape, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted <;>
      try contradiction
    rename_i parameter result
    by_cases mismatch : result ≠ specialized.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨parameterType, _, accepted⟩ := bind_ok accepted
      obtain ⟨resultType, projected, accepted⟩ := bind_ok accepted
      obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
      cases accepted
      have resultEq : result = specialized.function.inferredBodyType := Classical.byContradiction mismatch
      exact ⟨rfl, by simpa only [resultEq] using mapError_ok projected⟩


variable {compiled : SourceCoreUnifiedCompilation.Compiled} {row : SourceSpecialization.SpecializedFunction}
  (prepared : Prepared compiled row)

include prepared

theorem instantiated_of_catalog
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    Dynamic.FunctionInstantiates (Program.ofChecked compiled.sourceProgram)
      (CallableNamedMetadata.instantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) := by
  obtain ⟨request, signature, generic, signatureMember, genericMember, resolved, accepted⟩ := prepared.origin
  exact RecursiveNamedSpecializationValidity.instantiated signatureMember genericMember accepted
    (catalog.function_parameters signature signatureMember).1 range

theorem source_frame_of_catalog
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) (CallableNamedMetadata.instantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view := by
  refine ⟨instantiated_of_catalog prepared catalog range, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · exact congrArg (fun row => row.function.typedBody) prepared.same
  · exact congrArg (fun row => (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row).context) prepared.same
  · exact congrArg (fun row => row.function.typedBody.inputs) prepared.same
  · exact congrArg (fun row => row.function.inferredBodyType) prepared.same
  · change Dynamic.StatementRoots row.function.typedBody.roots prepared.compilation.statements
    simpa only [prepared.same] using RecursiveNamedPreparedSourceFrames.compiled_roots prepared.compilation
  · exact CallableEvidenceEnvironment.resolved_covers rfl prepared.resolved

theorem retained_frame_of_catalog
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) (CallableNamedCanonicalOrder.retainedInstantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view := by
  have frame := source_frame_of_catalog prepared catalog range
  exact ⟨RecursiveNamedRetainedSubstitutionFacts.retained_instantiates frame.instantiated,
    frame.source, frame.context, frame.parameters, frame.result, frame.captured, frame.roots, frame.covers⟩

theorem parameter_pack_of_certificate
    {types : List TypeSystem.Ty} {lexical : SourceSemantics.Context} {facts : BodyFacts}
    (certified : Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      (CallableNamedMetadata.instantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      types lexical facts) :
    prepared.named.signature.parameterType =
      SourceCoreCompatibleCatalog.packTypes (prepared.named.inputs.map Prod.snd) := by
  have raw := Dynamic.MonoBindersExtend.bodyTypes_eq certified.typing.inputs_extend
  have binders := prepared.agreement.parameters
  have sameInputs : row.function.typedBody.inputs = prepared.named.inputs.map Prod.fst := by
    simpa only [RecursiveNamedPublicSpecializationMeaning.Prepared.view,
      RecursiveNamedPreparedSourceFrames.view, prepared.same] using binders
  change row.function.typedBody.inputs.map (fun binder => binder.scheme.body) = types at raw
  rw [sameInputs] at raw
  simp only [List.map_map, Function.comp_def] at raw
  have shape := certified.callable_type
  change row.function.type = .function (TypeSystem.Ty.productMany types) row.function.inferredBodyType at shape
  rw [← raw] at shape
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled prepared.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  have sourceShape : specialized.function.type = .function
      (TypeSystem.Ty.productMany (prepared.named.inputs.map (fun binding => binding.1.scheme.body)))
      specialized.function.inferredBodyType := by
    rw [same.symm.trans prepared.same]
    exact shape
  have projected := RecursiveNamedHeaderParameterProjections.prepared_parameter accepted sourceShape
  have realProjected := CompatibleExpressionReads.projectType_of_accepted projected
  have vector := project_productMany
    (RecursiveNamedPreparedParameterProjections.cached_projected compiled prepared.selected)
  exact Except.ok.inj (realProjected.symm.trans vector)


private theorem outputs : prepared.named.signature.key = row.key ∧
    compiled.compatible.checked.catalog.project prepared.view.resultType = .ok prepared.named.signature.resultType := by
  obtain ⟨specialized, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled prepared.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  obtain ⟨key, result⟩ := prepared_outputs accepted
  have projected := CompatibleExpressionReads.projectType_of_accepted result
  refine ⟨key.trans (congrArg (·.key) (same.symm.trans prepared.same)), ?_⟩
  change compiled.compatible.checked.catalog.project prepared.named.specialized.function.inferredBodyType = _
  rw [same]
  exact projected


theorem header_of_certificate {values : SourceCoreCompatibleValues.Context}
    {types : List TypeSystem.Ty} {context : SourceSemantics.Context} {facts : BodyFacts}
    (certified : Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      (CallableNamedMetadata.instantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      types context facts)
    {instantiation : DeclarationInstantiation}
    (frame : NamedCalls.SourceFrame (Program.ofChecked compiled.sourceProgram) instantiation
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row) prepared.view)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan instantiation =
      .ok prepared.named.signature.key) :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram), HeaderAt prepared instantiation header := by
  have extended : MonoBindersExtend prepared.view.source.owner prepared.view.context
      prepared.view.parameters types context := by
    rw [frame.source, frame.context, frame.parameters]
    exact certified.typing.inputs_extend
  have unique : NodeOccurrencesUnique prepared.view.source := by
    rw [frame.source]
    exact certified.graph_closed.wellFormed.nodeOccurrencesUnique
  have bodyTyped : BodyHasType prepared.view.source context prepared.view.resultType facts := by
    rw [frame.source, frame.result]
    exact certified.typing.body_typed
  have ordinary : ∀ binder, binder ∈ prepared.view.parameters → binder.comptime = false := by
    simpa only [RecursiveNamedPublicSpecializationMeaning.Prepared.view,
      RecursiveNamedPreparedSourceFrames.view, prepared.same] using ordinaryParameters
  have originalLedger : ScopedRequirementLedgerWellFormed prepared.view.context prepared.view.source := by
    simpa only [frame.context, frame.source] using certified.requirement_ledger
  have ledger := (RecursiveNamedInitialContextValidity.mono_fields extended).scopedRequirementLedger originalLedger
  have valid : CompatibleRuntimeContextValidity.Valid
      prepared.named.specialized.function.solvedRequirements context prepared.view.evidence :=
    ⟨(RecursiveNamedInitialContextValidity.mono_fields extended).solvedRequirements,
      ledger.toRuntime, RecursiveNamedInitialContextValidity.covers frame extended⟩
  let header := Header.of_dictionary_body
    (values := values)
    (function := prepared.view) (instantiation := instantiation)
    (sourceBody := RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
    (frame := frame) (named := prepared.named) (agreement := prepared.agreement)
    (ordinaryReturn := by simpa only [prepared.same] using ordinaryReturn)
    (ordinaryParameters := ordinary) (target := target)
    (context := context) (types := types) (bindings := prepared.named.inputs)
    (parameters := prepared.agreement.parameters) (inputs := prepared.agreement.parameters)
    (extended := extended) (solved := prepared.named.specialized.function.solvedRequirements)
    (reasonAt := prepared.diagnostics.reasonAt prepared.named.signature.key)
    (readFuel := compiled.indexed.fuel) (output := prepared.named.signature.resultType)
    (policy := policy prepared) (fuel := compiled.indexed.fuel)
    (fellThrough := prepared.compilation.own.fellThroughReason)
    (escaped := prepared.compilation.own.table.escapedReason)
    (body := prepared.compilation.body) (parameterCode := prepared.compilation.parameterCode)
    (code := prepared.compilation.output) (layouts := compiled.indexed.layouts)
    (owner := prepared.named.signature.key) (active := []) (globals := compiled.indexed.base.globals.length)
    (onError := fun error => .sourceAllocation (reprStr error))
    (acceptedPrefix := prepared.compilation.parametersCompiled) (hook := prepared.compilation.hook)
    (definitions_eq := rfl) (registered := CallableIndexedAmbient.frame_registered compiled.indexed)
    (unique := unique) (parameterType := parameter_pack_of_certificate prepared certified)
    (resultType := rfl) (representation := CallableIndexedNamedGeneration.representation compiled.indexed)
    (compiledFuel := compiled.indexed.fuel) (compiled := compiled.indexed.secondPass)
    (slot := prepared.index) (selected := prepared.selected)
    (cached := prepared.cached.trans (congrArg some prepared.compilation.emitted))
    (valid := valid)
  refine ⟨header, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    prepared.compilation.bodyCompiled, ⟨facts, bodyTyped⟩, (outputs prepared).2⟩


/-- Selected original body typing constructs the retained Header from the same
accepted compiler action, dictionary and complete parameter substitution. -/
theorem retained_header
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key)
    {values : SourceCoreCompatibleValues.Context} :
    ∃ header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram),
      HeaderAt prepared (CallableNamedCanonicalOrder.retainedInstantiation row) header := by
  obtain ⟨types, context, facts, certificate⟩ := bodies.prepared_certificate prepared range
  exact header_of_certificate prepared certificate (retained_frame_of_catalog prepared bodies.signatures range)
    ordinaryReturn ordinaryParameters target

/-- The same instance certificate authenticates all selected diagnostics. -/
theorem diagnostic_typed (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    EmittedDiagnosticTokenPlan.UnaryTyped (CallableIndexedNamedGeneration.source prepared.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (CallableIndexedNamedGeneration.source prepared.named) := by
  obtain ⟨types, context, facts, certificate⟩ := bodies.prepared_certificate prepared range
  have typed := SourceDiagnosticTyping.diagnostic_typed_of_certificate certificate.toBodyInstanceTypingCertificate
  change EmittedDiagnosticTokenPlan.UnaryTyped row.function.typedBody ∧
    AssignmentDiagnosticOrigins.OperandsTyped row.function.typedBody at typed
  simpa only [CallableIndexedNamedGeneration.source, prepared.same] using typed

open CallableIndexedOwnedSelectedDiagnosticIssuerReceipts
open CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies
open CallableIndexedOwnedSelectedNamedHeaderReceipts (reissued reissued_view reason_at)

theorem retained_at_prepared (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    (ordinaryReturn : row.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false)
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok prepared.named.signature.key) :
    ∃ (selected : SelectedReceipt compiled prepared.named prepared.index)
      (header : CallableIndexedOwnedFunctionValues.Header compiled
        (Program.ofChecked compiled.sourceProgram)),
      RecursiveNamedPreparedHeaders.Prepared.HeaderAt (reissued prepared selected)
        (CallableNamedCanonicalOrder.retainedInstantiation row) header ∧
      header.function = prepared.view ∧ header.reasonAt = reasonAt selected := by
  obtain ⟨selected⟩ := at_selected prepared.selected (diagnostic_typed prepared bodies range)
  obtain ⟨header, aligned⟩ :=
    retained_header
      (reissued prepared selected) bodies range ordinaryReturn ordinaryParameters target
  exact ⟨selected, header, aligned, aligned.function.trans (reissued_view prepared selected),
    reason_at prepared selected aligned⟩


/-- Every authentic retained Header keeps a complete instance certificate at
its own parameter row and lexical context. -/
theorem certificate_at
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution)
    {values : SourceCoreCompatibleValues.Context}
    {header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram)}
    (aligned : HeaderAt prepared (CallableNamedCanonicalOrder.retainedInstantiation row) header) :
    ∃ facts, Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      header.instantiation header.sourceBody header.types header.context facts := by
  obtain ⟨types, context, facts, certificate⟩ := bodies.prepared_certificate prepared range
  have retained : Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      (CallableNamedCanonicalOrder.retainedInstantiation row)
      (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row)
      types context facts :=
    { certificate.toBodyInstanceTypingCertificate with callable_type := certificate.callable_type }
  rw [← aligned.metadata, ← aligned.sourceBody] at retained
  have extended : MonoBindersExtend header.sourceBody.source.owner header.sourceBody.context
      header.sourceBody.source.inputs header.types header.context := by
    simpa only [header.frame.source, header.frame.context, header.frame.parameters] using header.extended
  have typesEq : header.types = types :=
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended).symm.trans
      (Dynamic.MonoBindersExtend.bodyTypes_eq retained.typing.inputs_extend)
  have contextEq : header.context = context :=
    Dynamic.MonoBindersExtend.functional extended retained.typing.inputs_extend
  rw [typesEq, contextEq]
  exact ⟨facts, retained⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationHeaders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
open Core Frontend SourceInference TypeSystem
open RecursiveNamedPublicSpecializationMeaning (Origin Prepared)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Eligible Catalog)
open CallableIndexedOwnedPreparedOrdinaryCachedInputs
  (cached_record cached_key cached_slot of_cached_origin_at)

private theorem bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) :
    ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem reject_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then .error error else action) = .ok value) :
    action = .ok value := by
  split at accepted
  · cases accepted
  · exact accepted


private theorem specialization_key {signature : ProgramFunctionSignature}
    {generic : CheckedFunction} {supplied : ParameterSubstitution}
    {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok row) :
    row.key = ⟨row.declaration, row.parameterSubstitution.map Prod.snd⟩ := by
  unfold SourceSpecialization.specializeFunction at accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  have accepted := reject_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨canonical, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  cases analysis : SourceStageAnalysis.analyzeFunction
      (SourceSpecialization.applyCheckedFunction canonical generic) with
  | error error => simp only [analysis] at accepted; cases accepted
  | ok stages =>
      simp only [analysis, pure, Except.pure, bind, Except.bind,
        Except.ok.injEq] at accepted
      subst row
      rfl


private theorem filter_key {α β : Type} [DecidableEq β]
    (key : α → β) {items : List α} (unique : (items.map key).Nodup)
    {item : α} (member : item ∈ items) :
    items.filter (fun candidate => decide (key candidate = key item)) = [item] := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | member
      · subst item
        have empty : tail.filter (fun candidate => decide (key candidate = key head)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro candidate found
          simp only [decide_eq_true_eq]
          intro same
          exact absent (List.mem_map.mpr ⟨candidate, found, same⟩)
        simp [empty]
      · have different : key head ≠ key item := by
          intro same
          exact absent (List.mem_map.mpr ⟨item, member, same.symm⟩)
        simpa [different] using ih tailUnique member

private theorem substitution_self {substitution : ParameterSubstitution}
    (unique : (substitution.map Prod.fst).Nodup) :
    SourceCompilationPlan.parameterSubstitutionsEquivalent substitution substitution = true := by
  have each : ∀ entry ∈ substitution,
      SourceCompilationPlan.exactParameterBinding? substitution entry.1 = some entry.2 := by
    intro entry member
    have one := filter_key Prod.fst unique member
    have same : (fun candidate : TypeParameterId × TypeSystem.Ty => candidate.1 == entry.1) =
        (fun candidate => decide (candidate.1 = entry.1)) := by
      funext candidate
      exact Bool.eq_iff_iff.mpr (by simp)
    simp only [SourceCompilationPlan.exactParameterBinding?, same, one]
  simp only [SourceCompilationPlan.parameterSubstitutionsEquivalent, beq_self_eq_true,
    Bool.true_and, Bool.and_self]
  exact List.all_eq_true.mpr (fun entry member => by rw [each entry member]; simp)

private theorem function_impl_ne {program : CheckedProgram}
    (catalog : SignatureCatalogWellFormed program.signatures)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    {implementation : ProgramImplementationSignature}
    (implMember : implementation ∈ program.signatures.implementations) :
    signature.id ≠ implementation.id := by
  have unique := catalog.declaration_ids
  simp only [signatureDeclarationIds] at unique
  have separated := (List.nodup_append.mp (List.nodup_append.mp unique).1).2.2
  apply separated signature.id
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨signature, member, rfl⟩)))
    implementation.id (List.mem_map.mpr ⟨implementation, implMember, rfl⟩)

/-- A final row naming a real function signature is an ordinary request even
when it was discovered below an implementation-method root. -/
theorem ordinary_origin (compiled : SourceCoreUnifiedCompilation.Compiled)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.indexed.base.plan.specializations)
    {signature : ProgramFunctionSignature}
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (declaration : row.declaration = signature.id) : Origin compiled.sourceProgram row := by
  have tagged := CallablePreparedFinalCatalogOrigins.of_default_preparation
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) row member
  cases tagged with
  | ordinary origin => exact origin
  | method selected =>
      have identities := RecursiveNamedSpecializationBodyFacts.identities selected.specialized
      have owner := identities.2.2.trans identities.1.symm
      exact False.elim (function_impl_ne catalog signatureMember selected.implementationMember
        (declaration.symm.trans owner))

private theorem origin_signature {program : CheckedProgram}
    {row : SourceSpecialization.SpecializedFunction} (origin : Origin program row) :
    ∃ signature ∈ program.signatures.functions,
      row.declaration = signature.id ∧
      row.parameterSubstitution.map Prod.fst = signature.scheme.parameters ∧
      row.key = ⟨row.declaration, row.parameterSubstitution.map Prod.snd⟩ ∧
      row.function.declaration = row.declaration ∧
      row.function.typedBody.owner = row.declaration := by
  obtain ⟨request, signature, generic, member, _, _, accepted⟩ := origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have fields := CallableCoercionBodyProvenance.specialization_fields accepted
  refine ⟨signature, member, identities.2.2.trans identities.1.symm,
    SourceSpecialization.specializeFunction_parameterDomain accepted, specialization_key accepted, ?_, ?_⟩
  · rw [fields.1, SourceSpecialization.applyCheckedFunction_declaration, identities.2.2]
  · rw [fields.1, SourceSpecialization.applyCheckedFunction_bodyOwner, identities.2.1, identities.2.2]

private theorem exact_filter {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    plan.specializations.filter (fun candidate => decide (candidate.key = key)) = [row] := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try cases accepted
  assumption


theorem retained_target (compiled : SourceCoreUnifiedCompilation.Compiled)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (origin : Origin compiled.sourceProgram named.specialized) :
    SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation named.specialized) = .ok named.signature.key := by
  obtain ⟨signature, signatureMember, declaration, domain, key, functionOwner, sourceOwner⟩ :=
    origin_signature origin
  have domainUnique : (named.specialized.parameterSubstitution.map Prod.fst).Nodup :=
    domain ▸ (catalog.function_parameters signature signatureMember).1
  have selfMatch : SourceCompilationPlan.specializationMatchesInstantiation named.specialized
      (CallableNamedMetadata.instantiation named.specialized) = true := by
    simp [SourceCompilationPlan.specializationMatchesInstantiation,
      SourceCompilationPlan.specializationOwnershipCoherent, CallableNamedMetadata.instantiation,
      key, functionOwner, sourceOwner, decide_true,
      substitution_self domainUnique, Bool.and_self]
  have sameFilter : compiled.indexed.base.plan.specializations.filter
      (fun candidate => SourceCompilationPlan.specializationMatchesInstantiation candidate
        (CallableNamedMetadata.instantiation named.specialized)) = [named.specialized] := by
    rw [← exact_filter (cached_record compiled selected)]
    apply List.filter_congr
    intro candidate member
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro matched
      have matchedFields := CallableNamedMetadata.matches_of_checked matched
      have candidateOrigin := ordinary_origin compiled catalog member signatureMember
        (matchedFields.declaration.trans declaration)
      obtain ⟨other, otherMember, otherDeclaration, otherDomain, otherKey, _, _⟩ :=
        origin_signature candidateOrigin
      have sameSignature : other = signature := by
        have unique := catalog.function_ids
        have sameId := otherDeclaration.symm.trans (matchedFields.declaration.trans declaration)
        have retained : other ∈ compiled.sourceProgram.signatures.functions.filter
            (fun candidate => decide (candidate.id = signature.id)) :=
          List.mem_filter.mpr ⟨otherMember, by simpa using sameId⟩
        rw [filter_key (·.id) unique signatureMember] at retained
        exact List.mem_singleton.mp retained
      subst other
      have sameSubstitution := CallableNamedMetadata.substitution_eq_of_domain
        matchedFields.substitution (otherDomain.trans domain.symm)
      simp only [decide_eq_true_eq]
      rw [otherKey, matchedFields.declaration, sameSubstitution]
      change (⟨named.specialized.declaration, named.specialized.parameterSubstitution.map Prod.snd⟩ :
        SourceCompilationPlan.Key) = named.signature.key
      rw [← key, cached_key compiled selected]
    · intro accepted
      have sameKey : candidate.key = named.signature.key := of_decide_eq_true accepted
      have retained : candidate ∈ compiled.indexed.base.plan.specializations.filter
          (fun row => decide (row.key = named.signature.key)) :=
        List.mem_filter.mpr ⟨member, by simpa using sameKey⟩
      rw [exact_filter (cached_record compiled selected)] at retained
      have same : candidate = named.specialized := List.mem_singleton.mp retained
      simpa only [same] using selfMatch
  change SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
    (CallableNamedReversal.instantiation (CallableNamedMetadata.instantiation named.specialized)) = _
  rw [CallableNamedReversal.target_reverse]
  simp only [SourceCompilationPlan.exactInstantiationKey, sameFilter, cached_key compiled selected]


theorem of_cached (compiled : SourceCoreUnifiedCompilation.Compiled)
    (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (origin : Origin compiled.sourceProgram named.specialized)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) named.specialized.parameterSubstitution)
    (ordinaryReturn : named.specialized.function.returnComptime = false)
    (ordinaryParameters : ∀ binder, binder ∈ named.specialized.function.typedBody.inputs →
      binder.comptime = false) :
    ∃ input : Input compiled, input.row = named.specialized ∧
      input.prepared.index = index ∧ input.prepared.named = named := by
  obtain ⟨prepared, indexEq, namedEq⟩ := of_cached_origin_at compiled selected rfl origin
  let input : Input compiled := {
    row := named.specialized
    prepared := prepared
    range := range
    ordinaryReturn := ordinaryReturn
    ordinaryParameters := ordinaryParameters
    target := by rw [namedEq]; exact retained_target compiled catalog selected origin
    slot := by rw [indexEq, namedEq]; exact cached_slot compiled selected }
  exact ⟨input, rfl, indexEq, namedEq⟩

theorem exists_issued {compiled : SourceCoreUnifiedCompilation.Compiled}
    (input : Input compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled) :
    Nonempty (Issued input) := by
  obtain ⟨selected, header, aligned, function, reason⟩ :=
    SelectedCompilationHeaders.retained_at_prepared input.prepared
      bodies input.range input.ordinaryReturn input.ordinaryParameters input.target
  have named : header.named = input.prepared.named := aligned.named
  have slot : header.slot = input.prepared.index := aligned.slot
  have specialized : header.named.specialized = input.row :=
    (congrArg (·.specialized) named).trans input.prepared.same
  have metadata : header.instantiation =
      CallableNamedReversal.instantiation (CallableNamedMetadata.instantiation header.named.specialized) := by
    rw [aligned.metadata, specialized]
    rfl
  have target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation header.named.specialized) = .ok header.named.signature.key := by
    rw [← CallableNamedReversal.target_reverse, ← metadata]
    exact header.target
  have resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment
      compiled.indexed.base.sourceProgram header.named.signature.key header.named.specialized.assumptions =
      .ok input.prepared.available := by
    rw [(SourceCoreUnifiedPreparationCertificates.compiled_fields compiled).1, named,
      RecursiveNamedPreparedCallEvidence.Prepared.signature_key input.prepared, input.prepared.same]
    exact input.prepared.resolved
  have row : CallableIndexedNamedValues.Row compiled.indexed header.slot header.named.signature
      header.named.specialized input.prepared.available :=
    ⟨by simpa only [slot, named] using input.slot,
      CallableIndexedActualNamedSourceReceipts.header_record compiled header, target, resolved⟩
  have dictionary : header.function.evidence =
      (CallableNamedMetadata.global header.named.specialized input.prepared.available).evidence := by
    rw [function]
    rfl
  exact ⟨⟨selected, header, aligned, function, reason,
    CallableIndexedOwnedFunctionValues.NamedSourceAt.of_retained_header row metadata dictionary⟩⟩

theorem inventory {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (inputs : List (Input compiled)) : Nonempty (Inventory inputs) := by
  induction inputs with
  | nil => exact ⟨.nil⟩
  | cons input inputs tail =>
      obtain ⟨packet⟩ := exists_issued input bodies
      obtain ⟨rest⟩ := tail
      exact ⟨.cons packet rest⟩

theorem collect (compiled : SourceCoreUnifiedCompilation.Compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (receipt : ∀ index named, compiled.indexed.base.functions[index]? = some named →
      Eligible compiled named.specialized →
      ∃ input : Input compiled, input.row = named.specialized ∧
        input.prepared.index = index ∧ input.prepared.named = named) :
    Nonempty (Catalog compiled) := by
  classical
  let functions := compiled.indexed.base.functions
  let positions : List (Fin functions.length) := (List.finRange functions.length).filter
    (fun position => decide (Eligible compiled functions[position.val].specialized))
  have admittedPosition : ∀ position ∈ positions, Eligible compiled functions[position.val].specialized := by
    intro position member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  have available : ∀ position : {position // position ∈ positions},
      ∃ input : Input compiled, input.row = functions[position.val.val].specialized ∧
        input.prepared.index = position.val.val ∧ input.prepared.named = functions[position.val.val] := by
    intro position
    exact receipt position.val.val functions[position.val.val]
      (List.getElem?_eq_getElem position.val.isLt) (admittedPosition position.val position.property)
  let choose := fun position => Classical.choose (available position)
  have chosen := fun position => Classical.choose_spec (available position)
  let inputs := positions.attach.map choose
  have indices : inputs.map (fun input => input.prepared.index) = positions.map Fin.val := by
    calc
      _ = positions.attach.map (fun position => position.val.val) := by
        simp only [inputs, List.map_map]
        exact List.map_congr_left (fun position _ => (chosen position).2.1)
      _ = positions.map Fin.val := List.attach_map_val
  obtain ⟨rows⟩ := inventory bodies inputs
  refine ⟨{ inputs := inputs, rows := rows, distinct := ?_, admitted := ?_, covered := ?_ }⟩
  · rw [indices]
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp (fun different equal => different (Fin.ext equal))
      (List.Pairwise.filter _ (List.nodup_finRange functions.length))
  · intro input member
    obtain ⟨position, _member, rfl⟩ := List.mem_map.mp member
    rw [(chosen position).1]
    exact admittedPosition position.val position.property
  · intro index named selected eligible
    obtain ⟨bound, namedEq⟩ := List.getElem?_eq_some_iff.mp selected
    have namedAt : functions[index] = named := namedEq
    let position : Fin functions.length := ⟨index, bound⟩
    have present : position ∈ positions := by
      apply List.mem_filter.mpr
      exact ⟨List.mem_finRange position, by simpa only [position, namedAt, decide_eq_true_eq] using eligible⟩
    let attached : {position // position ∈ positions} := ⟨position, present⟩
    refine ⟨choose attached, List.mem_map.mpr ⟨attached, List.mem_attach _ _, rfl⟩,
      (chosen attached).2.1, ?_⟩
    exact (chosen attached).2.2.trans namedEq


/-- The complete actual cache issues the existing automatic catalog using
only selected original body typing and unchanged global signature identities. -/
theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled) : Nonempty (Catalog compiled) := by
  apply collect compiled bodies
  intro index named selected eligible
  exact of_cached compiled bodies.signatures selected eligible.origin eligible.range
    eligible.ordinaryReturn eligible.ordinaryParameters

/-- Every member of the unchanged inventory has the complete static instance
certificate at its own exact source body, parameter row and context. -/
theorem certificates {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    (header : CallableIndexedOwnedPreparedFiniteNamedInventories.Header compiled)
    (member : header ∈ headers rows) :
    ∃ facts, Dynamic.FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      header.instantiation header.sourceBody header.types header.context facts := by
  obtain ⟨input, packet, retained, same⟩ := rows.mem_headers header member
  subst header
  exact SelectedCompilationHeaders.certificate_at
    (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
    bodies input.range packet.aligned

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalOrigins
/-! Actual compilation retains the exact source and binder origins of every
prepared local instance, including instances selected at a lexical context. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalOrigins
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open PreparedLocalInstanceOrigins

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok output := by
  cases action with
  | error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ}
    {value : α} (accepted : action.mapError change = .ok value) : action = .ok value := by
  cases action with
  | error => cases accepted
  | ok result => cases accepted; rfl

theorem of_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base) :
    CatalogOrigins base.locals := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, prepared, accepted⟩ := bind_ok accepted
  have origins := PreparedLocalInstanceOrigins.of_preparation (mapError_ok prepared)
  change CatalogOrigins locals at origins
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    exact origins
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨assigned, decorated, accepted⟩ := bind_ok accepted
      have origins := PreparedLocalInstanceOrigins.with_contracts origins (mapError_ok decorated)
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact origins
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact origins

theorem of_automatic {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic) :
    CatalogOrigins automatic.prepared.locals := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, prepared, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog prepared

theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled) :
    CatalogOrigins compiled.indexed.base.locals := by
  have origins := of_automatic compiled.compatiblePrepared
  have same := SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared
  rw [same]
  exact origins

/-- The actual compiler, exact binding lookup and lexical context provide the
candidate origins. No independent whole-catalog property is required. -/
theorem at_context (compiled : SourceCoreUnifiedCompilation.Compiled)
    {caller : Key} {binder : Resolved.LocalId} {binding : Binding}
    {active : Substitution} {candidate : Instance}
    (located : compiled.indexed.base.locals.binding caller binder = .ok binding)
    (member : candidate ∈ binding.atContext active) :
    candidate.origin.caller = caller ∧ candidate.origin.source = binding.source ∧
      candidate.origin.binder = binding.binder ∧ candidate.origin.initializer = binding.initializer :=
  PreparedLocalInstanceOrigins.at_context (of_compiled compiled) located member

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalOrigins
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalMetadata
/-! The actual public compilation retains the successful preparation needed to
authenticate contextual local lambdas. An arbitrary indexed artifact does not
by itself retain this preparation equation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalMetadata
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open PreparedLocalInstanceMetadata

def projection (checked : SourceCoreCompatibleCatalog.Checked) (type : Ty) :
    Except SourceCoreLocalPolymorphism.Error Core.Ty :=
  (checked.project type).map (·.type) |>.mapError fun
    | .catalog error => .projection error
    | .metadata _ => .projection (.unsupportedType type)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok output := by
  cases action with
  | error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ}
    {value : α} (accepted : action.mapError change = .ok value) : action = .ok value := by
  cases action with
  | error => cases accepted
  | ok result => cases accepted; rfl

theorem of_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base) :
    CatalogMetadata (projection checked) base.locals := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, prepared, accepted⟩ := bind_ok accepted
  have metadata := PreparedLocalInstanceMetadata.of_preparation (mapError_ok prepared)
  change CatalogMetadata (projection checked) locals at metadata
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    exact metadata
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨assigned, decorated, accepted⟩ := bind_ok accepted
      have metadata := PreparedLocalInstanceMetadata.with_contracts metadata (mapError_ok decorated)
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact metadata
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact metadata

theorem of_automatic {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic) :
    CatalogMetadata (projection automatic.checked) automatic.prepared.locals := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, prepared, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog prepared

theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled) :
    CatalogMetadata (projection compiled.compatible.checked) compiled.indexed.base.locals := by
  have metadata := of_automatic compiled.compatiblePrepared
  have same := SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared
  rw [same]
  exact metadata

/-- The actual compiler, exact binding lookup and lexical context provide the
candidate metadata. No independent whole-catalog property is required. -/
theorem at_context (compiled : SourceCoreUnifiedCompilation.Compiled)
    {caller : Key} {binder : Resolved.LocalId} {binding : Binding}
    {active : Substitution} {candidate : Instance}
    (located : compiled.indexed.base.locals.binding caller binder = .ok binding)
    (member : candidate ∈ binding.atContext active) :
    candidate.origin.caller = caller ∧ candidate.origin.binder.id = binder ∧
      Metadata (projection compiled.compatible.checked) candidate :=
  PreparedLocalInstanceMetadata.at_context (of_compiled compiled) located member

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalMetadata
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceSignatureFacts
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceSignatureFacts
open Frontend SourceInference RecursiveNamedCatalog
open CallableIndexedOwnedPreparedFiniteNamedInventories
open CallableIndexedOwnedPreparedOrdinaryCachedInputs

theorem instance_shape_of_valid {program : Program} {instantiation : SourceInference.DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {signature : ProgramFunctionSignature}
    (catalog : SignatureCatalogWellFormed program.signatures)
    (owners : (program.functions.map fun definition => definition.body.owner).Nodup)
    {chosen : FunctionDefinition} (chosenMember : chosen ∈ program.functions)
    (chosenOwner : chosen.body.owner = instantiation.declaration)
    (chosenValid : FunctionDefinition.Valid program.signatures chosen)
    (member : signature ∈ program.signatures.functions)
    (selected : instantiation.declaration = signature.id)
    (instantiated : Dynamic.FunctionInstantiates program instantiation body) :
    body.source.inputs.map (fun binder => binder.scheme.body) =
      signature.parameterTypes.map instantiation.parameterSubstitution.apply ∧
    body.resultType = instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) := by
  cases instantiated with
  | @intro actual definition _ actualMember definitionMember actualSelected owner valid sourceEq resultEq contextEq =>
    have actualEq : actual = signature := StructuralSubstitution.eq_of_mem_of_mapped_nodup
      catalog.function_ids actualMember member (actualSelected.symm.trans selected)
    subst actual
    have same : chosen = definition := StructuralSubstitution.eq_of_mem_of_mapped_nodup
      owners chosenMember definitionMember
        (chosenOwner.trans (actualSelected.trans owner.symm))
    subst chosen
    cases chosenValid with
    | @intro declared facts declaredMember declaredOwner bodyTyped =>
      have declaredEq : declared = signature := StructuralSubstitution.eq_of_mem_of_mapped_nodup
        catalog.function_ids declaredMember member (declaredOwner.symm.trans owner)
      subst declared
      cases bodyTyped with
      | intro _ _ _ _ _ declaredResult _ _ _ extended _ _ _ _ _ _ =>
        refine ⟨?_, resultEq.trans (congrArg instantiation.parameterSubstitution.apply declaredResult)⟩
        have inputs := congrArg (List.map instantiation.parameterSubstitution.apply) extended.bodyTypes_eq
        simpa only [sourceEq, StructuralSubstitution.applyTypedSource, StructuralSubstitution.applyBinder,
          StructuralSubstitution.applyScheme, List.map_map, Function.comp_def] using inputs


/-- Source argument order and result of this exact selected Header. -/
def Shape {checked : CallableAncestryPairedLookup.Checked}
    {base : CallableAncestryPairedLookup.Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context} {definitions : Core.DataEnvironment} {program : Program}
    (header : RecursiveNamedCatalog.Header prepared values definitions program) : Prop :=
  ∀ signature ∈ program.signatures.functions,
    header.instantiation.declaration = signature.id →
      signature.parameterTypes.map header.instantiation.parameterSubstitution.apply =
        header.bindings.map (fun binding => binding.1.scheme.body) ∧
      header.instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) =
        header.function.resultType

theorem header_shape
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {values : SourceCoreCompatibleValues.Context}
    {header : Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
      (CallableNamedCanonicalOrder.retainedInstantiation row) header)
    {signature : ProgramFunctionSignature} (member : signature ∈ compiled.sourceProgram.signatures.functions)
    (selected : header.instantiation.declaration = signature.id) :
    signature.parameterTypes.map header.instantiation.parameterSubstitution.apply =
      header.bindings.map (fun binding => binding.1.scheme.body) ∧
    header.instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) =
      header.function.resultType := by
  obtain ⟨request, original, generic, originalMember, genericMember, resolved, accepted⟩ := prepared.origin
  have valid := bodies.ordinary generic
    ⟨prepared.index, prepared.named, original, request.parameterSubstitution, prepared.selected,
      originalMember, genericMember, by simpa only [prepared.same] using accepted⟩
  have owner : (FunctionDefinition.ofChecked generic).body.owner = header.instantiation.declaration := by
    rw [aligned.metadata]
    exact ((RecursiveNamedSpecializationBodyFacts.identities accepted).2.2).symm
  have shape := instance_shape_of_valid bodies.signatures bodies.function_ids
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩) owner valid member selected header.frame.instantiated
  have inputs : header.bindings.map (fun binding => binding.1.scheme.body) =
      header.sourceBody.source.inputs.map (fun binder => binder.scheme.body) := by
    have parameters := congrArg (List.map (fun binder => binder.scheme.body))
      (header.parameters.symm.trans header.frame.parameters)
    simpa only [List.map_map, Function.comp_def] using parameters
  exact ⟨shape.1.symm.trans inputs.symm, shape.2.symm.trans header.frame.result.symm⟩

theorem inventory_shape {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {inputs : List (Input compiled)}
    (rows : Inventory inputs)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (included : header ∈ headers rows)
    {signature : ProgramFunctionSignature} (member : signature ∈ compiled.sourceProgram.signatures.functions)
    (selected : header.instantiation.declaration = signature.id) :
    signature.parameterTypes.map header.instantiation.parameterSubstitution.apply =
      header.bindings.map (fun binding => binding.1.scheme.body) ∧
    header.instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) =
      header.function.resultType := by
  obtain ⟨input, packet, _, same⟩ := rows.mem_headers header included
  subst header
  exact header_shape (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected)
    bodies packet.aligned member selected

theorem Shape.of_prepared
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {values : SourceCoreCompatibleValues.Context}
    {header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values compiled.indexed.layouts.definitions
      (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
      (CallableNamedCanonicalOrder.retainedInstantiation row) header) : Shape header := by
  intro signature member selected
  exact header_shape prepared bodies aligned member selected

theorem Shape.of_inventory {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    (header : CallableIndexedOwnedPreparedFiniteNamedInventories.Header compiled)
    (included : header ∈ headers rows) : Shape header := by
  intro signature member selected
  exact inventory_shape bodies rows header included member selected

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceSignatureFacts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryGlobals
/-! Authentic registry scopes select cached original definitions. Successful
checking supplies the source-owner equality for the invoked definition. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryGlobals
open Frontend SourceInference TypeSystem SourceCoreStageContracts
open Solcore.SourceSemantics.Dynamic

theorem exact_member {plan : Plan} {key : Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected <;> try contradiction
  rename_i actual found
  cases selected
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [found]
    simp
  exact (List.mem_filter.mp member).1

theorem sidecar_metadata {plan : Plan} {key : Key} {sidecar : Sidecar}
    (accepted : prepareSidecar plan key = .ok sidecar) :
    SourceCompilationPlan.validateSpecializationMetadataWith true sidecar.caller = .ok () := by
  unfold prepareSidecar at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan key with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    cases valid : SourceCompilationPlan.validateSpecializationMetadataWith true caller with
    | error error => simp [valid, Functor.discard, Functor.mapConst, Except.map] at accepted
    | ok value =>
      cases value
      simp only [valid] at accepted
      dsimp [Functor.discard, Functor.mapConst, Except.map] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted; exact valid
        · cases accepted

theorem sidecar_owners {plan : Plan} {key : Key} {sidecar : Sidecar}
    (accepted : prepareSidecar plan key = .ok sidecar) :
    sidecar.caller.key.declaration = sidecar.caller.declaration ∧
      sidecar.caller.function.typedBody.owner = sidecar.caller.declaration := by
  have valid := sidecar_metadata accepted
  have coherent : SourceCompilationPlan.specializationOwnershipCoherent sidecar.caller = true := by
    by_cases same : SourceCompilationPlan.specializationOwnershipCoherent sidecar.caller = true
    · exact same
    · simp [SourceCompilationPlan.validateSpecializationMetadataWith, same, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at valid
  have fields := of_decide_eq_true coherent
  exact ⟨fields.1, fields.2.2⟩

theorem selected_owner {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    {function : Dynamic.Closure} {scope : Staging.Recursive.Scope}
    (selected : RecursiveNamedPreparedStageScopes.Selected compiled native function scope) :
    ∃ row ∈ compiled.indexed.base.plan.specializations,
      function.source.owner = row.declaration := by
  cases selected with
  | anonymous receipt =>
    obtain ⟨sidecar, active, prepared, rfl, owner⟩ := receipt.original
    exact ⟨sidecar.caller, exact_member (LambdaSourceAlignment.sidecar_lookup prepared),
      owner.trans (sidecar_owners prepared).1⟩
  | named prepared sidecar issued same =>
    refine ⟨sidecar.caller, exact_member (LambdaSourceAlignment.sidecar_lookup issued), ?_⟩
    change prepared.named.specialized.function.typedBody.owner = sidecar.caller.declaration
    rw [prepared.same, ← same]
    exact (sidecar_owners issued).2
  | method selection statements sidecar issued same =>
    refine ⟨sidecar.caller, exact_member (LambdaSourceAlignment.sidecar_lookup issued), ?_⟩
    simpa only [same, Staging.Recursive.methodView, Staging.Recursive.globalView,
      CallableCoercionMethodInstantiation.bodyInstance] using (sidecar_owners issued).2

theorem ordinary_certificate {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.indexed.base.plan.specializations)
    {instantiation : DeclarationInstantiation} {body : BodyInstance}
    (instantiates : FunctionInstantiates (Program.ofChecked compiled.sourceProgram) instantiation body)
    (owner : body.source.owner = row.declaration) :
    ∃ inputTypes lexicalContext facts,
      FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        instantiation body inputTypes lexicalContext facts := by
  have sourceOwner : body.source.owner = instantiation.declaration := by
    cases instantiates with
    | @intro signature definition _ signatureMember definitionMember declarationEq
        ownerEq _ sourceEq _ _ =>
      obtain ⟨generic, genericMember, rfl⟩ := List.mem_map.mp definitionMember
      obtain ⟨_, _, header⟩ := checkedFunctionHeaderWellFormed_ofCheckProgram checked genericMember
      simpa [sourceEq, StructuralSubstitution.applyTypedSource, FunctionDefinition.ofChecked,
        BodyDefinition.ofChecked] using header.source_owner.trans (ownerEq.trans declarationEq.symm)
  have signature : ∃ signature ∈ compiled.sourceProgram.signatures.functions,
      row.declaration = signature.id := by
    cases instantiates with
    | intro signatureMember _ declarationEq _ _ _ _ _ =>
      exact ⟨_, signatureMember, owner.symm.trans (sourceOwner.trans declarationEq)⟩
  obtain ⟨signature, signatureMember, declaration⟩ := signature
  have origin := SelectedCompilationCatalog.ordinary_origin compiled bodies.signatures member signatureMember declaration
  obtain ⟨request, selectedSignature, generic, selectedSignatureMember, genericMember, _, accepted⟩ := origin
  obtain ⟨cached⟩ := CallablePreparedMethodSelection.cached_row compiled member
  have valid := bodies.ordinary generic
    ⟨cached.index, cached.named, selectedSignature, request.parameterSubstitution, cached.selected,
      selectedSignatureMember, genericMember, by simpa only [cached.same] using accepted⟩
  have genericOwner : (FunctionDefinition.ofChecked generic).body.owner = instantiation.declaration := by
    exact (RecursiveNamedSpecializationBodyFacts.identities accepted).2.2.symm.trans
      (owner.symm.trans sourceOwner)
  exact instantiates.certificate_of_valid bodies.signatures bodies.function_ids
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩) genericOwner valid

theorem globals {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram) :
    Staging.Recursive.SelectedPreservation.GlobalBodiesTyped
      (Program.ofChecked compiled.sourceProgram) (RecursiveNamedPreparedStageScopes.registry actual) := by
  intro instantiation body evidence roots scope instantiates _ selected
  obtain ⟨row, member, owner⟩ := selected_owner selected
  exact ordinary_certificate bodies checked member instantiates owner

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryGlobals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedTargetInversion
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedTargetInversion
open Frontend SourceInference Staging.Recursive

variable {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {place : PlaceResolution} {target : Dynamic.ResolvedPlace}
  {size : Nat} {reason : Dynamic.SemanticFault}

/-- The actual projection derivation supplies its ordered key row and snapshot. -/
theorem resolved
    (trace : SourceExecutionSize.SourcePlaceResolves program size context evidence source environment before place target after) :
    ∃ keySize values, keySize < size ∧
      SourceExecutionSize.ExpressionsEvaluate program keySize context evidence source environment before
        (ProjectedTarget.keys place.projections) values after ∧
      ProjectedTarget.Snapshot environment before after place values target := by
  cases trace with
  | intro lookup initialRead projections currentRead initialValue selection =>
      obtain ⟨values, keySize, shaped, keys, bound⟩ := RecursiveNamedPlaceKeyContracts.projections_values projections
      refine ⟨keySize, values, Nat.lt_of_le_of_lt bound (SourceExecutionSize.child_lt_stepSize (by simp)), ?_,
        .intro lookup initialRead (ProjectedTarget.Values.of_data shaped) currentRead initialValue selection⟩
      simpa only [ProjectedTarget.keys_eq_sourceKeys] using keys

/-- No earlier fault is replaced by a getter or RHS result. -/
theorem failed
    (trace : SourceExecutionSize.SourcePlaceFaults program size context evidence source environment before place reason after) :
    (after = before ∧ ProjectedTarget.RootFault environment before place reason) ∨
    (∃ keySize, keySize < size ∧ ProjectedTarget.RootReady environment before place ∧
      SourceExecutionSize.ExpressionsFault program keySize context evidence source environment before
        (ProjectedTarget.keys place.projections) reason after) ∨
    (∃ keySize values, keySize < size ∧
      SourceExecutionSize.ExpressionsEvaluate program keySize context evidence source environment before
        (ProjectedTarget.keys place.projections) values after ∧
      ProjectedTarget.GetterFault environment before after place values reason) := by
  cases trace with
  | unbound missing => exact .inl ⟨rfl, .unbound missing⟩
  | dangling lookup missing => exact .inl ⟨rfl, .dangling lookup missing⟩
  | projectionExpression lookup read fault =>
      obtain ⟨keySize, keys, bound⟩ := RecursiveNamedPlaceKeyContracts.projections_fault fault
      exact .inr (.inl ⟨keySize, Nat.lt_of_le_of_lt bound (SourceExecutionSize.child_lt_stepSize (by simp)),
        .intro lookup read, by simpa only [ProjectedTarget.keys_eq_sourceKeys] using keys⟩)
  | danglingAfterProjections lookup read projections missing =>
      obtain ⟨values, keySize, shaped, keys, bound⟩ := RecursiveNamedPlaceKeyContracts.projections_values projections
      exact .inr (.inr ⟨keySize, values, Nat.lt_of_le_of_lt bound (SourceExecutionSize.child_lt_stepSize (by simp)),
        by simpa only [ProjectedTarget.keys_eq_sourceKeys] using keys,
        .dangling lookup read (ProjectedTarget.Values.of_data shaped) missing⟩)
  | projectionRead lookup initialRead projections currentRead initialValue fault =>
      obtain ⟨values, keySize, shaped, keys, bound⟩ := RecursiveNamedPlaceKeyContracts.projections_values projections
      exact .inr (.inr ⟨keySize, values, Nat.lt_of_le_of_lt bound (SourceExecutionSize.child_lt_stepSize (by simp)),
        by simpa only [ProjectedTarget.keys_eq_sourceKeys] using keys,
        .projection lookup initialRead (ProjectedTarget.Values.of_data shaped) currentRead initialValue fault⟩)
  | uninitialized lookup initialRead projections currentRead empty notMapping nonempty =>
      obtain ⟨values, keySize, shaped, keys, bound⟩ := RecursiveNamedPlaceKeyContracts.projections_values projections
      exact .inr (.inr ⟨keySize, values, Nat.lt_of_le_of_lt bound (SourceExecutionSize.child_lt_stepSize (by simp)),
        by simpa only [ProjectedTarget.keys_eq_sourceKeys] using keys,
        .uninitialized lookup initialRead (ProjectedTarget.Values.of_data shaped) currentRead empty notMapping nonempty⟩)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedTargetInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionLiftBounds
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionLiftBounds
open Frontend SourceInference
open Staging.Recursive.Lifting (Adapted)

inductive RawOutcome (program : Program) (size : Nat) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (form : ExpressionForm)
    (requirements : List RequirementId) (coercions : List CoercionStep) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {value after} (evaluated : SourceExecutionSize.ExpressionFormEvaluates program size
      context evidence source environment before form requirements coercions value after) :
      RawOutcome program size context evidence source environment before form requirements coercions (.value value) after
  | fault {reason after} (failed : SourceExecutionSize.ExpressionFormFaults program size
      context evidence source environment before form requirements coercions reason after) :
      RawOutcome program size context evidence source environment before form requirements coercions (.fault reason) after

inductive StepOutcome (program : Program) (size : Nat) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (step : CoercionStep) (input : Dynamic.Value) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {value after} (evaluated : SourceExecutionSize.CoercionStepExecutes program size
      context evidence before step input value after) :
      StepOutcome program size context evidence before step input (.value value) after
  | fault {reason after} (failed : SourceExecutionSize.CoercionStepFaults program size
      context evidence before step input reason after) :
      StepOutcome program size context evidence before step input (.fault reason) after

inductive PathOutcome (program : Program) (size : Nat) (context : Context)
    (evidence : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (steps : List CoercionStep) (input : Dynamic.Value) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {value after} (evaluated : SourceExecutionSize.CoercionPathExecutes program size
      context evidence before steps input value after) :
      PathOutcome program size context evidence before steps input (.value value) after
  | fault {reason after} (failed : SourceExecutionSize.CoercionPathFaults program size
      context evidence before steps input reason after) :
      PathOutcome program size context evidence before steps input (.fault reason) after

def RawLift (program : Program) (registry : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (form : ExpressionForm) (requirements : List RequirementId)
    (coercions : List CoercionStep) (plain : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ staged reached, Staging.Recursive.RawForm program registry invocation context environment before
    form requirements coercions staged reached ∧ Adapted plain after staged reached

def StepLift (program : Program) (registry : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : Context) (before : Dynamic.Heap)
    (step : CoercionStep) (input : Dynamic.Value) (plain : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ staged reached, Staging.Recursive.CoercionStep program registry invocation context before
    step input staged reached ∧ Adapted plain after staged reached

def PathLift (program : Program) (registry : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : Context) (before : Dynamic.Heap)
    (steps : List CoercionStep) (input : Dynamic.Value) (plain : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ staged reached, Staging.Recursive.CoercionPath program registry invocation context before
    steps input staged reached ∧ Adapted plain after staged reached

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercionLiftBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedSource
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedSource
open Frontend SourceInference
open SelectedCompilationStageCoercionLiftBounds

inductive Branches (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap) (node : ExpressionNode)
    (size : Nat) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {rawSize pathSize value middle outcome after}
      (raw : RawOutcome program rawSize context evidence source environment before node.form
        node.requirements node.coercions (.value value) middle)
      (path : PathOutcome program pathSize context evidence middle node.coercions value outcome after)
      (rawLess : rawSize < size) (pathLess : pathSize < size) :
      Branches program context evidence source environment before node size outcome after
  | fault {rawSize reason after}
      (raw : RawOutcome program rawSize context evidence source environment before node.form
        node.requirements node.coercions (.fault reason) after)
      (rawLess : rawSize < size) :
      Branches program context evidence source environment before node size (.fault reason) after

theorem branches {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {node : ExpressionNode} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation} {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation))
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    Branches program context evidence source environment before node size outcome after := by
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro contains raw path =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      exact .value (.value raw) (.value path) (SourceExecutionSize.child_lt_stepSize (by simp))
        (SourceExecutionSize.child_lt_stepSize (by simp))
    | generalizedLocal contains localForm _ _ _ _ _ _ _ =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [form] at localForm
      cases localForm
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
    | form contains raw =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      exact .fault (.fault raw) (SourceExecutionSize.child_lt_stepSize (by simp))
    | coercion contains raw path =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      exact .value (.value raw) (.fault path) (SourceExecutionSize.child_lt_stepSize (by simp))
        (SourceExecutionSize.child_lt_stepSize (by simp))
    | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _
    | generalizedLocalCoercion contains localForm _ _ _ _ _ _ _ =>
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [form] at localForm
      cases localForm

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageCoercedSource
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalClosure
/-! The actual public preparation preserves closed replacement ranges for
all prepared local candidates, including candidates chosen by a later read. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalClosure
open Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open PreparedLocalInstanceClosure

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok output := by
  cases action with
  | error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ}
    {value : α} (accepted : action.mapError change = .ok value) : action = .ok value := by
  cases action with
  | error => cases accepted
  | ok result => cases accepted; rfl

theorem of_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {base : SourceCoreCompatibleFunctions.Prepared checked}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base) :
    CatalogClosed base.locals := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, prepared, accepted⟩ := bind_ok accepted
  have origins := PreparedLocalInstanceClosure.of_preparation (mapError_ok prepared)
  change CatalogClosed locals at origins
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    exact origins
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨table, _, accepted⟩ := bind_ok accepted
      obtain ⟨callableDiagnostics, _, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨assigned, decorated, accepted⟩ := bind_ok accepted
      have origins := PreparedLocalInstanceClosure.with_contracts origins (mapError_ok decorated)
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact origins
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      exact origins

theorem of_automatic {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {fuel : Nat} {automatic : SourceCoreCompatibleFunctions.Automatic}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic) :
    CatalogClosed automatic.prepared.locals := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, prepared, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog prepared

theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled) :
    CatalogClosed compiled.indexed.base.locals := by
  have origins := of_automatic compiled.compatiblePrepared
  have same := SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared
  rw [same]
  exact origins

/-- The actual compiler and exact binding selection supply closed ranges;
no independent whole-catalog property is required. -/
theorem at_context (compiled : SourceCoreUnifiedCompilation.Compiled)
    {caller : Key} {binder : Resolved.LocalId} {binding : Binding}
    {active : Substitution} {candidate : Instance}
    (located : compiled.indexed.base.locals.binding caller binder = .ok binding)
    (member : candidate ∈ binding.atContext active) :
    CallableAncestryProfiles.SourceComposition.RangesClosed candidate.origin.substitution :=
  PreparedLocalInstanceClosure.at_context (of_compiled compiled) located member

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalClosure
end

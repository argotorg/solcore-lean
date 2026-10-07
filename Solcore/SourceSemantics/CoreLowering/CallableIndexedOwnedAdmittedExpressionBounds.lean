import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds

/-! Admitted expression children consume genuine deep Source heap typing and
all-row stability at their actual input. A value returns admission at the same
reached state; a fault retains that state and stable rows. The existing static
Calls/Tree support fold is reused without a new induction or transport law. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
  (certificate : GenericExpressionMeaning.Certificate) (faults : GenericExpressionMeaning.FaultRep)

def PreservesAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached

variable {bridge model context evidence source certificate faults}

/-- An already closed actual-state producer supplies its actual post. Real
Source preservation adds admission; no state or record list is reconstructed. -/
theorem PreservesAt.of_stateful {size : Nat}
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (meaning : ProtectedStateTransition.PreservesAt callerProtocol model program context evidence source certificate faults size) :
    PreservesAt bridge model context evidence source certificate faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  exact CallableIndexedOwnedSourceAdmission.preserves_at model initial admitted wellFormed runtime covers
    certified found sourceTyped environments heaps locals agrees typed meaning trace

/-- The native child retains its independently measured Source trace and the
same actual final witness when successful admission is added. -/
theorem ReflectsAt.of_stateful {size : Nat}
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (meaning : ProtectedStateTransition.ReflectsAt callerProtocol model program context evidence source certificate faults size) :
    ReflectsAt bridge model context evidence source certificate faults size := by
  intro scope id lowered certified node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  exact CallableIndexedOwnedSourceAdmission.reflects_at model initial admitted wellFormed runtime covers
    certified found sourceTyped environments heaps locals agrees typed meaning completed

/-- The actual two-child outcome preserves order and multiplicity. -/
def pairOutcome (first : Dynamic.Value) : Dynamic.ExpressionOutcome → DataExpressionSequence.Outcome
  | .value second => .ok [first, second]
  | .fault reason => .error reason

/-- A successful first child feeds its exact reached state and fresh admission
into the next producer. A fault in that second child stops at its real post.
The production packing helper and the original raw Source types are retained. -/
theorem preserves_pair_after_value
    {scope : SourceCoreLocalCell.Scope} {firstId secondId : ExpressionId}
    {firstCode secondCode : SourceCoreBasic.LoweredExpr} {firstNode secondNode : ExpressionNode}
    {firstSize secondSize : Nat}
    (firstMeaning : PreservesAt bridge model context evidence source certificate faults firstSize)
    (secondMeaning : PreservesAt bridge model context evidence source certificate faults secondSize)
    (firstCertified : certificate scope firstId firstCode) (secondCertified : certificate scope secondId secondCode)
    (firstFound : source.lookupExpression? firstId = some firstNode)
    (secondFound : source.lookupExpression? secondId = some secondNode)
    (firstTyped : ExpressionHasType source context firstId firstNode.type)
    (secondTyped : ExpressionHasType source context secondId secondNode.type)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before middle after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {firstValue : Dynamic.Value} {secondOutcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (firstTrace : RecursiveNamedCallBounds.ExpressionOutcome program firstSize context evidence source environment
      before firstId (.value firstValue) middle)
    (secondTrace : RecursiveNamedCallBounds.ExpressionOutcome program secondSize context evidence source environment
      middle secondId secondOutcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments [firstCode, secondCode]).expression.rename ξ) value finalStore ∧
      DataExpressionSequence.Result model finalMap finalWorld [firstNode.type, secondNode.type]
        [firstCode, secondCode] faults (pairOutcome firstValue secondOutcome) value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context secondNode.type secondOutcome reached := by
  obtain ⟨native, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
      firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
    firstMeaning firstCertified firstFound firstTyped environments heaps locals agrees typed initial admitted firstTrace
  cases represented with
  | @value sourceValue nativeValue payload =>
    obtain ⟨value, finalStore, finalMap, finalWorld, second, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      secondMeaning secondCertified secondFound secondTyped (environments.extend firstMaps firstWorlds)
        middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees nativeValue)
        (.cons (model.runtime_hasType payload) (typed.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
    rw [GenericExpressionMeaning.rename_prefix] at second
    cases represented with
    | @value nextSource nextNative nextPayload =>
      refine ⟨.inRight .word (.pair nativeValue nextNative), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
        reached, callerProtocol.trans firstRelated related, post⟩
      · simpa [SourceCoreCalls.packArguments, DataExpressionSequence.pair_rename] using
          LocalSequence.pair_success firstCode.type secondCode.type first second
      · simpa [pairOutcome, DataPatternValues.packValues] using
          DataExpressionSequence.Result.values (codes := [firstCode, secondCode])
            (.cons (model.extend payload maps worlds) (.cons nextPayload .nil))
    | fault matched =>
      refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
        reached, callerProtocol.trans firstRelated related, post⟩
      simpa [SourceCoreCalls.packArguments, DataExpressionSequence.pair_rename] using
        LocalSequence.pair_right_failure firstCode.type secondCode.type first second

section Tree
variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {reasonAt : ExpressionId → Word} {solved : List SolvedRequirement}
  {fuel : Nat} {literals : GenericExpressionMeaning.Certificate}
  (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)

/-- The existing support fold specializes to admitted contracts. No static
Tree, Source, runtime or sequence induction is added. -/
theorem preserves_tree_at_with_literals (budget size : Nat) (within : size ≤ budget)
    (fragments : ∀ child, child ≤ budget → PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionBuiltins.Tree.WithLiterals (fuel := fuel) (values := .initial compiled.compatible.checked)
        (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults child)
    (heads : ∀ certificate child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → PreservesAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults smaller) →
      PreservesAt bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
        (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate) faults child) :
    PreservesAt bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls) (fuel := fuel) (values := .initial compiled.compatible.checked)
        (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  exact RecursiveNamedExpressionTreeBounds.fold_contract_at_with_literals calls
    (fun child certificate => PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults child)
    (fun meaning _ _ _ certified _ _ _ point => by
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact meaning certified)
    (fun meanings scope id lowered certified => meanings certified ⟨rfl, rfl, rfl⟩)
    budget size within fragments heads

/-- The same fold gathers native child contracts with their independently
returned Source grades and actual admitted successful post witnesses. -/
theorem reflects_tree_at_with_literals (budget size : Nat) (within : size ≤ budget)
    (fragments : ∀ child, child ≤ budget → ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionBuiltins.Tree.WithLiterals (fuel := fuel) (values := .initial compiled.compatible.checked)
        (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults child)
    (heads : ∀ certificate child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → ReflectsAt bridge
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults smaller) →
      ReflectsAt bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
        (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate) faults child) :
    ReflectsAt bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source
      (CompatibleExpressionCalls.Tree.WithLiterals (calls := calls) (fuel := fuel) (values := .initial compiled.compatible.checked)
        (source := source) (context := context) (solved := solved) (reasonAt := reasonAt) literals) faults size := by
  exact RecursiveNamedExpressionTreeBounds.fold_contract_at_with_literals calls
    (fun child certificate => ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context evidence source certificate faults child)
    (fun meaning _ _ _ certified _ _ _ point => by
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact meaning certified)
    (fun meanings scope id lowered certified => meanings certified ⟨rfl, rfl, rfl⟩)
    budget size within fragments heads
end Tree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds

import Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedBodyEntries
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation

/-! Actual Source parameter typing closes direct function-body transfers.
Nested Source faults retain their original reason and emitted token. The
finish endpoints derive this control fact from the reached Source trace. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedLoopContracts (ExecutesAt)
open RecursiveNamedCallBounds (BodyTrace)
universe u v

namespace CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt

/-- The complete typed body is checked at the actual parameter heap. -/
theorem control_no_escape {program : Program} {function : Dynamic.Closure}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {size : Nat} {control : Dynamic.ControlOutcome}
    (receipt : SourceReceipt program function context environment before)
    (wellFormed : ProgramWellFormed program)
    (trace : ExecutesAt size true program context function.evidence function.source
      environment before function.body finalContext control after) :
    control.NoEscapedControl := by
  obtain ⟨staticFinal, facts, typing, completes⟩ := receipt.bodyTyped
  cases trace with
  | control executed =>
    exact Dynamic.FunctionStatementsExecute.noEscapedControl wellFormed
      receipt.runtime receipt.covers receipt.locals receipt.heapTyped typing
      completes executed.sound
  | fault failed =>
    constructor <;> intro next equal <;> cases equal

end CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt

namespace CallableIndexedOwnedTypedFunctionFinishBounds

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {expressionSyntax : ExpressionId → Prop} {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {type : Ty} {flow code : Expr}
  {fellThrough escaped : Word}
  (tree : GenericImperativeMatch.Tree layouts owner active frameLayout globals onError values function.source
    expressionSyntax certificates ambient.definitions administrative context scope
    (.statements true function.body) function.resultType type flow)
  (projection : values.checked.catalog.project function.resultType = .ok type)
  (unique : NodeOccurrencesUnique function.source)
  {faults : FunctionCalls.FaultRep}

include tree projection unique in
theorem WithReady.preserves_at_emitted_with_source_receipt {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
    (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness condition facts functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context) (bodyFacts : facts context true function.body function.resultType)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context initial)
    (receipt : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt
      program function context environment before)
    (wellFormed : ProgramWellFormed program)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness context outcome initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  apply RecursiveNamedFunctionFinishBounds.WithReady.preserves_at_emitted_with_state_when_with_transfers
    (functions := functions) (program := program) (tree := tree)
    (projection := projection) (unique := unique) protocol readiness condition facts
    emitted validity size meaning valid bodyFacts environments heaps locals
    agrees typed reference read unmapped initial gate ready
    (fun actualTrace => by
      have closed := receipt.control_no_escape wellFormed actualTrace
      exact ⟨fun next equal => False.elim (closed.1 next equal),
        fun next equal => False.elim (closed.2 next equal)⟩)
  exact trace

include tree projection unique in
theorem WithReady.reflects_at_emitted_with_source_receipt {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
    (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness condition facts functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context) (bodyFacts : facts context true function.body function.resultType)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping) (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context initial)
    (receipt : CallableIndexedOwnedAdmittedBodyEntries.SourceReceipt
      program function context environment before)
    (wellFormed : ProgramWellFormed program)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness context outcome initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  apply RecursiveNamedFunctionFinishBounds.WithReady.reflects_at_emitted_with_state_when_with_transfers
    (functions := functions) (program := program) (tree := tree)
    (projection := projection) (unique := unique) protocol readiness condition facts
    emitted validity budget size within meaning valid bodyFacts environments heaps locals
    agrees typed reference read unmapped initial gate ready
    (fun actualTrace => by
      have closed := receipt.control_no_escape wellFormed actualTrace
      exact ⟨fun next equal => False.elim (closed.1 next equal),
        fun next equal => False.elim (closed.2 next equal)⟩)
  exact evaluated

end CallableIndexedOwnedTypedFunctionFinishBounds
end Solcore.SourceSemantics.CoreLowering

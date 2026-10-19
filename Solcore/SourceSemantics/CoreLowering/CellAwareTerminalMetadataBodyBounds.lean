import Solcore.SourceSemantics.CoreLowering.CellAwareStagedTerminalBody
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyMeaning
import Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews

/-! Actual lambda metadata views preserve terminal statements literally.
Complete original body typing determines the used child and declared result;
strict expression hypotheses then construct both body directions at the same
reached parameter state. No execution law is part of the static input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareTerminalMetadataBodyBounds
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
  {cells : GenericHeap.CellModel definitions}
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
  (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include view bodyTyped complete certifies environments heaps locals agrees typed admitted in
/-- Original whole-body trace, complete Source typing and the literal receipt
construct the used strict expression step and full body post internally. -/
theorem preserves_body (unique : NodeOccurrencesUnique invocation.source) (budget : Nat)
    (children : CellAwareStagedExpressionBounds.PreservesBelow
      bridge context model cells registry invocation certificate faults budget)
    {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements program registry size invocation context environment
      before statements finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult expected bodyOutcome outcome)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected result faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
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
    CellAwareStagedTerminalBody.preserves bridge head
      (certifies _ receipt.generated) found sourceTyped environments heaps locals agrees typed initial admitted
      budget children escaped
      ((CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback receipt.child.type fellThrough).rename ξ)
      child (sameSize ▸ within)
  simpa only [sameType, receipt.sameType] using meaning

include view bodyTyped complete certifies environments heaps locals agrees typed admitted in
/-- The literal emitted body exposes a strict native child. Its reflection
constructs a separately graded original body and the same reached full post. -/
theorem reflects_body (unique : NodeOccurrencesUnique invocation.source) (budget : Nat)
    (children : CellAwareStagedExpressionBounds.ReflectsBelow
      bridge context model cells registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment
        before statements context (control outcome) after ∧
      Staging.Recursive.BodyResult expected (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld expected result faults outcome value ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context expected outcome reached := by
  have head := source_head receipt view
  obtain ⟨node, found, sameType, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head bodyTyped complete
  rw [CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.emitted receipt ξ] at completed
  have meaning := CellAwareStagedTerminalBody.reflects bridge head
    (certifies _ receipt.generated) found sourceTyped environments heaps locals agrees typed initial admitted
    budget children escaped
    ((CallableIndexedOwnedPreparedStagedTerminalBodyMeaning.fallback receipt.child.type fellThrough).rename ξ)
    completed within
  simpa only [sameType, receipt.sameType] using meaning

end Solcore.SourceSemantics.CoreLowering.CellAwareTerminalMetadataBodyBounds

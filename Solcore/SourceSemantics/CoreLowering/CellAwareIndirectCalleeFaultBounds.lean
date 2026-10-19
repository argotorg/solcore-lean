import Solcore.SourceSemantics.CoreLowering.CellAwareStagedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters

/-! A semantic or nested stage fault in the actual callee stops the original
indirect parent before any gate or argument runs.
The strict staged child IH supplies the computation and its actual post once;
no full staged meaning or body/application law is a premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareIndirectCalleeFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functionModel : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {cells : GenericHeap.CellModel compiled.indexed.layouts.definitions}
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents cells
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel

/-- One failure receipt carries its exact tag, failing Scope and token through
the original sum bind. Actual transient effects remain in after/finalStore. -/
def ResultAt (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) (token : Word)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
  RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type lowered.type
    faults (.fault failure) (.inLeft lowered.type (.word token)) ∧
  GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context compiler.original.type (.fault failure) reached

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The genuine staged parent grade makes the executed callee strictly smaller.
Both semantic and nested stage failures propagate by the same original rule. -/
theorem preserves_callee_fault (budget : Nat)
    (children : CellAwareStagedExpressionBounds.PreservesBelow bridge context model cells stages invocation certificate faults budget)
    {childSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages childSize
      invocation context environment before callee (.fault failure) after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [childSize]) invocation context environment before id (.fault failure) after ∧
    ∃ token finalStore finalMap finalWorld,
      ResultAt (cells := cells) (registry := registry) (faults := faults) (context := context)
        (actual := actual) (ξ := ξ) bridge functionModel compiler initial
        failure after token finalStore finalMap finalWorld := by
  have smaller : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize) (children := [childSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children childSize smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted child
  cases represented with
  | fault matched =>
    have whole := CallableContract.call_callee_failure (result := compiler.resultType)
      (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
      prepared.site.gates native.diagnostics.unknown evaluated
    rw [← prepared.lowered_rename compiler ξ] at whole
    have loweredType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    rw [← loweredType] at whole
    exact ⟨.calleeFault occurrence child, _, finalStore, finalMap, finalWorld, whole, .fault matched,
      finalHeaps, maps, worlds, frame, metadata, reached, related,
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_fault_type post⟩

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted in
/-- The supplied first-bind child is the original strict native computation.
Its independently returned staged Source grade grows by one parent step; the
failure tag/scope, token and exact reached caller state are unchanged. -/
theorem reflects_callee_fault (budget : Nat)
    (children : CellAwareStagedExpressionBounds.ReflectsBelow bridge context model cells stages invocation certificate faults budget)
    {size : Nat} {token : Word} {finalStore : Store}
    (completed : EvaluationSize size actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore)
    (smaller : size < budget) :
    ∃ sourceSize failure after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id (.fault failure) after ∧
      ResultAt (cells := cells) (registry := registry) (faults := faults) (context := context)
        (actual := actual) (ξ := ξ) bridge functionModel compiler initial
        failure after token finalStore finalMap finalWorld := by
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    children size smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted completed
  cases represented with
  | fault matched =>
    have whole := CallableContract.call_callee_failure (result := compiler.resultType)
      (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
      prepared.site.gates native.diagnostics.unknown completed.sound
    rw [← prepared.lowered_rename compiler ξ] at whole
    have loweredType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    rw [← loweredType] at whole
    exact ⟨Staging.Recursive.Size.stepSize [sourceSize], _, after, finalMap, finalWorld,
      .calleeFault occurrence trace, whole, .fault matched, finalHeaps, maps, worlds, frame, metadata,
      reached, related, CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_fault_type post⟩

end Calls
end Solcore.SourceSemantics.CoreLowering.CellAwareIndirectCalleeFaultBounds

import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectApplication
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LexicalBodyFaults
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualStoredCalls
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenOrdinaryCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.StoredClosures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeStatements
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies

/-!
# Cell-aware scopes: indirect calls

Indirect calls on the scope protocol: callee and argument prefixes, the two gates, application and fault dispatch, and their Source lifting.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectCalleeFaultBounds
/-! A semantic or nested stage fault in the actual callee stops the original
indirect parent before any gate or argument runs.
The strict staged child IH supplies the computation and its actual post once;
no full staged meaning or body/application law is a premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectCalleeFaultBounds
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
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel

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
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel) (GeneralizedLocalInstanceValues.model compiled.indexed))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location)


/-- One failure receipt carries its exact tag, failing Scope and token through
the original sum bind. Actual transient effects remain in after/finalStore. -/
def ResultAt (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) (token : Word)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates actual store (lowered.expression.rename ξ) (.inLeft lowered.type (.word token)) finalStore ∧
  RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type lowered.type
    faults (.fault failure) (.inLeft lowered.type (.word token)) ∧
  GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
    mapping world before store finalMap finalWorld after finalStore ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates initial reached ∧ CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context compiler.original.type (.fault failure) reached

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted authority physical owner ownerFrame in
/-- The genuine staged parent grade makes the executed callee strictly smaller.
Both semantic and nested stage failures propagate by the same original rule. -/
theorem preserves_callee_fault (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context model named stages invocation certificate faults budget)
    {childSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages childSize
      invocation context environment before callee (.fault failure) after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [childSize]) invocation context environment before id (.fault failure) after ∧
    ∃ token finalStore finalMap finalWorld,
      ResultAt (registry := registry) (faults := faults) (context := context)
        (actual := actual) (ξ := ξ) bridge functionModel compiler initial
        failure after token finalStore finalMap finalWorld := by
  have smaller : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize) (children := [childSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    children childSize smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame child
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
      finalHeaps, maps, worlds, frame, metadata, effect, reached, related,
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_fault_type post⟩

include prepared sourceEq occurrence certified found sourceTyped environments heaps locals agrees typed admitted authority physical owner ownerFrame in
/-- The supplied first-bind child is the original strict native computation.
Its independently returned staged Source grade grows by one parent step; the
failure tag/scope, token and exact reached caller state are unchanged. -/
theorem reflects_callee_fault (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context model named stages invocation certificate faults budget)
    {size : Nat} {token : Word} {finalStore : Store}
    (completed : EvaluationSize size actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore)
    (smaller : size < budget) :
    ∃ sourceSize failure after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id (.fault failure) after ∧
      ResultAt (registry := registry) (faults := faults) (context := context)
        (actual := actual) (ξ := ξ) bridge functionModel compiler initial
        failure after token finalStore finalMap finalWorld := by
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    children size smaller certified actualFound actualTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame completed
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
      .calleeFault occurrence trace, whole, .fault matched, finalHeaps, maps, worlds, frame, metadata, effect,
      reached, related, CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_fault_type post⟩

end Calls
end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectCalleeFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectNativePrefix
/-! Whole-parent finite native inversion with the strict staged callee IH.
A semantic or nested stage callee fault produces the original parent. A value
retains its original gate and strict suffix for actual argument/application
producers. Source and native grades and the actual reached state remain
independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectNativePrefix
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
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

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
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel) (GeneralizedLocalInstanceValues.model compiled.indexed))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel

/-- A successful callee keeps the original full receiving-model payload and
its actual reached state. The following guard reads at that same store. -/
def CalleePost (sourceValue : Dynamic.Value) (after : Dynamic.Heap) (carrier : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  Evaluates actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) finalStore ∧
  GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type sourceValue carrier compiler.calleeCode.type ∧
  CellAwareScopeGeneralizedReadBounds.StrongResult (compiled := compiled) finalMap finalWorld
    owner.key.frameLocation (.value sourceValue) (.inRight .word carrier) ∧
  GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
    mapping world before store finalMap finalWorld after finalStore ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates initial reached ∧
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context calleeNode.type (.value sourceValue) reached

/-- A callee fault records the actual strict native child and independent
staged Source grade, and constructs the original parent at the same endpoint. -/
def FaultPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize failure token after finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inLeft compiler.calleeCode.type (.word token)) finalStore ∧ nativeSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before callee (.fault failure) after ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [sourceSize]) invocation context environment before id (.fault failure) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CellAwareScopeIndirectCalleeFaultBounds.ResultAt
      (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
      bridge functionModel compiler initial failure after token finalStore finalMap finalWorld

/-- A successful callee retains its actual staged trace/post and the original
second bind. Its suffix remains measured at the original strict native budget. -/
def ValuePrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before callee (.value sourceValue) after ∧
    CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functionModel compiler initial owner
      sourceValue after carrier calleeStore finalMap finalWorld ∧
    CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore

include prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped environments heaps locals agrees typed admitted authority physical ownerFrame in
/-- The actual whole-parent completion yields its strict callee child. That
child uses the staged reflection IH once. Faults keep both exact failure tags;
values keep the original guard/suffix computation and the same reached state. -/
theorem reflects_prefix (budget : Nat)
    (children : CellAwareScopeGeneralizedReadBounds.ReflectsBelow bridge context model named stages invocation faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    FaultPrefix (registry := registry) (faults := faults) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge functionModel compiler initial budget value finalStore ∨
    ValuePrefix (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      bridge functionModel compiler prepared initial owner budget value finalStore := by
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  have full := completed
  rw [prepared.lowered_rename compiler ξ] at full
  cases CallableIndirectCallBounds.bind_completed full within with
  | failed child childStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, strong, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
      children _ childStrict calleeCertificate calleeRecipe actualFound actualTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame child
    cases represented with
    | @fault failure token matched =>
      have whole := CallableContract.call_callee_failure (result := compiler.resultType)
        (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
        prepared.site.gates native.diagnostics.unknown child.sound
      rw [← prepared.lowered_rename compiler ξ] at whole
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      rw [← loweredType] at whole
      left
      refine ⟨_, sourceSize, failure, token, after, finalMap, finalWorld, child, childStrict,
        trace, .calleeFault occurrence trace, ?_, whole, .fault matched, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related,
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_fault_type post⟩
      rw [loweredType]
  | continued child remaining childStrict remainingStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, strong, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
      children _ childStrict calleeCertificate calleeRecipe actualFound actualTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame child
    cases represented with
    | value represented =>
      right
      refine ⟨_, sourceSize, _, after, _, _, finalMap, finalWorld, child, childStrict, trace,
        ⟨child.sound, represented, strong, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related, post⟩, ?_⟩
      cases CallableIndirectCallBounds.bind_completed remaining (Nat.le_of_lt remainingStrict) with
      | failed gate gateStrict => exact .failed gate gateStrict
      | continued gate suffixTrace gateStrict suffixStrict => exact .passed gate suffixTrace gateStrict suffixStrict

end Calls
end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectNativePrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectArgumentPrefix
/-! The actual staged callee post constructs its original scoped boundary.
The first gate either constructs the exact staged rejection, retaining the
selected original row and exact token, or exposes the real argument helper.
That helper uses the ordered staged argument producer at the same reached
caller state. Application and diagnostic receiver transport follow separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectArgumentPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {named : SourceCoreGeneralFunctions.Function}
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
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel) (GeneralizedLocalInstanceValues.model compiled.indexed))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


open CellAwareScopeIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open GenericExpressionMeaning (agree_prefix rename_prefix)

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

include sourceEq found sourceParent tree unique parentTyped in
/-- Original parent typing and the actual ordered compiler tree determine the
raw callee and argument rows. The SourceParent requirements, output coercions
and physical-count cuts remain explicit for this exact compiler receipt. -/
theorem source_rows :
    ∃ rawParameter rawResult,
      calleeNode.type = .function rawParameter rawResult ∧
      ExpressionsHaveTypes invocation.source context ids sourceTypes ∧
      TypeSystem.Ty.productMany sourceTypes = rawParameter ∧
      compiler.original.type = rawResult := by
  have rawTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have rawUnique : NodeOccurrencesUnique source := by
    simpa only [sourceEq] using unique
  have rawParentTyped : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨rawParameter, rawResult, calleeFunction, argumentsTyped, bundle, originalResult⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent rawTree rawUnique rawParentTyped found
  exact ⟨rawParameter, rawResult, calleeFunction,
    by simpa only [sourceEq] using argumentsTyped, bundle, originalResult⟩

private theorem foldlApplication_ne_function
    (head : TypeSystem.Ty) (arguments : List TypeSystem.Ty)
    (head_ne : ∀ parameter result, head ≠ .function parameter result)
    (parameter result : TypeSystem.Ty) :
    arguments.foldl TypeSystem.Ty.application head ≠ .function parameter result := by
  induction arguments generalizing head with
  | nil => exact head_ne parameter result
  | cons argument arguments induction =>
      exact induction (.application head argument)
        (by intro candidateParameter candidateResult equality; cases equality)

private theorem nominal_ne_function
    (declaration : Resolved.DeclarationId) (arguments : List TypeSystem.Ty)
    (parameter result : TypeSystem.Ty) :
    TypeSystem.Ty.nominal declaration arguments ≠ .function parameter result :=
  foldlApplication_ne_function (.constructor (.declaration declaration)) arguments
    (by intro candidateParameter candidateResult equality; cases equality) parameter result

private theorem value_is_function {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {value : Dynamic.Value} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap value (.function parameter result)) : IsFunction value := by
  cases value with
  | closure function => exact .closure function
  | global function => exact .global function
  | builtin function => exact .builtin function
  | constructed instantiation arguments =>
    rcases Dynamic.ValueHasType.constructed_inv typed with
      ⟨same, valid, _⟩ | ⟨_inner, impossible, _⟩
    · cases valid with
      | intro dataType signature dataType_mem signature_mem signature_owner constructor_eq
          substitution_exact substitution_range payloadTypes_eq resultType_eq =>
        have impossible := same.trans resultType_eq
        exact False.elim ((nominal_ne_function dataType.id
          (ParameterSubstitution.orderedArguments instantiation.parameterSubstitution dataType.parameters)
          parameter result) impossible.symm)
    · cases impossible
  | unit | bool | word | integer | product | proxy | mapping => cases typed

include positive caller view originalUnique sourceEq found sourceParent tree unique parentTyped in
/-- The actual callee payload comes from the positive receiving model. Its
Source function type and reached admission supply genuine callable shape;
the original scoped boundary factory then runs at that same payload. -/
theorem scoped_boundary {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (post : CalleePost  (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial owner
      sourceValue after carrier calleeStore finalMap finalWorld) :
    ∃ before originalMetadata, ContainsExpression sidecar.source prepared.site.call before ∧
      before.form = .call callee ids (.indirect originalMetadata) ∧
      CallView before compiler.original originalMetadata metadata ∧
      BoundaryAt sidecar prepared.site callee ids originalMetadata before sourceValue carrier := by
  obtain ⟨_rawParameter, _rawResult, calleeFunction, _argumentsTyped, _bundle, _originalResult⟩ :=
    source_rows (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  obtain ⟨reached, _related, admitted⟩ := post.2.2.2.2.2.2.2.2.2
  have typedSource := CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value admitted |>.1
  rw [calleeFunction] at typedSource
  have actualOrigin := SelectedCompilationCallableOrigins.Origins.origin
    (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
    (faults := semanticFaults) (profile := profile) post.2.1 (value_is_function typedSource)
  exact CallableIndexedOwnedPreparedScopedCallBoundaryReceipts.boundary_at_source_view compiler prepared
    caller view originalUnique actualOrigin

/-- The stage branch retains its actual invocation and occurrence, exact
selected original row/metadata and native word. Its diagnostic representation
is identified later by the receiving codebook, not by changing the failure. -/
def StageRejectedPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld originalNode originalMetadata reason,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before callee (.value sourceValue) after ∧
    CalleePost  (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial owner
      sourceValue after carrier calleeStore finalMap finalWorld ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    ∃ dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue carrier,
      CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids originalMetadata originalNode dispatch.row ∧
      Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason ∧
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
        (Staging.Recursive.Size.stepSize [sourceSize]) invocation context environment before id
        (.fault (.stage invocation id reason)) after ∧
      value = .inLeft lowered.type (.word (dispatch.reason reason)) ∧ finalStore = calleeStore

/-- A real argument failure retains the cumulative reached state and full
receiving-model relation, with neither semantic nor nested stage tag changed. -/
def ArgumentFaultPrefix (value : Value) (finalStore : Store) : Prop :=
  ∃ calleeSize argumentsSize sourceValue calleeHeap failure after token finalMap finalWorld,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.fault failure) after ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize]) invocation context environment before id (.fault failure) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CellAwareScopeIndirectCalleeFaultBounds.ResultAt
      (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
      bridge functions compiler initial failure after token finalStore finalMap finalWorld

/-- Successful arguments retain their independent Source grade and actual
packed payload, raw callee/bundle/original-result rows, reached caller state
and strict original second-gate/application computation. No application trace
or body result is asserted here. -/
def ApplicationPrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧
    compiler.original.type = rawResult ∧
  ∃ calleeSize argumentsSize sourceValue calleeHeap sources values carrier argumentsHeap argumentsStore finalMap finalWorld originalNode originalMetadata,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type sourceValue carrier compiler.calleeCode.type ∧
    CellAwareScopeGeneralizedReadBounds.StrongResult (compiled := compiled) finalMap finalWorld
      owner.key.frameLocation (.value sourceValue) (.inRight .word carrier) ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world before store finalMap finalWorld argumentsHeap argumentsStore ∧
    (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
    ∃ size, EvaluationSize size (DataPatternValues.packValues values :: .unit :: carrier :: actual) argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore ∧ size < budget

private theorem argument_fault_post {failure : Staging.Recursive.Failure} {type : TypeSystem.Ty}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : CellAwareScopeExpressionSequence.PostAdmission bridge
      (context := context) (.fault failure) reached) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context type (.fault failure) reached := by
  cases failure with
  | semantic reason => exact ⟨post.rows, by intro _ impossible; cases impossible⟩
  | stage origin call reason => exact post.rows

include positive prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped environments heaps locals agrees typed admitted authority physical ownerFrame
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Whole-parent native reflection uses the strict staged callee IH once and
the actual scoped boundary. An accepted gate then invokes the concrete staged
argument fold at its genuine callee endpoint, preserving all transient effects. -/
theorem reflects_arguments (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.ReflectsBelow
      bridge context model named stages invocation faults budget)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow
      bridge context model named stages invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    CellAwareScopeIndirectNativePrefix.FaultPrefix
      (registry := registry) (faults := faults) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge functions compiler initial budget value finalStore ∨
    StageRejectedPrefix  (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner budget value finalStore ∨
    ArgumentFaultPrefix  (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (faults := faults) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      bridge profile compiler initial value finalStore ∨
    ApplicationPrefix  (functionModel := functionModel) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner budget value finalStore := by
  obtain ⟨rawParameter, rawResult, calleeFunction, argumentsTyped, bundle, originalResult⟩ :=
    source_rows (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  cases CellAwareScopeIndirectNativePrefix.reflects_prefix bridge functions compiler prepared
      sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame
      budget calleeMeaning completed within with
  | inl fault => exact .inl fault
  | inr positive =>
    obtain ⟨nativeSize, calleeSize, sourceValue, calleeHeap, carrier, calleeStore, calleeMap, calleeWorld,
      calleeNative, calleeStrict, calleeTrace, calleePost, gate⟩ := positive
    obtain ⟨original, originalMetadata, _contained, _form, callView, boundary⟩ :=
      scoped_boundary (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
        (tree := tree) (unique := unique) (parentTyped := parentTyped)
        bridge profile compiler prepared initial owner caller view originalUnique calleePost
    have gateResult :
        (∃ reason, Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason ∧
          ∃ dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids sourceValue carrier,
            CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids originalMetadata original dispatch.row ∧
            value = .inLeft compiler.resultType (.word (dispatch.reason reason)) ∧ finalStore = calleeStore) ∨
        (Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
          ∃ suffixSize, EvaluationSize suffixSize (.unit :: carrier :: actual) calleeStore
            (CallableIndexedOwnedStoredIndirectNativePrefix.suffix prepared.site
              compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
              ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore ∧ suffixSize < budget) := by
      cases boundary with
      | user dispatch selected =>
          cases gate.resolve dispatch with
          | inl rejected =>
              obtain ⟨reason, rejected, valueEq, storeEq, _represented⟩ := rejected
              left
              refine ⟨reason, ?_, dispatch, selected, valueEq, storeEq⟩
              simpa only [guardFrame, prepared.call] using rejected
          | inr accepted =>
              right
              simpa only [guardFrame, prepared.call] using accepted
      | builtin receipt =>
          right
          simpa only [guardFrame, prepared.call] using receipt.resolve_prefix gate
    cases gateResult with
    | inl rejected =>
        obtain ⟨reason, rejected, dispatch, selected, valueEq, storeEq⟩ := rejected
        right; left
        refine ⟨nativeSize, calleeSize, sourceValue, calleeHeap, carrier, calleeStore, calleeMap, calleeWorld,
          original, originalMetadata, reason, calleeNative, calleeStrict, calleeTrace, calleePost, callView,
          dispatch, selected, rejected, .rejected occurrence calleeTrace rejected, ?_, storeEq⟩
        simpa only [loweredType] using valueEq
    | inr accepted =>
        obtain ⟨accepted, suffixSize, suffixTrace, suffixStrict⟩ := accepted
        obtain ⟨_calleeEvaluated, payload, calleeStrong, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeEffect, calleeState, calleeRelated, calleeAdmission⟩ := calleePost
        have argumentLayout : EnvironmentsAgree
            (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
            canonical (Value.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
        have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
          (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
        cases CallableIndirectCallBounds.bind_completed suffixTrace (Nat.le_of_lt suffixStrict) with
        | failed arguments argumentsStrict =>
            have argumentNative := arguments
            rw [← rename_prefix, ← rename_prefix] at argumentNative
            obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, argumentsTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
              CellAwareScopeExpressionSequence.reflects bridge budget tree unique argumentsTyped children
                (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
                argumentTyped calleeState calleeAdmission.at_value.2 (authority.transport calleeEffect)
                (physical.transport calleeEffect calleeFrame) owner ownerFrame argumentNative argumentsStrict
            cases represented with
            | @fault failure token matched =>
                right; right; left
                refine ⟨calleeSize, argumentsSize, sourceValue, calleeHeap, failure, after, token, finalMap, finalWorld,
                  calleeTrace, accepted, argumentsTrace, .argumentsFault occurrence calleeTrace accepted argumentsTrace,
                  ?_, (by simpa only [loweredType] using completed.sound), .fault matched, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
                  calleeFrame.trans frame, calleeMetadata.trans heapMetadata, calleeEffect.trans effect,
                  reached, callerProtocol.trans calleeRelated related, argument_fault_post bridge post⟩
                simp only [loweredType]
        | continued arguments remaining argumentsStrict remainingStrict =>
            have argumentNative := arguments
            rw [← rename_prefix, ← rename_prefix] at argumentNative
            obtain ⟨argumentsSize, outcome, after, finalMap, finalWorld, argumentsTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
              CellAwareScopeExpressionSequence.reflects bridge budget tree unique argumentsTyped children
                (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
                argumentTyped calleeState calleeAdmission.at_value.2 (authority.transport calleeEffect)
                (physical.transport calleeEffect calleeFrame) owner ownerFrame argumentNative argumentsStrict
            cases represented with
            | @values sources values relatedValues =>
                right; right; right
                exact ⟨rawParameter, rawResult, calleeFunction, bundle, originalResult,
                  calleeSize, argumentsSize, sourceValue, calleeHeap, sources, values, carrier, after, _, finalMap, finalWorld,
                  original, originalMetadata, calleeTrace, accepted, argumentsTrace, relatedValues,
                  GenericHeap.PayloadModel.extend model payload maps worlds, calleeStrong.extend maps worlds, callView, boundary, finalHeaps,
                  calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
                  calleeMetadata.trans heapMetadata, calleeEffect.trans effect, ⟨reached, callerProtocol.trans calleeRelated related, post.at_values⟩,
                  _, remaining, remainingStrict⟩

end Calls
/-- Source function typing excludes data-valued callees before direct dispatch. -/
theorem callable_shape {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {value : Dynamic.Value} {parameter result : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap value (.function parameter result)) : IsFunction value :=
  value_is_function typed

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectArgumentPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectArgumentFaultBounds
/-! The original indirect parent stops at a real argument failure. Its strict
callee and ordered argument hypotheses run at their actual reached states.
The first gate is reconstructed from the authentic scoped boundary; semantic
and nested stage failures retain the same tag, token and transient effects. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectArgumentFaultBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CellAwareScopeIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel) (GeneralizedLocalInstanceValues.model compiled.indexed))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include guardFrame in
omit positive in
/-- The real original row supplies first-gate success at the callee store.
No native acceptance or verdict is added to a compiler certificate. -/
theorem first_gate {sourceValue : Dynamic.Value} {carrier : Value}
    {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
    (boundary : BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (calleeStore : Store) :
    Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore := by
  cases boundary with
  | user dispatch selected =>
      have passed := dispatch.accepted (by simpa only [guardFrame, prepared.call] using accepted)
      have read : Evaluates (carrier :: actual) calleeStore (.second (.var 0))
          (.word dispatch.contract) calleeStore := by
        exact .second (.var (by simpa only [List.getElem?_cons_zero] using congrArg some dispatch.shape))
      have gate := prepared.site.dispatch_known .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
        dispatch.contract dispatch.row dispatch.found read
      rw [SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeArguments passed] at gate
      simpa only [CallableContract.resultValue] using gate
  | builtin receipt =>
      exact receipt.first_gate compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown actual calleeStore

include positive prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped environments heaps locals agrees typed admitted authority physical ownerFrame
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Strict Source descent constructs the callee and argument computations.
The argument fold runs after the accepted first gate and its actual effects
are the parent post; the second gate and application are never evaluated. -/
theorem preserves_argument_fault (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.PreservesBelow
      bridge context model named stages invocation faults budget)
    (children : CellAwareScopeExpressionBounds.PreservesBelow
      bridge context model named stages invocation certificate faults budget)
    {calleeSize argumentsSize : Nat} {sourceValue : Dynamic.Value} {calleeHeap after : Dynamic.Heap}
    {failure : Staging.Recursive.Failure}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.fault failure) after)
    (within : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize]) invocation context environment before id
      (.fault failure) after ∧
    ∃ token finalStore finalMap finalWorld,
      CellAwareScopeIndirectCalleeFaultBounds.ResultAt
        (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
        bridge functions compiler initial failure after token finalStore finalMap finalWorld := by
  have calleeStrict : calleeSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := calleeSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have argumentsStrict : argumentsSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := argumentsSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, calleeStore, calleeMap, calleeWorld, calleeEvaluated, representation, calleeStrong, calleeHeaps,
    calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeEffect, calleeState, calleeRelated, calleeAdmission⟩ :=
    calleeMeaning calleeSize calleeStrict calleeCertificate calleeRecipe actualFound actualTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame calleeTrace
  cases representation with
  | value payload =>
      have calleePost : ∃ carrier, CalleePost  (registry := registry) (context := context)
          (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
          bridge functions compiler initial owner sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld :=
        ⟨_, calleeEvaluated, payload, calleeStrong, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeEffect, calleeState, calleeRelated, calleeAdmission⟩
      obtain ⟨carrier, post⟩ := calleePost
      obtain ⟨calleeEvaluated, payload, calleeStrong, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
        calleeMetadata, calleeEffect, calleeState, calleeRelated, calleeAdmission⟩ := post
      obtain ⟨originalNode, originalMetadata, _contains, _form, _callView, boundary⟩ :=
        CellAwareScopeIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial owner caller view originalUnique
          ⟨calleeEvaluated, payload, calleeStrong, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
            calleeMetadata, calleeEffect, calleeState, calleeRelated, calleeAdmission⟩
      obtain ⟨_rawParameter, _rawResult, _functionType, argumentsTyped, _bundle, _result⟩ :=
        CellAwareScopeIndirectArgumentPrefix.source_rows
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
      have argumentLayout : EnvironmentsAgree
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
          canonical (.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
      have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
        (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
      obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, postAdmission⟩ :=
        CellAwareScopeExpressionSequence.preserves_fault bridge budget tree unique argumentsTyped children
          (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
          argumentTyped calleeState calleeAdmission.at_value.2 (authority.transport calleeEffect)
          (physical.transport calleeEffect calleeFrame) owner ownerFrame argumentsTrace (Nat.le_of_lt argumentsStrict)
      have gate := first_gate (actual := actual) compiler prepared guardFrame boundary accepted calleeStore
      have whole : Evaluates actual store
          (CallableContract.call prepared.site.gates
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
            (compiler.calleeCode.expression.rename ξ)
            ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ))
          (.inLeft compiler.resultType (.word token)) finalStore := by
        apply LanguageResult.bind_success compiler.resultType calleeEvaluated
        apply LanguageResult.bind_success compiler.resultType gate
        apply LanguageResult.bind_failure compiler.resultType
        simpa only [← rename_prefix, ← rename_prefix] using argumentsEvaluated
      rw [← prepared.lowered_rename compiler ξ] at whole
      have loweredType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      rw [← loweredType] at whole
      have parentAdmission : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge context compiler.original.type (.fault failure) reached := by
        cases failure with
        | semantic reason => exact ⟨postAdmission.rows, by intro _ impossible; cases impossible⟩
        | stage origin call reason => exact postAdmission.rows
      exact ⟨.argumentsFault occurrence calleeTrace accepted argumentsTrace,
        token, finalStore, finalMap, finalWorld, whole, .fault matched, finalHeaps,
        calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
        calleeMetadata.trans heapMetadata, calleeEffect.trans effect, reached, callerProtocol.trans calleeRelated related, parentAdmission⟩

omit positive in
/-- The constructive whole argument-prefix reflection already contains the
actual parent trace and reached failure receipt. This branch exposes the
independent Source grade without rebuilding or relabeling the child failure. -/
theorem reflects_argument_fault_prefix {value : Value} {finalStore : Store}
    (reflected : CellAwareScopeIndirectArgumentPrefix.ArgumentFaultPrefix  (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry)
      (faults := faults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore) :
    ∃ sourceSize failure after token finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id (.fault failure) after ∧
      value = .inLeft lowered.type (.word token) ∧
      CellAwareScopeIndirectCalleeFaultBounds.ResultAt
        (registry := registry) (faults := faults) (context := context) (actual := actual) (ξ := ξ)
        bridge functions compiler initial failure after token finalStore finalMap finalWorld := by
  obtain ⟨calleeSize, argumentsSize, _sourceValue, _calleeHeap, failure, after, token, finalMap, finalWorld,
    _callee, _accepted, _arguments, parent, sameValue, result⟩ := reflected
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize], failure, after, token,
    finalMap, finalWorld, parent, sameValue, result⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectArgumentFaultBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectValuesPrefix
/-! Source preservation constructs the callee and ordered argument prefix
at their actual reached states. It retains callee typing and its complete
post for builtin and user application. The application itself follows later. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectValuesPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CellAwareScopeIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  {calleeNode : ExpressionNode}
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel) (GeneralizedLocalInstanceValues.model compiled.indexed))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


/-- Both native prefix actions use the same represented callee and argument
packet. The callee post is retained before the argument effects are composed. -/
def ValuesPrefix (sourceValue : Dynamic.Value) (calleeHeap argumentsHeap : Dynamic.Heap)
    (sources : List Dynamic.Value) : Prop :=
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧ compiler.original.type = rawResult ∧
  ∃ calleeStore calleeMap calleeWorld carrier values argumentsStore finalMap finalWorld
      originalNode originalMetadata,
    CalleePost  (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial owner
      sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld ∧
    Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type ∧
    Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore ∧
    Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes
      (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
      sourceValue carrier compiler.calleeCode.type ∧
    CellAwareScopeGeneralizedReadBounds.StrongResult (compiled := compiled) finalMap finalWorld
      owner.key.frameLocation (.value sourceValue) (.inRight .word carrier) ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functionModel) (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world before store finalMap finalWorld argumentsHeap argumentsStore ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached

include positive prepared sourceEq calleeCertificate calleeRecipe found sourceTyped environments heaps locals agrees typed admitted authority physical ownerFrame
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Strict callee preservation and the real ordered argument fold construct
the full prefix once. The returned admission belongs to the argument endpoint. -/
theorem preserves_values (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.PreservesBelow
      bridge context model named stages invocation faults budget)
    (children : CellAwareScopeExpressionBounds.PreservesBelow
      bridge context model named stages invocation certificate faults budget)
    {calleeSize argumentsSize : Nat} {sourceValue : Dynamic.Value}
    {calleeHeap argumentsHeap : Dynamic.Heap} {sources : List Dynamic.Value}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (within : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget) :
    ValuesPrefix  (functionModel := functionModel) (registry := registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner sourceValue calleeHeap argumentsHeap sources := by
  have calleeStrict : calleeSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := calleeSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have argumentsStrict : argumentsSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := argumentsSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, calleeStore, calleeMap, calleeWorld, calleeEvaluated, representation, calleeStrong, calleeHeaps,
    calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeEffect, calleeState, calleeRelated, calleeAdmission⟩ :=
    calleeMeaning calleeSize calleeStrict calleeCertificate calleeRecipe actualFound actualTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame calleeTrace
  cases representation with
  | value payload =>
      rename_i carrier
      have post : CalleePost  (registry := registry) (context := context) (actual := actual) (ξ := ξ)
          (calleeNode := calleeNode) bridge functions compiler initial owner
          sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld :=
        ⟨calleeEvaluated, payload, calleeStrong, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeEffect, calleeState, calleeRelated, calleeAdmission⟩
      have sourceValueTyped : Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type :=
        calleeAdmission.at_value.1
      obtain ⟨originalNode, originalMetadata, _contains, _form, callView, boundary⟩ :=
        CellAwareScopeIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial owner caller view originalUnique post
      obtain ⟨rawParameter, rawResult, functionType, argumentsTyped, bundle, resultType⟩ :=
        CellAwareScopeIndirectArgumentPrefix.source_rows
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
      have argumentLayout : EnvironmentsAgree
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
          canonical (.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
      have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
        (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
      obtain ⟨values, argumentsStore, finalMap, finalWorld, argumentsEvaluated, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, effect, reached, related, postAdmission⟩ :=
        CellAwareScopeExpressionSequence.preserves_values bridge budget tree unique argumentsTyped children
          (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
          argumentTyped calleeState calleeAdmission.at_value.2 (authority.transport calleeEffect)
          (physical.transport calleeEffect calleeFrame) owner ownerFrame argumentsTrace (Nat.le_of_lt argumentsStrict)
      have gate := CellAwareScopeIndirectArgumentFaultBounds.first_gate
        (actual := actual) compiler prepared guardFrame boundary accepted calleeStore
      exact ⟨rawParameter, rawResult, functionType, bundle, resultType, calleeStore, calleeMap, calleeWorld,
        carrier, values, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
        post, sourceValueTyped, gate, argumentsEvaluated, represented,
        GenericHeap.PayloadModel.extend model payload maps worlds, calleeStrong.extend maps worlds, callView, boundary, finalHeaps,
        calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
        calleeMetadata.trans heapMetadata, calleeEffect.trans effect, reached, callerProtocol.trans calleeRelated related,
        postAdmission.at_values⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectValuesPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectFirstGateBounds
/-! Actual first-gate rejection combines the original native failure producer
with the exact receiving stage diagnostic. The callee's concrete reached state
supplies the parent stage post. A strict child proof and the actual reflected
argument prefix feed this constructor; broader dispatch remains separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectFirstGateBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CellAwareScopeIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section Constructor
variable
  (functionModel : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functionModel
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include receiver prepared stagePrepared sourceEq occurrence view guardFrame in
/-- Both the Source parent and native parent stop at the actual callee endpoint.
The literal selected token and receiver lookup establish the stage relation;
the same reached child witness supplies stable rows for the parent. -/
theorem result_at_rejected
    {childSize : Nat} {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (child : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages childSize
      invocation context environment before callee (.value sourceValue) after)
    (post : CalleePost (registry := completion.result.context.registry) (context := context)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
      bridge functionModel compiler initial owner sourceValue after carrier calleeStore finalMap finalWorld)
    {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
    (callView : CallView originalNode compiler.original originalMetadata metadata)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      prepared.site prepared.site.call ids sourceValue carrier)
    (selected : Selected sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
    {reason : Staging.CallGuard.Fault}
    (rejected : Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [childSize]) invocation context environment before id
      (.fault (.stage invocation id reason)) after ∧
    CellAwareScopeIndirectCalleeFaultBounds.ResultAt
      (registry := completion.result.context.registry) (faults := callFaults) (context := context)
      (actual := actual) (ξ := ξ) bridge functionModel compiler initial
      (.stage invocation id reason) after (dispatch.reason reason) calleeStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, _payload, _strong, calleeHeaps, maps, worlds, frame, heapMetadata, effect,
    reached, related, calleeAdmission⟩ := post
  have actualRejected : Staging.CallBoundary.GuardRejects (CallableLedger.frame sidecar)
      prepared.site.call ids sourceValue reason := by
    simpa only [guardFrame, prepared.call] using rejected
  have shaped := calleeEvaluation
  rw [dispatch.shape] at shaped
  have whole := prepared.site.lower_stage_failure (result := compiler.resultType)
    (arguments := (SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.row
    (CallStageGuard.error dispatch.guard.sidecar.caller dispatch.guard.node dispatch.guard.contract.owner reason)
    dispatch.found (dispatch.rejected actualRejected) shaped
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  have evaluated : Evaluates actual store (lowered.expression.rename ξ)
      (.inLeft lowered.type (.word (dispatch.reason reason))) calleeStore := by
    simpa only [SourceCoreCallableContracts.Callsite.lower, CallStageBoundary.Dispatch.reason,
      prepared.lowered_rename compiler ξ, loweredType] using whole
  obtain ⟨diagnostic, decoded, error⟩ :=
    CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.receiving_diagnostic
      compiler prepared stagePrepared dispatch selected receiver actualRejected
  have scopeView : SourceView sidecar.source invocation.source := by rw [sourceEq]; exact view
  have actualContains : ContainsExpression invocation.source prepared.site.call compiler.original := by
    rw [sourceEq, prepared.call]
    exact lookupExpression?_sound compiler.found
  have errorView : CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.StageErrorView
      invocation prepared.site.call reason diagnostic.error := by
    rw [error]
    exact .selected scopeView actualContains compiler.originalForm callView guardFrame dispatch selected
      (by simpa only [prepared.call] using rejected)
  have represented : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults
      (.fault (.stage invocation id reason)) (.inLeft lowered.type (.word (dispatch.reason reason))) := by
    have received : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type
        (CallableIndexedOwnedPreparedReceivingFirstCallGateRejection.stagedFaults
          completion.result.diagnostics)
        (.fault (.stage invocation prepared.site.call reason))
        (.inLeft lowered.type (.word (dispatch.reason reason))) :=
      .fault ⟨diagnostic, decoded, errorView⟩
    have common := CallableIndexedOwnedPublicDecodedStagedCallFaults.first_gate_result model received
    simpa only [prepared.call] using common
  have parentAdmission : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      bridge context compiler.original.type (.fault (.stage invocation id reason)) reached :=
    calleeAdmission.rows
  exact ⟨.rejected occurrence child rejected, evaluated, represented, calleeHeaps,
    maps, worlds, frame, heapMetadata, effect, reached, related, parentAdmission⟩

end Constructor

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {named : SourceCoreGeneralFunctions.Function}
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel)
    (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (ownerFrame : owner.key.frameLocation = physical.location)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include positive receiver prepared stagePrepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
  environments heaps locals agrees typed admitted authority physical ownerFrame caller view originalUnique guardFrame
  sourceParent tree unique parentTyped in
/-- Strict Source descent supplies the actual successful callee post. Positive
payload and original Source rows construct its scoped boundary. A genuine
rejection excludes the builtin branch and invokes the concrete parent once. -/
theorem preserves_rejected (budget : Nat)
    (children : CellAwareScopeGeneralizedReadBounds.PreservesBelow
      bridge context model named stages invocation faults budget)
    {childSize : Nat} {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages childSize
      invocation context environment before callee (.value sourceValue) after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget)
    {reason : Staging.CallGuard.Fault}
    (rejected : Staging.CallBoundary.GuardRejects invocation.guards id ids sourceValue reason) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [childSize]) invocation context environment before id
      (.fault (.stage invocation id reason)) after ∧
    ∃ token finalStore finalMap finalWorld,
      CellAwareScopeIndirectCalleeFaultBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (context := context)
        (actual := actual) (ξ := ξ) bridge functions compiler initial
        (.stage invocation id reason) after token finalStore finalMap finalWorld := by
  have smaller : childSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := childSize) (children := [childSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by
    rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by
    rw [sourceEq]; exact sourceTyped
  obtain ⟨value, calleeStore, finalMap, finalWorld, evaluated, represented, strong, finalHeaps,
      maps, worlds, frame, heapMetadata, effect, reached, related, calleeAdmission⟩ :=
    children childSize smaller calleeCertificate calleeRecipe actualFound actualTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame child
  cases represented with
  | value payload =>
      have actualPost : ∃ carrier, CalleePost (registry := completion.result.context.registry) (context := context)
          (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
          bridge functions compiler initial owner sourceValue after carrier calleeStore finalMap finalWorld :=
        ⟨_, evaluated, payload, strong, finalHeaps, maps, worlds, frame, heapMetadata, effect,
          reached, related, calleeAdmission⟩
      obtain ⟨carrier, post⟩ := actualPost
      obtain ⟨originalNode, originalMetadata, _contains, _form, callView, boundary⟩ :=
        CellAwareScopeIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial owner caller view originalUnique post
      cases boundary with
      | user dispatch selected =>
          obtain ⟨trace, result⟩ := result_at_rejected bridge receiver compiler prepared stagePrepared
            sourceEq occurrence initial owner view guardFrame functions child post callView dispatch selected rejected
          exact ⟨trace, dispatch.reason reason, calleeStore, finalMap, finalWorld, result⟩
      | @builtin function carrier row receipt =>
          exact False.elim (Staging.CallBoundary.GuardAccepts.not_rejects
            (.builtin function) rejected)

include receiver prepared stagePrepared sourceEq occurrence view guardFrame in
omit positive in
/-- The real reflected first-gate prefix already retains its strict native
callee and independent Source grade. Its literal selected row supplies the
receiving token, completing this branch at the same final store and witness. -/
theorem reflects_rejected_prefix (budget : Nat) {value : Value} {finalStore : Store}
    (rejectedPrefix : CellAwareScopeIndirectArgumentPrefix.StageRejectedPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial owner
      budget value finalStore) :
    ∃ sourceSize reason after token finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id (.fault (.stage invocation id reason)) after ∧
      value = .inLeft lowered.type (.word token) ∧
      CellAwareScopeIndirectCalleeFaultBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (context := context)
        (actual := actual) (ξ := ξ) bridge functions compiler initial
        (.stage invocation id reason) after token finalStore finalMap finalWorld := by
  obtain ⟨_nativeSize, childSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
    originalNode, originalMetadata, reason, _native, _strict, child, post, callView,
    dispatch, selected, rejected, _trace, valueEq, storeEq⟩ := rejectedPrefix
  subst finalStore
  obtain ⟨trace, result⟩ := result_at_rejected bridge receiver compiler prepared stagePrepared
    sourceEq occurrence initial owner view guardFrame functions child post callView dispatch selected rejected
  exact ⟨Staging.Recursive.Size.stepSize [childSize], reason, after, dispatch.reason reason,
    finalMap, finalWorld, trace, valueEq, result⟩

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectFirstGateBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectSourcePrefixDispatch
/-! The original recursively staged indirect parent selects its actual executed
prefix. Faults construct full native parent results from strict child hypotheses;
successful arguments retain the original application trace and real native
prefix. No application execution law is supplied to the classifier. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectSourcePrefixDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

private inductive SourcePrefix (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (call callee : ExpressionId) (ids : List ExpressionId) (metadata : IndirectCallResolution) :
    Nat → Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | calleeFault {childSize failure after}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.fault failure) after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault failure) after
  | notCallable {childSize value after}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) after)
      (invalid : ¬ Dynamic.CallableValue value) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault (.semantic .notCallable)) after
  | rejected {childSize value after reason}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) after)
      (rejected : Staging.CallBoundary.GuardRejects invocation.guards call ids value reason) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize]) (.fault (.stage invocation call reason)) after
  | argumentsFault {childSize argumentsSize value middle after failure}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) middle)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment middle ids (.fault failure) after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize]) (.fault failure) after
  | sourceArity {childSize argumentsSize value middle after values}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) middle)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment middle ids (.values values) after)
      (mismatch : ids.length ≠ metadata.argumentCount) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize])
        (.fault (.semantic (.argumentArityMismatch metadata.argumentCount ids.length))) after
  | applied {childSize argumentsSize applicationSize value calleeHeap argumentsHeap after values outcome}
      (child : Staging.Recursive.Size.Expression program stages childSize invocation context
        environment before callee (.value value) calleeHeap)
      (accepted : Staging.CallBoundary.GuardAccepts invocation.guards call ids value)
      (arguments : Staging.Recursive.Size.Expressions program stages argumentsSize invocation context
        environment calleeHeap ids (.values values) argumentsHeap)
      (called : Staging.Recursive.Size.Applies program stages applicationSize invocation context
        argumentsHeap value values outcome after) :
      SourcePrefix program stages invocation context environment before call callee ids metadata
        (Staging.Recursive.Size.stepSize [childSize, argumentsSize, applicationSize]) outcome after

private theorem source_prefix
    {program : Program} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {node : ExpressionNode} {size : Nat} {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (trace : Staging.Recursive.Size.Expression program stages size invocation context
      environment before id outcome after) :
    SourcePrefix program stages invocation context environment before id callee ids metadata size outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm requirements}, Staging.Recursive.Occurrence invocation id actualForm requirements →
      actualForm = .call callee ids (.indirect metadata) := by
    intro actualForm requirements occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have actual := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actual] at actualForm
      cases actualForm
  | calleeFault occurrence child =>
      cases occurrence_form occurrence
      exact .calleeFault child
  | notCallable occurrence child invalid =>
      cases occurrence_form occurrence
      exact .notCallable child invalid
  | rejected occurrence child rejected =>
      cases occurrence_form occurrence
      exact .rejected child rejected
  | argumentsFault occurrence child accepted arguments =>
      cases occurrence_form occurrence
      exact .argumentsFault child accepted arguments
  | sourceArity occurrence child accepted arguments mismatch =>
      cases occurrence_form occurrence
      exact .sourceArity child accepted arguments mismatch
  | applied occurrence _uncoerced child accepted arguments _arity called =>
      cases occurrence_form occurrence
      exact .applied child accepted arguments called
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | tupleValue occurrence _ _ | tupleFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _ => cases occurrence_form occurrence

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel)
    (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

/-- The actual failed Source parent already supplies its original grade,
outcome and heap. This is the native result and complete caller post at that
same endpoint, constructed by strict child preservation. -/
def NativeResultAt (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ value finalStore finalMap finalWorld,
    Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type
      lowered.type callFaults outcome value ∧
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world before store finalMap finalWorld after finalStore ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context compiler.original.type outcome reached

/-- The successful prefix keeps the actual Source application and its strict
grade, together with the constructed original native callee/arguments and
complete reached admission. It contains no native application law. -/
def ApplicationAt (budget size : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap sources,
    size = Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize] ∧
    applicationSize < budget ∧
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after ∧
    CellAwareScopeIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial owner
      sourceValue calleeHeap argumentsHeap sources

include positive prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped environments heaps locals agrees typed admitted authority physical ownerFrame
  caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver in
/-- The literal original Source trace selects a branch once. Its three prefix
failure constructors produce the complete native parent. The actual successful
argument endpoint is retained for the independent application producer. -/
theorem preserves_fault_or_application (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    (children : CellAwareScopeExpressionBounds.PreservesBelow
      bridge context model named stages invocation certificate callFaults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    NativeResultAt (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) bridge profile compiler initial outcome after ∨
    ApplicationAt (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner budget size outcome after := by
  have calleeCertified : CellAwareScopeGeneralizedReadProjection.Certificate
      (compiled := compiled) named invocation scope callee compiler.calleeCode :=
    ⟨reasonAt, calleeCertificate, ⟨calleeRecipe⟩⟩
  have calleeChildren : CellAwareScopeExpressionBounds.PreservesBelow
      bridge context model named stages invocation
      (CellAwareScopeGeneralizedReadProjection.Certificate (compiled := compiled) named invocation)
      callFaults budget := fun size smaller =>
    CellAwareScopeGeneralizedReadProjection.preserves bridge context model named stages invocation
      callFaults (calleeMeaning size smaller)
  have parentFound : invocation.source.lookupExpression? id = some compiler.original := by
    rw [sourceEq]
    exact compiler.found
  have selected := source_prefix unique parentFound compiler.originalForm trace
  cases selected with
  | calleeFault child =>
    obtain ⟨_parent, token, finalStore, finalMap, finalWorld, result⟩ :=
      CellAwareScopeIndirectCalleeFaultBounds.preserves_callee_fault
        bridge functions compiler prepared sourceEq occurrence calleeCertified found sourceTyped
        environments heaps locals agrees typed initial admitted authority physical owner ownerFrame budget calleeChildren child within
    exact .inl ⟨.inLeft lowered.type (.word token), finalStore, finalMap, finalWorld, result⟩
  | @notCallable childSize sourceValue after child invalid =>
    have smaller : childSize < budget := Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize
      (child := childSize) (children := [childSize]) (by simp)) within
    have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
    have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
    obtain ⟨value, finalStore, finalMap, finalWorld, _evaluated, _represented, strong, _rest⟩ :=
      calleeMeaning _ smaller calleeCertificate calleeRecipe actualFound actualTyped environments heaps
        locals agrees typed initial admitted authority physical owner ownerFrame child
    obtain ⟨function, native, bindings, parameter, result, sourceValueEq, _output, _member⟩ := strong sourceValue rfl
    cases sourceValueEq
    exact False.elim (invalid trivial)
  | rejected child rejected =>
    obtain ⟨_parent, token, finalStore, finalMap, finalWorld, result⟩ :=
      CellAwareScopeIndirectFirstGateBounds.preserves_rejected
        bridge receiver compiler prepared stagePrepared sourceEq occurrence initial owner view guardFrame
        profile calleeCertificate calleeRecipe found sourceTyped environments heaps locals agrees typed admitted
        authority physical ownerFrame caller originalUnique sourceParent tree unique parentTyped budget calleeMeaning child within rejected
    exact .inl ⟨.inLeft lowered.type (.word token), finalStore, finalMap, finalWorld, result⟩
  | argumentsFault child accepted arguments =>
    obtain ⟨_parent, token, finalStore, finalMap, finalWorld, result⟩ :=
      CellAwareScopeIndirectArgumentFaultBounds.preserves_argument_fault
        bridge profile compiler prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped environments heaps locals
        agrees typed initial admitted authority physical owner ownerFrame caller view originalUnique guardFrame sourceParent tree unique parentTyped
        budget calleeMeaning children child accepted arguments within
    exact .inl ⟨.inLeft lowered.type (.word token), finalStore, finalMap, finalWorld, result⟩
  | sourceArity _ _ _ mismatch => exact False.elim (mismatch sourceParent.arity)
  | @applied calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap after sources outcome child accepted arguments called =>
    have prefixBound : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget := by
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil] at within ⊢
      omega
    have strict : applicationSize < budget := Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize
      (child := applicationSize) (children := [calleeSize, argumentsSize, applicationSize]) (by simp)) within
    have constructedPrefix := CellAwareScopeIndirectValuesPrefix.preserves_values
      bridge profile compiler prepared sourceEq calleeCertificate calleeRecipe found sourceTyped environments heaps locals agrees
      typed initial admitted authority physical owner ownerFrame caller view originalUnique guardFrame sourceParent tree unique parentTyped
      budget calleeMeaning children child accepted arguments prefixBound
    exact .inr ⟨_, _, _, _, _, _, _, rfl, strict, child, accepted, arguments, called, constructedPrefix⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectSourcePrefixDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationArguments
/-! Actual successful argument rows are aligned with the materialized closure.
The selected physical count supplies Source arity independently of packed types. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {environment : Dynamic.Environment}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {function : Dynamic.Closure} {carrier : Value} {parameter result : TypeSystem.Ty}
  {sourceTypes : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
  {calleeHeap : Dynamic.Heap} {index : ProtectedStateTransition.Index}
  (reached : callerProtocol.State index)
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
    site site.call ids (.closure function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar site callee ids originalMetadata originalNode dispatch.row)
  (count : dispatch.row.entry.parameterCount = ids.length)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

include bridge profile compiler reached dispatch selected count in
theorem at_arguments
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap sources sourceTypes)
    (extension : Dynamic.HeapMetadataExtend calleeHeap index.heap)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (admitted : Admission bridge context reached)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (calleeRelated : GenericHeap.PayloadModel.Represents model index.mapping index.world
      (.function parameter result) (.closure function) carrier compiler.calleeCode.type)
    (member : GeneralizedLocalMaterializedAssociation.Association compiled index.mapping index.world
      function carrier bindings parameterCore resultCore)
    (represented : DataExpressionSequence.Values model index.mapping index.world
      sourceTypes (compiler.codes.map (·.type)) sources values)
    {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment calleeHeap ids (.values sources) index.heap) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function index.heap sources ∧
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function ∧
    compiler.parameterType = parameterCore ∧ compiler.resultType = resultCore ∧
    CallableIndexedParameterMeaning.Arguments model index.mapping index.world bindings sources values := by
  have arity := SelectedCompilationPhysicalClosureArgumentRows.source_arity dispatch selected count trace
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack sources
  obtain ⟨raw, _rows⟩ := CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
    bridge reached runtime admitted calleeTyped extension argumentsTyped packing bundle arity
  obtain ⟨parameters, sourceResult, signatures, code, evidence, _captures⟩ := calleeTyped.closure_function_inv
  have valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function :=
    ⟨signatures.trans runtime.signatures, code.owner, code, code.requirement_ledger.idsUnique, evidence⟩
  have nativeType : compiler.calleeCode.type = CallableContract.functionType parameterCore resultCore :=
    (GenericHeap.PayloadModel.runtime_hasType model calleeRelated).type_eq.symm.trans member.runtime_hasType.type_eq
  have sameTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    ((actualFunctionType ▸ compiler.callableType).trans nativeType)
  have nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) = parameterCore :=
    (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
      (compiler.packedType.symm.trans sameTypes.1)
  exact ⟨raw, valid, sameTypes.1, sameTypes.2,
    GeneralizedLocalMaterializedArgumentRows.arguments member valid profile represented arity
      (bundle.trans parameters) nativeBundle⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationArguments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeApplicationBounds
/-! The application leaf consumes the actual materialized local closure at
its reached argument state. Its caller, frame owner and concrete effects are
retained; the finite expression dispatcher supplies the ordered prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open GeneralizedLocalMaterializedAssociation (Association)
open CallableIndexedOwnedStoredClosureSourceArguments (SourceArguments)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep)

/-- The actual Source application begins after all argument effects. -/
def PreservesAt (size : Nat) : Prop :=
  ∀ {scope mapping world environment canonical before store function native bindings parameter result sources values},
  ∀ association : Association compiled mapping world function native bindings parameter result,
    SourceArguments function before sources →
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function →
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment →
  ∀ physical : CellAwareScopePhysical.Physical compiled named context scope canonical
      mapping world before store environment,
  ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location → association.AtFrame owner.key.frameLocation →
  ∀ {outcome after},
    Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) registry size invocation
      context before (.closure function) sources outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates [native, DataPatternValues.packValues values] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld function.resultType result faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context function.resultType outcome reached

/-- The native payload computation yields its independent Source grade. -/
def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope mapping world environment canonical before store function native bindings parameter result sources values},
  ∀ association : Association compiled mapping world function native bindings parameter result,
    SourceArguments function before sources →
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function →
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources values →
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment →
  ∀ physical : CellAwareScopePhysical.Physical compiled named context scope canonical
      mapping world before store environment,
  ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    owner.key.frameLocation = physical.location → association.AtFrame owner.key.frameLocation →
  ∀ {value finalStore},
    EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) registry sourceSize invocation
        context before (.closure function) sources outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld function.resultType result faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context function.resultType outcome reached

def PreservesBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → PreservesAt bridge context model named registry invocation faults size

def ReflectsBelow (budget : Nat) : Prop :=
  ∀ size, size < budget → ReflectsAt bridge context model named registry invocation faults size

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationParentBounds
/-! The actual materialized application consumes the reached mixed argument
state and restores its caller. Ordered prefix effects compose with the body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open GeneralizedLocalMaterializedAssociation (Association)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}

section Parent
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {named : SourceCoreGeneralFunctions.Function}
  {functionModel : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {argumentMap : LocationMap} {argumentWorld : StoreTyping}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, argumentMap, argumentWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel)
    (GeneralizedLocalInstanceValues.model compiled.indexed)) argumentMap argumentWorld argumentsHeap argumentsStore)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] argumentMap argumentWorld argumentsHeap argumentsStore environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical
    argumentMap argumentWorld argumentsHeap argumentsStore environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  (maps : LocationMap.Extends mapping argumentMap) (worlds : WorldExtends world argumentWorld)
  (frame : AdministrativePreserved mapping store argumentMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)
  (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
    mapping world before store argumentMap argumentWorld argumentsHeap argumentsStore)
  {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
  (count : dispatch.row.entry.parameterCount = ids.length)
  (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids (.closure function))
  (argumentsTyped : Dynamic.ValuesHaveTypes context argumentsHeap sources sourceTypes)
  (argumentMetadata : Dynamic.HeapMetadataExtend calleeHeap argumentsHeap)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
  (calleeHeapTyped : Dynamic.HeapWellTyped context calleeHeap)
  (typing : ExpressionsHaveTypes invocation.source context ids sourceTypes)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (calleeRelated : GenericHeap.PayloadModel.Represents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel)
    argumentMap argumentWorld (.function parameter result) (.closure function) carrier compiler.calleeCode.type)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel)
    argumentMap argumentWorld sourceTypes (compiler.codes.map (·.type)) sources values)
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (association : Association compiled argumentMap argumentWorld function carrier bindings parameterCore resultCore)
  (atFrame : association.AtFrame owner.key.frameLocation)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions

local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bridge profile compiler prepared sourceParent occurrence related admitted heaps authority physical ownerFrame
  maps worlds frame heapMetadata effect dispatch selected count accepted argumentsTyped argumentMetadata runtime calleeTyped
  actualFunctionType calleeRelated represented association atFrame bundle originalResult in
/-- The genuine argument endpoint feeds the actual closure application once.
Its native suffix and original three binds complete the whole parent. -/
theorem preserves_parent
    (budget : Nat)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    {calleeSize argumentsSize applicationSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.closure function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap (.closure function) sources outcome after)
    (within : applicationSize < budget)
    {calleeStore : Store}
    (calleeNative : Evaluates actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore)
    (firstGate : Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore)
    (argumentsNative : Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
      invocation context environment before id outcome after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type callFaults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨raw, valid, _parameterEq, resultEq, parameters⟩ :=
    CellAwareScopeIndirectApplicationArguments.at_arguments bridge profile compiler reached dispatch
      selected count runtime argumentsTyped argumentMetadata calleeTyped bundle admitted
      actualFunctionType calleeRelated association represented argumentsTrace
  obtain ⟨value, finalStore, finalMap, finalWorld, application, resultRep, finalHeaps,
    applicationMaps, applicationWorlds, applicationFrame, applicationMetadata, applicationEffect,
    returned, callerRelated, returnedPost⟩ :=
    applicationMeaning _ within association raw valid parameters heaps reached admitted authority physical
      owner ownerFrame atFrame called
  have suffix := CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.preserves_suffix
    (actual := actual) (result := compiler.resultType)
    (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
    dispatch.shape selected dispatch.found count application
  have whole : Evaluates actual store
      (CallableContract.call prepared.site.gates
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
        (compiler.calleeCode.expression.rename ξ)
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore := by
    apply LanguageResult.bind_success compiler.resultType calleeNative
    apply LanguageResult.bind_success compiler.resultType firstGate
    apply LanguageResult.bind_success compiler.resultType
    · simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
    · exact suffix
  rw [← prepared.lowered_rename compiler ξ] at whole
  have sameSource : compiler.original.type = function.resultType := by
    obtain ⟨_parameters, sourceResult, _signatures, _code, _covers, _captures⟩ := calleeTyped.closure_function_inv
    exact originalResult.trans sourceResult
  have sameCore : lowered.type = resultCore :=
    (congrArg (fun output => output.type) compiler.output).trans (compiler.resultTypeEq.symm.trans resultEq)
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    exact returnedPost
  exact ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    value, finalStore, finalMap, finalWorld, whole, parentRep, finalHeaps,
    maps.trans applicationMaps, worlds.trans applicationWorlds, frame.trans applicationFrame,
    heapMetadata.trans applicationMetadata, effect.trans applicationEffect, returned, callerProtocol.trans related callerRelated, parentPost⟩

include bridge profile compiler prepared sourceParent occurrence related admitted heaps authority physical ownerFrame
  maps worlds frame heapMetadata effect dispatch selected count accepted argumentsTyped argumentMetadata runtime calleeTyped
  actualFunctionType calleeRelated represented association atFrame bundle originalResult in
/-- The concrete selected closure suffix constructs the original applied
parent. Both numeric grades and every transient reached effect are retained. -/
theorem reflects_suffix
    (budget : Nat)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    {calleeSize argumentsSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.closure function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {suffixSize : Nat} {value : Value} {finalStore : Store}
    (suffix : EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : suffixSize ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type callFaults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨raw, valid, _parameterEq, resultEq, parameters⟩ :=
    CellAwareScopeIndirectApplicationArguments.at_arguments bridge profile compiler reached dispatch
      selected count runtime argumentsTyped argumentMetadata calleeTyped bundle admitted
      actualFunctionType calleeRelated association represented argumentsTrace
  obtain ⟨applicationSize, strict, application⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.reflects_suffix dispatch.shape
      selected dispatch.found count suffix within
  obtain ⟨applicationSourceSize, outcome, after, finalMap, finalWorld, applied, resultRep, finalHeaps,
    applicationMaps, applicationWorlds, applicationFrame, applicationMetadata, applicationEffect,
    returned, callerRelated, returnedPost⟩ :=
    applicationMeaning _ strict association raw valid parameters heaps reached admitted authority physical
      owner ownerFrame atFrame application
  have sameSource : compiler.original.type = function.resultType := by
    obtain ⟨_parameters, sourceResult, _signatures, _code, _covers, _captures⟩ := calleeTyped.closure_function_inv
    exact originalResult.trans sourceResult
  have sameCore : lowered.type = resultCore :=
    (congrArg (fun output => output.type) compiler.output).trans (compiler.resultTypeEq.symm.trans resultEq)
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    exact returnedPost
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSourceSize],
    outcome, after, finalMap, finalWorld,
    .applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity applied,
    parentRep, finalHeaps, maps.trans applicationMaps, worlds.trans applicationWorlds,
    frame.trans applicationFrame, heapMetadata.trans applicationMetadata, effect.trans applicationEffect,
    returned, callerProtocol.trans related callerRelated, parentPost⟩

end Parent

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationParentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectSecondGateBounds
/-! The reached second gate uses the original selected row and receiving
word. Its genuine count branch preserves the same mixed argument heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectSecondGateBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds (NamedOrigin source_at_boundary rejected_suffix)
universe u

section WholeParent
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (sourceParent : SourceParent compiler)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "publicFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include caller occurrence sourceParent preparedStages receiver in
omit positive in
/-- The actual selected count decides the branch internally. Successful
arguments already carry their real independent grades and reached admission.
The mismatch constructs Source arity, its literal receiver lookup and the same
whole-parent fault post. The equal-count alternative retains only that actual
row fact for the separate application producer. -/
theorem classify_application_prefix {budget size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    («prefix» : CellAwareScopeIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context) (stages := stages)
      (invocation := invocation) (environment := environment) (actual := actual)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner budget value finalStore) :
    ∃ originalNode originalMetadata row,
      Selected sidecar prepared.site callee ids originalMetadata originalNode row ∧
      (row.entry.parameterCount = ids.length ∨
        ∃ sourceSize after token finalMap finalWorld,
          Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
            invocation context environment before id
            (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length))) after ∧
          value = .inLeft lowered.type (.word token) ∧
          CellAwareScopeIndirectCalleeFaultBounds.ResultAt
            (registry := completion.result.context.registry) (faults := publicFaults) (context := context)
            (actual := actual) (ξ := ξ) bridge functions compiler initial
            (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)) after token finalStore finalMap finalWorld) := by
  obtain ⟨rawParameter, rawResult, _calleeType, _bundle, _originalResult,
    calleeSize, argumentsSize, sourceValue, calleeHeap, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    child, accepted, arguments, _representedValues, _representedCallee, strong, _callView, boundary,
    finalHeaps, maps, worlds, frame, metadataExtension, effect, ⟨reached, related, admitted⟩,
    suffixSize, suffix, _strict⟩ := «prefix»
  have namedOrigins : NamedOrigin compiled sourceValue := by
    intro global same
    obtain ⟨function, native, bindings, parameter, result, closure, _rest⟩ := strong sourceValue rfl
    rw [closure] at same
    cases same
  obtain ⟨raw, tag, row, shape, selected, found, sourceFault⟩ :=
    source_at_boundary caller occurrence compiler.argumentCoercions sourceParent.arity
      child accepted arguments boundary namedOrigins
  refine ⟨originalNode, originalMetadata, row, selected, ?_⟩
  by_cases same : row.entry.parameterCount = ids.length
  · exact .inl same
  · have lowerType : lowered.type = compiler.resultType :=
      (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
    obtain ⟨sameValue, sameStore⟩ := rejected_suffix shape selected found same suffix
    cases sameStore
    obtain ⟨diagnostic, decoded, error⟩ :=
      CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiving_diagnostic
        compiler prepared preparedStages selected receiver same
    have represented : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type
        (CallableIndexedOwnedPreparedSecondCallGateRejection.stagedArityFaults completion.result.diagnostics)
        (.fault (.semantic (.argumentArityMismatch row.entry.parameterCount ids.length)))
        (.inLeft lowered.type (.word (prepared.site.reasonAt row.caller row.call row.entry.id
          .beforeApplication (.argumentArityMismatch row.entry.parameterCount ids.length)))) :=
      .fault ⟨row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩
    refine .inr ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
      argumentsHeap, prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
        (.argumentArityMismatch row.entry.parameterCount ids.length),
      finalMap, finalWorld, sourceFault same, ?_, ?_⟩
    · simpa only [lowerType] using sameValue
    · refine ⟨?_, CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model represented,
        finalHeaps, maps, worlds, frame, metadataExtension, effect, reached, related, ?_⟩
      · simpa only [sameValue, lowerType] using completed.sound
      · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
        exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩
end WholeParent
end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectSecondGateBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationDispatch
/-! The materialization retained by the original callee determines the
application branch. Both real gates and every reached argument effect remain
part of the parent computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel)
    (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) stages)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

include prepared sourceEq occurrence found locals authority physical ownerFrame guardFrame sourceParent
  tree unique parentTyped stagePrepared receiver selectedBodies runtime covers actualFunctionType in
omit positive in
theorem preserves_application_selected (budget : Nat)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    {calleeSize argumentsSize applicationSize : Nat} {sourceValue : Dynamic.Value}
    {calleeHeap argumentsHeap after : Dynamic.Heap} {sources : List Dynamic.Value}
    {outcome : Staging.Recursive.Outcome}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after)
    (within : applicationSize < budget)
    (prefixResult : CellAwareScopeIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner sourceValue calleeHeap argumentsHeap sources) :
    CellAwareScopeIndirectSourcePrefixDispatch.NativeResultAt (functionModel := functionModel)
      (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) bridge profile compiler initial outcome after := by
  obtain ⟨rawParameter, rawResult, functionType, bundle, originalResult,
    calleeStore, calleeMap, calleeWorld, carrier, values, argumentsStore, finalMap, finalWorld,
    originalNode, originalMetadata, calleePost, calleeTyped, firstGate, argumentsNative,
    represented, calleeRelated, strong, _callView, boundary, heaps, maps, worlds,
    frame, heapMetadata, effect, reached, related, admitted⟩ := prefixResult
  obtain ⟨function, native, bindings, parameterCore, resultCore, sourceValueEq, nativeEq, association, atFrame⟩ :=
    strong sourceValue rfl
  cases sourceValueEq
  have nativeSame := Value.inRight.inj nativeEq
  cases nativeSame.2
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
      originalTree originalUnique originalTyping found
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  cases boundary with
  | user dispatch selected =>
    by_cases count : dispatch.row.entry.parameterCount = ids.length
    · have calleeNative := calleePost.1
      obtain ⟨_nativeCallee, _representedCallee, _strong, _calleeHeaps, _calleeMaps, _calleeWorlds,
        _calleeFrame, calleeMetadata, _calleeEffect, calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
      have rawCallee : Dynamic.ValueHasType context calleeHeap (.closure function)
          (.function rawParameter rawResult) := by simpa only [functionType] using calleeTyped
      have relatedCallee : GenericHeap.PayloadModel.Represents model finalMap finalWorld
          (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type := by
        simpa only [functionType] using calleeRelated
      obtain ⟨sourceValuesTyped, _heapTyped, argumentMetadata⟩ :=
        SelectedStagedArgumentTyping.values_at selectedBodies runtime covers
          (locals.mono calleeMetadata) calleeAdmission.at_value.2.heap typing argumentsTrace
      exact (CellAwareScopeIndirectApplicationParentBounds.preserves_parent
        bridge profile compiler prepared sourceParent occurrence initial reached related admitted heaps
        (authority.transport effect) (physical.transport effect frame) owner ownerFrame
        maps worlds frame heapMetadata effect dispatch selected count accepted sourceValuesTyped argumentMetadata
        runtime rawCallee actualFunctionType relatedCallee represented association atFrame bundle originalResult
        budget applicationMeaning calleeTrace argumentsTrace called within calleeNative firstGate argumentsNative).2
    · have physicalCount := CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected
      have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
      have different : function.parameters.length ≠ ids.length := by simpa only [physicalCount] using count
      cases called with
      | closure selectedChild valid parameters _copy allocate bodyTrace bodyResult =>
        exact False.elim (different (allocate.length_eq.trans valuesCount))
      | closureArity mismatch =>
        have actualAccepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar)
            prepared.site.call ids (.closure function) := by simpa only [guardFrame, prepared.call] using accepted
        have argumentsWeaken : Evaluates (.unit :: carrier :: actual) calleeStore
            (((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
            (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
          simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
        have evaluated := CallableIndexedOwnedPreparedSecondCallGateRejection.user_native_preserves
          (result := compiler.resultType) dispatch selected actualAccepted count
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown calleePost.1 argumentsWeaken
        change Evaluates actual store
          (CallableContract.call prepared.site.gates compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
            compiler.resultType (compiler.calleeCode.expression.rename ξ)
            ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) _ argumentsStore at evaluated
        rw [← prepared.lowered_rename compiler ξ] at evaluated
        obtain ⟨diagnostic, decoded, error⟩ :=
          CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiving_diagnostic
            compiler prepared stagePrepared selected receiver count
        have received : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type lowered.type
            (CallableIndexedOwnedPreparedSecondCallGateRejection.stagedArityFaults completion.result.diagnostics)
            (.fault (.semantic (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)))
            (.inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
              .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)))) :=
          .fault ⟨dispatch.row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩
        have lowerType : lowered.type = compiler.resultType :=
          (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
        have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model received
        refine ⟨.inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
            .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))),
          argumentsStore, finalMap, finalWorld, ?_, ?_, heaps, maps, worlds, frame,
          heapMetadata, effect, reached, related, ?_⟩
        · simpa only [lowerType] using evaluated
        · simpa only [physicalCount, valuesCount] using faultRep
        · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
          exact ⟨admitted.rows, by intro value impossible; cases impossible⟩

/-- The real native suffix returns its independent Source grade and exact post. -/
def ReflectedResult (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize outcome after finalMap finalWorld,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before id outcome after ∧
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type lowered.type
      callFaults outcome value ∧
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
      (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
      mapping world before store finalMap finalWorld after finalStore ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial reached ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context compiler.original.type outcome reached

include prepared sourceEq occurrence found sourceTyped locals admitted authority physical ownerFrame sourceParent
  tree unique parentTyped stagePrepared receiver selectedBodies runtime covers actualFunctionType in
omit positive in
theorem reflects_application_selected (budget : Nat)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (_completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (prefixResult : CellAwareScopeIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner budget value finalStore) :
    ReflectedResult (functionModel := functionModel) (completion := completion)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      bridge profile compiler initial value finalStore := by
  obtain ⟨rawParameter, rawResult, functionType, bundle, originalResult,
    calleeSize, argumentsSize, sourceValue, calleeHeap, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    calleeTrace, accepted, argumentsTrace, represented, calleeRelated, strong, _callView, boundary,
    heaps, maps, worlds, frame, heapMetadata, effect, ⟨reached, related, reachedAdmission⟩,
    suffixSize, suffix, strict⟩ := prefixResult
  obtain ⟨function, native, bindings, parameterCore, resultCore, sourceValueEq, nativeEq, association, atFrame⟩ :=
    strong sourceValue rfl
  cases sourceValueEq
  have nativeSame := Value.inRight.inj nativeEq
  cases nativeSame.2
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent originalTree originalUnique originalTyping found
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by
    simpa only [sourceEq] using sourceTyped
  have calleeSource := Staging.Recursive.SelectedPreservation.expression selectedBodies
    runtime covers locals admitted.heap actualTyped calleeTrace
  have rawCallee : Dynamic.ValueHasType context calleeHeap (.closure function) (.function rawParameter rawResult) := by
    simpa only [functionType] using calleeSource.value_typed _ rfl
  have relatedCallee : GenericHeap.PayloadModel.Represents model finalMap finalWorld
      (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type := by
    simpa only [functionType] using calleeRelated
  obtain ⟨sourceValuesTyped, _heapTyped, argumentMetadata⟩ :=
    SelectedStagedArgumentTyping.values_at selectedBodies runtime covers
      (locals.mono calleeSource.heap_extends) calleeSource.heap_typed typing argumentsTrace
  cases boundary with
  | user dispatch selected =>
    by_cases count : dispatch.row.entry.parameterCount = ids.length
    · exact CellAwareScopeIndirectApplicationParentBounds.reflects_suffix
        bridge profile compiler prepared sourceParent occurrence initial reached related reachedAdmission heaps
        (authority.transport effect) (physical.transport effect frame) owner ownerFrame
        maps worlds frame heapMetadata effect dispatch selected count accepted sourceValuesTyped argumentMetadata
        runtime rawCallee actualFunctionType relatedCallee represented association atFrame bundle originalResult
        budget applicationMeaning calleeTrace argumentsTrace suffix (Nat.le_of_lt strict)
    · have physicalCount := CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected
      have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
      have mismatch : function.parameters.length ≠ sources.length := by simpa only [physicalCount, valuesCount] using count
      obtain ⟨valueEq, storeEq⟩ := CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix
        dispatch.shape selected dispatch.found count suffix
      cases storeEq
      obtain ⟨diagnostic, decoded, error⟩ :=
        CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics.receiving_diagnostic
          compiler prepared stagePrepared selected receiver count
      have received : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld compiler.original.type lowered.type
          (CallableIndexedOwnedPreparedSecondCallGateRejection.stagedArityFaults completion.result.diagnostics)
          (.fault (.semantic (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)))
          (.inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
            .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)))) :=
        .fault ⟨dispatch.row.entry.parameterCount, ids.length, diagnostic, rfl, decoded, error⟩
      have lowerType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model received
      refine ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
        .fault (.semantic (.argumentArityMismatch function.parameters.length sources.length)),
        argumentsHeap, finalMap, finalWorld,
        .applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity (.closureArity mismatch),
        ?_, heaps, maps, worlds, frame, heapMetadata, effect, reached, related, ?_⟩
      · simpa only [valueEq, lowerType, physicalCount, valuesCount] using faultRep
      · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
        exact ⟨reachedAdmission.rows, by intro value impossible; cases impossible⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include prepared sourceEq occurrence found locals authority physical ownerFrame guardFrame sourceParent
  tree unique parentTyped stagePrepared receiver wellFormed runtime covers actualFunctionType in
omit positive in
theorem preserves_application (budget : Nat)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    {calleeSize argumentsSize applicationSize : Nat} {sourceValue : Dynamic.Value}
    {calleeHeap argumentsHeap after : Dynamic.Heap} {sources : List Dynamic.Value}
    {outcome : Staging.Recursive.Outcome}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after)
    (within : applicationSize < budget)
    (prefixResult : CellAwareScopeIndirectValuesPrefix.ValuesPrefix (functionModel := functionModel)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner sourceValue calleeHeap argumentsHeap sources) :
    CellAwareScopeIndirectSourcePrefixDispatch.NativeResultAt (functionModel := functionModel)
      (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) bridge profile compiler initial outcome after := by
  apply preserves_application_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (prepared := prepared) (sourceEq := sourceEq) (occurrence := occurrence) (found := found) (locals := locals) (authority := authority) (physical := physical) (ownerFrame := ownerFrame) (guardFrame := guardFrame) (sourceParent := sourceParent) (tree := tree) (unique := unique) (parentTyped := parentTyped) (stagePrepared := stagePrepared) (receiver := receiver) (runtime := runtime) (covers := covers) (actualFunctionType := actualFunctionType) <;> assumption

include prepared sourceEq occurrence found sourceTyped locals admitted authority physical ownerFrame sourceParent
  tree unique parentTyped stagePrepared receiver wellFormed runtime covers actualFunctionType in
omit positive in
theorem reflects_application (budget : Nat)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (_completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (prefixResult : CellAwareScopeIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner budget value finalStore) :
    ReflectedResult (functionModel := functionModel) (completion := completion)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      bridge profile compiler initial value finalStore := by
  apply reflects_application_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (prepared := prepared) (sourceEq := sourceEq) (occurrence := occurrence) (found := found) (sourceTyped := sourceTyped) (locals := locals) (admitted := admitted) (authority := authority) (physical := physical) (ownerFrame := ownerFrame) (sourceParent := sourceParent) (tree := tree) (unique := unique) (parentTyped := parentTyped) (stagePrepared := stagePrepared) (receiver := receiver) (runtime := runtime) (covers := covers) (actualFunctionType := actualFunctionType) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectFaultDispatch
/-! Whole-parent reflection joins the genuine callee, first-gate and ordered-argument fault prefixes. The authentic successful argument suffix remains available for its concrete application producer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectFaultDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CellAwareScopeIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {certificate : GenericExpressionMeaning.Certificate}
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel)
    (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (ownerFrame : owner.key.frameLocation = physical.location)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

/-- A fault branch of the actual native parent, with its independently sized
Source derivation and the exact token, reached state and failure tag. -/
def FaultResult (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize failure after token finalMap finalWorld,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
      invocation context environment before id (.fault failure) after ∧
    value = .inLeft lowered.type (.word token) ∧
    CellAwareScopeIndirectCalleeFaultBounds.ResultAt
      (registry := completion.result.context.registry) (faults := callFaults) (context := context)
      (actual := actual) (ξ := ξ) bridge functions compiler initial
      failure after token finalStore finalMap finalWorld

include positive receiver prepared stagePrepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
  environments heaps locals agrees typed admitted authority physical ownerFrame caller view originalUnique guardFrame
  sourceParent tree unique parentTyped in
/-- The actual whole parent is inverted once. Every reached callee, first-gate
or ordered-argument failure becomes its exact parent result. Successful
arguments retain the authentic application suffix for its concrete producer. -/
theorem reflects_fault_or_application (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow
      bridge context model named stages invocation certificate callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    FaultResult (functionModel := functionModel) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ)
      bridge compiler initial profile value finalStore ∨
    CellAwareScopeIndirectArgumentPrefix.ApplicationPrefix (functionModel := functionModel)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (registry := completion.result.context.registry) (context := context)
      (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial owner budget value finalStore := by
  rcases CellAwareScopeIndirectArgumentPrefix.reflects_arguments
      bridge profile compiler prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
      environments heaps locals agrees typed initial admitted authority physical owner ownerFrame caller view originalUnique
      guardFrame sourceParent tree unique parentTyped budget calleeMeaning children completed within with
    calleeFault | stageRejected | argumentFault | application
  · obtain ⟨_nativeSize, sourceSize, failure, token, after, finalMap, finalWorld,
      _native, _strict, _child, parentTrace, valueEq, post⟩ := calleeFault
    exact .inl ⟨Staging.Recursive.Size.stepSize [sourceSize], failure, after, token,
      finalMap, finalWorld, parentTrace, valueEq, post⟩
  · obtain ⟨sourceSize, reason, after, token, finalMap, finalWorld,
      parentTrace, valueEq, post⟩ :=
      CellAwareScopeIndirectFirstGateBounds.reflects_rejected_prefix
        bridge receiver compiler prepared stagePrepared sourceEq occurrence initial owner
        view guardFrame profile budget stageRejected
    exact .inl ⟨sourceSize, .stage invocation id reason, after, token,
      finalMap, finalWorld, parentTrace, valueEq, post⟩
  · obtain ⟨calleeSize, argumentsSize, sourceValue, calleeHeap, failure, after,
      token, finalMap, finalWorld, _callee, _accepted, _arguments,
      parentTrace, valueEq, post⟩ := argumentFault
    exact .inl ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize],
      failure, after, token, finalMap, finalWorld, parentTrace, valueEq, post⟩
  · exact .inr application

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectFaultDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectBounds
/-! The whole indirect parent connects its literal callee, gates, ordered
arguments and actual materialized application in both directions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving
    headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins
    headers keys bodyRegistry semanticFaults profile functionModel]
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functionModel)
    (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)

local notation "functions" => functionModel
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) stages)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

include positive prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
  environments heaps locals agrees typed admitted authority physical ownerFrame
  caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver
  selectedBodies runtime covers actualFunctionType in
theorem preserves_selected (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    (children : CellAwareScopeExpressionBounds.PreservesBelow
      bridge context model named stages invocation certificate callFaults budget)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    CellAwareScopeIndirectSourcePrefixDispatch.NativeResultAt (functionModel := functionModel)
      (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) bridge profile compiler initial outcome after := by
  rcases CellAwareScopeIndirectSourcePrefixDispatch.preserves_fault_or_application
      bridge profile compiler prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
      environments heaps locals agrees typed initial admitted authority physical owner ownerFrame
      caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver
      budget calleeMeaning children trace within with failed | applied
  · exact failed
  · obtain ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap, argumentsHeap, sources,
      _size, strict, child, accepted, arguments, called, prefixResult⟩ := applied
    exact CellAwareScopeIndirectApplicationDispatch.preserves_application_selected
      bridge profile compiler prepared sourceEq occurrence found locals initial authority physical owner ownerFrame
      guardFrame sourceParent tree unique parentTyped stagePrepared receiver selectedBodies runtime covers actualFunctionType
      budget applicationMeaning child accepted arguments called strict prefixResult

include positive prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
  environments heaps locals agrees typed admitted authority physical ownerFrame
  caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver
  selectedBodies runtime covers actualFunctionType in
theorem reflects_selected (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow
      bridge context model named stages invocation certificate callFaults budget)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    CellAwareScopeIndirectApplicationDispatch.ReflectedResult (functionModel := functionModel)
      (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      bridge profile compiler initial value finalStore := by
  rcases CellAwareScopeIndirectFaultDispatch.reflects_fault_or_application
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial owner view guardFrame
      profile calleeCertificate calleeRecipe found sourceTyped environments heaps locals agrees typed admitted
      authority physical ownerFrame caller originalUnique sourceParent tree unique parentTyped
      budget calleeMeaning children completed within with failed | applied
  · obtain ⟨sourceSize, failure, after, token, finalMap, finalWorld, trace, valueEq,
      _evaluated, represented, rest⟩ := failed
    rw [valueEq]
    exact ⟨sourceSize, .fault failure, after, finalMap, finalWorld, trace, represented, rest⟩
  · exact CellAwareScopeIndirectApplicationDispatch.reflects_application_selected
      bridge profile compiler prepared sourceEq occurrence found sourceTyped locals initial admitted authority physical
      owner ownerFrame sourceParent tree unique parentTyped stagePrepared receiver selectedBodies runtime covers actualFunctionType
      budget applicationMeaning completed applied

/- Compatibility adapters for callers with a whole-program receipt. -/
include positive prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
  environments heaps locals agrees typed admitted authority physical ownerFrame
  caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver
  wellFormed runtime covers actualFunctionType in
theorem preserves (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    (children : CellAwareScopeExpressionBounds.PreservesBelow
      bridge context model named stages invocation certificate callFaults budget)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow
      bridge context model named stages invocation callFaults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    CellAwareScopeIndirectSourcePrefixDispatch.NativeResultAt (functionModel := functionModel)
      (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) bridge profile compiler initial outcome after := by
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (positive := positive) (prepared := prepared) (sourceEq := sourceEq) (occurrence := occurrence) (calleeCertificate := calleeCertificate) (calleeRecipe := calleeRecipe) (found := found) (sourceTyped := sourceTyped) (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed) (admitted := admitted) (authority := authority) (physical := physical) (ownerFrame := ownerFrame) (caller := caller) (view := view) (originalUnique := originalUnique) (guardFrame := guardFrame) (sourceParent := sourceParent) (tree := tree) (unique := unique) (parentTyped := parentTyped) (stagePrepared := stagePrepared) (receiver := receiver) (runtime := runtime) (covers := covers) (actualFunctionType := actualFunctionType) <;> assumption

include positive prepared sourceEq occurrence calleeCertificate calleeRecipe found sourceTyped
  environments heaps locals agrees typed admitted authority physical ownerFrame
  caller view originalUnique guardFrame sourceParent tree unique parentTyped stagePrepared receiver
  wellFormed runtime covers actualFunctionType in
theorem reflects (budget : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow
      bridge context model named stages invocation certificate callFaults budget)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow
      bridge context model named stages invocation callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    CellAwareScopeIndirectApplicationDispatch.ReflectedResult (functionModel := functionModel)
      (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      bridge profile compiler initial value finalStore := by
  apply reflects_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (positive := positive) (prepared := prepared) (sourceEq := sourceEq) (occurrence := occurrence) (calleeCertificate := calleeCertificate) (calleeRecipe := calleeRecipe) (found := found) (sourceTyped := sourceTyped) (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees) (typed := typed) (admitted := admitted) (authority := authority) (physical := physical) (ownerFrame := ownerFrame) (caller := caller) (view := view) (originalUnique := originalUnique) (guardFrame := guardFrame) (sourceParent := sourceParent) (tree := tree) (unique := unique) (parentTyped := parentTyped) (stagePrepared := stagePrepared) (receiver := receiver) (runtime := runtime) (covers := covers) (actualFunctionType := actualFunctionType) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectHeadBounds
/-! The actual named compiler head supplies static call authority. Strong
read and materialized application leaves are joined internally at real states. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared SourceParent)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port Point)
open CellAwareScopeExpressionBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {named : SourceCoreGeneralFunctions.Function}
  {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry semanticFaults profile functionModel]
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) stages)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functionModel
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include positive bridge receiver stagePrepared sourceEq profile selectedBodies runtime covers unique actualFunctionType in
theorem preserves_selected
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      source scope callee reasonAt compiler.calleeCode)
    (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
    {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.PreservesBelow bridge context model named stages invocation callFaults size)
    (children : PreservesBelow bridge context model named stages invocation certificate callFaults size)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow bridge context model named stages invocation callFaults size) :
    PreservesAt bridge context model named stages invocation (Point scope id lowered) callFaults size := by
  intro current child code point node found parentTyped
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases sourceEq
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨parameter, result, rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  exact CellAwareScopeIndirectBounds.preserves_selected
    bridge profile compiler port.prepared rfl occurrence calleeCertificate calleeRecipe port.calleeFound sourceTyped
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame
    port.caller port.view port.originalUnique port.guardFrame port.sourceParent tree unique parentTyped
    stagePrepared receiver selectedBodies runtime covers actualFunctionType
    size calleeMeaning children applicationMeaning trace (Nat.le_refl _)

include positive bridge receiver stagePrepared sourceEq profile selectedBodies runtime covers unique actualFunctionType in
theorem reflects_selected
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      source scope callee reasonAt compiler.calleeCode)
    (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
    {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.ReflectsBelow bridge context model named stages invocation callFaults size)
    (children : ReflectsBelow bridge context model named stages invocation certificate callFaults size)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow bridge context model named stages invocation callFaults size) :
    ReflectsAt bridge context model named stages invocation (Point scope id lowered) callFaults size := by
  intro current child code point node found parentTyped
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases sourceEq
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨parameter, result, rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  exact CellAwareScopeIndirectBounds.reflects_selected
    bridge profile compiler port.prepared rfl occurrence calleeCertificate calleeRecipe port.calleeFound sourceTyped
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame
    port.caller port.view port.originalUnique port.guardFrame port.sourceParent tree unique parentTyped
    stagePrepared receiver selectedBodies runtime covers actualFunctionType
    size calleeMeaning children applicationMeaning completed (Nat.le_refl _)

/- Compatibility adapters for callers with a whole-program receipt. -/
include positive bridge receiver stagePrepared sourceEq profile wellFormed runtime covers unique actualFunctionType in
theorem preserves
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      source scope callee reasonAt compiler.calleeCode)
    (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
    {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.PreservesBelow bridge context model named stages invocation callFaults size)
    (children : PreservesBelow bridge context model named stages invocation certificate callFaults size)
    (applicationMeaning : CellAwareScopeApplicationBounds.PreservesBelow bridge context model named stages invocation callFaults size) :
    PreservesAt bridge context model named stages invocation (Point scope id lowered) callFaults size := by
  apply preserves_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (positive := positive) (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared) (sourceEq := sourceEq) (profile := profile) (runtime := runtime) (covers := covers) (unique := unique) (actualFunctionType := actualFunctionType) <;> assumption

include positive bridge receiver stagePrepared sourceEq profile wellFormed runtime covers unique actualFunctionType in
theorem reflects
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      source scope callee reasonAt compiler.calleeCode)
    (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
    {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (calleeMeaning : CellAwareScopeGeneralizedReadBounds.ReflectsBelow bridge context model named stages invocation callFaults size)
    (children : ReflectsBelow bridge context model named stages invocation certificate callFaults size)
    (applicationMeaning : CellAwareScopeApplicationBounds.ReflectsBelow bridge context model named stages invocation callFaults size) :
    ReflectsAt bridge context model named stages invocation (Point scope id lowered) callFaults size := by
  apply reflects_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) (positive := positive) (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared) (sourceEq := sourceEq) (profile := profile) (runtime := runtime) (covers := covers) (unique := unique) (actualFunctionType := actualFunctionType) <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceCalleeLifting
/-! A lifted indirect callee reaches its actual physical payload before the
original authenticated stage guard is classified. Rejection preserves that
prefix heap; acceptance retains the same state for ordered arguments. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceCalleeLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open Staging.Recursive.Lifting (ExpressionLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functions : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry semanticFaults profile functions]
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include positive port tree unique parentTyped in
theorem guard_at {value : Dynamic.Value} {after : Dynamic.Heap}
    {carrier : Value} {calleeStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (post : CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := port.calleeNode) bridge functions compiler initial owner
      value after carrier calleeStore finalMap finalWorld) :
    Staging.CallBoundary.GuardAccepts invocation.guards id ids value ∨
      ∃ reason, Staging.CallBoundary.GuardRejects invocation.guards id ids value reason := by
  obtain ⟨_original, _originalMetadata, _contained, _form, _view, boundary⟩ :=
    CellAwareScopeIndirectArgumentPrefix.scoped_boundary
      (sourceEq := rfl) (found := port.calleeFound) (sourceParent := port.sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped)
      bridge profile compiler port.prepared initial owner port.caller port.view port.originalUnique post
  cases boundary with
  | user dispatch _selected =>
    rcases Staging.CallGuard.complete (CallableLedger.frame port.sidecar).stages _ port.prepared.site.call ids with accepted | ⟨reason, rejected⟩
    · left
      simpa only [port.guardFrame, port.prepared.call] using
        (Staging.CallBoundary.GuardAccepts.contract dispatch.bound accepted)
    · right
      refine ⟨reason, ?_⟩
      simpa only [port.guardFrame, port.prepared.call] using
        (Staging.CallBoundary.GuardRejects.contract dispatch.bound rejected)
  | builtin _receipt => exact .inl (.builtin _)

include positive calleeCertificate calleeRecipe sourceTyped tree unique parentTyped environments heaps locals agrees typed admitted authority physical ownerFrame in
theorem callee_value
    (preservation : ∀ stageSize, CellAwareScopeGeneralizedReadBounds.PreservesAt
      bridge context model named stages invocation faults stageSize)
    {size : Nat} {value : Dynamic.Value} {calleeHeap : Dynamic.Heap}
    {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) size context
      invocation.evidence invocation.source environment before callee value calleeHeap) :
    ExpressionLift (Program.ofChecked compiled.sourceProgram) stages invocation context environment before id plain after ∨
    ∃ carrier calleeStore finalMap finalWorld,
      Staging.Recursive.Expression (Program.ofChecked compiled.sourceProgram) stages invocation context environment
        before callee (.value value) calleeHeap ∧
      CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
        (calleeNode := port.calleeNode) bridge functions compiler initial owner
        value calleeHeap carrier calleeStore finalMap finalWorld ∧
      Staging.CallBoundary.GuardAccepts invocation.guards id ids value := by
  have occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  have lifted := CellAwareSourceReadLifting.read (registry := stages) unique
    calleeCertificate.observations.originalFound calleeCertificate.observations.originalForm
    calleeCertificate.observations.originalCoercions (.value trace.sound)
  obtain ⟨stageSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
  obtain ⟨carrier, calleeStore, finalMap, finalWorld, evaluated, represented, strong, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    preservation stageSize calleeCertificate calleeRecipe port.calleeFound sourceTyped
      environments heaps locals agrees typed initial admitted authority physical owner ownerFrame measured
  cases represented with
  | value payload =>
    have full : CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
        (calleeNode := port.calleeNode) bridge functions compiler initial owner
        value calleeHeap _ calleeStore finalMap finalWorld :=
      ⟨evaluated, payload, strong, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
    rcases guard_at bridge profile compiler port tree unique parentTyped initial owner full with accepted | ⟨reason, rejected⟩
    · exact .inr ⟨_, _, _, _, lifted, full, accepted⟩
    · exact .inl ⟨_, _, .rejected occurrence lifted rejected, .rejected invocation id reason _⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceCalleeLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourcePrefixLifting
/-! The original ordinary indirect call reaches either its exact staged
outcome or the genuine post-argument application prefix. Every nested rejection
keeps the heap reached before the remaining ordinary effects. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourcePrefixLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareScopeSourceLiftBounds (LiftsAt)
open CellAwareScopeIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open Staging.Recursive.Lifting (ExpressionLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functions : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry semanticFaults profile functions]
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
    invocation.source scope callee reasonAt compiler.calleeCode)
  (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
  (sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
    named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


def ApplicationPrefix (budget : Nat) (plain : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ calleeSize argumentsSize callSize sourceValue calleeHeap argumentsHeap sources callEvidence,
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap ∧
    Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue ∧
    Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap ∧
    RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize
      context invocation.evidence callEvidence argumentsHeap sourceValue sources plain after ∧
    callSize < budget ∧
    CellAwareScopeIndirectValuesPrefix.ValuesPrefix
      (functionModel := functions) (registry := registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := port.calleeNode) (sidecar := port.sidecar)
      bridge profile compiler port.prepared initial owner sourceValue calleeHeap argumentsHeap sources

include positive calleeCertificate calleeRecipe sourceTyped tree unique parentTyped environments heaps locals agrees typed admitted authority physical ownerFrame in
theorem lift_prefix (budget : Nat)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model named stages invocation certificate childSize)
    (preservation : ∀ stageSize, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named stages invocation certificate faults stageSize)
    (calleeMeaning : ∀ stageSize, CellAwareScopeGeneralizedReadBounds.PreservesAt
      bridge context model named stages invocation faults stageSize)
    {size : Nat} {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (execution : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      context invocation.evidence invocation.source environment before id plain after)
    (within : size ≤ budget) :
    ExpressionLift (Program.ofChecked compiled.sourceProgram) stages invocation context environment before id plain after ∨
    ApplicationPrefix (functions := functions) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (registry := registry) (context := context) (stages := stages)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (environment := environment)
      bridge profile compiler port initial owner budget plain after := by
  have occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  obtain ⟨_parameter, _result, _functionType, argumentTypes, _bundle, _originalType⟩ :=
    CellAwareScopeIndirectArgumentPrefix.source_rows
      (sourceEq := rfl) (found := port.calleeFound) (sourceParent := port.sourceParent)
      (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
  cases SelectedCompilationStageIndirectSourceTrace.source_inv unique compiler.found compiler.originalForm
    port.sourceParent.coercions compiler.argumentCoercions port.sourceParent.arity execution with
  | calleeFault failed _smaller =>
    have trace := CellAwareSourceReadLifting.read (registry := stages) unique
      calleeCertificate.observations.originalFound calleeCertificate.observations.originalForm
      calleeCertificate.observations.originalCoercions (.fault failed.sound)
    exact .inl ⟨_, _, .calleeFault occurrence trace, .completed⟩
  | notCallable evaluated invalid _smaller =>
    rcases CellAwareScopeSourceCalleeLifting.callee_value bridge profile compiler port calleeCertificate calleeRecipe sourceTyped
      tree unique parentTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame calleeMeaning
      evaluated with complete | ⟨carrier, calleeStore, calleeMap, calleeWorld, _calleeTrace, _post, accepted⟩
    · exact .inl complete
    · exact False.elim (invalid accepted.callable)
  | argumentsFault calleeTrace _callable failed _calleeSmaller argumentsSmaller =>
    rcases CellAwareScopeSourceCalleeLifting.callee_value bridge profile compiler port calleeCertificate calleeRecipe sourceTyped
      tree unique parentTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame calleeMeaning
      calleeTrace with complete | ⟨carrier, calleeStore, calleeMap, calleeWorld, liftedCallee, post, accepted⟩
    · exact .inl complete
    · obtain ⟨_native, _payload, _strong, calleeHeaps, maps, worlds, frame, metadata, effect, reached, _related, post⟩ := post
      obtain ⟨outcome, finalHeap, liftedArguments, adapted⟩ := CellAwareScopeSourceSequenceLifting.fault bridge
        budget tree unique argumentTypes children preservation (environments.extend maps worlds) calleeHeaps
        (locals.mono metadata) agrees (typed.weaken worlds) reached post.at_value.2 (authority.transport effect) (physical.transport effect frame) owner ownerFrame failed
        (Nat.le_of_lt (Nat.lt_of_lt_of_le argumentsSmaller within))
      cases adapted with
      | completed => exact .inl ⟨_, _, .argumentsFault occurrence liftedCallee accepted liftedArguments, .completed⟩
      | rejected origin call reason reached =>
        exact .inl ⟨_, _, .argumentsFault occurrence liftedCallee accepted liftedArguments, .rejected origin call reason _⟩
  | apply calleeTrace argumentsTrace called _calleeSmaller argumentsSmaller callSmaller =>
    rcases CellAwareScopeSourceCalleeLifting.callee_value bridge profile compiler port calleeCertificate calleeRecipe sourceTyped
      tree unique parentTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame calleeMeaning
      calleeTrace with complete | ⟨carrier, calleeStore, calleeMap, calleeWorld, liftedCallee, post, accepted⟩
    · exact .inl complete
    · obtain ⟨_native, _payload, _strong, calleeHeaps, maps, worlds, frame, metadata, effect, reached, _related, post⟩ := post
      obtain ⟨outcome, finalHeap, liftedArguments, adapted⟩ := CellAwareScopeSourceSequenceLifting.values bridge
        budget tree unique argumentTypes children preservation (environments.extend maps worlds) calleeHeaps
        (locals.mono metadata) agrees (typed.weaken worlds) reached post.at_value.2 (authority.transport effect) (physical.transport effect frame) owner ownerFrame argumentsTrace
        (Nat.le_of_lt (Nat.lt_of_lt_of_le argumentsSmaller within))
      cases adapted with
      | rejected origin call reason reached =>
        exact .inl ⟨_, _, .argumentsFault occurrence liftedCallee accepted liftedArguments, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨calleeSize, sizedCallee⟩ := Staging.Recursive.Size.Expression.of_trace liftedCallee
        obtain ⟨argumentsSize, sizedArguments⟩ := Staging.Recursive.Size.Expressions.of_trace liftedArguments
        have valuePrefix := CellAwareScopeIndirectValuesPrefix.preserves_values
          bridge profile compiler port.prepared rfl calleeCertificate calleeRecipe port.calleeFound sourceTyped environments heaps locals agrees typed
          initial admitted authority physical owner ownerFrame port.caller port.view port.originalUnique port.guardFrame port.sourceParent tree unique parentTyped
          (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize]) (fun size _ => calleeMeaning size) (fun size _ => preservation size)
          sizedCallee accepted sizedArguments (Nat.le_refl _)
        exact .inr ⟨_, _, _, _, _, _, _, _, sizedCallee, accepted, sizedArguments,
          called, Nat.lt_of_lt_of_le callSmaller within, valuePrefix⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourcePrefixLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceIndirectLifting
/-! Original indirect calls lift through the actual generalized local value.
The retained materialization supplies its real body compiler and parameter
context; ordered arguments keep their reached descriptor cells and effects. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceIndirectLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Port)
open CellAwareScopeSourceLiftBounds (LiftsAt)
open Staging.Recursive.Lifting (ApplicationLift)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {functions : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry semanticFaults profile}
  [positive : SelectedCompilationCallableOrigins.Origins headers keys bodyRegistry semanticFaults profile functions]
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation invocation.source scope
    id callee ids metadata reasonAt lowered)
  (port : Port (compiled := compiled) (invocation := invocation) compiler)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages compiled

include positive port runtime unique in
/-- The finite compiler certificate determines the actual callee and call
body. The only recursive inputs are the ordered argument children. -/
theorem indirect_selected {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled))
    (covers : invocation.evidence.Covers context)
    (budget : Nat)
    (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      invocation.source scope callee reasonAt compiler.calleeCode)
    (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source children scope ids sourceTypes compiler.codes)
    (childLift : ∀ size, size < budget → LiftsAt bridge context model named stages invocation children size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named stages invocation children faults size)
    (calleeMeaning : ∀ size, CellAwareScopeGeneralizedReadBounds.PreservesAt
      bridge context model named stages invocation faults size) :
    LiftsAt bridge context model named stages invocation
      (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Point scope id lowered) budget := by
  intro current expression code point actualNode found parentTyped
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial admitted authority physical owner ownerFrame execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨_parameter, _result, _rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation expression (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  rcases CellAwareScopeSourcePrefixLifting.lift_prefix
    (functions := functions) bridge profile compiler port calleeCertificate calleeRecipe sourceTyped
    tree unique parentTyped environments heaps locals agrees typed initial admitted authority physical owner ownerFrame
    budget childLift preservation calleeMeaning execution (Nat.le_refl _) with complete | application
  · exact complete
  · obtain ⟨_calleeSize, _argumentsSize, _callSize, sourceValue, _calleeHeap, _argumentsHeap, sources, _callEvidence,
      calleeTrace, accepted, argumentsTrace, called, _smaller, prefixResult⟩ := application
    obtain ⟨rawParameter, rawResult, functionType, bundle, _originalResult,
      _calleeStore, _calleeMap, _calleeWorld, _carrier, _values, _argumentsStore, _finalMap, _finalWorld,
      _originalNode, _originalMetadata, _calleePost, calleeTyped, _firstGate, _argumentsNative,
      _represented, _calleeRelated, strong, _callView, _boundary, _heaps, _maps, _worlds,
      _frame, _heapMetadata, _effect, _reached, _related, _admitted⟩ := prefixResult
    obtain ⟨function, _native, _bindings, _parameterCore, _resultCore, sourceValueEq, _nativeEq, association, _atFrame⟩ :=
      strong sourceValue rfl
    cases sourceValueEq
    have lifted : ApplicationLift (Program.ofChecked compiled.sourceProgram) stages invocation context _argumentsHeap
        (.closure function) sources outcome after := by
      by_cases arity : function.parameters.length = sources.length
      · have rawCallee : Dynamic.ValueHasType context _calleeHeap (.closure function)
            (.function rawParameter rawResult) := by
          simpa only [functionType] using calleeTyped
        obtain ⟨_parameters, _sourceResult, signatures, sourceCode, evidence, _captures⟩ := rawCallee.closure_function_inv
        have frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function :=
          ⟨signatures.trans runtime.signatures, sourceCode.owner, sourceCode,
            sourceCode.requirement_ledger.idsUnique, evidence⟩
        obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
          CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler port.sourceParent
            tree unique parentTyped port.calleeFound
        obtain ⟨_nativeCallee, _representedCallee, _strong, _calleeHeaps, _calleeMaps, _calleeWorlds,
          _calleeFrame, calleeMetadata, _calleeEffect, _calleeReached, _calleeRelated, calleeAdmission⟩ := _calleePost
        obtain ⟨sourceValuesTyped, _heapTyped, argumentMetadata⟩ :=
          SelectedStagedArgumentTyping.values_at selectedBodies runtime covers
            (locals.mono calleeMetadata) calleeAdmission.at_value.2.heap argumentsTyped argumentsTrace
        obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack sources
        have raw := CallableIndexedOwnedStoredClosureSourceArguments.at_arguments runtime
          (rawCallee.mono argumentMetadata) _admitted.heap sourceValuesTyped packing bundle arity.symm
        cases association with
        | viewed material _view _typed =>
          obtain ⟨inputs⟩ := GeneralizedLocalBodyCompiler.entry_context material frame material.ownership
          exact GeneralizedLocalSourceApplicationLifting.selected_application material inputs (selectedBodies) raw arity called
      · exact SelectedCompilationStageApplicationArity.closure_mismatch arity called
    obtain ⟨staged, reached, applied, adapted⟩ := lifted
    exact ⟨staged, reached, .applied occurrence compiler.argumentCoercions calleeTrace.sound accepted
      argumentsTrace.sound port.sourceParent.arity applied, adapted⟩

/- Compatibility adapters for callers with a whole-program receipt. -/
include positive port runtime unique in
theorem indirect {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (covers : invocation.evidence.Covers context)
    (budget : Nat)
    (calleeCertificate : GeneralizedLocalNamedReadCompilation.Certificate compiled.indexed named
      invocation.source scope callee reasonAt compiler.calleeCode)
    (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Receipt calleeCertificate)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source children scope ids sourceTypes compiler.codes)
    (childLift : ∀ size, size < budget → LiftsAt bridge context model named stages invocation children size)
    (preservation : ∀ size, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named stages invocation children faults size)
    (calleeMeaning : ∀ size, CellAwareScopeGeneralizedReadBounds.PreservesAt
      bridge context model named stages invocation faults size) :
    LiftsAt bridge context model named stages invocation
      (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Point scope id lowered) budget := by
  apply indirect_selected (selectedBodies := Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed)  <;> assumption

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeSourceIndirectLifting
end

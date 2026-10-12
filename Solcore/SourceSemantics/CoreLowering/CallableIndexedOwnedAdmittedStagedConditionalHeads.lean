import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion

/-! Conditional heads use the actual staged condition and selected arm. The
outer statement fold owns fallthrough sequencing and restores its original
lexical context while retaining the arm's heap and captured cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CompatibleExpressionPrimitives (bool_fields)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

/-- The two children that actually execute are retained with their own grades.
No unselected arm or suffix execution is asserted. -/
inductive Trace (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (test : ExpressionId) (left : List StatementId) (right : Option (List StatementId)) :
    Nat → Staging.Recursive.BodyOutcome → Dynamic.Heap → Prop where
  | fault {testSize failure after}
      (testTrace : Staging.Recursive.Size.Expression program stages testSize invocation context environment before
        test (.fault failure) after) :
      Trace program stages invocation context environment before test left right
        (Staging.Recursive.Size.stepSize [testSize]) (.fault failure) after
  | branch {testSize branchSize truth middle innerContext outcome after}
      (testTrace : Staging.Recursive.Size.Expression program stages testSize invocation context environment before
        test (.value (.bool truth)) middle)
      (branchTrace : Staging.Recursive.Size.StatementsIn program stages false branchSize invocation context
        environment middle (if truth then left else right.getD []) innerContext outcome after) :
      Trace program stages invocation context environment before test left right
        (Staging.Recursive.Size.stepSize [testSize, branchSize]) outcome after

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A selected scoped arm's numeric reflection port, closed by the surrounding
compiler-tree induction. Its postcondition is at the original outer context. -/
def FlowReflects (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) (mode : Bool)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_conditioned : condition contextLocation native)
    (_admitted : Admission bridge context initial),
    EvaluationSize size actual store (code.rename ξ) value finalStore →
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages mode sourceSize invocation context environment before
        statements finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached

/-- The corresponding Source-to-native port retains successful branch typing,
fallthrough admission, and the same final heap for every admitted caller. -/
def FlowPreserves (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) (mode : Bool)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_conditioned : condition contextLocation native)
    (_admitted : Admission bridge context initial),
    ∀ {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap},
      Staging.Recursive.Size.StatementsIn program stages mode size invocation context environment before
        statements finalContext outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached

/-- Scoped branch aliases fix only the mode; all caller/state parameters are identical. -/
abbrev BranchReflects (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  FlowReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
    (stages := stages) (invocation := invocation) (faults := faults)
    bridge functions condition context scope false statements expected type code budget

abbrev BranchPreserves (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  FlowPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
    (stages := stages) (invocation := invocation) (faults := faults)
    bridge functions condition context scope false statements expected type code budget

variable {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode}
  {left : List StatementId} {right : Option (List StatementId)}
  {expected : TypeSystem.Ty} {type : Ty} {testCode leftCode rightCode : Expr}

include bridge functions condition in
theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → ReflectsAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (leftCorrect : BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope left expected type leftCode budget)
    (rightCorrect : BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope (right.getD []) expected type rightCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store ((LocalLoop.conditional type testCode leftCode rightCode).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Trace program stages invocation context environment before test left right sourceSize outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  rw [LoopRenaming.conditional] at completed
  obtain ⟨testSize, middleStore, input, smaller, testEval⟩ := completed.bind_computation
  obtain ⟨testSourceSize, testOutcome, middle, middleMap, middleWorld, testTrace, represented,
      middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, testPost⟩ :=
    children testSize (Nat.lt_of_lt_of_le smaller within) generated found typed
      environments heaps locals agrees actualTyped initial admitted testEval
  cases represented with
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalControl.choose_failure _ testEval.sound)
      exact ⟨_, _, middle, middleMap, middleWorld, .fault testTrace, .fault matched, middleHeaps,
        maps, worlds, preservation, metadata, middleState, expressionRelated, testPost.at_fault_type⟩
  | value payload =>
      rw [nodeType] at payload
      obtain ⟨truth, sourceEq, coreEq⟩ := bool_fields payload
      subst sourceEq
      subst coreEq
      have selected : BranchReflects (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
          (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope
          (if truth then left else right.getD []) expected type (if truth then leftCode else rightCode) budget := by
        cases truth <;> assumption
      have branch : ∃ branchSize, branchSize < size ∧ EvaluationSize branchSize (.bool truth :: actual)
          middleStore (((if truth then leftCode else rightCode).rename ξ).weakenAt 0) value finalStore := by
        cases truth with
        | false => exact completed.choose_false testEval.sound
        | true => exact completed.choose_true testEval.sound
      obtain ⟨branchSize, branchSmaller, branchEval⟩ := branch
      obtain ⟨branchSourceSize, finalContext, outcome, after, finalMap, finalWorld, branchTrace,
          represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, reached, branchRelated, post⟩ :=
        selected (Nat.le_trans (Nat.le_of_lt branchSmaller) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (GenericExpressionMeaning.agree_prefix agrees (.bool truth))
          (.cons .bool (actualTyped.weaken worlds)) reference
          ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState conditioned testPost.at_value.2
          (by simpa only [GenericExpressionMeaning.rename_prefix] using branchEval)
      exact ⟨_, outcome, after, finalMap, finalWorld, .branch testTrace branchTrace, represented, finalHeaps,
        maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
        reached, callerProtocol.trans expressionRelated branchRelated, post⟩

include bridge functions condition in
theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → PreservesAt bridge context model stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (leftCorrect : BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope left expected type leftCode budget)
    (rightCorrect : BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope (right.getD []) expected type rightCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Trace program stages invocation context environment before test left right size outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.conditional type testCode leftCode rightCode).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  cases trace with
  | @fault testSize failure after testTrace =>
      have smaller : testSize < budget := Nat.lt_of_lt_of_le
        (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩ :=
        children testSize smaller generated found typed environments heaps locals agrees actualTyped initial admitted testTrace
      cases represented with
      | fault matched =>
          refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
            maps, worlds, preservation, metadata, reached, related, post.at_fault_type⟩
          rw [LoopRenaming.conditional]
          exact LocalControl.choose_failure _ evaluated
  | @branch testSize branchSize truth middle innerContext outcome after testTrace branchTrace =>
      have smaller : testSize < budget := Nat.lt_of_lt_of_le
        (Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, middleStore, middleMap, middleWorld, testEval, represented, middleHeaps,
          maps, worlds, preservation, metadata, middleState, expressionRelated, testPost⟩ :=
        children testSize smaller generated found typed environments heaps locals agrees actualTyped initial admitted testTrace
      cases represented with
      | value payload =>
          rw [nodeType] at payload
          obtain ⟨actualTruth, sourceEq, coreEq⟩ := bool_fields payload
          cases sourceEq
          subst coreEq
          have selected : BranchPreserves (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
              (stages := stages) (invocation := invocation) (faults := faults) bridge functions condition context scope
              (if truth then left else right.getD []) expected type (if truth then leftCode else rightCode) budget := by
            cases truth <;> assumption
          have branchWithin : branchSize ≤ budget := Nat.le_trans
            (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within
          obtain ⟨value, finalStore, finalMap, finalWorld, branchEval, represented, finalHeaps,
              lastMaps, lastWorlds, lastFrame, lastMetadata, reached, branchRelated, post⟩ :=
            selected branchWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix agrees (.bool truth))
              (.cons .bool (actualTyped.weaken worlds)) reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState conditioned testPost.at_value.2 branchTrace
          refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
            maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
            reached, callerProtocol.trans expressionRelated branchRelated, post⟩
          rw [LoopRenaming.conditional]
          rw [GenericExpressionMeaning.rename_prefix] at branchEval
          cases truth with
          | false => exact LocalControl.choose_false _ testEval branchEval
          | true => exact LocalControl.choose_true _ testEval branchEval

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalHeads

import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLoopContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexical
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalGate
import Solcore.SourceSemantics.CoreLowering.ProtectedStateFunctionFinishReady
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchFallthrough
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchControlShape
import Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBodyMeaning

/-! The actual function finish consumes the original measured flow. Source
body and flow witnesses have the same source grade; native finish inversion
selects a strict original flow child. Reflection constructs its independent
source grade, retaining the reached lexical exit and actual concrete outer transition. Legacy wrappers preserve the original guarded entry.
The Match Tree supplies source control shape; the original For entry embeds
without changing code. Flow meaning remains an explicit pointwise premise for
catalog mutual induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedLoopContracts (ExecutesAt)
open RecursiveNamedCallBounds (BodyTrace)
universe u v

/-- The wrapper adds no source execution step: every case retains the same
measured function-statement witness and its distinct source call exit. -/
theorem trace_flow {program : Program} {size : Nat} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ finalContext control,
      ExecutesAt size true program context function.evidence function.source environment before function.body finalContext control after ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
  cases trace with
  | returned trace => exact ⟨_, _, .control trace, .returned _⟩
  | unit same trace => exact ⟨_, _, .control trace, .unit _ same⟩
  | fault failed => exact ⟨_, _, .fault failed, .fault _⟩
  | escaped trace escape =>
    rcases escape with ⟨next, rfl⟩ | ⟨next, rfl⟩
    · exact ⟨_, _, .control trace, .breaking next⟩
    · exact ⟨_, _, .control trace, .continuing next⟩

section Match

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
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word}
  (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope function.body
    type reasonAt fellThrough escaped = .ok code)
  (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope function.body
    type reasonAt true escaped = .ok flow)
  (tree : GenericImperativeMatch.Tree layouts owner active frameLayout globals onError values function.source
    expressionSyntax certificates ambient.definitions administrative context scope
    (.statements true function.body) function.resultType type flow)
  (projection : values.checked.catalog.project function.resultType = .ok type)
  (unique : NodeOccurrencesUnique function.source)
  {faults : FunctionCalls.FaultRep} (escapedFault : faults .controlEscapedFunction escaped)
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include accepted generated in
private theorem emitted : code = CompatibleStatements.finish type flow fellThrough escaped := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  rw [generated] at accepted
  exact Except.ok.inj accepted.symm

include tree projection unique in
theorem WithReady.preserves_at_emitted_with_state_when_with_transfers {Records : Type v}
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
    (transfers : ∀ {sourceSize finalContext control after},
      ExecutesAt sourceSize true program context function.evidence function.source
        environment before function.body finalContext control after →
      ImperativeFunctionFinish.TransferFaults faults escaped control)
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
  obtain ⟨finalContext, control, trace, exit⟩ := trace_flow trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, retained, post⟩ :=
    meaning valid bodyFacts environments heaps locals agrees typed reference read unmapped initial gate ready trace
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow_with_transfers functions (fun next same => by
    cases same
    exact GenericImperativeMatch.Tree.true_fallthrough_unit tree unique trace.sound)
    projection fellThrough escaped (transfers trace) represented evaluated
  have evaluated : Evaluates actual store (code.rename ξ) result finalStore := by
    rw [emitted, ImperativeFunctionFinish.rename]
    exact completed
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, ImperativeFunctionFinish.result related exit,
    finalHeaps, maps, worlds, frame, metadata, ⟨finalContext, control, trace.sound, exit, lexical⟩,
    ⟨reached, retained, ProtectedStateTransition.FunctionFinish.post_of_exit exit post⟩⟩


include tree projection unique escapedFault in
theorem WithReady.preserves_at_emitted_with_state_when {Records : Type v}
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
  apply WithReady.preserves_at_emitted_with_state_when_with_transfers (functions := functions) (program := program)
    (tree := tree) (projection := projection) (unique := unique)
    protocol readiness condition facts emitted validity size meaning valid bodyFacts environments heaps locals agrees typed reference read unmapped
    initial gate ready (fun _ => ⟨fun _ _ => escapedFault, fun _ _ => escapedFault⟩)
  exact trace


include tree projection unique escapedFault in
theorem preserves_at_emitted_with_state_when {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol condition functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context)
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
    (gate : condition contextLocation native)
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
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ :=
    WithReady.preserves_at_emitted_with_state_when (functions := functions) (program := program)
      (tree := tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
      protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) condition
      (fun _ _ _ _ => True) emitted validity size
      (RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith.of_true
        protocol condition functions program function.evidence meaning) valid True.intro
      environments heaps locals agrees typed reference read unmapped initial gate True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
    ProtectedStateTransition.FunctionFinish.Reached.forget reached⟩

include tree projection unique escapedFault in
theorem preserves_at_emitted_with_state {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : ProtectedStateTransition.Lexical.PreservesAtFor protocol functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context)
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
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_at_emitted_with_state_when (functions := functions) (program := program)
    (tree := tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
    protocol (fun _ _ => True) emitted validity size
    (ProtectedStateTransition.Lexical.Gated.preserves_of_unguarded protocol (fun _ _ => True)
      functions program function.evidence meaning) valid
    environments heaps locals agrees typed reference read unmapped initial True.intro trace

include tree projection unique escapedFault transport in
theorem preserves_at_emitted (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAtFor (entry := entry) functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context)
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
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical  := by
  have stateful := ProtectedStateTransition.Lexical.legacy_preserves
    (functions := functions) (program := program) (evidence := function.evidence) transport meaning
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, transition⟩ :=
    preserves_at_emitted_with_state (functions := functions) (program := program)
      (tree := tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
      (ProtectedStateTransition.Lexical.legacyProtocol entry) emitted validity size stateful valid
      environments heaps locals agrees typed reference read unmapped ⟨installed⟩ trace
  obtain ⟨final, _⟩ := transition
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, final.down⟩


include accepted generated tree projection unique escapedFault transport in
theorem preserves_at_with (validity : SourceSemantics.Context → Prop) (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAtFor (entry := entry) functions program function.evidence validity
      (source := function.source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : validity context)
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
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  apply preserves_at_emitted (functions := functions) (program := program)
    (tree := tree) (projection := projection) (unique := unique)
    (escapedFault := escapedFault) (transport := transport)
    (emitted accepted generated) validity size meaning valid
  all_goals assumption

include tree projection unique in
theorem WithReady.reflects_at_emitted_with_state_when_with_transfers {Records : Type v}
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
    (transfers : ∀ {sourceSize finalContext control after},
      ExecutesAt sourceSize true program context function.evidence function.source
        environment before function.body finalContext control after →
      ImperativeFunctionFinish.TransferFaults faults escaped control)
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
  rw [emitted, ImperativeFunctionFinish.rename] at evaluated
  obtain ⟨flowSize, flowValue, middleStore, smaller, flowEval⟩ := RecursiveNamedCallBounds.finish_flow evaluated
  obtain ⟨sourceSize, finalContext, control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, retained, post⟩ :=
    meaning flowSize (Nat.lt_of_lt_of_le smaller within) valid bodyFacts
      environments heaps locals agrees typed reference read unmapped initial gate ready flowEval
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow_with_transfers functions (fun next same => by
    cases same
    exact GenericImperativeMatch.Tree.true_fallthrough_unit tree unique trace.sound)
    projection fellThrough escaped (transfers trace) represented flowEval.sound
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound completed
  have sourceResult : ∃ outcome, BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
    generalize raw : function.resultType = expected at related
    cases related with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed => exact ⟨_, .unit raw executed, .value .unit, .unit _ rfl⟩
    | returned payload =>
      cases trace with
      | control executed => exact ⟨_, .returned executed, .value payload, .returned _⟩
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (tree.control_not_fault unique executed.sound)
      | fault failed => exact ⟨_, .fault failed, .fault matched, .fault _⟩
    | breaking finalEnvironment matched =>
      cases trace with
      | control executed => exact ⟨_, .escaped executed (.inl ⟨_, rfl⟩), .fault matched, .breaking _⟩
    | continuing finalEnvironment matched =>
      cases trace with
      | control executed => exact ⟨_, .escaped executed (.inr ⟨_, rfl⟩), .fault matched, .continuing _⟩
  obtain ⟨outcome, bodyTrace, represented, exit⟩ := sourceResult
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, bodyTrace, represented, finalHeaps, maps, worlds, frame, metadata,
    ⟨finalContext, control, trace.sound, exit, lexical⟩,
    ⟨reached, retained, ProtectedStateTransition.FunctionFinish.post_of_exit exit post⟩⟩


include tree projection unique escapedFault in
theorem WithReady.reflects_at_emitted_with_state_when {Records : Type v}
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
  apply WithReady.reflects_at_emitted_with_state_when_with_transfers (functions := functions) (program := program)
    (tree := tree) (projection := projection) (unique := unique)
    protocol readiness condition facts emitted validity budget size within meaning valid bodyFacts environments heaps locals agrees typed reference read unmapped
    initial gate ready (fun _ => ⟨fun _ _ => escapedFault, fun _ _ => escapedFault⟩)
  exact evaluated


include tree projection unique escapedFault in
theorem reflects_at_emitted_with_state_when {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (condition : Location → CallableIndexedHistory.NativeFrame → Prop) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol condition functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context)
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
    (gate : condition contextLocation native)
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
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ :=
    WithReady.reflects_at_emitted_with_state_when (functions := functions) (program := program)
      (tree := tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
      protocol (RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) condition
      (fun _ _ _ _ => True) emitted validity budget size within
      (fun child smaller => RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith.of_true
        protocol condition functions program function.evidence (meaning child smaller)) valid True.intro
      environments heaps locals agrees typed reference read unmapped initial gate True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical,
    ProtectedStateTransition.FunctionFinish.Reached.forget reached⟩

include tree projection unique escapedFault in
theorem reflects_at_emitted_with_state {Records : Type v}
    (protocol : ProtectedStateTransition.Protocol.{u, v} Records) (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      ProtectedStateTransition.Lexical.ReflectsAtFor protocol functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context)
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
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_at_emitted_with_state_when (functions := functions) (program := program)
    (tree := tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
    protocol (fun _ _ => True) emitted validity budget size within
    (fun child smaller => ProtectedStateTransition.Lexical.Gated.reflects_of_unguarded protocol (fun _ _ => True)
      functions program function.evidence (meaning child smaller)) valid
    environments heaps locals agrees typed reference read unmapped initial True.intro evaluated

include tree projection unique escapedFault transport in
theorem reflects_at_emitted (emitted : code = CompatibleStatements.finish type flow fellThrough escaped) (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAtFor (entry := entry) functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context)
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
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical  := by
  have stateful : RecursiveNamedBoundedContracts.Below budget (fun child =>
      ProtectedStateTransition.Lexical.ReflectsAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry)
        functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow) :=
    fun child smaller => ProtectedStateTransition.Lexical.legacy_reflects
      (functions := functions) (program := program) (evidence := function.evidence) transport (meaning child smaller)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, transition⟩ :=
    reflects_at_emitted_with_state (functions := functions) (program := program)
      (tree := tree) (projection := projection) (unique := unique) (escapedFault := escapedFault)
      (ProtectedStateTransition.Lexical.legacyProtocol entry) emitted validity budget size within stateful valid
      environments heaps locals agrees typed reference read unmapped ⟨installed⟩ evaluated
  obtain ⟨final, _⟩ := transition
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, final.down⟩

include accepted generated tree projection unique escapedFault transport in
theorem reflects_at_with (validity : SourceSemantics.Context → Prop) (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAtFor (entry := entry) functions program function.evidence validity
        (source := function.source) (context := context) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : validity context)
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
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  apply reflects_at_emitted (functions := functions) (program := program)
    (tree := tree) (projection := projection) (unique := unique)
    (escapedFault := escapedFault) (transport := transport)
    (emitted accepted generated) validity budget size within meaning valid
  all_goals assumption



include accepted generated tree projection unique escapedFault transport in
theorem preserves_at_match (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program function.evidence
      (source := function.source) (context := context) (registry := registry) (solved := solved) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
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
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  exact preserves_at_with functions program accepted generated tree projection unique escapedFault transport
    (fun context => CompatibleExpressionLiterals.ContextValid solved context function.evidence)
    size meaning valid environments heaps locals agrees typed reference read unmapped installed trace

include accepted generated tree projection unique escapedFault transport in
theorem reflects_at_match (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAt (entry := entry) functions program function.evidence
        (source := function.source) (context := context) (registry := registry) (solved := solved) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
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
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  exact reflects_at_with functions program accepted generated tree projection unique escapedFault transport
    (fun context => CompatibleExpressionLiterals.ContextValid solved context function.evidence)
    budget size within meaning valid environments heaps locals agrees typed reference read unmapped installed evaluated


end Match

/- Original For entry retains the exact emitted code. -/
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
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word}
  (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope function.body
    type reasonAt fellThrough escaped = .ok code)
  (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope function.body
    type reasonAt true escaped = .ok flow)
  (tree : GenericImperativeFor.Tree layouts owner active frameLayout globals onError values function.source
    expressionSyntax certificates ambient.definitions administrative context scope
    (.statements true function.body) function.resultType type flow)
  (projection : values.checked.catalog.project function.resultType = .ok type)
  (unique : NodeOccurrencesUnique function.source)
  {faults : FunctionCalls.FaultRep} (escapedFault : faults .controlEscapedFunction escaped)
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include accepted generated tree projection unique escapedFault transport in
theorem preserves_at (size : Nat)
    (meaning : RecursiveNamedLoopContracts.PreservesAt (entry := entry) functions program function.evidence
      (source := function.source) (context := context) (registry := registry) (solved := solved) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      size (scope := scope) true function.body function.resultType type flow)
    (valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
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
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  exact preserves_at_match functions program accepted generated (GenericImperativeMatch.Tree.of_for tree)
    projection unique escapedFault transport size meaning valid environments heaps locals agrees typed reference read unmapped installed trace

include accepted generated tree projection unique escapedFault transport in
theorem reflects_at (budget size : Nat) (within : size ≤ budget)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun child =>
      RecursiveNamedLoopContracts.ReflectsAt (entry := entry) functions program function.evidence
        (source := function.source) (context := context) (registry := registry) (solved := solved) (faults := faults)
        (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        child (scope := scope) true function.body function.resultType type flow))
    (valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
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
    (unmapped : contextLocation ∉ mapping) (installed : entry scope mapping world before store canonical)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧ entry scope finalMap finalWorld after finalStore canonical := by
  exact reflects_at_match functions program accepted generated (GenericImperativeMatch.Tree.of_for tree)
    projection unique escapedFault transport budget size within meaning valid environments heaps locals agrees typed reference read unmapped installed evaluated

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedFunctionFinishBounds

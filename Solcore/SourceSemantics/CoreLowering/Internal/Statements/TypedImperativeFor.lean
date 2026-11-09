import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedImperative
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalWhile
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopRenaming

/-!
# Typed imperative for loops

Native typing, allocation, state, post items, iteration, reflection and endpoints of `for` loops.

The trees are in `Statements/TypedImperativeForTrees` on purpose. These bodies read `Scope` and `ValuesContext` from `TypedLexicalWhile` through an `open`, and that file holds names of the same spelling in the namespace they share, which would win.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForNative
/-! Static inversion of the actual for closure. This removes only syntactic
administrative insertions; it makes no runtime capture or source-type claim. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor.Native
open Core TypedLexicalWhile.Native

theorem advance_children {definitions : DataEnvironment} {context : Core.Context} {type result : Ty} {computation body : Expr}
    (typed : HasType context (LocalLoop.advance type computation body) result definitions) :
    (∃ headType, HasType context computation headType definitions) ∧
    (∃ tailType, HasType context body tailType definitions) := by
  cases typed with
  | caseE computation failure next =>
    cases next with
    | caseE outer inner transfer =>
      cases inner with
      | caseE tested continued returned =>
        exact ⟨⟨_, computation⟩, ⟨_, remove_front (remove_front (remove_front continued))⟩⟩

theorem iterate_children {definitions : DataEnvironment} {context : Core.Context} {type result : Ty}
    {condition body post : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.iterate type condition body post reason) result definitions) :
    (∃ bodyType, HasType context body bodyType definitions) ∧
    (∃ postType, HasType context post postType definitions) ∧
    HasType context (LocalLoop.iterate type condition body post reason) (LocalLoop.resultType type) definitions := by
  cases typed with
  | letE allocation installed =>
    cases allocation with
    | newCell empty =>
      cases installed with
      | letE written invoked =>
        cases written with
        | storeCell reference closure =>
          cases closure with
          | inRight unitWF raw =>
            cases raw with
            | lambda parameterWF resultWF loop =>
              obtain ⟨⟨_, yes⟩, _⟩ := conditional_children loop
              obtain ⟨⟨_, bodyTyped⟩, ⟨_, postAdvance⟩⟩ := advance_children yes
              obtain ⟨_, postTyped⟩ := advance_child postAdvance
              refine ⟨⟨_, remove_front (remove_front bodyTyped)⟩,
                ⟨_, remove_front (remove_front postTyped)⟩, ?_⟩
              apply HasType.letE (.newCell empty)
              apply HasType.letE (.storeCell reference (.inRight unitWF (.lambda parameterWF resultWF loop)))
              apply LocalLoop.invoke_hasType reason ?_ (.var rfl)
              cases resultWF with
              | sum _ control =>
                cases control with
                | sum normal transfer =>
                  cases normal with | sum _ returned => exact returned

/-- The annotation on the emitted Unit closure fixes its body result. -/
theorem installed_body {definitions : DataEnvironment} {context : Core.Context}
    {type : Ty} {condition body post : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.iterate type condition body post reason) (LocalLoop.resultType type) definitions) :
    HasType (.unit :: OptionalCell.referenceType (LocalLoop.functionType type) :: context)
      (LocalLoop.loopBody type condition body post reason) (LocalLoop.resultType type) definitions := by
  cases typed with
  | letE allocation next =>
    cases allocation with
    | newCell initializer =>
      cases next with
      | letE write invocation =>
        cases write with
        | storeCell reference value =>
          cases reference with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Ty.cell.injEq] at found
            cases found
            cases value with
            | inRight _ closure =>
              cases closure with
              | lambda _ _ typedBody => exact typedBody
end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor.Native
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForAllocation
/-! The real for closure is installed as one administrative cell, with its
actual post code and ambient captured values. Existing source cells remain
represented by the same location map. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (installedStore installedWorld)

/-- Install exactly the closure allocated by `LocalLoop.iterate`, preserving
all source cells and every pre-existing administrative location. -/
theorem install {values : SourceCoreCompatibleValues.Context} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {environment : Environment} {context : Core.Context} {type : Ty} {condition body post : Expr}
    (reason : Word)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (typed : HasType context (LocalLoop.iterate type condition body post reason) (LocalLoop.resultType type) ambient.definitions) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping (installedWorld world type) heap
      (installedStore store type condition body post reason environment) ∧
    WorldExtends world (installedWorld world type) ∧ store.length ∉ mapping ∧
    (installedWorld world type)[store.length]? = some (OptionalCell.cellType (LocalLoop.functionType type)) ∧
    (installedStore store type condition body post reason environment).read? store.length =
      some (.inRight .unit (LocalLoop.installedClosure type condition body post reason store.length environment)) ∧
    AdministrativePreserved mapping store mapping (installedStore store type condition body post reason environment) := by
  have worlds : WorldExtends world (installedWorld world type) := ⟨_, rfl⟩
  have found : (installedWorld world type)[store.length]? = some (OptionalCell.cellType (LocalLoop.functionType type)) := by
    rw [← heaps.runtime_hasTypes.length_eq]
    simp [installedWorld, LoopAdministration.installedWorld]
  have closureTyped : RuntimeValueHasType (installedWorld world type)
      (LocalLoop.installedClosure type condition body post reason store.length environment)
      (LocalLoop.functionType type) ambient.definitions :=
    .closure (.cons (.cellRef found) (environmentTyped.weaken worlds)) (Native.installed_body typed)
  have absentTyped : RuntimeValueHasType world (.inLeft (LocalLoop.functionType type) .unit)
      (OptionalCell.cellType (LocalLoop.functionType type)) ambient.definitions := .inLeft .unit
  have allocated := heaps.allocate_administrative absentTyped
  have written : (store.allocate (.inLeft (LocalLoop.functionType type) .unit)).1.write? store.length
      (.inRight .unit (LocalLoop.installedClosure type condition body post reason store.length environment)) =
      some (installedStore store type condition body post reason environment) := by
    simp [Store.allocate, Store.write?, installedStore, LoopAdministration.installedStore]
  have filled := allocated.write_administrative heaps.fresh_unmapped found (.inRight closureTyped) written
  refine ⟨filled, worlds, ?_, found, ?_, AdministrativePreserved.allocate_administrative _ _ _⟩
  · intro member
    obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
    exact heaps.fresh_unmapped lookup
  · simp [installedStore, LoopAdministration.installedStore, Store.read?]


end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForState
/-! Actual compatible for activation state and concrete condition/body edges.
The administrative self cell contains the real post code; all later effects
must preserve it through the common administrative-frame relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Preserves Reflects FlowRep retain)
open CompatibleExpressionPrimitives (bool_fields)

variable {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode body postCode : Expr} {selfReason : Word}

/-- One live loop activation. Its source lexical frame is fixed across
iterations; body-local allocations survive solely in the represented heap. -/
structure LoopState (values : ValuesContext) {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (context : SourceSemantics.Context) (scope : Scope) (administrative actualContext : Core.Context)
    (frameLayout : SourceCoreCallableIndexedFrames.Layout)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (contextLocation location : Location) (type : Ty) (condition body post : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) : Prop where
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
    mapping world administrative scope environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions
  contextRead : ∃ native, store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native)
  contextUnmapped : contextLocation ∉ mapping
  selfTyped : world[location]? = some (OptionalCell.cellType (LocalLoop.functionType type))
  selfRead : store.read? location = some (.inRight .unit
    (LocalLoop.installedClosure type condition body post reason location actual))
  selfUnmapped : location ∉ mapping

variable {scope : Scope} {mapping futureMap : LocationMap} {world futureWorld : StoreTyping}
  {before after : Dynamic.Heap} {store futureStore : Store}

/-- Both the mutable ancestry frame and immutable loop code are real
administrative locations, retained through the supplied common heap frame. -/
theorem LoopState.advance
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body postCode selfReason mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after futureStore)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body postCode selfReason futureMap futureWorld after futureStore := by
  obtain ⟨native, contextRead⟩ := state.contextRead
  obtain ⟨contextUnmapped, contextRead⟩ := retain state.contextUnmapped contextRead frame
  obtain ⟨selfUnmapped, selfRead⟩ := retain state.selfUnmapped state.selfRead frame
  exact ⟨state.environments.extend maps worlds, heaps, state.locals.mono metadata, state.actualTyped.weaken worlds,
    ⟨native, contextRead⟩, contextUnmapped, worlds.lookup state.selfTyped, selfRead, selfUnmapped⟩

def Progress (values : ValuesContext) {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (before after : Dynamic.Heap) (mapping futureMap : LocationMap) (world futureWorld : StoreTyping)
    (store futureStore : Store) : Prop :=
  CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after futureStore ∧
  LocationMap.Extends mapping futureMap ∧ WorldExtends world futureWorld ∧
  AdministrativePreserved mapping store futureMap futureStore ∧ Dynamic.HeapMetadataExtend before after

theorem Progress.trans {middle : Dynamic.Heap} {middleMap : LocationMap} {middleWorld : StoreTyping} {middleStore : Store}
    (first : Progress values registry functions before middle mapping middleMap world middleWorld store middleStore)
    (second : Progress values registry functions middle after middleMap futureMap middleWorld futureWorld middleStore futureStore) :
    Progress values registry functions before after mapping futureMap world futureWorld store futureStore :=
  ⟨second.1, first.2.1.trans second.2.1, first.2.2.1.trans second.2.2.1,
    first.2.2.2.1.trans second.2.2.2.1, first.2.2.2.2.trans second.2.2.2.2⟩

theorem LoopState.progress
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body postCode selfReason mapping world before store)
    (progress : Progress values registry functions before after mapping futureMap world futureWorld store futureStore) :
    LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body postCode selfReason futureMap futureWorld after futureStore :=
  state.advance progress.1 progress.2.1 progress.2.2.1 progress.2.2.2.1 progress.2.2.2.2

variable (functions) (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension uninitialized missing in
theorem condition_preserves [FunctionCalls.FaultTokens faults] {condition : ExpressionId} {node : ExpressionNode}
    (tree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (unique : NodeOccurrencesUnique source)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, frame, metadata⟩ :=
    CompatibleExpressionTyped.preserves functions extension program evidence valid unique uninitialized missing tree found
      state.environments state.heaps state.locals actualAgrees (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)) trace
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, heaps, maps, worlds, frame, metadata⟩

include extension uninitialized missing in
theorem condition_reflects [FunctionCalls.FaultTokens faults] {condition : ExpressionId} {node : ExpressionNode}
    (tree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩ :=
    CompatibleExpressionTyped.reflects functions extension program evidence valid uninitialized missing tree found
      state.environments state.heaps state.locals actualAgrees (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped))
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata⟩

/-- Run a structurally certified body under the actual Bool/Unit/self prefix.
The body-local lexical result is intentionally discharged at this loop edge. -/
theorem body_preserves {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (correct : Preserves functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : Executes false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨native, read⟩ := state.contextRead
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ))) canonical
      (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata, _⟩ :=
    correct valid state.environments state.heaps state.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped))) reference read state.contextUnmapped trace
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, heaps, maps, worlds, frame, metadata⟩

theorem body_reflects {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (correct : Reflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ finalContext outcome after finalMap finalWorld,
      Executes false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨native, read⟩ := state.contextRead
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ))) canonical
      (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata, _⟩ :=
    correct valid state.environments state.heaps state.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped))) reference read state.contextUnmapped
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  exact ⟨finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForPost
/-! Concrete post headers run beneath the actual six loop temporaries. Their
success restores the lexical capture used by the next self invocation, while
all post allocations and writes remain in the common compatible heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)

/-- Real envelope values, not merely a count of administrative slots. -/
def postValues (type : Ty) (location : Location) (continued : Bool) : List Value :=
  (if continued then ForLoop.continuingPrefix type else ForLoop.fallthroughPrefix type) ++
    [.unit, .cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location]

theorem postValues_length (type : Ty) (location : Location) (continued : Bool) :
    (postValues type location continued).length = 6 := by cases continued <;> rfl

theorem postValues_typed {definitions : DataEnvironment} {world : StoreTyping}
    {actual : Environment} {actualContext : Core.Context} {type : Ty} {location : Location}
    (continued : Bool) (selfTyped : world[location]? = some (OptionalCell.cellType (LocalLoop.functionType type)))
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions) :
    ∃ context, RuntimeEnvironmentHasTypes world (postValues type location continued ++ actual) context definitions := by
  cases continued
  · exact ⟨_, .cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit))
      (.cons .bool (.cons .unit (.cons (.cellRef selfTyped) typed)))))⟩
  · exact ⟨_, .cons .unit (.cons (.inRight .unit) (.cons (.inRight (.inRight .unit))
      (.cons .bool (.cons .unit (.cons (.cellRef selfTyped) typed)))))⟩

theorem postValues_agree {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (type : Ty) (location : Location) (continued : Bool) :
    EnvironmentsAgree ((fun index => index + 6).comp ξ) canonical (postValues type location continued ++ actual) := by
  have renamed : DataPlaceChildExpressions.prefixRenaming 6 ξ = ((fun index => index + 6).comp ξ) := by
    funext index
    simp [DataPlaceChildExpressions.prefixRenaming, Renaming.comp, Renaming.insertion]
  rw [← renamed]
  intro index value found
  have actual := DataPlaceChildExpressions.prefix_agrees agrees (postValues type location continued) found
  simpa only [postValues_length] using actual

theorem post_rename (code : Expr) (ξ : Renaming) :
    ForLoop.postCode (code.rename ξ) = code.rename ((fun index => index + 6).comp ξ) := by
  simp only [ForLoop.postCode, Core.LoopExecution.conditionCode, ← Expr.rename_insertion, Expr.rename_comp]
  congr 1

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {administrative actualContext : Core.Context}
  {type : Ty} {context : SourceSemantics.Context} {scope : Scope}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {conditionCode body postCode : Expr} {selfReason : Word}
  {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

include definitions registered extension uninitialized missing faithful observations in
theorem post_preserves [FunctionCalls.FaultTokens faults] {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : TypedForHeader.Tree layouts owner active frameLayout globals onError readFuel values source solved reasonAt ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (unique : NodeOccurrencesUnique source)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨native, read⟩ := state.contextRead
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.selfTyped state.actualTyped
  obtain ⟨tail, maps, worlds, preservation, metadata, evaluated, _, _, _⟩ :=
    tree.preserves_post functions definitions registered extension program evidence uninitialized missing faithful observations
      valid unique state.environments state.heaps state.locals (postValues_agree agrees type location continued) postTyped
      reference read state.contextUnmapped trace
  exact ⟨tail.store, tail.mapping, tail.world, by simpa only [post_rename] using evaluated,
    tail.heaps, maps, worlds, preservation, metadata⟩

include definitions registered extension uninitialized missing faithful observations in
theorem post_fault [FunctionCalls.FaultTokens faults] {items : List ForItemForm} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (tree : TypedForHeader.Tree layouts owner active frameLayout globals onError readFuel values source solved reasonAt ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : TypedForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (unique : NodeOccurrencesUnique source)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨native, read⟩ := state.contextRead
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.selfTyped state.actualTyped
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, preservation, metadata⟩ :=
    tree.preserves_fault functions definitions registered extension program evidence uninitialized missing faithful observations
      errors valid unique state.environments state.heaps state.locals (postValues_agree agrees type location continued) postTyped
      reference read state.contextUnmapped trace
  exact ⟨token, finalStore, finalMap, finalWorld, by simpa only [post_rename] using evaluated,
    matched, heaps, maps, worlds, preservation, metadata⟩

include definitions registered extension uninitialized missing faithful observations in
theorem post_reflects [FunctionCalls.FaultTokens faults] (functionTypes : FunctionRuntimeViews functions)
    {items : List ForItemForm} {value : Value} {finalStore : Store}
    (tree : TypedForHeader.Tree layouts owner active frameLayout globals onError readFuel values source solved reasonAt ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : TypedForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (unique : NodeOccurrencesUnique source)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (evaluated : Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ)) value finalStore) :
    (∃ finalContext finalEnvironment after finalMap finalWorld,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) := by
  obtain ⟨native, read⟩ := state.contextRead
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.selfTyped state.actualTyped
  rcases tree.reflects_post functions definitions registered extension program evidence uninitialized missing faithful observations
      functionTypes errors valid unique state.environments state.heaps state.locals
      (postValues_agree agrees type location continued) postTyped reference read state.contextUnmapped
      (by simpa only [post_rename] using evaluated) with done | fault
  · obtain ⟨finalContext, finalEnvironment, after, tail, trace, same, storeEq, maps, worlds, preservation, metadata, _, _, _⟩ := done
    subst finalStore
    exact .inl ⟨finalContext, finalEnvironment, after, tail.mapping, tail.world, trace, same,
      tail.heaps, maps, worlds, preservation, metadata⟩
  · obtain ⟨finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched, heaps, maps, worlds, preservation, metadata⟩ := fault
    exact .inr ⟨finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched,
      heaps, maps, worlds, preservation, metadata⟩

end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForIteration
/-! Finite source for iteration runs condition, body and post in their specified
order. Body and post contracts are internal structural induction hypotheses;
the final concrete tree supplies them without a runtime certificate field. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Preserves Reflects FlowRep)
open CompatibleExpressionPrimitives (bool_fields)

/-- Internal structural contract supplied by the concrete post header tree. -/
def PostPreserves {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment},
    LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store →
    ∀ continued : Bool,
    Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after →
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore

theorem iterations_success
    {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (trace : Dynamic.ForLoopExecutes program context evidence source environment before condition post statements finalContext outcome after) :
    ∀ {readFuel : Nat} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      SourceCoreRawMetadata.Extends values.registry registry →
      (∀ id location, faults (.uninitializedLocation location) (reasonAt id)) →
      (∀ id key value tag, MetadataRep registry (.mapping key value) tag → faults (.missingMappingDefault value) ((reasonAt id).add tag)) →
      CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      PostPreserves functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  refine LoopStatements.for_induction
    (motive := fun context evidence source environment before condition post statements _ outcome after =>
      ∀ {readFuel : Nat} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      SourceCoreRawMetadata.Extends values.registry registry →
      (∀ id location, faults (.uninitializedLocation location) (reasonAt id)) →
      (∀ id key value tag, MetadataRep registry (.mapping key value) tag → faults (.missingMappingDefault value) ((reasonAt id).add tag)) →
      CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      PostPreserves functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ?_ ?_ ?_ ?_ ?_ trace
  · intro context evidence source environment before after condition post statements conditionEvaluation
      readFuel values scope solved reasonAt ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
      condition_preserves functions extension program evidence uninitialized missing conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases represented with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      exact ⟨_, nextStore, nextMap, nextWorld, Core.LoopExecution.condition_false evaluated, .fallthrough environment, progress⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment outcome
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      readFuel values scope solved reasonAt ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions extension program evidence uninitialized missing conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | fallthrough _ =>
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := postCorrect (state.progress bodyTotal) false postEvaluation
        have progress := bodyTotal.trans postProgress
        have nextState := state.progress progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          ForLoop.body_fallthrough conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
            nextState.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment outcome
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      readFuel values scope solved reasonAt ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions extension program evidence uninitialized missing conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | continuing _ =>
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := postCorrect (state.progress bodyTotal) true postEvaluation
        have progress := bodyTotal.trans postProgress
        have nextState := state.progress progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          ForLoop.body_continuing conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
            nextState.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap after condition post statements bodyFinalContext bodyEnvironment
      conditionEvaluation bodyEvaluation
      readFuel values scope solved reasonAt ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions extension program evidence uninitialized missing conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | breaking _ =>
        exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_breaking conditionEval bodyEval, .fallthrough environment, conditionProgress.trans bodyProgress⟩
  · intro context evidence source environment before conditionHeap after condition post statements bodyFinalContext returned
      conditionEvaluation bodyEvaluation
      readFuel values scope solved reasonAt ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions extension program evidence uninitialized missing conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | returned payload =>
        exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_returned conditionEval bodyEval, .returned payload, conditionProgress.trans bodyProgress⟩


/-- Internal structural contract supplied by the concrete post header tree. -/
def PostFaults {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault},
    LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store →
    ∀ continued : Bool,
    Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after →
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore


theorem iterations_fault
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForLoopFaults program context evidence source environment before condition post statements reason after) :
    ∀ {readFuel : Nat} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      SourceCoreRawMetadata.Extends values.registry registry →
      (∀ id location, faults (.uninitializedLocation location) (reasonAt id)) →
      (∀ id key value tag, MetadataRep registry (.mapping key value) tag → faults (.missingMappingDefault value) ((reasonAt id).add tag)) →
      CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      PostPreserves functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      PostFaults functions program evidence (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  refine LoopStatements.for_fault_induction
    (motive := fun context evidence source environment before condition post statements reason after =>
      ∀ {readFuel : Nat} {values : ValuesContext} {scope : Scope} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
      {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
      {registry : SourceCoreRawMetadata.Registry} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
      {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
      {contextLocation location : Location} {expected : TypeSystem.Ty} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
      {mapping : LocationMap} {world : StoreTyping} {store : Store} {node : ExpressionNode} {faults : FunctionCalls.FaultRep} [FunctionCalls.FaultTokens faults],
      SourceCoreRawMetadata.Extends values.registry registry →
      (∀ id location, faults (.uninitializedLocation location) (reasonAt id)) →
      (∀ id key value tag, MetadataRep registry (.mapping key value) tag → faults (.missingMappingDefault value) ((reasonAt id).add tag)) →
      CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩ →
      source.lookupExpression? condition = some node →
      CompatibleExpressionLiterals.ContextValid solved context evidence → NodeOccurrencesUnique source →
      EnvironmentsAgree ξ canonical actual →
      canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation) →
      Preserves functions program evidence (source := source) (context := context) (registry := registry)
        (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
        (scope := scope) false statements expected type code →
      PostPreserves functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      PostFaults functions program evidence (source := source) (context := context) (scope := scope) (registry := registry) (faults := faults)
        (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
        (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
        (contextLocation := contextLocation) (location := location) (type := type)
        (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode →
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type (.fault reason) value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ?_ ?_ ?_ ?_ ?_ ?_ ?_ trace
  · intro context evidence source environment before after condition post statements reason conditionFault
      readFuel values scope solved reasonAt ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
      condition_preserves functions extension program evidence uninitialized missing conditionTree found valid unique agrees state (.fault conditionFault)
    cases represented with
    | fault matched => exact ⟨_, nextStore, nextMap, nextWorld, Core.LoopExecution.condition_failure evaluated, .fault matched, progress⟩
  · intro context evidence source environment before after condition post statements value actualType conditionEvaluation notBoolean runtimeType
      readFuel values scope solved reasonAt ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, nextStore, nextMap, nextWorld, evaluated, represented, progress⟩ :=
      condition_preserves functions extension program evidence uninitialized missing conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases represented with
    | value payload =>
      obtain ⟨boolean, rfl, _⟩ := bool_fields payload
      exact False.elim (notBoolean trivial)
  · intro context evidence source environment before conditionHeap after condition post statements bodyContext reason conditionEvaluation bodyFault
      readFuel values scope solved reasonAt ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions extension program evidence uninitialized missing conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.fault bodyFault)
      cases bodyRelated with
      | fault matched => exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_failure conditionEval bodyEval, .fault matched, conditionProgress.trans bodyProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition post statements bodyFinalContext bodyEnvironment finalContext reason
      conditionEvaluation bodyEvaluation postEvaluation
      readFuel values scope solved reasonAt ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions extension program evidence uninitialized missing conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | fallthrough _ =>
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨token, postStore, postMap, postWorld, postEval, matched, postProgress⟩ :=
          postFailed (state.progress bodyTotal) false postEvaluation
        exact ⟨_, postStore, postMap, postWorld,
          ForLoop.body_fallthrough_post_fault conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval),
          .fault matched, bodyTotal.trans postProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition post statements bodyFinalContext bodyEnvironment finalContext reason
      conditionEvaluation bodyEvaluation postEvaluation
      readFuel values scope solved reasonAt ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions extension program evidence uninitialized missing conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | continuing _ =>
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨token, postStore, postMap, postWorld, postEval, matched, postProgress⟩ :=
          postFailed (state.progress bodyTotal) true postEvaluation
        exact ⟨_, postStore, postMap, postWorld,
          ForLoop.body_continuing_post_fault conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval),
          .fault matched, bodyTotal.trans postProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      readFuel values scope solved reasonAt ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions extension program evidence uninitialized missing conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | fallthrough _ =>
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := postCorrect (state.progress bodyTotal) false postEvaluation
        have progress := bodyTotal.trans postProgress
        have nextState := state.progress progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect postFailed nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          ForLoop.body_fallthrough conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
            nextState.selfRead nativeTrace, related, progress.trans finalProgress⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      readFuel values scope solved reasonAt ambient functions registry frameLayout globals administrative actualContext canonical actual ξ
      contextLocation location expected type conditionCode code postCode selfReason mapping world store node faults _
      extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect postFailed state
    obtain ⟨value, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated, conditionProgress⟩ :=
      condition_preserves functions extension program evidence uninitialized missing conditionTree found valid unique agrees state (.value conditionEvaluation)
    cases conditionRelated with
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      cases sameSource
      subst sameCore
      obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress⟩ :=
        body_preserves functions program evidence correct valid agrees reference (state.progress conditionProgress) (.control bodyEvaluation)
      cases bodyRelated with
      | continuing _ =>
        have bodyTotal := conditionProgress.trans bodyProgress
        obtain ⟨postStore, postMap, postWorld, postEval, postProgress⟩ := postCorrect (state.progress bodyTotal) true postEvaluation
        have progress := bodyTotal.trans postProgress
        have nextState := state.progress progress
        obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress⟩ :=
          nextIH extension uninitialized missing conditionTree found valid unique agrees reference correct postCorrect postFailed nextState
        exact ⟨result, finalStore, finalMap, finalWorld,
          ForLoop.body_continuing conditionEval bodyEval
            (by simpa only [postValues, Bool.false_eq_true, ↓reduceIte, List.append_assoc, Core.LoopExecution.entryEnvironment, List.cons_append, List.nil_append] using postEval)
            nextState.selfRead nativeTrace, related, progress.trans finalProgress⟩

end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForReflection
/-! Completed native iterations reconstruct source iterations by strict
induction on the actual Core derivation. Condition and body traces are obtained
from their concrete-tree induction hypotheses, including their heap effects. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (Executes)
open TypedLexicalWhile (Scope ValuesContext Reflects FlowRep)
open CompatibleExpressionPrimitives (bool_fields)

inductive SourceLoop (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) :
    Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {outcome after} (trace : Dynamic.ForLoopExecutes program context evidence source environment before condition post statements context outcome after) :
      SourceLoop program context evidence source environment before condition post statements outcome after
  | fault {reason after} (trace : Dynamic.ForLoopFaults program context evidence source environment before condition post statements reason after) :
      SourceLoop program context evidence source environment before condition post statements (.fault reason) after

/-- Internal post contract, discharged by `TypedForHeader.Tree.reflects_post`.
It consumes the actual post subtree, not a prior source execution. -/
def PostReflects {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {registry : SourceCoreRawMetadata.Registry} {source : TypedSource} {context : SourceSemantics.Context} {scope : Scope}
    {administrative actualContext : Core.Context} {frameLayout : SourceCoreCallableIndexedFrames.Layout}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {contextLocation location : Location} {type : Ty} {conditionCode body : Expr} {selfReason : Word}
    (faults : FunctionCalls.FaultRep) (items : List ForItemForm) (code : Expr) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
    LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (code.rename ξ) selfReason mapping world before store →
    ∀ continued : Bool,
    Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (code.rename ξ)) value finalStore →
    (∃ finalContext finalEnvironment after finalMap finalWorld,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore)

private theorem insertion_zero : Renaming.insertion 0 = (fun index => index + 1) := by
  funext index
  simp [Renaming.insertion]

private theorem shift_comp (left right : Nat) :
    Renaming.comp (fun index => index + left) (fun index => index + right) =
      (fun index => index + (right + left)) := by
  funext index
  simp [Renaming.comp, Nat.add_assoc]

set_option maxRecDepth 3000 in
/-- Inversion of the actual body envelope exposes the actual post computation.
The four branch temporaries and Unit/self slots retain their concrete values. -/
theorem post_computation {size : Nat} {actual : Environment} {before bodyStore after : Store}
    {type : Ty} {location : Location} {body post : Expr} {reason : Word} {value : Value}
    (continued : Bool)
    (evaluation : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) before
      (LocalLoop.advance type (Core.LoopExecution.bodyCode body)
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).weakenAt 0)) value after)
    (bodyEval : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) before
      (Core.LoopExecution.bodyCode body) (if continued then LocalLoop.continuingValue type else LocalLoop.fallthroughValue type) bodyStore) :
    ∃ postStore postValue,
      Evaluates (postValues type location continued ++ actual) bodyStore (ForLoop.postCode post) postValue postStore := by
  cases continued
  · obtain ⟨next, _, postAdvance⟩ := evaluation.advance_fallthrough bodyEval
    have renamed : EvaluationSize next
        (ForLoop.fallthroughPrefix type ++ Core.LoopExecution.entryEnvironment type location actual) bodyStore
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).rename
          (fun index => index + 4)) value after := by
      simpa only [← Expr.rename_insertion, Expr.rename_comp, insertion_zero, shift_comp, Nat.reduceAdd, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, ForLoop.fallthroughPrefix, ForLoop.continuingPrefix, List.cons_append, List.nil_append] using postAdvance
    rw [LoopRenaming.advance] at renamed
    obtain ⟨_, store, result, _, evaluated⟩ := renamed.bind_computation
    exact ⟨store, result, evaluated.sound⟩
  · obtain ⟨next, _, postAdvance⟩ := evaluation.advance_continuing bodyEval
    have renamed : EvaluationSize next
        (ForLoop.continuingPrefix type ++ Core.LoopExecution.entryEnvironment type location actual) bodyStore
        ((LocalLoop.advance type (Core.LoopExecution.conditionCode post) (LocalLoop.invoke type (.var 1) reason)).rename
          (fun index => index + 4)) value after := by
      simpa only [← Expr.rename_insertion, Expr.rename_comp, insertion_zero, shift_comp, Nat.reduceAdd, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, ForLoop.fallthroughPrefix, ForLoop.continuingPrefix, List.cons_append, List.nil_append] using postAdvance
    rw [LoopRenaming.advance] at renamed
    obtain ⟨_, store, result, _, evaluated⟩ := renamed.bind_computation
    exact ⟨store, result, evaluated.sound⟩

variable {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : Scope}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension uninitialized missing in
theorem iterations_reflect [FunctionCalls.FaultTokens faults] {condition : ExpressionId} {node : ExpressionNode}
    {post : List ForItemForm} {statements : List StatementId} {expected : TypeSystem.Ty}
    (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (correct : Reflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (postCorrect : PostReflects functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := location) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode)
    (bodyCannotFault : ∀ {before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    ∀ (size : Nat) {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value},
      LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ outcome after finalMap finalWorld,
        SourceLoop program context evidence source environment before condition post statements outcome after ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro mapping world before store finalStore value state evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, _, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionOutcome, conditionHeap, conditionMap, conditionWorld, conditionTrace, conditionRelated, conditionProgress⟩ :=
      condition_reflects functions extension program evidence uninitialized missing conditionTree found valid agrees state conditionEval.sound
    cases conditionRelated with
    | fault matched =>
      cases conditionTrace with
      | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure conditionEval.sound)
        exact ⟨_, conditionHeap, conditionMap, conditionWorld, .fault (.condition failed), .fault matched, conditionProgress⟩
    | value payload =>
      obtain ⟨boolean, sameSource, sameCore⟩ := bool_fields payload
      subst sameSource
      subst sameCore
      cases conditionTrace with
      | value conditionTrace =>
        cases boolean with
        | false =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false conditionEval.sound)
          exact ⟨_, conditionHeap, conditionMap, conditionWorld, .control (.done conditionTrace), .fallthrough environment, conditionProgress⟩
        | true =>
          obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch conditionEval.sound
          obtain ⟨bodySize, bodyStore, bodyValue, _, bodyEval⟩ := branch.bind_computation
          obtain ⟨bodyContext, bodyOutcome, bodyHeap, bodyMap, bodyWorld, bodyTrace, bodyRelated, bodyProgress⟩ :=
            body_reflects functions program evidence correct valid agrees reference (state.progress conditionProgress) bodyEval.sound
          have progress := conditionProgress.trans bodyProgress
          cases bodyRelated with
          | fault matched =>
            cases bodyTrace with
            | control impossible => exact False.elim (bodyCannotFault impossible)
            | fault failed =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_failure conditionEval.sound bodyEval.sound)
              exact ⟨_, bodyHeap, bodyMap, bodyWorld, .fault (.body conditionTrace failed), .fault matched, progress⟩
          | returned payload =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_returned conditionEval.sound bodyEval.sound)
              exact ⟨_, bodyHeap, bodyMap, bodyWorld, .control (.returns conditionTrace bodyTrace), .returned payload, progress⟩
          | breaking bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_breaking conditionEval.sound bodyEval.sound)
              exact ⟨_, bodyHeap, bodyMap, bodyWorld, .control (.breaks conditionTrace bodyTrace), .fallthrough environment, progress⟩
          | fallthrough bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨postStore, postValue, postEval⟩ := post_computation false branch bodyEval.sound
              rcases postCorrect (state.progress progress) false postEval with done | failed
              · obtain ⟨postContext, postEnvironment, postHeap, postMap, postWorld, postTrace, rfl, postProgress⟩ := done
                have prefixProgress := progress.trans postProgress
                have nextState := state.progress prefixProgress
                obtain ⟨nextSize, smaller, nextEval⟩ := ForLoop.next_fallthrough branch bodyEval.sound postEval nextState.selfRead
                obtain ⟨outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress⟩ :=
                  ih nextSize (Nat.lt_trans smaller branchSmaller) nextState nextEval
                cases nextTrace with
                | control nextTrace => exact ⟨_, after, finalMap, finalWorld, .control (.nextFallthrough conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
                | fault nextTrace => exact ⟨_, after, finalMap, finalWorld, .fault (.nextFallthrough conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
              · obtain ⟨postContext, reason, token, postHeap, postMap, postWorld, postTrace, rfl, matched, postProgress⟩ := failed
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                  (ForLoop.body_fallthrough_post_fault conditionEval.sound bodyEval.sound postEval)
                exact ⟨_, postHeap, postMap, postWorld, .fault (.postFallthrough conditionTrace bodyTrace postTrace), .fault matched, progress.trans postProgress⟩
          | continuing bodyEnvironment =>
            cases bodyTrace with
            | control bodyTrace =>
              obtain ⟨postStore, postValue, postEval⟩ := post_computation true branch bodyEval.sound
              rcases postCorrect (state.progress progress) true postEval with done | failed
              · obtain ⟨postContext, postEnvironment, postHeap, postMap, postWorld, postTrace, rfl, postProgress⟩ := done
                have prefixProgress := progress.trans postProgress
                have nextState := state.progress prefixProgress
                obtain ⟨nextSize, smaller, nextEval⟩ := ForLoop.next_continuing branch bodyEval.sound postEval nextState.selfRead
                obtain ⟨outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress⟩ :=
                  ih nextSize (Nat.lt_trans smaller branchSmaller) nextState nextEval
                cases nextTrace with
                | control nextTrace => exact ⟨_, after, finalMap, finalWorld, .control (.nextContinue conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
                | fault nextTrace => exact ⟨_, after, finalMap, finalWorld, .fault (.nextContinue conditionTrace bodyTrace postTrace nextTrace), related, prefixProgress.trans nextProgress⟩
              · obtain ⟨postContext, reason, token, postHeap, postMap, postWorld, postTrace, rfl, matched, postProgress⟩ := failed
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                  (ForLoop.body_continuing_post_fault conditionEval.sound bodyEval.sound postEval)
                exact ⟨_, postHeap, postMap, postWorld, .fault (.postContinue conditionTrace bodyTrace postTrace), .fault matched, progress.trans postProgress⟩

end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForEndpoint
/-! Concrete for endpoints install one real administrative self cell. The body
contract is solely the recursive statement-tree hypothesis; the post uses its
actual header tree, including early failures and lexical restoration. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep Preserves Reflects installedStore installedWorld environment_respects retain)

variable {administrative : Core.Context} {readFuel : Nat} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

def LoopPreserves {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_trace : SourceLoop program context evidence source environment before condition post statements outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

def LoopReflects {scope : Scope} (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (_evaluated : Evaluates actual store (code.rename ξ) value finalStore),
    ∃ outcome after finalMap finalWorld,
      SourceLoop program context evidence source environment before condition post statements outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after

variable {scope : Scope} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}

variable {actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {contextLocation : Location}

theorem initial_state {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
    {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions) :
    LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation store.length type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping (installedWorld world type) before
      (installedStore store type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason actual) ∧
    Progress values registry functions before before mapping mapping world (installedWorld world type) store
      (installedStore store type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason actual) := by
  have actualCode := typed.rename (environment_respects environments.runtime_hasTypes actualTyped agrees)
  rw [LoopRenaming.iterate] at actualCode
  obtain ⟨installedHeaps, worlds, fresh, selfTyped, selfRead, frame⟩ := install selfReason heaps actualTyped actualCode
  obtain ⟨contextUnmapped, contextRead⟩ := retain unmapped read frame
  exact ⟨⟨environments.extend (.refl _) worlds, installedHeaps, locals, actualTyped.weaken worlds,
    ⟨native, contextRead⟩, contextUnmapped, selfTyped, selfRead, fresh⟩,
    installedHeaps, .refl _, worlds, frame, .refl _⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

include extension uninitialized missing unique definitions registered faithful observations in
theorem loop_preserves [FunctionCalls.FaultTokens faults] {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : TypedForHeader.Tree layouts owner active frameLayout globals onError readFuel values source solved reasonAt ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : TypedForHeader.Tree.Errors registry faults postTree)
    (correct : Preserves functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code) :
    LoopPreserves functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees actualTyped reference read unmapped trace
  obtain ⟨state, installedProgress⟩ := initial_state functions environments heaps locals agrees actualTyped read unmapped typed
  have postCorrect : PostPreserves functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := store.length) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) post postCode := by
    intro mapping world before after store finalContext finalEnvironment state continued trace
    exact post_preserves functions definitions registered extension program evidence uninitialized missing faithful observations postTree
      valid unique agrees reference state continued trace
  have postFailed : PostFaults functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := store.length) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) (faults := faults) post postCode := by
    intro mapping world before after store finalContext reason state continued trace
    exact post_fault functions definitions registered extension program evidence uninitialized missing faithful observations postTree postErrors
      valid unique agrees reference state continued trace
  cases trace with
  | control sourceTrace =>
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress⟩ :=
      iterations_success sourceTrace extension uninitialized missing conditionTree conditionFound valid unique agrees reference correct postCorrect state
    exact ⟨value, finalStore, finalMap, finalWorld,
      by
        rw [LoopRenaming.iterate]
        apply LocalLoop.iterate_evaluates
        exact LocalLoop.invoke_success _ _ (.var rfl) state.selfRead nativeTrace,
      represented, installedProgress.trans progress⟩
  | fault failed =>
    obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress⟩ :=
      iterations_fault failed extension uninitialized missing conditionTree conditionFound valid unique agrees reference correct postCorrect postFailed state
    exact ⟨value, finalStore, finalMap, finalWorld,
      by
        rw [LoopRenaming.iterate]
        apply LocalLoop.iterate_evaluates
        exact LocalLoop.invoke_success _ _ (.var rfl) state.selfRead nativeTrace,
      represented, installedProgress.trans progress⟩

include extension uninitialized missing unique definitions registered faithful observations in
theorem loop_reflects [FunctionCalls.FaultTokens faults] (functionTypes : FunctionRuntimeViews functions)
    {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {post : List ForItemForm} {expected : TypeSystem.Ty}
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : CompatibleExpressionTyped.Tree readFuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type conditionCode code postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
    (postTree : TypedForHeader.Tree layouts owner active frameLayout globals onError readFuel values source solved reasonAt ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope post postCode)
    (postErrors : TypedForHeader.Tree.Errors registry faults postTree)
    (correct : Reflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) false statements expected type code)
    (bodyCannotFault : ∀ {program context evidence environment before after finalContext reason},
      Dynamic.StatementsExecute program context evidence source environment before statements finalContext (.fault reason) after → False) :
    LoopReflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type (LocalLoop.iterate type conditionCode code postCode selfReason) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped evaluated
  obtain ⟨state, installedProgress⟩ := initial_state functions environments heaps locals agrees actualTyped read unmapped typed
  have postCorrect : PostReflects functions program evidence (source := source) (context := context) (scope := scope) (registry := registry)
      (frameLayout := frameLayout) (administrative := administrative) (actualContext := actualContext)
      (environment := environment) (canonical := canonical) (actual := actual) (ξ := ξ)
      (contextLocation := contextLocation) (location := store.length) (type := type)
      (conditionCode := conditionCode.rename ξ) (body := code.rename ξ) (selfReason := selfReason) faults post postCode := by
    intro mapping world before store finalStore value state continued trace
    exact post_reflects functions definitions registered extension program evidence uninitialized missing faithful observations functionTypes postTree postErrors
      valid unique agrees reference state continued trace
  rw [LoopRenaming.iterate] at evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨entrySize, _, entry⟩ := sized.iterate_entry
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, progress⟩ :=
    iterations_reflect functions extension program evidence uninitialized missing conditionTree conditionFound valid agrees reference correct
      postCorrect bodyCannotFault entrySize state entry
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, installedProgress.trans progress⟩

end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedImperativeForInitializers
/-! Header effects precede the installed loop. These composition lemmas are
used inside concrete statement-tree induction: their endpoint propositions
are proved from the recursive body, never stored in the compiler certificate.
The outer lexical environment is restored without discarding header cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext HeadPreserves HeadReflects restored restore_rep)

variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag → faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

abbrev PreservingHeader (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : TypedForHeader.Tree layouts owner active frameLayout globals onError readFuel values source solved reasonAt ambient.definitions administrative
    type (fun context scope code => LoopPreserves functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (administrative := administrative) condition post statements expected type code) context scope items code,
    TypedForHeader.Tree.Errors registry faults tree

abbrev ReflectingHeader (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : TypedForHeader.Tree layouts owner active frameLayout globals onError readFuel values source solved reasonAt ambient.definitions administrative
    type (fun context scope code => LoopReflects functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (administrative := administrative) condition post statements expected type code) context scope items code,
    TypedForHeader.Tree.Errors registry faults tree

include definitions registered extension uninitialized missing faithful observations in
theorem header_preserves [FunctionCalls.FaultTokens faults] (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : PreservingHeader functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frameLayout := frameLayout) (globals := globals) (onError := onError) (readFuel := readFuel)
      (source := source) (solved := solved) (reasonAt := reasonAt) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    HeadPreserves functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped trace
  obtain ⟨header, errors⟩ := headers
  cases trace with
  | control executed =>
    obtain ⟨rfl, loopContext, loopFinalContext, loopEnvironment, initialized, loopOutcome, rfl, initialization, loop⟩ :=
      ForSourceViews.success unique (lookupStatement?_sound found) form executed
    have sameContext : loopFinalContext = loopContext := by cases loop <;> rfl
    subst loopFinalContext
    obtain ⟨tail, maps, worlds, frame, metadata, agreement⟩ :=
      header.preserves_prefix functions definitions registered extension program evidence uninitialized missing faithful observations
        valid unique environments heaps locals agrees actualTyped reference read unmapped initialization
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩ :=
      tail.certificate tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped (.control loop)
    exact ⟨rfl, restored environment loopOutcome, value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
      restore_rep represented environment, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
      frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2⟩
  | fault failed =>
    rcases ForSourceViews.fault unique (lookupStatement?_sound found) form failed with initialFailure | loopFailure
    · obtain ⟨_, fault⟩ := initialFailure
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, frame, metadata⟩ :=
        header.preserves_fault functions definitions registered extension program evidence uninitialized missing faithful observations errors
          valid unique environments heaps locals agrees actualTyped reference read unmapped fault
      exact ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld,
        evaluated, .fault matched, heaps, maps, worlds, frame, metadata⟩
    · obtain ⟨loopContext, loopEnvironment, initialized, initialization, loop⟩ := loopFailure
      obtain ⟨tail, maps, worlds, frame, metadata, agreement⟩ :=
        header.preserves_prefix functions definitions registered extension program evidence uninitialized missing faithful observations
          valid unique environments heaps locals agrees actualTyped reference read unmapped initialization
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩ :=
        tail.certificate tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped (.fault loop)
      exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
        represented, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
        frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2⟩

include definitions registered extension uninitialized missing faithful observations in
theorem header_reflects [FunctionCalls.FaultTokens faults] (functionTypes : FunctionRuntimeViews functions) (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : ReflectingHeader functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frameLayout := frameLayout) (globals := globals) (onError := onError) (readFuel := readFuel)
      (source := source) (solved := solved) (reasonAt := reasonAt) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    HeadReflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped evaluated
  obtain ⟨header, errors⟩ := headers
  have result := header.reflects functions definitions registered extension program evidence uninitialized missing faithful observations functionTypes errors
    valid unique environments heaps locals agrees actualTyped reference read unmapped evaluated
  cases result with
  | continues tail trace maps worlds frame metadata remaining =>
    obtain ⟨outcome, after, finalMap, finalWorld, loop, represented, progress⟩ :=
      tail.certificate tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped remaining
    refine ⟨Dynamic.restoreControl environment outcome, after, finalMap, finalWorld, ?_, restored environment outcome,
      restore_rep represented environment, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
      frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2⟩
    cases loop with
    | control loop => exact .control (.forLoop (lookupStatement?_sound found) form trace loop)
    | fault loop => exact .fault (.forIteration (lookupStatement?_sound found) form trace loop)
  | fault trace same matched heaps maps worlds frame metadata =>
    subst value
    exact ⟨_, _, _, _, .fault (.forInitializer (lookupStatement?_sound found) form trace),
      (by intro next impossible; cases impossible), .fault matched, heaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
end

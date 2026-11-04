import Solcore.SourceSemantics.CoreLowering.Internal.Statements.ForFinite
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopCertificates
import Solcore.SourceSemantics.CoreLowering.CoreContinuationAgreement
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.ScalarAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.ScalarStatementViews

/-!
# For statements

`for` statements and their correspondence: headers, initializers, posts, success, faults and reflection.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForFiniteFault
/-! Forward simulation of every supplied finite for-loop fault, including
post faults and successful body/post prefixes before a later fault. The
post contracts are structural induction interfaces, not compiler axioms. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Internal

open Frontend Frontend.SourceInference TypeSystem LocalCell
open Core.LoopExecution

def PostFaultPreserves (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context)
    (environment : Dynamic.Environment) (canonical actual : Core.Environment) (actualContext : Core.Context)
    (type : Core.Ty) (location : Core.Location) (items : List ForItemForm) (code : Core.Expr)
    (reasonAt : ExpressionId → Core.Word) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {heap after : Dynamic.Heap}
    {store : Core.Store} {finalContext : Context} {reason : Dynamic.SemanticFault},
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Core.RuntimeEnvironmentHasTypes world actual actualContext →
    world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
    Dynamic.ForItemsFault program context evidence source environment heap items finalContext reason after →
    ∀ continued : Bool, ∃ token finalStore finalMap finalWorld,
      FaultRepresents program evidence source reasonAt reason token ∧
      Core.Evaluates ((if continued then CoreProof.ForLoop.continuingPrefix type else CoreProof.ForLoop.fallthroughPrefix type) ++
        entryEnvironment type location actual) store (CoreProof.ForLoop.postCode code)
        (.inLeft (Core.LocalLoop.controlType type) (.word token)) finalStore ∧
      GeneralHeap.HeapRepresents finalMap finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMap finalStore

private theorem condition_evaluates
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {condition : ExpressionId} {code : Core.Expr} {depth : Nat}
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool code depth)
    (unique : NodeOccurrencesUnique source)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment}
    {heap after : Dynamic.Heap} {store : Core.Store} {ξ : Core.Renaming} {boolean : Bool}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual)
    (type : Core.Ty) (location : Core.Location)
    (evaluation : Dynamic.ExpressionEvaluates program context evidence source environment heap condition (.bool boolean) after) :
    after = heap ∧ Core.Evaluates (entryEnvironment type location actual) store
      (conditionCode (code.rename ξ)) (.inRight .word (.bool boolean)) store := by
  obtain ⟨rfl, staged, same, typed, core⟩ := ScalarExpressionReflection.Primitive.source_success tree unique environments heaps evaluation
  obtain ⟨other, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
  cases same
  have restricted := GeneralExpressions.Primitive.readOnly tree
  have renamed := restricted.evaluation_rename core agree
  have shifted := (restricted.rename ξ).evaluation_weakenAt_zero renamed
    (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) location)
  have shiftedAgain := ((restricted.rename ξ).weakenAt 0).evaluation_weakenAt_zero shifted .unit
  exact ⟨rfl, shiftedAgain⟩

private theorem self_retained
    {mapping futureMapping : GeneralHeap.LocationMap} {before after : Core.Store}
    {location : Core.Location} {value : Core.Value}
    (unmapped : location ∉ mapping) (read : before.read? location = some value)
    (frame : GeneralHeap.AdministrativePreserved mapping before futureMapping after) :
    location ∉ futureMapping ∧ after.read? location = some value := by
  have bounded : location < before.length := by
    exact (List.getElem?_eq_some_iff.mp read).1
  obtain ⟨unmapped, same⟩ := frame location unmapped bounded
  exact ⟨unmapped, same.trans read⟩

def ForFaultResult (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (type : Core.Ty) (condition body postBody : Core.Expr) (selfReason : Core.Word)
    (location : Core.Location) (actual : Core.Environment)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) : Prop :=
  ∃ resultReason finalStore finalMapping finalWorld,
    FaultRepresents program evidence source reasonAt reason resultReason ∧
    Core.Evaluates (entryEnvironment type location actual) store (Core.LocalLoop.loopBody type condition body postBody selfReason)
      (.inLeft (Core.LocalLoop.controlType type) (.word resultReason)) finalStore ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

/-- Internal fault composition, including earlier successful iterations. The
body contracts remain explicit induction hypotheses, not compiler properties. -/
theorem for_fault
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {reason : Dynamic.SemanticFault}
    (execution : Dynamic.ForLoopFaults program context evidence source environment heap condition post statements reason after) :
    ∀ {compilation : SourceCorePrimitive.Context} {scope : SourceCoreLocalCell.Scope}
      {reasonAt : ExpressionId → Core.Word} {conditionCode : Core.Expr} {conditionDepth : Nat}
      {body postBody : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
      {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
      {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context} {store : Core.Store},
      PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth →
      NodeOccurrencesUnique source → PrimitiveExpressions.ContextValid compilation context → evidence.Covers context →
      Core.ReadOnly.EnvironmentsAgree ξ canonical actual →
      BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location statements body →
      BodyFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location statements body reasonAt →
      PostPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location post postBody →
      PostFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location post postBody reasonAt →
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
      GeneralHeap.HeapRepresents mapping world heap store →
      Core.RuntimeEnvironmentHasTypes world actual actualContext →
      world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
      location ∉ mapping →
      store.read? location = some (.inRight .unit
        (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body postBody selfReason location actual)) →
      ForFaultResult program evidence source reasonAt type (conditionCode.rename ξ) body postBody selfReason location actual
        mapping world store reason after := by
  refine @for_fault_induction program
    (fun context evidence source environment heap condition post statements reason after =>
      ∀ {compilation : SourceCorePrimitive.Context} {scope : SourceCoreLocalCell.Scope}
        {reasonAt : ExpressionId → Core.Word} {conditionCode : Core.Expr} {conditionDepth : Nat}
        {body postBody : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
        {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
        {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context} {store : Core.Store},
        PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth →
        NodeOccurrencesUnique source → PrimitiveExpressions.ContextValid compilation context → evidence.Covers context →
        Core.ReadOnly.EnvironmentsAgree ξ canonical actual →
        BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
          type location statements body →
        BodyFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
          type location statements body reasonAt →
      PostPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location post postBody →
      PostFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
        type location post postBody reasonAt →
        GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
        GeneralHeap.HeapRepresents mapping world heap store →
        Core.RuntimeEnvironmentHasTypes world actual actualContext →
        world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) → location ∉ mapping →
        store.read? location = some (.inRight .unit
          (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body postBody selfReason location actual)) →
        ForFaultResult program evidence source reasonAt type (conditionCode.rename ξ) body postBody selfReason location actual
          mapping world store reason after)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ context evidence source environment heap condition post statements reason after execution
  · intro context evidence source environment before after condition post statements reason conditionFault
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, site, faultLocation, rfl, origin, core⟩ := ScalarExpressionReflection.Primitive.source_fault
      conditionTree unique valid covers environments heaps conditionFault
    have restricted := GeneralExpressions.Primitive.readOnly conditionTree
    have renamed := restricted.evaluation_rename core agree
    have shifted := (restricted.rename ξ).evaluation_weakenAt_zero renamed
      (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) location)
    have shiftedAgain := ((restricted.rename ξ).weakenAt 0).evaluation_weakenAt_zero shifted .unit
    exact ⟨_, store, mapping, world, .uninitialized site faultLocation origin,
      Core.LoopExecution.condition_failure shiftedAgain, heaps, .refl _, .refl _, .refl _ _⟩
  · intro context evidence source environment before after condition post statements value actualType evaluation notBool actualTypeProof
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨_, staged, rfl, typed, _⟩ := ScalarExpressionReflection.Primitive.source_success
      conditionTree unique environments heaps evaluation
    obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
    exact False.elim (notBool trivial)
  · intro context evidence source environment before conditionHeap after condition post statements finalContext reason
      conditionEvaluation bodyFault
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨resultReason, finalStore, finalMapping, finalWorld, related, bodyCore, finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyFaultCorrect environments heaps actualTyped selfTyped bodyFault
    exact ⟨_, finalStore, finalMapping, finalWorld, related, Core.LoopExecution.body_failure conditionCore bodyCore,
      finalHeaps, mapsExtended, worldsExtended, bodyFrame⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition post statements bodyFinalContext bodyEnvironment finalContext reason
      conditionEvaluation bodyEvaluation postFault
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, nextStore, nextMapping, nextWorld, related, bodyCore, nextHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | fallthrough =>
      obtain ⟨token, postStore, postMap, postWorld, postRelated, postCore, postHeaps, postMaps, postWorlds, postFrame⟩ :=
        postFaultCorrect (environments.extend mapsExtended worldsExtended) nextHeaps
          (Core.RuntimeEnvironmentHasTypes.weaken worldsExtended actualTyped)
          (worldsExtended.lookup selfTyped) postFault false
      exact ⟨token, postStore, postMap, postWorld, postRelated,
        CoreProof.ForLoop.body_fallthrough_post_fault conditionCore bodyCore postCore,
        postHeaps, mapsExtended.trans postMaps, worldsExtended.trans postWorlds, bodyFrame.trans postFrame⟩
  · intro context evidence source environment before conditionHeap bodyHeap after condition post statements bodyFinalContext bodyEnvironment finalContext reason
      conditionEvaluation bodyEvaluation postFault
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, nextStore, nextMapping, nextWorld, related, bodyCore, nextHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | continuing =>
      obtain ⟨token, postStore, postMap, postWorld, postRelated, postCore, postHeaps, postMaps, postWorlds, postFrame⟩ :=
        postFaultCorrect (environments.extend mapsExtended worldsExtended) nextHeaps
          (Core.RuntimeEnvironmentHasTypes.weaken worldsExtended actualTyped)
          (worldsExtended.lookup selfTyped) postFault true
      exact ⟨token, postStore, postMap, postWorld, postRelated,
        CoreProof.ForLoop.body_continuing_post_fault conditionCore bodyCore postCore,
        postHeaps, mapsExtended.trans postMaps, worldsExtended.trans postWorlds, bodyFrame.trans postFrame⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, nextStore, nextMapping, nextWorld, related, bodyCore, nextHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | fallthrough =>
        obtain ⟨postStore, postMap, postWorld, postCore, postHeaps, postMaps, postWorlds, postFrame⟩ :=
          postCorrect (environments.extend mapsExtended worldsExtended) nextHeaps
            (Core.RuntimeEnvironmentHasTypes.weaken worldsExtended actualTyped)
            (worldsExtended.lookup selfTyped) postEvaluation false
        obtain ⟨stillUnmapped, stillInstalled⟩ := self_retained unmapped installed (bodyFrame.trans postFrame)
        obtain ⟨resultReason, finalStore, finalMapping, finalWorld, resultRelated, trace, finalHeaps, mapsAgain, worldsAgain, nextFrame⟩ :=
          nextIH conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect
            (environments.extend (mapsExtended.trans postMaps) (worldsExtended.trans postWorlds)) postHeaps
            (Core.RuntimeEnvironmentHasTypes.weaken (worldsExtended.trans postWorlds) actualTyped)
            ((worldsExtended.trans postWorlds).lookup selfTyped) stillUnmapped stillInstalled
        exact ⟨resultReason, finalStore, finalMapping, finalWorld, resultRelated,
          CoreProof.ForLoop.body_fallthrough conditionCore bodyCore postCore stillInstalled trace, finalHeaps,
          (mapsExtended.trans postMaps).trans mapsAgain, (worldsExtended.trans postWorlds).trans worldsAgain,
          (bodyFrame.trans postFrame).trans nextFrame⟩
  · intro context evidence source environment before conditionHeap bodyHeap postHeap after condition post statements bodyFinalContext postFinalContext bodyEnvironment postEnvironment reason
      conditionEvaluation bodyEvaluation postEvaluation next nextIH
      compilation scope reasonAt conditionCode conditionDepth body postBody type selfReason location canonical actual actualContext ξ mapping world admin store
      conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect environments heaps actualTyped selfTyped unmapped installed
    obtain ⟨rfl, conditionCore⟩ := condition_evaluates conditionTree unique environments heaps agree type location conditionEvaluation
    obtain ⟨bodyResult, nextStore, nextMapping, nextWorld, related, bodyCore, nextHeaps, mapsExtended, worldsExtended, bodyFrame⟩ :=
      bodyCorrect environments heaps actualTyped selfTyped bodyEvaluation
    cases related with
    | continuing =>
        obtain ⟨postStore, postMap, postWorld, postCore, postHeaps, postMaps, postWorlds, postFrame⟩ :=
          postCorrect (environments.extend mapsExtended worldsExtended) nextHeaps
            (Core.RuntimeEnvironmentHasTypes.weaken worldsExtended actualTyped)
            (worldsExtended.lookup selfTyped) postEvaluation true
        obtain ⟨stillUnmapped, stillInstalled⟩ := self_retained unmapped installed (bodyFrame.trans postFrame)
        obtain ⟨resultReason, finalStore, finalMapping, finalWorld, resultRelated, trace, finalHeaps, mapsAgain, worldsAgain, nextFrame⟩ :=
          nextIH conditionTree unique valid covers agree bodyCorrect bodyFaultCorrect postCorrect postFaultCorrect
            (environments.extend (mapsExtended.trans postMaps) (worldsExtended.trans postWorlds)) postHeaps
            (Core.RuntimeEnvironmentHasTypes.weaken (worldsExtended.trans postWorlds) actualTyped)
            ((worldsExtended.trans postWorlds).lookup selfTyped) stillUnmapped stillInstalled
        exact ⟨resultReason, finalStore, finalMapping, finalWorld, resultRelated,
          CoreProof.ForLoop.body_continuing conditionCore bodyCore postCore stillInstalled trace, finalHeaps,
          (mapsExtended.trans postMaps).trans mapsAgain, (worldsExtended.trans postWorlds).trans worldsAgain,
          (bodyFrame.trans postFrame).trans nextFrame⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Internal
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopStatementReconstruction
/-! Compositional source-trace reconstruction for generated statement helpers.
Only syntax certificates, represented initial state, and finite Core
executions are supplied; source child executions are constructed here. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Internal CoreProof

theorem stagedTyped (value : SourceStagedValue.Value) (world : Core.StoreTyping) :
    Core.RuntimeValueHasType world (SourceStagedValue.toCore value) (SourceStagedValue.coreType value) :=
  GeneralHeap.ValueRepresents.runtime_hasType (mapping := []) (.scalar value)

private theorem valid_extend
    {compilation : SourceCorePrimitive.Context} {owner : Resolved.DeclarationId}
    {context middle : Context} {binder : TypedBinder}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (extension : BinderExtends owner context binder middle) :
    PrimitiveExpressions.ContextValid compilation middle := by
  cases extension
  exact ⟨valid.ledger, valid.valid.transport rfl rfl rfl⟩

theorem expression_meaning
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt id type code depth)
    (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (valid : PrimitiveExpressions.ContextValid compilation context)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ) :
    ∃ outcome value,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome heap ∧
      PrimitiveExpressions.OutcomeRepresents program context evidence source environment heap reasonAt id type outcome value ∧
      Core.Evaluates actual store (code.rename ξ) value store := by
  obtain ⟨outcome, value, sourceEval, related, coreEval⟩ :=
    GeneralExpressions.Primitive.preserves tree program context evidence valid environments heaps
  exact ⟨outcome, value, sourceEval, related,
    (GeneralExpressions.Primitive.readOnly tree).evaluation_rename coreEval layout.agrees⟩

theorem prepend
    {program : Program} {context middleContext finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {mode : Bool}
    {environment nextEnvironment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {rest : List StatementId} {type : Core.Ty}
    {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    (contains : ContainsStatement source id node)
    (notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough nextEnvironment) middle)
    (tail : Meaning program middleContext evidence source reasonAt mode nextEnvironment middle rest type finalContext outcome after result) :
    Meaning program context evidence source reasonAt mode environment before (id :: rest) type finalContext outcome after result := by
  cases mode with
  | false =>
    cases tail with
    | control execution related => exact .control (.cons head execution) related
    | fault fault related => exact .fault (.tail head fault) related
  | true =>
    cases rest with
    | nil =>
      cases tail with
      | control execution related =>
        cases execution
        exact .control (.singleton contains (notTail rfl rfl) head) related
      | fault fault _ => cases fault
    | cons next rest =>
      cases tail with
      | control execution related => exact .control (.cons head execution) related
      | fault fault related => exact .fault (.tail head fault) related

theorem terminal
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {mode : Bool}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {rest : List StatementId} {type : Core.Ty}
    {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    (contains : ContainsStatement source id node) (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after)
    (terminal : Dynamic.TerminalControl outcome) (related : ControlRepresents type outcome result) :
    Meaning program context evidence source reasonAt mode environment before (id :: rest) type finalContext outcome after result := by
  cases mode with
  | false => exact .control (.terminal head terminal) related
  | true =>
    cases rest with
    | nil => exact .control (.singleton contains notTail head) related
    | cons => exact .control (.terminal head terminal) related

theorem head_fault
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {mode : Bool}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {type : Core.Ty} {reason : Dynamic.SemanticFault} {word : Core.Word}
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after)
    (related : FaultRepresents program evidence source reasonAt reason word) :
    Meaning program context evidence source reasonAt mode environment before (id :: rest) type context (.fault reason) after
      (.inLeft (Core.LocalLoop.controlType type) (.word word)) := by
  cases mode with
  | false => exact .fault (.head fault) related
  | true => cases rest with
    | nil => exact .fault (.singleton fault) related
    | cons => exact .fault (.head fault) related

theorem reflects_nil (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (mode : Bool) (type : Core.Ty) :
    Reflects compilation program evidence source reasonAt scope context mode [] type (Core.LocalLoop.fallthrough type) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    _ _ _ heaps _ evaluated
  simp only [Core.LoopRenaming.fallthrough] at evaluated
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.fallthrough_evaluates type actual store)
  refine ⟨context, _, heap, mapping, world, .control ?_ (.fallthrough environment), heaps, .refl _, .refl _, .refl _ _⟩
  cases mode <;> exact .nil

theorem reflects_breaking
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type : Core.Ty}
    (contains : ContainsStatement source id node) (form : node.form = .breakStmt) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type (Core.LocalLoop.breaking type) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    _ _ _ heaps _ evaluated
  simp only [Core.LoopRenaming.breaking] at evaluated
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.breaking_evaluates type actual store)
  exact ⟨context, _, heap, mapping, world,
    terminal contains (by intro expression; simp [form]) (.breakStmt contains form) (.breaking environment) (.breaking environment),
    heaps, .refl _, .refl _, .refl _ _⟩

theorem reflects_continuing
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type : Core.Ty}
    (contains : ContainsStatement source id node) (form : node.form = .continueStmt) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type (Core.LocalLoop.continuing type) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    _ _ _ heaps _ evaluated
  simp only [Core.LoopRenaming.continuing] at evaluated
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.continuing_evaluates type actual store)
  exact ⟨context, _, heap, mapping, world,
    terminal contains (by intro expression; simp [form]) (.continueStmt contains form) (.continuing environment) (.continuing environment),
    heaps, .refl _, .refl _, .refl _ _⟩

theorem reflects_returnUnit
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (contains : ContainsStatement source id node) (form : node.form = .returnStmt none) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) .unit (Core.LocalLoop.returned .unit) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    _ _ _ heaps _ evaluated
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.returned_evaluates Core.Evaluates.unit)
  exact ⟨context, _, heap, mapping, world,
    terminal contains (by intro expression; simp [form]) (.returnUnit contains form) (.returned .unit) (.returned .unit rfl),
    heaps, .refl _, .refl _, .refl _ _⟩

theorem reflects_returnValue
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type : Core.Ty}
    {valueId : ExpressionId} {code : Core.Expr} {depth : Nat}
    (contains : ContainsStatement source id node) (form : node.form = .returnStmt (some valueId))
    (valueTree : PrimitiveExpressions.Tree compilation source scope reasonAt valueId type code depth) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type (Core.LocalLoop.returnValue type code) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    _ valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.returnValue] at evaluated
  obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
  cases related with
  | value staged typed =>
    cases sourceEval with
    | value sourceEval =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.returnValue_success type coreEval)
      exact ⟨context, _, heap, mapping, world,
        terminal contains (by intro expression; simp [form]) (.returnValue contains form sourceEval) (.returned _) (.returned staged typed),
        heaps, .refl _, .refl _, .refl _ _⟩
  | uninitialized site location origin =>
    cases sourceEval with
    | fault sourceFault =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.returnValue_failure type coreEval)
      exact ⟨context, _, heap, mapping, world,
        head_fault (.returnValue contains form sourceFault) (.uninitialized site location origin),
        heaps, .refl _, .refl _, .refl _ _⟩

theorem reflects_tailExpression
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {id : StatementId} {node : StatementNode} {type : Core.Ty} {valueId : ExpressionId} {code : Core.Expr} {depth : Nat}
    (contains : ContainsStatement source id node) (form : node.form = .expression valueId false)
    (valueTree : PrimitiveExpressions.Tree compilation source scope reasonAt valueId type code depth) :
    Reflects compilation program evidence source reasonAt scope context true [id] type (Core.LocalLoop.returnValue type code) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    _ valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.returnValue] at evaluated
  obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
  cases related with
  | value staged typed =>
    cases sourceEval with
    | value sourceEval =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.returnValue_success type coreEval)
      exact ⟨context, _, heap, mapping, world, .control (.tailExpression contains form sourceEval) (.returned staged typed),
        heaps, .refl _, .refl _, .refl _ _⟩
  | uninitialized site location origin =>
    cases sourceEval with
    | fault sourceFault =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.returnValue_failure type coreEval)
      exact ⟨context, _, heap, mapping, world, .fault (.tailExpression contains form sourceFault) (.uninitialized site location origin),
        heaps, .refl _, .refl _, .refl _ _⟩


private theorem notTail_expression {mode semicolon : Bool} {rest : List StatementId}
    {node : StatementNode} {valueId : ExpressionId}
    (form : node.form = .expression valueId semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false) :
    mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
  intro sameMode empty expression impossible
  rw [form] at impossible
  cases impossible
  simp [sameMode, empty] at notTail

theorem reflects_discard
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode semicolon : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type valueType : Core.Ty}
    {valueId : ExpressionId} {code body : Core.Expr} {depth : Nat}
    (contains : ContainsStatement source id node) (form : node.form = .expression valueId semicolon)
    (notTail : (!semicolon && mode && rest.isEmpty) = false)
    (valueTree : PrimitiveExpressions.Tree compilation source scope reasonAt valueId valueType code depth)
    (tail : Reflects compilation program evidence source reasonAt scope context mode rest type body) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type
      (Core.LocalSequence.discard (Core.LocalLoop.controlType type) code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.discard] at evaluated
  obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
  cases related with
  | value staged typed =>
    cases sourceEval with
    | value sourceEval =>
      obtain ⟨size, sized⟩ := evaluation_has_size evaluated
      obtain ⟨_, _, continuation⟩ := sized.bind_success coreEval
      obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
        tail wellFormed valid environments heaps (layout.insert (stagedTyped staged world))
          (by simpa only [rename_insert] using continuation.sound)
      exact ⟨finalContext, outcome, after, finalMap, finalWorld,
        prepend contains (notTail_expression form notTail) (.expression contains form sourceEval) meaning,
        finalHeaps, maps, worlds, frame⟩
  | uninitialized site location origin =>
    cases sourceEval with
    | fault sourceFault =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalSequence.discard_failure (Core.LocalLoop.controlType type) coreEval)
      exact ⟨context, _, heap, mapping, world,
        head_fault (.expression contains form sourceFault) (.uninitialized site location origin),
        heaps, .refl _, .refl _, .refl _ _⟩

theorem reflects_letUninitialized
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context middleContext : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type payload : Core.Ty} {body : Core.Expr} {binder : TypedBinder}
    (contains : ContainsStatement source id node) (form : node.form = .letDecl binder none)
    (binding : BinderCertificate source scope binder payload)
    (extension : BinderExtends source.owner context binder middleContext)
    (tail : Reflects compilation program evidence source reasonAt ((binder.id, payload) :: scope) middleContext mode rest type body) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type
      (Core.LocalSequence.letUninitialized payload body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.letUninitialized] at evaluated
  have allocated : Dynamic.Heap.Allocates heap binder.scheme.body none
      ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩ := .append
  obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
  have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
  have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
    rw [← heaps.runtime_hasTypes.length_eq]; simp
  have nextLayout := (layout.extend worlds).bind (Core.RuntimeValueHasType.cellRef found)
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨_, _, continuation⟩ := sized.let_body (Core.OptionalCell.allocate_evaluates payload actual store)
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, futureWorlds, frame⟩ :=
    tail wellFormed (valid_extend valid extension) nextEnvironments nextHeaps nextLayout continuation.sound
  exact ⟨finalContext, outcome, after, finalMap, finalWorld,
    prepend contains (by intros; simp [form]) (.letUninitialized contains form binding.monomorphic extension allocated) meaning,
    finalHeaps, (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps,
    worlds.trans futureWorlds, (GeneralHeap.AdministrativePreserved.allocate mapping store (.inLeft payload .unit)).trans frame⟩

theorem reflects_letInitialized
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context middleContext : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type payload : Core.Ty} {code body : Core.Expr} {binder : TypedBinder}
    {initializer : ExpressionId} {depth : Nat}
    (contains : ContainsStatement source id node) (form : node.form = .letDecl binder (some initializer))
    (binding : BinderCertificate source scope binder payload)
    (extension : BinderExtends source.owner context binder middleContext)
    (valueTree : PrimitiveExpressions.Tree compilation source scope reasonAt initializer payload code depth)
    (tail : Reflects compilation program evidence source reasonAt ((binder.id, payload) :: scope) middleContext mode rest type body) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type
      (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType type) payload code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.letInitialized] at evaluated
  obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
  cases related with
  | value staged typed =>
    cases sourceEval with
    | value sourceEval =>
      have allocated : Dynamic.Heap.Allocates heap binder.scheme.body (some (StagedValue.toSource staged))
          ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := some (StagedValue.toSource staged) }]⟩ := .append
      have sameSource : binder.scheme.body = SourceStagedValue.sourceType staged := binding.types.source_unique (typed ▸ stagedTypes staged)
      have cell : CellRepresents {type := binder.scheme.body, value := some (StagedValue.toSource staged)}
          (.inRight .unit (SourceStagedValue.toCore staged)) payload := by
        rw [sameSource, ← typed]; exact .initialized staged
      obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
      have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
      have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
        rw [← heaps.runtime_hasTypes.length_eq]; simp
      have nextLayout := ((layout.extend worlds).insert (stagedTyped staged _)).bind (Core.RuntimeValueHasType.cellRef found)
      obtain ⟨size, sized⟩ := evaluation_has_size evaluated
      obtain ⟨_, _, allocation⟩ := sized.bind_success coreEval
      obtain ⟨_, _, continuation⟩ := allocation.let_body (Core.OptionalCell.allocateInitialized_evaluates (.var rfl))
      obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, futureWorlds, frame⟩ :=
        tail wellFormed (valid_extend valid extension) nextEnvironments nextHeaps nextLayout
          (by simpa only [rename_insert_lift, Core.Store.allocate] using continuation.sound)
      exact ⟨finalContext, outcome, after, finalMap, finalWorld,
        prepend contains (by intros; simp [form]) (.letInitialized contains form sourceEval binding.monomorphic extension allocated) meaning,
        finalHeaps, (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩).trans maps,
        worlds.trans futureWorlds,
        (GeneralHeap.AdministrativePreserved.allocate mapping store (.inRight .unit (SourceStagedValue.toCore staged))).trans frame⟩
  | uninitialized site location origin =>
    cases sourceEval with
    | fault sourceFault =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated
        (Core.LocalSequence.letInitialized_failure (Core.LocalLoop.controlType type) payload coreEval)
      exact ⟨context, _, heap, mapping, world,
        head_fault (.letInitializer contains form binding.monomorphic sourceFault) (.uninitialized site location origin),
        heaps, .refl _, .refl _, .refl _ _⟩

private theorem cellsWrite_set {cells : List Dynamic.Cell} {index : Nat}
    {previous : Dynamic.Cell} (selected : Dynamic.Heap.CellAt cells index previous)
    (replacement : Dynamic.Cell) :
    Dynamic.Heap.CellsWrite cells index replacement (cells.set index replacement) := by
  induction selected with
  | head => exact .head
  | tail _ ih => exact .tail ih

/-- Basic expression RHS evaluation leaves its heap unchanged. The captured
source location and independently mapped Core location identify the same cell. -/
private theorem equal_assignment
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap : Dynamic.Heap} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    {target : PlaceResolution} {rhs : ExpressionId} {index : Nat} {payloadType : Core.Ty}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (slot : SourceCoreLocalCell.lookup? scope target.root = some (index, payloadType))
    (bare : target.projections = []) (value : SourceStagedValue.Value)
    (valueType : SourceStagedValue.coreType value = payloadType)
    (rhsEvaluated : Dynamic.ExpressionEvaluates program context evidence source environment
      heap rhs (StagedValue.toSource value) heap) :
    ∃ (coreLocation : Core.Location) (after : Dynamic.Heap) (finalStore : Core.Store),
      Dynamic.SourcePlaceAssignment program context evidence source
        (Dynamic.AssignmentValueApplies .equal) environment heap target rhs (StagedValue.toSource value) after ∧
      coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation) ∧
      (∃ oldValue, store.read? coreLocation = some oldValue) ∧
      store.write? coreLocation (.inRight .unit (SourceStagedValue.toCore value)) = some finalStore ∧
      GeneralHeap.HeapRepresents mapping world after finalStore ∧
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store mapping finalStore := by
  obtain ⟨location, coreLocation, cell, stored, lookup, coreLookup, reference, read, coreRead, represented⟩ :=
    environments.lookup_heap heaps slot
  let replacement : Dynamic.Cell := { cell with value := some (StagedValue.toSource value) }
  let after : Dynamic.Heap := ⟨heap.cells.set location.index replacement⟩
  have sourceWrite : Dynamic.Heap.Writes heap location (some (StagedValue.toSource value)) after := by
    cases read with
    | intro selected => exact .intro (.intro selected) (cellsWrite_set selected replacement)
  obtain ⟨finalStore, written, heapRelated⟩ := heaps.write_initialized reference value valueType sourceWrite
  let captured : Dynamic.ResolvedPlace := {
    location, rootType := cell.type, valueType := target.type, projections := [], selected := cell.value
  }
  have resolved : Dynamic.SourcePlaceResolves program context evidence source environment heap target captured heap := by
    apply Dynamic.SourcePlaceResolves.intro lookup read
    · rw [bare]; exact .nil
    · exact read
    · exact represented.rootInitialValue
    · exact .nil
  exact ⟨coreLocation, after, finalStore,
    .intro resolved rhsEvaluated
      (.intro read rfl represented.rootInitialValue (.leaf (.equal cell.value (StagedValue.toSource value))) sourceWrite),
    coreLookup, ⟨stored, coreRead⟩, written, heapRelated, environments,
    GeneralHeap.AdministrativePreserved.write (List.mem_of_getElem? reference.mapped) written⟩


theorem reflects_assign
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type payload : Core.Ty}
    {rhs : ExpressionId} {code body : Core.Expr} {depth index : Nat} {assignment : AssignmentResolution}
    (contains : ContainsStatement source id node) (form : node.form = .assignValue assignment .equal rhs)
    (target : AssignmentCertificate source scope assignment .equal index payload)
    (valueTree : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payload code depth)
    (tail : Reflects compilation program evidence source reasonAt scope context mode rest type body) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type
      (Core.LocalSequence.assign (Core.LocalLoop.controlType type) (.var index) code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.assign] at evaluated
  obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
  cases related with
  | value staged typed =>
    cases sourceEval with
    | value sourceEval =>
      obtain ⟨location, afterWrite, writtenStore, assigned, lookup, ⟨old, readable⟩, written,
        updatedHeaps, updatedEnvironments, writeFrame⟩ := equal_assignment environments heaps target.slot target.bare staged typed sourceEval
      have actualLookup := layout.agrees lookup
      have referenceTyped : Core.RuntimeValueHasType world
          (.cellRef (Core.OptionalCell.cellType payload) location) (Core.OptionalCell.referenceType payload) := by
        obtain ⟨found, foundEq, foundTyped⟩ := Core.RuntimeEnvironmentHasTypes.lookup layout.typed
          (layout.respects (SourceCoreLocalCell.lookup?_context target.slot))
        rw [actualLookup] at foundEq
        cases foundEq
        exact foundTyped
      obtain ⟨size, sized⟩ := evaluation_has_size evaluated
      obtain ⟨_, _, rhsEvaluation⟩ := sized.let_body (.var actualLookup)
      obtain ⟨_, _, writeEvaluation⟩ := rhsEvaluation.bind_success
        (((GeneralExpressions.Primitive.readOnly valueTree).rename ξ).evaluation_weakenAt_zero coreEval _)
      have writeEval : Core.Evaluates
          (SourceStagedValue.toCore staged :: .cellRef (Core.OptionalCell.cellType payload) location :: actual) store
          (.storeCell (.var 1) (.inRight .unit (.var 0))) .unit writtenStore :=
        .storeCell (.var rfl) readable (.inRight (.var rfl)) written
      obtain ⟨_, _, continuation⟩ := writeEvaluation.let_body writeEval
      have nextLayout := ((layout.insert referenceTyped).insert (stagedTyped staged world)).insert Core.RuntimeValueHasType.unit
      obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
        tail wellFormed valid updatedEnvironments updatedHeaps nextLayout
          (by simpa only [rename_insert] using continuation.sound)
      exact ⟨finalContext, outcome, after, finalMap, finalWorld,
        prepend contains (by intros; simp [form]) (.assignValue contains form assigned) meaning,
        finalHeaps, maps, worlds, writeFrame.trans frame⟩
  | uninitialized site location origin =>
    cases sourceEval with
    | fault sourceFault =>
      obtain ⟨sourceLocation, coreLocation, cell, stored, lookup, coreLookup, reference, read, coreRead, represented⟩ :=
        environments.lookup_heap heaps target.slot
      let captured : Dynamic.ResolvedPlace := {
        location := sourceLocation, rootType := cell.type, valueType := assignment.target.type,
        projections := [], selected := cell.value
      }
      have resolved : Dynamic.SourcePlaceResolves program context evidence source environment heap assignment.target captured heap := by
        apply Dynamic.SourcePlaceResolves.intro lookup read
        · rw [target.bare]; exact .nil
        · exact read
        · exact represented.rootInitialValue
        · exact .nil
      have core := Core.LocalSequence.assign_failure (next := body.rename ξ) (Core.LocalLoop.controlType type)
        (Core.Evaluates.var (layout.agrees coreLookup))
        (((GeneralExpressions.Primitive.readOnly valueTree).rename ξ).evaluation_weakenAt_zero coreEval _)
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated core
      exact ⟨context, _, heap, mapping, world,
        head_fault (.assignValue contains form (.rhs resolved sourceFault)) (.uninitialized site location origin),
        heaps, .refl _, .refl _, .refl _ _⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForHeaderMeaning
/-! Execute only a finite scalar/product header prefix in independent source
semantics. Its static continuation is preserved as an unevaluated Core hole:
finite evaluations can be composed around it and recovered from the whole
header. The loop itself is never evaluated by this construction. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements CoreProof
open LoopStatements

structure TailState (administrativeContext : Core.Context)
    (continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop) where
  scope : SourceCoreLocalCell.Scope
  context : Context
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  canonical : Core.Environment
  actual : Core.Environment
  actualContext : Core.Context
  embedding : Core.Renaming
  store : Core.Store
  code : Core.Expr
  certificate : continuation scope context code
  environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical
  heaps : GeneralHeap.HeapRepresents mapping world heap store
  layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual embedding

/-- A header only adds lexical binders to its context. This records the
source binder derivation needed to transport ledger validity and evidence. -/
def ContextExtends (owner : Resolved.DeclarationId) (before after : Context) : Prop :=
  ∃ binders, BindersExtend owner before binders after

namespace ContextExtends

theorem refl (owner : Resolved.DeclarationId) (context : Context) : ContextExtends owner context context :=
  ⟨[], .nil _⟩

theorem binder {owner : Resolved.DeclarationId} {before after : Context} {binder : TypedBinder}
    (extension : BinderExtends owner before binder after) : ContextExtends owner before after :=
  ⟨[binder], .cons extension (.nil _)⟩

private theorem append {owner : Resolved.DeclarationId} {before middle after : Context}
    {left right : List TypedBinder} (first : BindersExtend owner before left middle)
    (second : BindersExtend owner middle right after) : BindersExtend owner before (left ++ right) after := by
  induction first with
  | nil => exact second
  | cons head _ tail => exact .cons head (tail second)

theorem trans {owner : Resolved.DeclarationId} {before middle after : Context}
    (first : ContextExtends owner before middle) (second : ContextExtends owner middle after) :
    ContextExtends owner before after := by
  obtain ⟨left, first⟩ := first
  obtain ⟨right, second⟩ := second
  exact ⟨left ++ right, append first second⟩

theorem valid {owner : Resolved.DeclarationId} {before after : Context} {compilation : SourceCorePrimitive.Context}
    (extension : ContextExtends owner before after) (valid : PrimitiveExpressions.ContextValid compilation before) :
    PrimitiveExpressions.ContextValid compilation after := by
  obtain ⟨binders, extension⟩ := extension
  induction extension with
  | nil => exact valid
  | cons head _ tail =>
    apply tail
    cases head
    exact ⟨valid.ledger, valid.valid.transport rfl rfl rfl⟩

theorem covers {owner : Resolved.DeclarationId} {before after : Context} {evidence : Dynamic.EvidenceEnvironment}
    (extension : ContextExtends owner before after) (covers : evidence.Covers before) : evidence.Covers after := by
  obtain ⟨binders, extension⟩ := extension
  exact covers.transportBinders extension

end ContextExtends

inductive Result (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (resultType : Core.Ty)
    (continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop) (administrativeContext : Core.Context)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) (items : List ForItemForm)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (actual : Core.Environment) (store : Core.Store) (code : Core.Expr) : Prop where
  | continues (tail : TailState administrativeContext continuation)
      (execution : Dynamic.ForItemsExecute program context evidence source environment heap items
        tail.context tail.environment tail.heap)
      (contextExtension : ContextExtends source.owner context tail.context)
      (maps : GeneralHeap.LocationMap.Extends mapping tail.mapping)
      (worlds : Core.WorldExtends world tail.world)
      (frame : GeneralHeap.AdministrativePreserved mapping store tail.mapping tail.store)
      (agreement : ContinuationAgreement actual store code tail.actual tail.store (tail.code.rename tail.embedding)) :
      Result program context evidence source reasonAt resultType continuation administrativeContext environment heap items mapping world actual store code
  | fault {finalContext reason word after finalMap finalWorld finalStore}
      (fault : Dynamic.ForItemsFault program context evidence source environment heap items finalContext reason after)
      (related : Internal.FaultRepresents program evidence source reasonAt reason word)
      (heaps : GeneralHeap.HeapRepresents finalMap finalWorld after finalStore)
      (maps : GeneralHeap.LocationMap.Extends mapping finalMap)
      (worlds : Core.WorldExtends world finalWorld)
      (frame : GeneralHeap.AdministrativePreserved mapping store finalMap finalStore)
      (evaluation : Core.Evaluates actual store code (.inLeft (Core.LocalLoop.controlType resultType) (.word word)) finalStore) :
      Result program context evidence source reasonAt resultType continuation administrativeContext environment heap items mapping world actual store code

theorem Result.prepend
    {program : Program} {context middleContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {resultType : Core.Ty}
    {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop} {administrativeContext : Core.Context}
    {environment middleEnvironment : Dynamic.Environment} {heap middleHeap : Dynamic.Heap}
    {item : ForItemForm} {items : List ForItemForm} {mapping middleMap : GeneralHeap.LocationMap}
    {world middleWorld : Core.StoreTyping} {actual middleActual : Core.Environment}
    {store middleStore : Core.Store} {code middleCode : Core.Expr}
    (head : Dynamic.ForItemExecutes program context evidence source environment heap item middleContext middleEnvironment middleHeap)
    (contextExtension : ContextExtends source.owner context middleContext)
    (maps : GeneralHeap.LocationMap.Extends mapping middleMap) (worlds : Core.WorldExtends world middleWorld)
    (frame : GeneralHeap.AdministrativePreserved mapping store middleMap middleStore)
    (agreement : ContinuationAgreement actual store code middleActual middleStore middleCode)
    (tail : Result program middleContext evidence source reasonAt resultType continuation administrativeContext
      middleEnvironment middleHeap items middleMap middleWorld middleActual middleStore middleCode) :
    Result program context evidence source reasonAt resultType continuation administrativeContext
      environment heap (item :: items) mapping world actual store code := by
  cases tail with
  | continues tail execution tailContext futureMaps futureWorlds futureFrame futureAgreement =>
    exact .continues tail (.cons head execution) (contextExtension.trans tailContext) (maps.trans futureMaps) (worlds.trans futureWorlds)
      (frame.trans futureFrame) (agreement.trans futureAgreement)
  | fault fault related heaps futureMaps futureWorlds futureFrame evaluated =>
    exact .fault (.tail head fault) related heaps (maps.trans futureMaps) (worlds.trans futureWorlds)
      (frame.trans futureFrame) (agreement.wrap evaluated)

end Solcore.SourceSemantics.CoreLowering.ForHeaders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForHeaderConstruction
/-! A certified finite default header constructs its independent source
prefix execution or specified fault. Successful prefixes retain a two-way
agreement around the unevaluated static continuation, including exact lexical
binder insertion and mapped source/Core allocations and writes. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements CoreProof
open LoopStatements Reflection

private theorem valid_extend
    {compilation : SourceCorePrimitive.Context} {owner : Resolved.DeclarationId}
    {context middle : Context} {binder : TypedBinder}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (extension : BinderExtends owner context binder middle) :
    PrimitiveExpressions.ContextValid compilation middle := by
  cases extension
  exact ⟨valid.ledger, valid.valid.transport rfl rfl rfl⟩

private theorem cellsWrite_set {cells : List Dynamic.Cell} {index : Nat}
    {previous : Dynamic.Cell} (selected : Dynamic.Heap.CellAt cells index previous)
    (replacement : Dynamic.Cell) :
    Dynamic.Heap.CellsWrite cells index replacement (cells.set index replacement) := by
  induction selected with
  | head => exact .head
  | tail _ ih => exact .tail ih

/-- Basic expression RHS evaluation leaves its heap unchanged. The captured
source location and independently mapped Core location identify the same cell. -/
private theorem equal_assignment
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap : Dynamic.Heap} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    {target : PlaceResolution} {rhs : ExpressionId} {index : Nat} {payloadType : Core.Ty}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (slot : SourceCoreLocalCell.lookup? scope target.root = some (index, payloadType))
    (bare : target.projections = []) (value : SourceStagedValue.Value)
    (valueType : SourceStagedValue.coreType value = payloadType)
    (rhsEvaluated : Dynamic.ExpressionEvaluates program context evidence source environment
      heap rhs (StagedValue.toSource value) heap) :
    ∃ (coreLocation : Core.Location) (after : Dynamic.Heap) (finalStore : Core.Store),
      Dynamic.SourcePlaceAssignment program context evidence source
        (Dynamic.AssignmentValueApplies .equal) environment heap target rhs (StagedValue.toSource value) after ∧
      coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payloadType) coreLocation) ∧
      (∃ oldValue, store.read? coreLocation = some oldValue) ∧
      store.write? coreLocation (.inRight .unit (SourceStagedValue.toCore value)) = some finalStore ∧
      GeneralHeap.HeapRepresents mapping world after finalStore ∧
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment ∧
      GeneralHeap.AdministrativePreserved mapping store mapping finalStore := by
  obtain ⟨location, coreLocation, cell, stored, lookup, coreLookup, reference, read, coreRead, represented⟩ :=
    environments.lookup_heap heaps slot
  let replacement : Dynamic.Cell := { cell with value := some (StagedValue.toSource value) }
  let after : Dynamic.Heap := ⟨heap.cells.set location.index replacement⟩
  have sourceWrite : Dynamic.Heap.Writes heap location (some (StagedValue.toSource value)) after := by
    cases read with
    | intro selected => exact .intro (.intro selected) (cellsWrite_set selected replacement)
  obtain ⟨finalStore, written, heapRelated⟩ := heaps.write_initialized reference value valueType sourceWrite
  let captured : Dynamic.ResolvedPlace := {
    location, rootType := cell.type, valueType := target.type, projections := [], selected := cell.value
  }
  have resolved : Dynamic.SourcePlaceResolves program context evidence source environment heap target captured heap := by
    apply Dynamic.SourcePlaceResolves.intro lookup read
    · rw [bare]; exact .nil
    · exact read
    · exact represented.rootInitialValue
    · exact .nil
  exact ⟨coreLocation, after, finalStore,
    .intro resolved rhsEvaluated
      (.intro read rfl represented.rootInitialValue (.leaf (.equal cell.value (StagedValue.toSource value))) sourceWrite),
    coreLookup, ⟨stored, coreRead⟩, written, heapRelated, environments,
    GeneralHeap.AdministrativePreserved.write (List.mem_of_getElem? reference.mapped) written⟩



theorem Tree.construct
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {resultType : Core.Ty} {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {code : Core.Expr}
    (tree : Tree compilation source reasonAt resultType continuation scope context items code)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store : Core.Store}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ) :
    Result program context evidence source reasonAt resultType continuation administrativeContext
      environment heap items mapping world actual store (code.rename ξ) := by
  induction tree generalizing mapping world administrativeContext environment canonical actual actualContext ξ heap store with
  | nil next =>
    exact .continues {
      scope := _, context := _, environment := environment, heap := heap, mapping := mapping,
      world := world, canonical := canonical, actual := actual, actualContext := actualContext,
      embedding := ξ, store := store, code := _, certificate := next,
      environments := environments, heaps := heaps, layout := layout }
      .nil (.refl _ _) (.refl _) (.refl _) (.refl _ _) (.refl _ _ _)
  | @letUninitialized scope context middleContext binder rest payload body binding extension tail ih =>
    have allocated : Dynamic.Heap.Allocates heap binder.scheme.body none
        ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := none }]⟩ := .append
    obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
    have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
    have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
      rw [← heaps.runtime_hasTypes.length_eq]; simp
    have nextLayout := (layout.extend worlds).bind (Core.RuntimeValueHasType.cellRef found)
    apply Result.prepend (.letUninitialized binding.monomorphic extension allocated) (.binder extension)
      (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩) worlds
      (GeneralHeap.AdministrativePreserved.allocate mapping store (.inLeft payload .unit))
      (tail := ih (valid_extend valid extension) nextEnvironments nextHeaps nextLayout)
    rw [Core.LoopRenaming.letUninitialized]
    simpa only [Core.LocalSequence.letUninitialized, Core.Store.allocate] using
      (ContinuationAgreement.letE (body := body.rename ξ.lift) (Core.OptionalCell.allocate_evaluates payload actual store))
  | @letInitialized scope context middleContext binder rest payload initializer initializerCode body depth binding extension valueTree tail ih =>
    obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
    cases related with
    | value staged typed =>
      cases sourceEval with
      | value sourceEval =>
        have allocated : Dynamic.Heap.Allocates heap binder.scheme.body (some (StagedValue.toSource staged))
            ⟨heap.cells.length⟩ ⟨heap.cells ++ [{ type := binder.scheme.body, value := some (StagedValue.toSource staged) }]⟩ := .append
        have sameSource : binder.scheme.body = SourceStagedValue.sourceType staged := binding.types.source_unique (typed ▸ stagedTypes staged)
        have cell : CellRepresents {type := binder.scheme.body, value := some (StagedValue.toSource staged)}
            (.inRight .unit (SourceStagedValue.toCore staged)) payload := by
          rw [sameSource, ← typed]; exact .initialized staged
        obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
        have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
        have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
          rw [← heaps.runtime_hasTypes.length_eq]; simp
        have nextLayout := ((layout.extend worlds).insert (stagedTyped staged _)).bind (Core.RuntimeValueHasType.cellRef found)
        have restResult := ih (valid_extend valid extension) nextEnvironments nextHeaps nextLayout
        simp only [rename_insert_lift] at restResult
        apply Result.prepend (.letInitialized sourceEval binding.monomorphic extension allocated) (.binder extension)
          (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩) worlds
          (GeneralHeap.AdministrativePreserved.allocate mapping store (.inRight .unit (SourceStagedValue.toCore staged)))
          (tail := restResult)
        simp only [Core.LoopRenaming.letInitialized]
        exact (ContinuationAgreement.bind coreEval).trans
          (ContinuationAgreement.letE (Core.OptionalCell.allocateInitialized_evaluates (.var rfl)))
    | uninitialized site location origin =>
      cases sourceEval with
      | fault sourceFault =>
        apply Result.fault (.head (.letInitializer binding.monomorphic sourceFault))
          (.uninitialized site location origin) heaps (.refl _) (.refl _) (.refl _ _)
        simpa only [Core.LoopRenaming.letInitialized] using
          Core.LocalSequence.letInitialized_failure (Core.LocalLoop.controlType resultType) payload coreEval
  | @discard scope context expression expressionType expressionCode rest body depth valueTree tail ih =>
    obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
    cases related with
    | value staged typed =>
      cases sourceEval with
      | value sourceEval =>
        have restResult := ih valid environments heaps (layout.insert (stagedTyped staged world))
        simp only [rename_insert] at restResult
        apply Result.prepend (.expression sourceEval) (.refl _ _) (.refl _) (.refl _) (.refl _ _) (tail := restResult)
        rw [Core.LoopRenaming.discard]
        simpa only [Core.LocalSequence.discard] using
          (ContinuationAgreement.bind (type := Core.LocalLoop.controlType resultType)
            (body := (body.rename ξ).weakenAt 0) coreEval)
    | uninitialized site location origin =>
      cases sourceEval with
      | fault sourceFault =>
        apply Result.fault (.head (.expression sourceFault)) (.uninitialized site location origin) heaps (.refl _) (.refl _) (.refl _ _)
        simpa only [Core.LoopRenaming.discard] using
          Core.LocalSequence.discard_failure (Core.LocalLoop.controlType resultType) coreEval
  | @assign scope context assignment index payload rhs rhsCode rest body depth target valueTree tail ih =>
    obtain ⟨valueOutcome, valueResult, sourceEval, related, coreEval⟩ := expression_meaning valueTree program context evidence valid environments heaps layout
    cases related with
    | value staged typed =>
      cases sourceEval with
      | value sourceEval =>
        obtain ⟨location, afterWrite, writtenStore, assigned, lookup, ⟨old, readable⟩, written,
          updatedHeaps, updatedEnvironments, writeFrame⟩ := equal_assignment environments heaps target.slot target.bare staged typed sourceEval
        have actualLookup := layout.agrees lookup
        have referenceTyped : Core.RuntimeValueHasType world
            (.cellRef (Core.OptionalCell.cellType payload) location) (Core.OptionalCell.referenceType payload) := by
          obtain ⟨found, foundEq, foundTyped⟩ := Core.RuntimeEnvironmentHasTypes.lookup layout.typed
            (layout.respects (SourceCoreLocalCell.lookup?_context target.slot))
          rw [actualLookup] at foundEq
          cases foundEq
          exact foundTyped
        have nextLayout := ((layout.insert referenceTyped).insert (stagedTyped staged world)).insert Core.RuntimeValueHasType.unit
        have restResult := ih valid updatedEnvironments updatedHeaps nextLayout
        simp only [rename_insert] at restResult
        apply Result.prepend (.assignValue assigned) (.refl _ _) (.refl _) (.refl _) writeFrame (tail := restResult)
        simp only [Core.LoopRenaming.assign]
        refine (ContinuationAgreement.letE (Core.Evaluates.var actualLookup)).trans ?_
        refine (ContinuationAgreement.bind
          (((GeneralExpressions.Primitive.readOnly valueTree).rename ξ).evaluation_weakenAt_zero coreEval _)).trans ?_
        exact ContinuationAgreement.letE (.storeCell (.var rfl) readable (.inRight (.var rfl)) written)
    | uninitialized site location origin =>
      cases sourceEval with
      | fault sourceFault =>
        obtain ⟨sourceLocation, coreLocation, cell, stored, lookup, coreLookup, reference, read, coreRead, represented⟩ :=
          environments.lookup_heap heaps target.slot
        let captured : Dynamic.ResolvedPlace := {
          location := sourceLocation, rootType := cell.type, valueType := assignment.target.type,
          projections := [], selected := cell.value
        }
        have resolved : Dynamic.SourcePlaceResolves program context evidence source environment heap assignment.target captured heap := by
          apply Dynamic.SourcePlaceResolves.intro lookup read
          · rw [target.bare]; exact .nil
          · exact read
          · exact represented.rootInitialValue
          · exact .nil
        apply Result.fault (.head (.assignValue (.rhs resolved sourceFault))) (.uninitialized site location origin)
          heaps (.refl _) (.refl _) (.refl _ _)
        simpa only [Core.LoopRenaming.assign, Core.Expr.rename] using
          Core.LocalSequence.assign_failure (Core.LocalLoop.controlType resultType)
            (Core.Evaluates.var (layout.agrees coreLookup))
            (((GeneralExpressions.Primitive.readOnly valueTree).rename ξ).evaluation_weakenAt_zero coreEval _)

end Solcore.SourceSemantics.CoreLowering.ForHeaders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForPostMeaning
/-! A certified post vector finishes or raises its specified scalar read
fault. Its final lexical bindings are recorded in independent source semantics
and can be discarded when the next loop iteration restores its captured scope. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell CoreProof LoopStatements

inductive PostMeaning (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (items : List ForItemForm) (type : Core.Ty) :
    Context → Dynamic.ControlOutcome → Dynamic.Heap → Core.Value → Prop where
  | success {finalContext finalEnvironment after}
      (execution : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
      PostMeaning program context evidence source reasonAt environment before items type finalContext
        (.fallthrough finalEnvironment) after (Core.LocalLoop.fallthroughValue type)
  | fault {finalContext reason word after}
      (fault : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after)
      (related : Internal.FaultRepresents program evidence source reasonAt reason word) :
      PostMeaning program context evidence source reasonAt environment before items type finalContext
        (.fault reason) after (.inLeft (Core.LocalLoop.controlType type) (.word word))

def PostResult (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (items : List ForItemForm) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (actual : Core.Environment) (store : Core.Store) (code : Core.Expr) : Prop :=
  ∃ finalContext outcome after result finalStore finalMap finalWorld,
    PostMeaning program context evidence source reasonAt environment before items type finalContext outcome after result ∧
    Core.Evaluates actual store code result finalStore ∧
    GeneralHeap.HeapRepresents finalMap finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMap finalStore

theorem Tree.construct_post
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {resultType : Core.Ty} {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {code : Core.Expr}
    (tree : Tree compilation source reasonAt resultType (Fallthrough resultType) scope context items code)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store : Core.Store}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ) :
    PostResult program context evidence source reasonAt environment heap items resultType mapping world actual store (code.rename ξ) := by
  have constructed := tree.construct program evidence valid environments heaps layout
  cases constructed with
  | continues tail execution _ maps worlds frame agreement =>
    have endpoint : tail.code = Core.LocalLoop.fallthrough resultType := tail.certificate
    have completed : Core.Evaluates tail.actual tail.store (tail.code.rename tail.embedding)
        (Core.LocalLoop.fallthroughValue resultType) tail.store := by
      rw [endpoint, Core.LoopRenaming.fallthrough]
      exact Core.LocalLoop.fallthrough_evaluates _ _ _
    exact ⟨tail.context, _, tail.heap, _, tail.store, tail.mapping, tail.world,
      .success execution, agreement.wrap completed, tail.heaps, maps, worlds, frame⟩
  | @fault finalContext reason word after finalMap finalWorld finalStore fault related heaps maps worlds frame evaluation =>
    exact ⟨finalContext, _, after, _, finalStore, finalMap, finalWorld,
      .fault fault related, evaluation, heaps, maps, worlds, frame⟩

end Solcore.SourceSemantics.CoreLowering.ForHeaders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForLoopReflectionInterfaces
/-! Internal proof contracts for finite for iteration reflection. The body
contract is discharged by statement-tree induction; the post contract below
is constructed directly from its static header tree. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof

inductive ForMeaning (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty) :
    Context → Dynamic.ControlOutcome → Dynamic.Heap → Core.Value → Prop where
  | control {finalContext outcome after result}
      (execution : Dynamic.ForLoopExecutes program context evidence source environment before condition post statements finalContext outcome after)
      (related : ControlRepresents type outcome result) :
      ForMeaning program context evidence source reasonAt environment before condition post statements type finalContext outcome after result
  | fault {reason after word}
      (fault : Dynamic.ForLoopFaults program context evidence source environment before condition post statements reason after)
      (related : FaultRepresents program evidence source reasonAt reason word) :
      ForMeaning program context evidence source reasonAt environment before condition post statements type context (.fault reason) after
        (.inLeft (Core.LocalLoop.controlType type) (.word word))

def ForResult (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (result : Core.Value) (finalStore : Core.Store) : Prop :=
  ∃ finalContext outcome after finalMapping finalWorld,
    ForMeaning program context evidence source reasonAt environment before condition post statements type finalContext outcome after result ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

def PostConstructs (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word)
    (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context)
    (environment : Dynamic.Environment) (canonical actual : Core.Environment) (actualContext : Core.Context)
    (type : Core.Ty) (location : Core.Location) (items : List ForItemForm) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap} {store : Core.Store},
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Core.RuntimeEnvironmentHasTypes world actual actualContext →
    world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
    ∀ continued : Bool,
      ForHeaders.PostResult program context evidence source reasonAt environment heap items type mapping world
        ((if continued then ForLoop.continuingPrefix type else ForLoop.fallthroughPrefix type) ++
          Core.LoopExecution.entryEnvironment type location actual) store (ForLoop.postCode code)

theorem post_constructs
    {compilation : SourceCorePrimitive.Context} {program : Program} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {type : Core.Ty} {location : Core.Location} {items : List ForItemForm} {code : Core.Expr} {ξ : Core.Renaming}
    (tree : ForHeaders.Tree compilation source reasonAt type (ForHeaders.Fallthrough type) scope context items code)
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (respects : Core.Renaming.Respects ξ (SourceCoreLocalCell.coreContext scope) actualContext)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual) :
    PostConstructs program context evidence source reasonAt scope administrativeContext environment canonical actual actualContext
      type location items (code.rename ξ) := by
  intro mapping world heap store environments heaps actualTyped locationTyped continued
  have layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ := ⟨respects, agree, actualTyped⟩
  have entry := ((layout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert Core.RuntimeValueHasType.unit).insert
    (Core.RuntimeValueHasType.bool (value := true))
  cases continued with
  | false =>
    have shifted := ((entry.insert (Core.RuntimeValueHasType.inLeft (rightType := Core.LocalLoop.transferType)
      (Core.RuntimeValueHasType.inLeft (rightType := type) .unit))).insert
      (Core.RuntimeValueHasType.inLeft (rightType := type) .unit)).insert Core.RuntimeValueHasType.unit
    have result := tree.construct_post program evidence valid environments heaps shifted
    simpa only [ForLoop.postCode_eq, rename_insert, ForLoop.fallthroughPrefix, Core.LoopExecution.entryEnvironment,
      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] using result
  | true =>
    have shifted := ((entry.insert (Core.RuntimeValueHasType.inRight (leftType := Core.LocalControl.controlType type)
      (Core.RuntimeValueHasType.inRight (leftType := .unit) .unit))).insert
      (Core.RuntimeValueHasType.inRight (leftType := .unit) .unit)).insert Core.RuntimeValueHasType.unit
    have result := tree.construct_post program evidence valid environments heaps shifted
    simpa only [ForLoop.postCode_eq, rename_insert, ForLoop.continuingPrefix, Core.LoopExecution.entryEnvironment,
      ↓reduceIte, List.cons_append, List.nil_append] using result

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForFiniteReflection
/-! Reconstruct a finite independent for execution from a finite execution
of its installed Core closure. Body reflection is the structural child-tree
induction hypothesis; the next iteration is proved by decreasing Core
execution size, never assumed as an external source execution. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof
open Core.LoopExecution

private theorem self_retained
    {mapping futureMapping : GeneralHeap.LocationMap} {before after : Core.Store}
    {location : Core.Location} {value : Core.Value}
    (unmapped : location ∉ mapping) (read : before.read? location = some value)
    (frame : GeneralHeap.AdministrativePreserved mapping before futureMapping after) :
    location ∉ futureMapping ∧ after.read? location = some value := by
  have bounded : location < before.length := (List.getElem?_eq_some_iff.mp read).1
  obtain ⟨unmapped, same⟩ := frame location unmapped bounded
  exact ⟨unmapped, same.trans read⟩

private theorem for_context
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {outcome : Dynamic.ControlOutcome}
    (execution : Dynamic.ForLoopExecutes program context evidence source environment before condition post statements finalContext outcome after) :
    finalContext = context := by cases execution <;> rfl

/-- The static condition constructs its source execution without any source
trace premise. The body contract is discharged by the statement-tree theorem. -/
theorem for_reflect
    {compilation : SourceCorePrimitive.Context} {program : Program} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {condition : ExpressionId} {conditionCode : Core.Expr} {conditionDepth : Nat}
    {post : List ForItemForm} {postBody : Core.Expr} {statements : List StatementId} {body : Core.Expr} {type : Core.Ty} {selfReason : Core.Word} {location : Core.Location}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {administrativeContext : Core.Context}
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth)
    (valid : PrimitiveExpressions.ContextValid compilation context)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual)
    (bodyCorrect : BodyReflects program context evidence source reasonAt scope administrativeContext
      environment canonical actual actualContext type location statements body)
    (postCorrect : PostConstructs program context evidence source reasonAt scope administrativeContext
      environment canonical actual actualContext type location post postBody) :
    ∀ (size : Nat) {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {heap : Dynamic.Heap}
      {store finalStore : Core.Store} {result : Core.Value},
      GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
      GeneralHeap.HeapRepresents mapping world heap store →
      Core.RuntimeEnvironmentHasTypes world actual actualContext →
      world[location]? = some (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) →
      location ∉ mapping →
      store.read? location = some (.inRight .unit
        (Core.LocalLoop.installedClosure type (conditionCode.rename ξ) body postBody selfReason location actual)) →
      EvaluationSize size (entryEnvironment type location actual) store
        (Core.LocalLoop.loopBody type (conditionCode.rename ξ) body postBody selfReason) result finalStore →
      ForResult program context evidence source reasonAt environment heap condition post statements type mapping world store result finalStore := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro mapping world heap store finalStore result environments heaps actualTyped locationTyped unmapped installed evaluation
    obtain ⟨conditionOutcome, conditionValue, conditionSource, related, conditionCore⟩ :=
      GeneralExpressions.Primitive.preserves conditionTree program context evidence valid environments heaps
    have restricted := GeneralExpressions.Primitive.readOnly conditionTree
    have renamed := restricted.evaluation_rename conditionCore agree
    have first := (restricted.rename ξ).evaluation_weakenAt_zero renamed
      (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) location)
    have shifted := ((restricted.rename ξ).weakenAt 0).evaluation_weakenAt_zero first .unit
    cases related with
    | uninitialized site faultLocation origin =>
      cases conditionSource with
      | fault sourceFault =>
        obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure shifted)
        exact ⟨context, _, heap, mapping, world,
          .fault (.condition sourceFault) (.uninitialized site faultLocation origin), heaps, .refl _, .refl _, .refl _ _⟩
    | value staged typed =>
      obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
      cases conditionSource with
      | value sourceCondition =>
        cases boolean with
        | false =>
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false shifted)
          exact ⟨context, _, heap, mapping, world,
            .control (.done sourceCondition) (.fallthrough environment), heaps, .refl _, .refl _, .refl _ _⟩
        | true =>
          obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch shifted
          obtain ⟨bodySize, bodyStore, bodyValue, _, bodyEvaluation⟩ := branch.bind_computation
          obtain ⟨bodyContext, bodyOutcome, bodyHeap, bodyMapping, bodyWorld, bodyMeaning,
            bodyHeaps, maps, worlds, frame⟩ :=
            bodyCorrect environments heaps actualTyped locationTyped bodyEvaluation.sound
          cases bodyMeaning with
          | fault sourceFault related =>
            obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound
              (Core.LoopExecution.body_failure shifted bodyEvaluation.sound)
            exact ⟨context, _, bodyHeap, bodyMapping, bodyWorld,
              .fault (.body sourceCondition sourceFault) related, bodyHeaps, maps, worlds, frame⟩
          | control sourceBody related =>
            cases related with
            | returned staged typed =>
              obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_returned shifted bodyEvaluation.sound)
              exact ⟨context, _, bodyHeap, bodyMapping, bodyWorld,
                .control (.returns sourceCondition sourceBody) (.returned staged typed), bodyHeaps, maps, worlds, frame⟩
            | breaking bodyEnvironment =>
              obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound
                (Core.LoopExecution.body_breaking shifted bodyEvaluation.sound)
              exact ⟨context, _, bodyHeap, bodyMapping, bodyWorld,
                .control (.breaks sourceCondition sourceBody) (.fallthrough environment), bodyHeaps, maps, worlds, frame⟩
            | fallthrough bodyEnvironment =>
              obtain ⟨postContext, postOutcome, postHeap, postValue, postStore, postMap, postWorld,
                postMeaning, postEvaluation, postHeaps, postMaps, postWorlds, postFrame⟩ :=
                postCorrect (environments.extend maps worlds) bodyHeaps
                  (Core.RuntimeEnvironmentHasTypes.weaken worlds actualTyped) (worlds.lookup locationTyped) false
              cases postMeaning with
              | fault postFault postRelated =>
                obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound
                  (ForLoop.body_fallthrough_post_fault shifted bodyEvaluation.sound postEvaluation)
                exact ⟨context, _, postHeap, postMap, postWorld,
                  .fault (.postFallthrough sourceCondition sourceBody postFault) postRelated,
                  postHeaps, maps.trans postMaps, worlds.trans postWorlds, frame.trans postFrame⟩
              | success sourcePost =>
                obtain ⟨unmappedAgain, installedAgain⟩ := self_retained unmapped installed (frame.trans postFrame)
                obtain ⟨nextSize, nextSmaller, nextEvaluation⟩ :=
                  ForLoop.next_fallthrough branch bodyEvaluation.sound postEvaluation installedAgain
                obtain ⟨nextContext, nextOutcome, after, finalMapping, finalWorld, nextMeaning,
                  finalHeaps, mapsAgain, worldsAgain, frameAgain⟩ :=
                  ih nextSize (Nat.lt_trans nextSmaller branchSmaller)
                    (environments.extend (maps.trans postMaps) (worlds.trans postWorlds)) postHeaps
                    (Core.RuntimeEnvironmentHasTypes.weaken (worlds.trans postWorlds) actualTyped)
                    ((worlds.trans postWorlds).lookup locationTyped) unmappedAgain installedAgain nextEvaluation
                cases nextMeaning with
                | control nextSource nextRelated =>
                  have sameContext := for_context nextSource
                  subst nextContext
                  exact ⟨context, _, after, finalMapping, finalWorld,
                    .control (.nextFallthrough sourceCondition sourceBody sourcePost nextSource) nextRelated,
                    finalHeaps, (maps.trans postMaps).trans mapsAgain,
                    (worlds.trans postWorlds).trans worldsAgain, (frame.trans postFrame).trans frameAgain⟩
                | fault nextFault nextRelated =>
                  exact ⟨context, _, after, finalMapping, finalWorld,
                    .fault (.nextFallthrough sourceCondition sourceBody sourcePost nextFault) nextRelated,
                    finalHeaps, (maps.trans postMaps).trans mapsAgain,
                    (worlds.trans postWorlds).trans worldsAgain, (frame.trans postFrame).trans frameAgain⟩
            | continuing bodyEnvironment =>
              obtain ⟨postContext, postOutcome, postHeap, postValue, postStore, postMap, postWorld,
                postMeaning, postEvaluation, postHeaps, postMaps, postWorlds, postFrame⟩ :=
                postCorrect (environments.extend maps worlds) bodyHeaps
                  (Core.RuntimeEnvironmentHasTypes.weaken worlds actualTyped) (worlds.lookup locationTyped) true
              cases postMeaning with
              | fault postFault postRelated =>
                obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluation.sound
                  (ForLoop.body_continuing_post_fault shifted bodyEvaluation.sound postEvaluation)
                exact ⟨context, _, postHeap, postMap, postWorld,
                  .fault (.postContinue sourceCondition sourceBody postFault) postRelated,
                  postHeaps, maps.trans postMaps, worlds.trans postWorlds, frame.trans postFrame⟩
              | success sourcePost =>
                obtain ⟨unmappedAgain, installedAgain⟩ := self_retained unmapped installed (frame.trans postFrame)
                obtain ⟨nextSize, nextSmaller, nextEvaluation⟩ :=
                  ForLoop.next_continuing branch bodyEvaluation.sound postEvaluation installedAgain
                obtain ⟨nextContext, nextOutcome, after, finalMapping, finalWorld, nextMeaning,
                  finalHeaps, mapsAgain, worldsAgain, frameAgain⟩ :=
                  ih nextSize (Nat.lt_trans nextSmaller branchSmaller)
                    (environments.extend (maps.trans postMaps) (worlds.trans postWorlds)) postHeaps
                    (Core.RuntimeEnvironmentHasTypes.weaken (worlds.trans postWorlds) actualTyped)
                    ((worlds.trans postWorlds).lookup locationTyped) unmappedAgain installedAgain nextEvaluation
                cases nextMeaning with
                | control nextSource nextRelated =>
                  have sameContext := for_context nextSource
                  subst nextContext
                  exact ⟨context, _, after, finalMapping, finalWorld,
                    .control (.nextContinue sourceCondition sourceBody sourcePost nextSource) nextRelated,
                    finalHeaps, (maps.trans postMaps).trans mapsAgain,
                    (worlds.trans postWorlds).trans worldsAgain, (frame.trans postFrame).trans frameAgain⟩
                | fault nextFault nextRelated =>
                  exact ⟨context, _, after, finalMapping, finalWorld,
                    .fault (.nextContinue sourceCondition sourceBody sourcePost nextFault) nextRelated,
                    finalHeaps, (maps.trans postMaps).trans mapsAgain,
                    (worlds.trans postWorlds).trans worldsAgain, (frame.trans postFrame).trans frameAgain⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForHeaderSuccess
/-! A supplied independent successful header derivation reaches a related
static continuation. Exact source context, environment and heap are retained,
so a later loop proof may use the supplied source trace without assuming that
it coincides with a separately constructed trace. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements CoreProof
open LoopStatements Reflection

def SuccessResult (continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop)
    (administrativeContext : Core.Context) (finalContext : Context) (finalEnvironment : Dynamic.Environment)
    (after : Dynamic.Heap) (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (actual : Core.Environment) (store : Core.Store) (code : Core.Expr) : Prop :=
  ∃ tail : TailState administrativeContext continuation,
    tail.context = finalContext ∧ tail.environment = finalEnvironment ∧ tail.heap = after ∧
    GeneralHeap.LocationMap.Extends mapping tail.mapping ∧ Core.WorldExtends world tail.world ∧
    GeneralHeap.AdministrativePreserved mapping store tail.mapping tail.store ∧
    ContinuationAgreement actual store code tail.actual tail.store (tail.code.rename tail.embedding)

theorem SuccessResult.prepend
    {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    {administrativeContext : Core.Context} {finalContext : Context} {finalEnvironment : Dynamic.Environment}
    {after : Dynamic.Heap} {mapping middleMap : GeneralHeap.LocationMap} {world middleWorld : Core.StoreTyping}
    {actual middleActual : Core.Environment} {store middleStore : Core.Store} {code middleCode : Core.Expr}
    (maps : GeneralHeap.LocationMap.Extends mapping middleMap) (worlds : Core.WorldExtends world middleWorld)
    (frame : GeneralHeap.AdministrativePreserved mapping store middleMap middleStore)
    (agreement : ContinuationAgreement actual store code middleActual middleStore middleCode)
    (tail : SuccessResult continuation administrativeContext finalContext finalEnvironment after
      middleMap middleWorld middleActual middleStore middleCode) :
    SuccessResult continuation administrativeContext finalContext finalEnvironment after mapping world actual store code := by
  obtain ⟨tail, contextEq, environmentEq, heapEq, moreMaps, moreWorlds, moreFrame, moreAgreement⟩ := tail
  exact ⟨tail, contextEq, environmentEq, heapEq, maps.trans moreMaps, worlds.trans moreWorlds,
    frame.trans moreFrame, agreement.trans moreAgreement⟩

private theorem expression_success
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {id : ExpressionId} {type : Core.Ty} {code : Core.Expr} {depth : Nat}
    (tree : PrimitiveExpressions.Tree compilation source scope reasonAt id type code depth)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap after : Dynamic.Heap} {store : Core.Store} {value : Dynamic.Value}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ)
    (executed : Dynamic.ExpressionEvaluates program context evidence source environment heap id value after) :
    after = heap ∧ ∃ staged : SourceStagedValue.Value,
      value = StagedValue.toSource staged ∧ SourceStagedValue.coreType staged = type ∧
      Core.Evaluates actual store (code.rename ξ) (.inRight .word (SourceStagedValue.toCore staged)) store := by
  obtain ⟨rfl, staged, same, typed, evaluated⟩ :=
    ScalarExpressionReflection.Primitive.source_success tree unique environments heaps executed
  exact ⟨rfl, staged, same, typed, (GeneralExpressions.Primitive.readOnly tree).evaluation_rename evaluated layout.agrees⟩

theorem Tree.source_success
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {resultType : Core.Ty} {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {code : Core.Expr}
    (tree : Tree compilation source reasonAt resultType continuation scope context items code)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap after : Dynamic.Heap} {store : Core.Store} {finalContext : Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ)
    (executed : Dynamic.ForItemsExecute program context evidence source environment heap items finalContext finalEnvironment after) :
    SuccessResult continuation administrativeContext finalContext finalEnvironment after mapping world actual store (code.rename ξ) := by
  induction tree generalizing mapping world administrativeContext environment finalEnvironment canonical actual actualContext ξ heap after store finalContext with
  | nil next =>
    cases executed
    exact ⟨{
      scope := _, context := _, environment := environment, heap := heap, mapping := mapping,
      world := world, canonical := canonical, actual := actual, actualContext := actualContext,
      embedding := ξ, store := store, code := _, certificate := next,
      environments := environments, heaps := heaps, layout := layout },
      rfl, rfl, rfl, .refl _, .refl _, .refl _ _, .refl _ _ _⟩
  | @letUninitialized scope context middleContext binder rest payload body binding extension tail ih =>
    cases executed with
    | cons head remaining =>
      cases head with
      | letUninitialized _ otherExtension allocated =>
        have sameContext := Dynamic.BinderExtends.functional otherExtension extension
        subst_vars
        obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps (.uninitialized binding.types) allocated
        have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
        have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
          rw [← heaps.runtime_hasTypes.length_eq]; simp
        have nextLayout := (layout.extend worlds).bind (Core.RuntimeValueHasType.cellRef found)
        apply SuccessResult.prepend (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩) worlds
          (GeneralHeap.AdministrativePreserved.allocate mapping store (.inLeft payload .unit))
          (tail := ih nextEnvironments nextHeaps nextLayout remaining)
        rw [Core.LoopRenaming.letUninitialized]
        simpa only [Core.LocalSequence.letUninitialized, Core.Store.allocate] using
          (ContinuationAgreement.letE (body := body.rename ξ.lift) (Core.OptionalCell.allocate_evaluates payload actual store))
  | @letInitialized scope context middleContext binder rest payload initializer initializerCode body depth binding extension valueTree tail ih =>
    cases executed with
    | cons head remaining =>
      cases head with
      | letInitialized sourceEval _ otherExtension allocated =>
        have sameContext := Dynamic.BinderExtends.functional otherExtension extension
        subst_vars
        obtain ⟨rfl, staged, rfl, typed, coreEval⟩ := expression_success valueTree unique environments heaps layout sourceEval
        have sameSource : binder.scheme.body = SourceStagedValue.sourceType staged := binding.types.source_unique (typed ▸ stagedTypes staged)
        have cell : CellRepresents {type := binder.scheme.body, value := some (StagedValue.toSource staged)}
            (.inRight .unit (SourceStagedValue.toCore staged)) payload := by
          rw [sameSource, ← typed]; exact .initialized staged
        obtain ⟨nextEnvironments, nextHeaps⟩ := environments.bind heaps cell allocated
        have worlds : Core.WorldExtends world (world ++ [Core.OptionalCell.cellType payload]) := ⟨_, rfl⟩
        have found : (world ++ [Core.OptionalCell.cellType payload])[store.length]? = some (Core.OptionalCell.cellType payload) := by
          rw [← heaps.runtime_hasTypes.length_eq]; simp
        have nextLayout := ((layout.extend worlds).insert (stagedTyped staged _)).bind (Core.RuntimeValueHasType.cellRef found)
        have restResult := ih nextEnvironments nextHeaps nextLayout remaining
        simp only [rename_insert_lift] at restResult
        apply SuccessResult.prepend (show GeneralHeap.LocationMap.Extends mapping (mapping ++ [store.length]) from ⟨_, rfl⟩) worlds
          (GeneralHeap.AdministrativePreserved.allocate mapping store (.inRight .unit (SourceStagedValue.toCore staged)))
          (tail := restResult)
        simp only [Core.LoopRenaming.letInitialized]
        exact (ContinuationAgreement.bind coreEval).trans
          (ContinuationAgreement.letE (Core.OptionalCell.allocateInitialized_evaluates (.var rfl)))
      | letInitializedGeneralized _ _ polymorphic _ _ => exact False.elim (polymorphic binding.monomorphic)
  | @discard scope context expression expressionType expressionCode rest body depth valueTree tail ih =>
    cases executed with
    | cons head remaining =>
      cases head with
      | expression sourceEval =>
        obtain ⟨rfl, staged, _, _, coreEval⟩ := expression_success valueTree unique environments heaps layout sourceEval
        have restResult := ih environments heaps (layout.insert (stagedTyped staged world)) remaining
        simp only [rename_insert] at restResult
        apply SuccessResult.prepend (.refl _) (.refl _) (.refl _ _) (tail := restResult)
        rw [Core.LoopRenaming.discard]
        simpa only [Core.LocalSequence.discard] using
          (ContinuationAgreement.bind (type := Core.LocalLoop.controlType resultType)
            (body := (body.rename ξ).weakenAt 0) coreEval)
  | @assign scope context assignment index payload rhs rhsCode rest body depth target valueTree tail ih =>
    cases executed with
    | cons head remaining =>
      cases head with
      | assignValue assigned =>
        obtain ⟨staged, location, writtenStore, _, typed, rhsCore, lookup, ⟨old, readable⟩, written,
          updatedHeaps, writeFrame⟩ := ScalarAssignmentReflection.source_success valueTree unique target.slot target.bare environments heaps assigned
        have actualLookup := layout.agrees lookup
        have referenceTyped : Core.RuntimeValueHasType world
            (.cellRef (Core.OptionalCell.cellType payload) location) (Core.OptionalCell.referenceType payload) := by
          obtain ⟨found, foundEq, foundTyped⟩ := Core.RuntimeEnvironmentHasTypes.lookup layout.typed
            (layout.respects (SourceCoreLocalCell.lookup?_context target.slot))
          rw [actualLookup] at foundEq
          cases foundEq
          exact foundTyped
        have nextLayout := ((layout.insert referenceTyped).insert (stagedTyped staged world)).insert Core.RuntimeValueHasType.unit
        have restResult := ih environments updatedHeaps nextLayout remaining
        simp only [rename_insert] at restResult
        have coreEval := (GeneralExpressions.Primitive.readOnly valueTree).evaluation_rename rhsCore layout.agrees
        apply SuccessResult.prepend (.refl _) (.refl _) writeFrame (tail := restResult)
        simp only [Core.LoopRenaming.assign]
        refine (ContinuationAgreement.letE (Core.Evaluates.var actualLookup)).trans ?_
        refine (ContinuationAgreement.bind
          (((GeneralExpressions.Primitive.readOnly valueTree).rename ξ).evaluation_weakenAt_zero coreEval _)).trans ?_
        exact ContinuationAgreement.letE (.storeCell (.var rfl) readable (.inRight (.var rfl)) written)

end Solcore.SourceSemantics.CoreLowering.ForHeaders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForHeaderFault
/-! Preservation of supplied independent header faults. Successful prefixes
use their source derivations and exact Core continuation agreement; faulting
heads use the independent scalar-expression/assignment fault rules. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ForHeaders

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements CoreProof
open LoopStatements Reflection

private theorem item_context_extends
    {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment finalEnvironment : Dynamic.Environment} {heap after : Dynamic.Heap} {item : ForItemForm}
    (executed : Dynamic.ForItemExecutes program context evidence source environment heap item finalContext finalEnvironment after) :
    ContextExtends source.owner context finalContext := by
  cases executed with
  | letUninitialized _ extension _ | letInitialized _ _ extension _ | letInitializedGeneralized _ _ _ extension _ =>
      exact .binder extension
  | expression | assignValue | assignBitNot => exact .refl _ _

def FaultResult (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (type : Core.Ty)
    (reason : Dynamic.SemanticFault) (after : Dynamic.Heap)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping)
    (actual : Core.Environment) (store : Core.Store) (code : Core.Expr) : Prop :=
  ∃ token finalStore finalMap finalWorld,
    Internal.FaultRepresents program evidence source reasonAt reason token ∧
    Core.Evaluates actual store code (.inLeft (Core.LocalLoop.controlType type) (.word token)) finalStore ∧
    GeneralHeap.HeapRepresents finalMap finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMap finalStore

def Fault (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (type : Core.Ty)
    (scope : SourceCoreLocalCell.Scope) (context : Context) (items : List ForItemForm) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap after : Dynamic.Heap} {store : Core.Store} {finalContext : Context} {reason : Dynamic.SemanticFault},
    PrimitiveExpressions.ContextValid compilation context → evidence.Covers context →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Dynamic.ForItemsFault program context evidence source environment heap items finalContext reason after →
    FaultResult program evidence source reasonAt type reason after mapping world actual store (code.rename ξ)

private theorem fault_after_success
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {type : Core.Ty}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {item : ForItemForm} {rest : List ForItemForm} {code : Core.Expr}
    (header : Tree compilation source reasonAt type
      (fun scope context code => Fault compilation program evidence source reasonAt type scope context rest code)
      scope context [item] code)
    (unique : NodeOccurrencesUnique source)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment middleEnvironment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap middle after : Dynamic.Heap} {store : Core.Store}
    {middleContext finalContext : Context} {reason : Dynamic.SemanticFault}
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ)
    (head : Dynamic.ForItemExecutes program context evidence source environment heap item middleContext middleEnvironment middle)
    (fault : Dynamic.ForItemsFault program middleContext evidence source middleEnvironment middle rest finalContext reason after) :
    FaultResult program evidence source reasonAt type reason after mapping world actual store (code.rename ξ) := by
  obtain ⟨tail, contextEq, environmentEq, heapEq, maps, worlds, frame, agreement⟩ :=
    header.source_success unique program evidence environments heaps layout (.cons head .nil)
  have extension := item_context_extends head
  rw [← contextEq] at extension fault
  rw [← environmentEq, ← heapEq] at fault
  obtain ⟨token, finalStore, finalMap, finalWorld, related, core, finalHeaps, tailMaps, tailWorlds, tailFrame⟩ :=
    tail.certificate (extension.valid valid) (extension.covers covers) tail.environments tail.heaps tail.layout fault
  exact ⟨token, finalStore, finalMap, finalWorld, related, agreement.wrap core, finalHeaps,
    maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame⟩

theorem Tree.source_fault
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {type : Core.Ty} {continuation : SourceCoreLocalCell.Scope → Context → Core.Expr → Prop}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {items : List ForItemForm} {code : Core.Expr}
    (tree : Tree compilation source reasonAt type continuation scope context items code)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    Fault compilation program evidence source reasonAt type scope context items code := by
  induction tree with
  | nil _ =>
    intro mapping world admin env canonical actual actualContext ξ heap after store finalContext reason valid covers environments heaps layout fault
    cases fault
  | letUninitialized binding extension _ ih =>
    intro mapping world admin env canonical actual actualContext ξ heap after store finalContext reason valid covers environments heaps layout fault
    cases fault with
    | head fault =>
      cases fault with
      | polymorphicLet impossible _ => exact False.elim (impossible binding.monomorphic)
    | tail head fault =>
      exact fault_after_success (.letUninitialized binding extension (.nil ih)) unique valid covers environments heaps layout head fault
  | @letInitialized scope context middleContext binder rest payload initializer initializerCode body depth binding extension valueTree tail ih =>
    intro mapping world admin env canonical actual actualContext ξ heap after store finalContext reason valid covers environments heaps layout fault
    cases fault with
    | head fault =>
      cases fault with
      | polymorphicLet impossible _ => exact False.elim (impossible binding.monomorphic)
      | letInitializer _ fault =>
        obtain ⟨rfl, site, location, rfl, origin, evaluated⟩ :=
          ScalarExpressionReflection.Primitive.source_fault valueTree unique valid covers environments heaps fault
        have core := (GeneralExpressions.Primitive.readOnly valueTree).evaluation_rename evaluated layout.agrees
        refine ⟨_, store, mapping, world, .uninitialized site location origin, ?_, heaps, .refl _, .refl _, .refl _ _⟩
        simpa only [Core.LoopRenaming.letInitialized] using Core.LocalSequence.letInitialized_failure
          (Core.LocalLoop.controlType type) payload core
    | tail head fault =>
      exact fault_after_success (.letInitialized binding extension valueTree (.nil ih)) unique valid covers environments heaps layout head fault
  | discard valueTree _ ih =>
    intro mapping world admin env canonical actual actualContext ξ heap after store finalContext reason valid covers environments heaps layout fault
    cases fault with
    | head fault =>
      cases fault with
      | expression fault =>
        obtain ⟨rfl, site, location, rfl, origin, evaluated⟩ :=
          ScalarExpressionReflection.Primitive.source_fault valueTree unique valid covers environments heaps fault
        have core := (GeneralExpressions.Primitive.readOnly valueTree).evaluation_rename evaluated layout.agrees
        refine ⟨_, store, mapping, world, .uninitialized site location origin, ?_, heaps, .refl _, .refl _, .refl _ _⟩
        simpa only [Core.LoopRenaming.discard] using Core.LocalSequence.discard_failure (Core.LocalLoop.controlType type) core
    | tail head fault =>
      exact fault_after_success (.discard valueTree (.nil ih)) unique valid covers environments heaps layout head fault
  | assign target valueTree _ ih =>
    intro mapping world admin env canonical actual actualContext ξ heap after store finalContext reason valid covers environments heaps layout fault
    cases fault with
    | head fault =>
      cases fault with
      | assignValue fault =>
        obtain ⟨rfl, site, location, rfl, origin, evaluated⟩ :=
          ScalarAssignmentReflection.source_fault valueTree unique valid covers target.slot target.bare environments heaps fault
        obtain ⟨_, _, _, _, _, lookup, _, _, _, _⟩ := environments.lookup_heap heaps target.slot
        have core := (GeneralExpressions.Primitive.readOnly valueTree).evaluation_rename evaluated layout.agrees
        refine ⟨_, store, mapping, world, .uninitialized site location origin, ?_, heaps, .refl _, .refl _, .refl _ _⟩
        simpa only [Core.LoopRenaming.assign, Core.Expr.rename] using
          Core.LocalSequence.assign_failure (Core.LocalLoop.controlType type) (.var (layout.agrees lookup))
            (((GeneralExpressions.Primitive.readOnly valueTree).rename ξ).evaluation_weakenAt_zero core _)
    | tail head fault =>
      exact fault_after_success (.assign target valueTree (.nil ih)) unique valid covers environments heaps layout head fault

end Solcore.SourceSemantics.CoreLowering.ForHeaders
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForPostPreservation
/-! Static post headers discharge the success and fault interfaces used by
finite source for induction, under the actual six temporary loop binders. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell CoreProof

theorem post_preserves
    {compilation : SourceCorePrimitive.Context} {program : Program} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {type : Core.Ty} {location : Core.Location} {items : List ForItemForm} {code : Core.Expr} {ξ : Core.Renaming}
    (tree : ForHeaders.Tree compilation source reasonAt type (ForHeaders.Fallthrough type) scope context items code)
    (unique : NodeOccurrencesUnique source)
    (respects : Core.Renaming.Respects ξ (SourceCoreLocalCell.coreContext scope) actualContext)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual) :
    Internal.PostPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
      type location items (code.rename ξ) := by
  intro mapping world heap after store finalContext finalEnvironment environments heaps actualTyped locationTyped executed continued
  have layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ := ⟨respects, agree, actualTyped⟩
  have entry := ((layout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert Core.RuntimeValueHasType.unit).insert
    (Core.RuntimeValueHasType.bool (value := true))
  cases continued with
  | false =>
    have shifted := ((entry.insert (Core.RuntimeValueHasType.inLeft (rightType := Core.LocalLoop.transferType)
      (Core.RuntimeValueHasType.inLeft (rightType := type) .unit))).insert
      (Core.RuntimeValueHasType.inLeft (rightType := type) .unit)).insert Core.RuntimeValueHasType.unit
    obtain ⟨tail, _, _, heapEq, maps, worlds, frame, agreement⟩ :=
      tree.source_success unique program evidence environments heaps shifted executed
    have endpoint : tail.code = Core.LocalLoop.fallthrough type := tail.certificate
    have completed : Core.Evaluates tail.actual tail.store (tail.code.rename tail.embedding)
        (Core.LocalLoop.fallthroughValue type) tail.store := by
      rw [endpoint, Core.LoopRenaming.fallthrough]
      exact Core.LocalLoop.fallthrough_evaluates _ _ _
    refine ⟨tail.store, tail.mapping, tail.world, ?_, heapEq ▸ tail.heaps, maps, worlds, frame⟩
    have result := agreement.wrap completed
    simpa only [ForLoop.postCode_eq, rename_insert, ForLoop.fallthroughPrefix, Core.LoopExecution.entryEnvironment,
      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] using result
  | true =>
    have shifted := ((entry.insert (Core.RuntimeValueHasType.inRight (leftType := Core.LocalControl.controlType type)
      (Core.RuntimeValueHasType.inRight (leftType := .unit) .unit))).insert
      (Core.RuntimeValueHasType.inRight (leftType := .unit) .unit)).insert Core.RuntimeValueHasType.unit
    obtain ⟨tail, _, _, heapEq, maps, worlds, frame, agreement⟩ :=
      tree.source_success unique program evidence environments heaps shifted executed
    have endpoint : tail.code = Core.LocalLoop.fallthrough type := tail.certificate
    have completed : Core.Evaluates tail.actual tail.store (tail.code.rename tail.embedding)
        (Core.LocalLoop.fallthroughValue type) tail.store := by
      rw [endpoint, Core.LoopRenaming.fallthrough]
      exact Core.LocalLoop.fallthrough_evaluates _ _ _
    refine ⟨tail.store, tail.mapping, tail.world, ?_, heapEq ▸ tail.heaps, maps, worlds, frame⟩
    have result := agreement.wrap completed
    simpa only [ForLoop.postCode_eq, rename_insert, ForLoop.continuingPrefix, Core.LoopExecution.entryEnvironment,
      ↓reduceIte, List.cons_append, List.nil_append] using result

theorem post_fault_preserves
    {compilation : SourceCorePrimitive.Context} {program : Program} {context : Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {type : Core.Ty} {location : Core.Location} {items : List ForItemForm} {code : Core.Expr} {ξ : Core.Renaming}
    (tree : ForHeaders.Tree compilation source reasonAt type (ForHeaders.Fallthrough type) scope context items code)
    (unique : NodeOccurrencesUnique source)
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    (respects : Core.Renaming.Respects ξ (SourceCoreLocalCell.coreContext scope) actualContext)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual) :
    Internal.PostFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
      type location items (code.rename ξ) reasonAt := by
  intro mapping world heap after store finalContext reason environments heaps actualTyped locationTyped fault continued
  have layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ := ⟨respects, agree, actualTyped⟩
  have entry := ((layout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert Core.RuntimeValueHasType.unit).insert
    (Core.RuntimeValueHasType.bool (value := true))
  cases continued with
  | false =>
    have shifted := ((entry.insert (Core.RuntimeValueHasType.inLeft (rightType := Core.LocalLoop.transferType)
      (Core.RuntimeValueHasType.inLeft (rightType := type) .unit))).insert
      (Core.RuntimeValueHasType.inLeft (rightType := type) .unit)).insert Core.RuntimeValueHasType.unit
    have result := tree.source_fault unique program evidence valid covers environments heaps shifted fault
    simpa only [ForHeaders.FaultResult, ForLoop.postCode_eq, rename_insert, ForLoop.fallthroughPrefix, Core.LoopExecution.entryEnvironment,
      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append] using result
  | true =>
    have shifted := ((entry.insert (Core.RuntimeValueHasType.inRight (leftType := Core.LocalControl.controlType type)
      (Core.RuntimeValueHasType.inRight (leftType := .unit) .unit))).insert
      (Core.RuntimeValueHasType.inRight (leftType := .unit) .unit)).insert Core.RuntimeValueHasType.unit
    have result := tree.source_fault unique program evidence valid covers environments heaps shifted fault
    simpa only [ForHeaders.FaultResult, ForLoop.postCode_eq, rename_insert, ForLoop.continuingPrefix, Core.LoopExecution.entryEnvironment,
      ↓reduceIte, List.cons_append, List.nil_append] using result


end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForInitializerSuccess
/-! Successful initializer and iteration composition under arbitrary actual
lexical layouts, for use by the complete static for-tree induction. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Internal Default

def InitializersSuccess (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (context : Context) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment loopEnvironment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap initialized after : Dynamic.Heap} {store : Core.Store}
    {loopContext finalContext : Context} {outcome : Dynamic.ControlOutcome},
    Core.Ty.WellFormed [] type →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Dynamic.ForItemsExecute program context evidence source environment heap items loopContext loopEnvironment initialized →
    Dynamic.ForLoopExecutes program loopContext evidence source loopEnvironment initialized condition post statements finalContext outcome after →
    Default.SuccessResult type mapping world store after outcome actual (code.rename ξ)

theorem success_initializers_empty
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {statements : List StatementId} {post : List ForItemForm} {type : Core.Ty}
    {condition : ExpressionId} {conditionCode bodyCode postCode : Core.Expr} {depth : Nat} {selfReason : Core.Word}
    (unique : NodeOccurrencesUnique source)
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (bodyTyped : Core.Ty.WellFormed [] type → Core.HasType (SourceCoreLocalCell.coreContext scope) bodyCode (Core.LocalLoop.resultType type))
    (bodyCorrect : Success program evidence source scope context false statements type bodyCode)
    (postTree : ForHeaders.Tree compilation source reasonAt type (ForHeaders.Fallthrough type) scope context post postCode) :
    InitializersSuccess program evidence source scope context [] condition post statements type
      (Core.LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  intro mapping world admin environment loopEnvironment canonical actual actualContext ξ heap initialized after store loopContext finalContext outcome
    wellFormed environments heaps layout initialSource loop
  cases initialSource
  have postTyped := postTree.hasType wellFormed (by
    intro scope context code endpoint
    cases endpoint
    exact Core.LocalLoop.fallthrough_hasType wellFormed)
  obtain ⟨installedHeaps, extended, unmapped, selfTyped, installed, installFrame⟩ :=
    LoopAdministration.install selfReason heaps layout.typed wellFormed
      (conditionTree.hasType.rename layout.respects) ((bodyTyped wellFormed).rename layout.respects)
      (postTyped.rename layout.respects)
  have bodyPreserves : BodyPreserves program context evidence source scope admin environment canonical actual actualContext
      type store.length statements (bodyCode.rename ξ) := by
    intro bodyMapping bodyWorld bodyHeap bodyAfter bodyStore bodyFinalContext bodyOutcome
      bodyEnvironments bodyHeaps actualTyped locationTyped bodySource
    have bodyLayout : Layout bodyWorld (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ :=
      ⟨layout.respects, layout.agrees, actualTyped⟩
    have shiftedLayout := ((bodyLayout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert
      Core.RuntimeValueHasType.unit).insert (Core.RuntimeValueHasType.bool (value := true))
    obtain ⟨result, finalStore, finalMapping, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
      bodyCorrect wellFormed bodyEnvironments bodyHeaps shiftedLayout bodySource
    exact ⟨result, finalStore, finalMapping, finalWorld, related,
      by simpa only [rename_insert, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, Core.LoopExecution.bodyCode] using core, finalHeaps, maps, worlds, frame⟩
  obtain ⟨result, finalStore, finalMapping, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
    Internal.for_success loop conditionTree unique layout.agrees bodyPreserves
      (Reflection.post_preserves postTree unique layout.respects layout.agrees)
      (environments.extend (.refl _) extended) installedHeaps
      (Core.RuntimeEnvironmentHasTypes.weaken extended layout.typed) selfTyped unmapped installed
  refine ⟨result, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, extended.trans worlds, installFrame.trans frame⟩
  rw [Core.LoopRenaming.iterate]
  apply Core.LocalLoop.iterate_evaluates
  apply Core.LocalLoop.invoke_success _ _ (.var rfl) _ core
  exact installed

theorem success_initializers_prepend
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {item : ForItemForm} {rest : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (header : ForHeaders.Tree compilation source reasonAt type
      (fun scope context code => InitializersSuccess program evidence source scope context rest condition post statements type code)
      scope context [item] code)
    (unique : NodeOccurrencesUnique source) :
    InitializersSuccess program evidence source scope context (item :: rest) condition post statements type code := by
  intro mapping world admin environment loopEnvironment canonical actual actualContext ξ heap initialized after store loopContext finalContext outcome
    wellFormed environments heaps layout initialSource loop
  cases initialSource with
  | cons head remaining =>
    obtain ⟨tail, contextEq, environmentEq, heapEq, maps, worlds, frame, agreement⟩ :=
      header.source_success unique program evidence environments heaps layout (.cons head .nil)
    rw [← contextEq, ← environmentEq, ← heapEq] at remaining
    obtain ⟨result, finalStore, finalMap, finalWorld, related, core, finalHeaps, tailMaps, tailWorlds, tailFrame⟩ :=
      tail.certificate wellFormed tail.environments tail.heaps tail.layout remaining loop
    exact ⟨result, finalStore, finalMap, finalWorld, related, agreement.wrap core, finalHeaps,
      maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame⟩

private theorem restore_related {type : Core.Ty} {outcome : Dynamic.ControlOutcome} {value : Core.Value}
    (related : ControlRepresents type outcome value) (environment : Dynamic.Environment) :
    ControlRepresents type (Dynamic.restoreControl environment outcome) value := by
  cases related with
  | fallthrough => exact .fallthrough environment
  | returned value typed => exact .returned value typed
  | breaking => exact .breaking environment
  | continuing => exact .continuing environment

theorem success_for_head
    {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {context : Context} {id : StatementId} {node : StatementNode}
    {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .forLoop items condition post statements)
    (correct : InitializersSuccess program evidence source scope context items condition post statements type code) :
    ScopedSuccess program evidence source scope context id type code := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store finalContext outcome
    wellFormed environments heaps layout executed
  obtain ⟨rfl, loopContext, loopFinalContext, loopEnvironment, initialized, loopOutcome, rfl, initialization, loop⟩ :=
    ForSourceViews.success unique contains form executed
  obtain ⟨result, finalStore, finalMap, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
    correct wellFormed environments heaps layout initialization loop
  refine ⟨rfl, ?_, result, finalStore, finalMap, finalWorld, restore_related related environment, core, finalHeaps, maps, worlds, frame⟩
  intro next same
  cases loopOutcome <;> simp_all [Dynamic.restoreControl]

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForInitializerFault
/-! Successful initializers followed by a finite iteration fault preserve the
specified source failure. Initializer faults themselves are handled through
the independent header theorem at the scoped statement boundary. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Internal Default

def InitializersFault (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope) (context : Context) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment loopEnvironment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap initialized after : Dynamic.Heap} {store : Core.Store}
    {loopContext : Context} {reason : Dynamic.SemanticFault},
    Core.Ty.WellFormed [] type → PrimitiveExpressions.ContextValid compilation context → evidence.Covers context →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Dynamic.ForItemsExecute program context evidence source environment heap items loopContext loopEnvironment initialized →
    Dynamic.ForLoopFaults program loopContext evidence source loopEnvironment initialized condition post statements reason after →
    Default.FaultResult program evidence source reasonAt type mapping world store after reason actual (code.rename ξ)

theorem fault_initializers_empty
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {statements : List StatementId} {post : List ForItemForm} {type : Core.Ty}
    {condition : ExpressionId} {conditionCode bodyCode postCode : Core.Expr} {depth : Nat} {selfReason : Core.Word}
    (unique : NodeOccurrencesUnique source)
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (bodyTyped : Core.Ty.WellFormed [] type → Core.HasType (SourceCoreLocalCell.coreContext scope) bodyCode (Core.LocalLoop.resultType type))
    (bodyCorrect : Success program evidence source scope context false statements type bodyCode)
    (bodyFaultCorrect : Fault compilation program evidence source reasonAt scope context false statements type bodyCode)
    (postTree : ForHeaders.Tree compilation source reasonAt type (ForHeaders.Fallthrough type) scope context post postCode) :
    InitializersFault compilation program evidence source reasonAt scope context [] condition post statements type
      (Core.LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  intro mapping world admin environment loopEnvironment canonical actual actualContext ξ heap initialized after store loopContext reason
    wellFormed valid covers environments heaps layout initialSource loop
  cases initialSource
  have postTyped := postTree.hasType wellFormed (by
    intro scope context code endpoint
    cases endpoint
    exact Core.LocalLoop.fallthrough_hasType wellFormed)
  obtain ⟨installedHeaps, extended, unmapped, selfTyped, installed, installFrame⟩ :=
    LoopAdministration.install selfReason heaps layout.typed wellFormed
      (conditionTree.hasType.rename layout.respects) ((bodyTyped wellFormed).rename layout.respects)
      (postTyped.rename layout.respects)
  have bodyPreserves : BodyPreserves program context evidence source scope admin environment canonical actual actualContext
      type store.length statements (bodyCode.rename ξ) := by
    intro bodyMapping bodyWorld bodyHeap bodyAfter bodyStore bodyFinalContext bodyOutcome
      bodyEnvironments bodyHeaps actualTyped locationTyped bodySource
    have bodyLayout : Layout bodyWorld (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ :=
      ⟨layout.respects, layout.agrees, actualTyped⟩
    have shiftedLayout := ((bodyLayout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert
      Core.RuntimeValueHasType.unit).insert (Core.RuntimeValueHasType.bool (value := true))
    obtain ⟨result, finalStore, finalMapping, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
      bodyCorrect wellFormed bodyEnvironments bodyHeaps shiftedLayout bodySource
    exact ⟨result, finalStore, finalMapping, finalWorld, related,
      by simpa only [rename_insert, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, Core.LoopExecution.bodyCode] using core, finalHeaps, maps, worlds, frame⟩
  have bodyFaultPreserves : BodyFaultPreserves program context evidence source scope admin environment canonical actual actualContext
      type store.length statements (bodyCode.rename ξ) reasonAt := by
    intro bodyMapping bodyWorld bodyHeap bodyAfter bodyStore bodyFinalContext bodyReason
      bodyEnvironments bodyHeaps actualTyped locationTyped bodySource
    have bodyLayout : Layout bodyWorld (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ :=
      ⟨layout.respects, layout.agrees, actualTyped⟩
    have shiftedLayout := ((bodyLayout.insert (Core.RuntimeValueHasType.cellRef locationTyped)).insert
      Core.RuntimeValueHasType.unit).insert (Core.RuntimeValueHasType.bool (value := true))
    obtain ⟨word, finalStore, finalMapping, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
      bodyFaultCorrect wellFormed valid covers bodyEnvironments bodyHeaps shiftedLayout bodySource
    exact ⟨word, finalStore, finalMapping, finalWorld, related,
      by simpa only [rename_insert, Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment, Core.LoopExecution.bodyCode] using core, finalHeaps, maps, worlds, frame⟩
  obtain ⟨result, finalStore, finalMapping, finalWorld, related, core, finalHeaps, maps, worlds, frame⟩ :=
    Internal.for_fault loop conditionTree unique valid covers layout.agrees bodyPreserves bodyFaultPreserves
      (Reflection.post_preserves postTree unique layout.respects layout.agrees)
      (Reflection.post_fault_preserves postTree unique valid covers layout.respects layout.agrees)
      (environments.extend (.refl _) extended) installedHeaps
      (Core.RuntimeEnvironmentHasTypes.weaken extended layout.typed) selfTyped unmapped installed
  refine ⟨result, finalStore, finalMapping, finalWorld, related, ?_, finalHeaps, maps, extended.trans worlds, installFrame.trans frame⟩
  rw [Core.LoopRenaming.iterate]
  apply Core.LocalLoop.iterate_evaluates
  apply Core.LocalLoop.invoke_success _ _ (.var rfl) _ core
  exact installed

theorem fault_initializers_prepend
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {item : ForItemForm} {rest : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (header : ForHeaders.Tree compilation source reasonAt type
      (fun scope context code => InitializersFault compilation program evidence source reasonAt scope context rest condition post statements type code)
      scope context [item] code)
    (unique : NodeOccurrencesUnique source) :
    InitializersFault compilation program evidence source reasonAt scope context (item :: rest) condition post statements type code := by
  intro mapping world admin environment loopEnvironment canonical actual actualContext ξ heap initialized after store loopContext reason
    wellFormed valid covers environments heaps layout initialSource loop
  cases initialSource with
  | cons head remaining =>
    obtain ⟨tail, contextEq, environmentEq, heapEq, maps, worlds, frame, agreement⟩ :=
      header.source_success unique program evidence environments heaps layout (.cons head .nil)
    have extension : ForHeaders.ContextExtends source.owner context tail.context := by
      rw [contextEq]
      cases head with
      | letUninitialized _ extension _ | letInitialized _ _ extension _ | letInitializedGeneralized _ _ _ extension _ =>
          exact .binder extension
      | expression | assignValue | assignBitNot => exact .refl _ _
    rw [← contextEq, ← environmentEq, ← heapEq] at remaining
    obtain ⟨result, finalStore, finalMap, finalWorld, related, core, finalHeaps, tailMaps, tailWorlds, tailFrame⟩ :=
      tail.certificate wellFormed (extension.valid valid) (extension.covers covers) tail.environments tail.heaps tail.layout remaining loop
    exact ⟨result, finalStore, finalMap, finalWorld, related, agreement.wrap core, finalHeaps,
      maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame⟩

theorem fault_for_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {id : StatementId} {node : StatementNode} {items post : List ForItemForm} {condition : ExpressionId}
    {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .forLoop items condition post statements)
    (header : ForHeaders.Tree compilation source reasonAt type (fun _ _ _ => True) scope context items code)
    (correct : InitializersFault compilation program evidence source reasonAt scope context items condition post statements type code) :
    ScopedFault compilation program evidence source reasonAt scope context id type code := by
  intro mapping world admin environment canonical actual actualContext ξ heap after store reason
    wellFormed valid covers environments heaps layout fault
  rcases ForSourceViews.fault unique contains form fault with ⟨finalContext, initialFault⟩ | ⟨loopContext, loopEnvironment, initialized, initialSource, loopFault⟩
  · exact header.source_fault unique program evidence valid covers environments heaps layout initialFault
  · exact correct wellFormed valid covers environments heaps layout initialSource loopFault

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopScopedReflection
/-! Scoped-head reconstruction contracts and sequencing. Source local names
and contexts are restored at a block, conditional, or loop boundary; allocated
cells and their location-map/world extensions remain observable. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof

inductive ScopedMeaning (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : StatementId) (type : Core.Ty) : Dynamic.ControlOutcome → Dynamic.Heap → Core.Value → Prop where
  | control {outcome after result}
      (execution : Dynamic.StatementExecutes program context evidence source environment before id context
        (Dynamic.restoreControl environment outcome) after)
      (related : ControlRepresents type outcome result) :
      ScopedMeaning program context evidence source reasonAt environment before id type outcome after result
  | fault {reason after word}
      (execution : Dynamic.StatementFaults program context evidence source environment before id reason after)
      (related : FaultRepresents program evidence source reasonAt reason word) :
      ScopedMeaning program context evidence source reasonAt environment before id type (.fault reason) after
        (.inLeft (Core.LocalLoop.controlType type) (.word word))

def ScopedResult (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : StatementId) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (result : Core.Value) (finalStore : Core.Store) : Prop :=
  ∃ outcome after finalMapping finalWorld,
    ScopedMeaning program context evidence source reasonAt environment before id type outcome after result ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

def ScopedReflects (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (id : StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store finalStore : Core.Store} {result : Core.Value},
    Core.Ty.WellFormed [] type → PrimitiveExpressions.ContextValid compilation context →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Core.Evaluates actual store (code.rename ξ) result finalStore →
    ScopedResult program context evidence source reasonAt environment heap id type mapping world store result finalStore

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopScopedComposition
/-! Reconstruct scoped statement sequencing from finite Core evaluation.
The head and tail contracts are static-tree induction hypotheses, and the
actual helper evaluation selects whether the tail is entered. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof

theorem reflects_scoped
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {type : Core.Ty} {code body : Core.Expr}
    (contains : ContainsStatement source id node) (notTail : ∀ expression, node.form ≠ .expression expression false)
    (head : ScopedReflects compilation program evidence source reasonAt scope context id type code)
    (tail : Reflects compilation program evidence source reasonAt scope context mode rest type body) :
    Reflects compilation program evidence source reasonAt scope context mode (id :: rest) type (Core.LocalLoop.sequence type code body) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.sequence] at evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨_, middleStore, headResult, _, headSized⟩ := sized.bind_computation
  obtain ⟨headOutcome, middle, middleMap, middleWorld, headMeaning, middleHeaps, maps, worlds, frame⟩ :=
    head wellFormed valid environments heaps layout headSized.sound
  cases headMeaning with
  | control sourceHead related =>
    cases related with
    | fallthrough nextEnvironment =>
      have shiftedLayout := (((layout.extend worlds).insert
        (Core.RuntimeValueHasType.inLeft (rightType := Core.LocalLoop.transferType) (Core.RuntimeValueHasType.inLeft (rightType := type) .unit))).insert
        (Core.RuntimeValueHasType.inLeft (rightType := type) .unit)).insert Core.RuntimeValueHasType.unit
      obtain ⟨_, _, continuation⟩ := sized.sequence_fallthrough headSized.sound
      obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, futureMaps, futureWorlds, futureFrame⟩ :=
        tail wellFormed valid (environments.extend maps worlds) middleHeaps shiftedLayout
          (by simpa only [rename_insert] using continuation.sound)
      exact ⟨finalContext, outcome, after, finalMap, finalWorld,
        prepend contains (fun _ _ => notTail) sourceHead meaning,
        finalHeaps, maps.trans futureMaps, worlds.trans futureWorlds, frame.trans futureFrame⟩
    | returned staged typed =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.sequence_returned type headSized.sound)
      exact ⟨context, _, middle, middleMap, middleWorld,
        terminal contains notTail sourceHead (.returned _) (.returned staged typed),
        middleHeaps, maps, worlds, frame⟩
    | breaking nextEnvironment =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.sequence_transfer type headSized.sound)
      exact ⟨context, _, middle, middleMap, middleWorld,
        terminal contains notTail sourceHead (.breaking environment) (.breaking environment),
        middleHeaps, maps, worlds, frame⟩
    | continuing nextEnvironment =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.sequence_transfer type headSized.sound)
      exact ⟨context, _, middle, middleMap, middleWorld,
        terminal contains notTail sourceHead (.continuing environment) (.continuing environment),
        middleHeaps, maps, worlds, frame⟩
  | fault sourceFault related =>
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated (Core.LocalLoop.sequence_failure type headSized.sound)
    exact ⟨context, _, middle, middleMap, middleWorld, head_fault sourceFault related,
      middleHeaps, maps, worlds, frame⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopWhileReflection
/-! The actual generated while prelude determines its self-cell and closure.
A finite Core execution reconstructs a finite independent source while trace;
body reflection is supplied only as the structural child-tree hypothesis. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof

theorem reflects_while_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {id : StatementId} {statements : List StatementId} {node : StatementNode} {type : Core.Ty}
    {condition : ExpressionId} {conditionCode bodyCode : Core.Expr} {depth : Nat} {selfReason : Core.Word}
    (contains : ContainsStatement source id node) (form : node.form = .whileLoop condition statements)
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (bodyTyped : Core.Ty.WellFormed [] type → Core.HasType (SourceCoreLocalCell.coreContext scope) bodyCode (Core.LocalLoop.resultType type))
    (bodyCorrect : Reflects compilation program evidence source reasonAt scope context false statements type bodyCode) :
    ScopedReflects compilation program evidence source reasonAt scope context id type
      (Core.LocalLoop.whileLoop type conditionCode bodyCode selfReason) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.whileLoop] at evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨entrySize, _, entry⟩ := sized.iterate_entry
  obtain ⟨installedHeaps, extended, unmapped, selfTyped, installed, installFrame⟩ :=
    LoopAdministration.install selfReason heaps layout.typed wellFormed
      (conditionTree.hasType.rename layout.respects) ((bodyTyped wellFormed).rename layout.respects)
      (Core.LocalLoop.fallthrough_hasType wellFormed)
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
    while_reflect conditionTree valid layout.agrees
      (bodyCorrect.body wellFormed valid layout.respects layout.agrees) entrySize
      (environments.extend (.refl _) extended) installedHeaps
      (Core.RuntimeEnvironmentHasTypes.weaken extended layout.typed) selfTyped unmapped installed entry
  refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps, extended.trans worlds, installFrame.trans frame⟩
  cases meaning with
  | control sourceLoop related => exact .control (.whileLoop contains form sourceLoop) related
  | fault sourceFault related => exact .fault (.whileIteration contains form sourceFault) related

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForInitializerReflection
/-! Reconstruct initialization and iteration under the actual lexical scope.
The header continuation is a structural induction contract, while all source
header executions are built from its static tree and the represented heap. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof

inductive InitializersMeaning (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (items : List ForItemForm) (condition : ExpressionId)
    (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty) :
    Dynamic.ControlOutcome → Dynamic.Heap → Core.Value → Prop where
  | control {loopContext loopFinalContext loopEnvironment initialized outcome after result}
      (initialization : Dynamic.ForItemsExecute program context evidence source environment before items
        loopContext loopEnvironment initialized)
      (iteration : Dynamic.ForLoopExecutes program loopContext evidence source loopEnvironment initialized
        condition post statements loopFinalContext outcome after)
      (related : ControlRepresents type outcome result) :
      InitializersMeaning program context evidence source reasonAt environment before items condition post statements type outcome after result
  | initialFault {finalContext reason word after}
      (fault : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after)
      (related : FaultRepresents program evidence source reasonAt reason word) :
      InitializersMeaning program context evidence source reasonAt environment before items condition post statements type
        (.fault reason) after (.inLeft (Core.LocalLoop.controlType type) (.word word))
  | iterationFault {loopContext loopEnvironment initialized reason word after}
      (initialization : Dynamic.ForItemsExecute program context evidence source environment before items
        loopContext loopEnvironment initialized)
      (fault : Dynamic.ForLoopFaults program loopContext evidence source loopEnvironment initialized
        condition post statements reason after)
      (related : FaultRepresents program evidence source reasonAt reason word) :
      InitializersMeaning program context evidence source reasonAt environment before items condition post statements type
        (.fault reason) after (.inLeft (Core.LocalLoop.controlType type) (.word word))

def InitializersResult (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (items : List ForItemForm) (condition : ExpressionId)
    (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (result : Core.Value) (finalStore : Core.Store) : Prop :=
  ∃ outcome after finalMap finalWorld,
    InitializersMeaning program context evidence source reasonAt environment before items condition post statements type outcome after result ∧
    GeneralHeap.HeapRepresents finalMap finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMap ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMap finalStore

def InitializersReflects (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (items : List ForItemForm) (condition : ExpressionId)
    (post : List ForItemForm) (statements : List StatementId) (type : Core.Ty) (code : Core.Expr) : Prop :=
  ∀ {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store finalStore : Core.Store} {result : Core.Value},
    Core.Ty.WellFormed [] type → PrimitiveExpressions.ContextValid compilation context →
    GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical →
    GeneralHeap.HeapRepresents mapping world heap store →
    Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ →
    Core.Evaluates actual store (code.rename ξ) result finalStore →
    InitializersResult program context evidence source reasonAt environment heap items condition post statements type
      mapping world store result finalStore

theorem reflects_initializers_empty
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {statements : List StatementId} {post : List ForItemForm} {type : Core.Ty}
    {condition : ExpressionId} {conditionCode bodyCode postCode : Core.Expr} {depth : Nat} {selfReason : Core.Word}
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (bodyTyped : Core.Ty.WellFormed [] type → Core.HasType (SourceCoreLocalCell.coreContext scope) bodyCode (Core.LocalLoop.resultType type))
    (bodyCorrect : Reflects compilation program evidence source reasonAt scope context false statements type bodyCode)
    (postTree : ForHeaders.Tree compilation source reasonAt type (ForHeaders.Fallthrough type) scope context post postCode) :
    InitializersReflects compilation program evidence source reasonAt scope context [] condition post statements type
      (Core.LocalLoop.iterate type conditionCode bodyCode postCode selfReason) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.iterate] at evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨entrySize, _, entry⟩ := sized.iterate_entry
  have postTyped := postTree.hasType wellFormed (by
    intro scope context code endpoint
    cases endpoint
    exact Core.LocalLoop.fallthrough_hasType wellFormed)
  obtain ⟨installedHeaps, extended, unmapped, selfTyped, installed, installFrame⟩ :=
    LoopAdministration.install selfReason heaps layout.typed wellFormed
      (conditionTree.hasType.rename layout.respects) ((bodyTyped wellFormed).rename layout.respects)
      (postTyped.rename layout.respects)
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
    for_reflect conditionTree valid layout.agrees
      (bodyCorrect.body wellFormed valid layout.respects layout.agrees)
      (post_constructs postTree valid layout.respects layout.agrees) entrySize
      (environments.extend (.refl _) extended) installedHeaps
      (Core.RuntimeEnvironmentHasTypes.weaken extended layout.typed) selfTyped unmapped installed entry
  refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps, extended.trans worlds, installFrame.trans frame⟩
  cases meaning with
  | control sourceLoop related => exact .control .nil sourceLoop related
  | fault sourceFault related => exact .iterationFault .nil sourceFault related

/-- One statically certified initializer prefix composes with the recursive
initializer contract. It does not assume a source execution of either part. -/
theorem reflects_initializers_prepend
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {item : ForItemForm} {rest : List ForItemForm} {condition : ExpressionId} {post : List ForItemForm}
    {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (header : ForHeaders.Tree compilation source reasonAt type
      (fun scope context code => InitializersReflects compilation program evidence source reasonAt scope context
        rest condition post statements type code) scope context [item] code) :
    InitializersReflects compilation program evidence source reasonAt scope context (item :: rest) condition post statements type code := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  have construction := header.construct program evidence valid environments heaps layout
  cases construction with
  | continues tail execution contextExtension maps worlds frame agreement =>
    obtain ⟨outcome, after, finalMap, finalWorld, meaning, finalHeaps, tailMaps, tailWorlds, tailFrame⟩ :=
      tail.certificate wellFormed (contextExtension.valid valid) tail.environments tail.heaps tail.layout (agreement.unwrap evaluated)
    refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds, frame.trans tailFrame⟩
    cases execution with
    | cons head empty =>
      cases empty
      cases meaning with
      | control initialization iteration related => exact .control (.cons head initialization) iteration related
      | initialFault fault related => exact .initialFault (.tail head fault) related
      | iterationFault initialization fault related => exact .iterationFault (.cons head initialization) fault related
  | @fault finalContext reason word after finalMap finalWorld finalStore fault related finalHeaps maps worlds frame evaluation =>
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated evaluation
    refine ⟨.fault reason, _, _, _, ?_, finalHeaps, maps, worlds, frame⟩
    cases fault with
    | head fault => exact .initialFault (.head fault) related
    | tail _ impossible => cases impossible

theorem reflects_for_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context}
    {id : StatementId} {node : StatementNode} {items : List ForItemForm} {condition : ExpressionId}
    {post : List ForItemForm} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (contains : ContainsStatement source id node) (form : node.form = .forLoop items condition post statements)
    (correct : InitializersReflects compilation program evidence source reasonAt scope context items condition post statements type code) :
    ScopedReflects compilation program evidence source reasonAt scope context id type code := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  obtain ⟨outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
    correct wellFormed valid environments heaps layout evaluated
  refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps, worlds, frame⟩
  cases meaning with
  | control initialization iteration related => exact .control (.forLoop contains form initialization iteration) related
  | initialFault fault related => exact .fault (.forInitializer contains form fault) related
  | iterationFault initialization fault related => exact .fault (.forIteration contains form initialization fault) related

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForStatementSuccess
/-! Supplied successful source executions of the complete static default
while/for profile produce finite Core executions. Static-tree induction
closes body/post/initializer contracts; loop recursion follows the given
independent finite source derivation. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Default

def SuccessPosition (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (position : Position) (type : Core.Ty) (code : Core.Expr) : Prop :=
  match position with
  | .statements mode statements => Success program evidence source scope context mode statements type code
  | .initializers items condition post statements =>
      InitializersSuccess program evidence source scope context items condition post statements type code

theorem Tree.source_success
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {position : Position} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context position type code)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    SuccessPosition program evidence source scope context position type code := by
  induction tree with
  | nil => exact success_nil program evidence source _ _ _ _
  | breaking _ metadata form => exact success_breaking unique metadata.contains form
  | continuing _ metadata form => exact success_continuing unique metadata.contains form
  | returnUnit _ metadata form => exact success_returnUnit unique metadata.contains form
  | returnValue _ metadata form value => exact success_returnValue unique metadata.contains form value
  | tailExpression metadata form value => exact success_tailExpression unique metadata.contains form value
  | letUninitialized metadata form binding extension _ ih =>
      exact success_letUninitialized unique metadata.contains form binding extension ih
  | letInitialized metadata form binding extension value _ ih =>
      exact success_letInitialized unique metadata.contains form binding extension value ih
  | assign metadata form target value _ ih => exact success_assign unique metadata.contains form target value ih
  | discard metadata form notTail _ value _ ih => exact success_discard unique metadata.contains form notTail value ih
  | block metadata form _ _ bodyIH tailIH =>
      exact success_scoped unique metadata.contains (by intros; simp [form])
        (success_block_head unique metadata.contains form bodyIH) tailIH
  | ifThen metadata form condition _ _ _ thenIH elseIH tailIH =>
      exact success_scoped unique metadata.contains (by intros; simp [form])
        (success_if_head unique metadata.contains form condition thenIH elseIH) tailIH
  | whileLoop metadata form condition body _ bodyIH tailIH =>
      exact success_scoped unique metadata.contains (by intros; simp [form])
        (success_while_head unique metadata.contains form condition body.hasType bodyIH) tailIH

  | forLoop metadata form _ _ initialIH tailIH =>
      exact success_scoped unique metadata.contains (by intros; simp [form])
        (success_for_head unique metadata.contains form initialIH) tailIH
  | initializersDone condition body post bodyIH =>
      exact success_initializers_empty unique condition body.hasType bodyIH post
  | initializerUninitialized binding extension _ ih =>
      exact success_initializers_prepend (compilation := compilation) (reasonAt := reasonAt) (.letUninitialized binding extension (.nil ih)) unique
  | initializerInitialized binding extension value _ ih =>
      exact success_initializers_prepend (.letInitialized binding extension value (.nil ih)) unique
  | initializerAssign target value _ ih =>
      exact success_initializers_prepend (.assign target value (.nil ih)) unique
  | initializerDiscard value _ ih =>
      exact success_initializers_prepend (.discard value (.nil ih)) unique

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForStatementFault
/-! Static-tree induction discharges every body/post/initializer premise for
supplied finite source faults in the complete default while/for profile. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Default

def FaultPosition (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (position : Position) (type : Core.Ty) (code : Core.Expr) : Prop :=
  match position with
  | .statements mode statements => Fault compilation program evidence source reasonAt scope context mode statements type code
  | .initializers items condition post statements =>
      InitializersFault compilation program evidence source reasonAt scope context items condition post statements type code

/-- Whole-list fault correspondence, including successful earlier iterations.
The only dynamic premise is the complete independent source fault derivation. -/
theorem Tree.source_fault
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {position : Position} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context position type code)
    (unique : NodeOccurrencesUnique source) (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    FaultPosition compilation program evidence source reasonAt scope context position type code := by
  induction tree with
  | nil => exact fault_nil compilation program evidence source reasonAt _ _ _ _
  | breaking _ metadata form => exact fault_breaking unique metadata.contains form
  | continuing _ metadata form => exact fault_continuing unique metadata.contains form
  | returnUnit _ metadata form => exact fault_returnUnit unique metadata.contains form
  | returnValue _ metadata form value => exact fault_returnValue unique metadata.contains form value
  | tailExpression metadata form value => exact fault_tailExpression unique metadata.contains form value
  | letUninitialized metadata form binding extension _ ih =>
    exact fault_letUninitialized unique metadata.contains form binding extension ih
  | letInitialized metadata form binding extension value _ ih =>
    exact fault_letInitialized unique metadata.contains form binding extension value ih
  | assign metadata form target value _ ih => exact fault_assign unique metadata.contains form target value ih
  | discard metadata form notTail _ value _ ih => exact fault_discard unique metadata.contains form notTail value ih
  | block metadata form body _ bodyIH tailIH =>
    exact fault_scoped unique metadata.contains (by intro value; simp [form])
      (success_block_head unique metadata.contains form (body.source_success unique program evidence))
      (fault_block_head unique metadata.contains form bodyIH) tailIH
  | ifThen metadata form condition thenBody elseBody _ thenIH elseIH tailIH =>
    exact fault_scoped unique metadata.contains (by intro value; simp [form])
      (success_if_head unique metadata.contains form condition
        (thenBody.source_success unique program evidence) (elseBody.source_success unique program evidence))
      (fault_if_head unique metadata.contains form condition thenIH elseIH) tailIH
  | whileLoop metadata form condition loopBody _ bodyIH tailIH =>
    exact fault_scoped unique metadata.contains (by intro value; simp [form])
      (success_while_head unique metadata.contains form condition loopBody.hasType (loopBody.source_success unique program evidence))
      (fault_while_head unique metadata.contains form condition loopBody.hasType
        (loopBody.source_success unique program evidence) bodyIH) tailIH

  | forLoop metadata form initial _ initialIH tailIH =>
    exact fault_scoped unique metadata.contains (by intro value; simp [form])
      (success_for_head unique metadata.contains form (initial.source_success unique program evidence))
      (fault_for_head unique metadata.contains form initial.header initialIH) tailIH
  | initializersDone condition body post bodyIH =>
    exact fault_initializers_empty unique condition body.hasType (body.source_success unique program evidence) bodyIH post
  | initializerUninitialized binding extension _ ih =>
    exact fault_initializers_prepend (.letUninitialized binding extension (.nil ih)) unique
  | initializerInitialized binding extension value _ ih =>
    exact fault_initializers_prepend (.letInitialized binding extension value (.nil ih)) unique
  | initializerAssign target value _ ih =>
    exact fault_initializers_prepend (.assign target value (.nil ih)) unique
  | initializerDiscard value _ ih =>
    exact fault_initializers_prepend (.discard value (.nil ih)) unique

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForStatementBridge
/-! Accepted default while/for lowering preserves supplied finite source success
and fault derivations. The source trace is the only termination witness. This
does not assert termination of every checked loop or general source fault
completeness. All completed Core runs agree with the preserved finite trace. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference BasicStatements Internal ScalarStatementViews
open Default (FinishedControlRepresents FinishedOutcomeRepresents fallback)

private theorem identity_respects (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context) :
    Core.Renaming.Respects Core.Renaming.id (SourceCoreLocalCell.coreContext scope)
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) := by
  intro index foundType found
  change (SourceCoreLocalCell.coreContext scope ++ administrativeContext)[index]? = some foundType
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem canonical_layout
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
    Layout world (SourceCoreLocalCell.coreContext scope) coreEnvironment
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) coreEnvironment Core.Renaming.id :=
  ⟨identity_respects scope administrativeContext, fun found => found, environments.runtime_hasTypes⟩

theorem Tree.hasType_with_administrative
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {mode : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context (.statements mode statements) type code)
    (wellFormed : Core.Ty.WellFormed [] type) (administrativeContext : Core.Context) :
    Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code (Core.LocalLoop.resultType type) := by
  simpa only [Core.Expr.rename_id] using (tree.hasType wellFormed).rename (identity_respects scope administrativeContext)

/-- A successful source trace determines a finite executable Core result,
including the allocated administrative cells and the source-location map. -/
theorem lowerFlowStatements_source_success_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context finalContext : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasons)
      fuel source scope statements type reasonAt tailReturns selfReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (execution : ListExecutes tailReturns program context evidence source environment heap statements finalContext outcome after) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LocalLoop.resultType type) ∧
    ∃ result finalStore finalMapping finalWorld required,
      ControlRepresents type outcome result ∧ GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  have tree := tree_of_lowerFlowStatementsWithExpression aligned unique accepted
  obtain ⟨result, finalStore, finalMapping, finalWorld, related, evaluated, finalHeaps, maps, worlds, frame⟩ :=
    tree.source_success unique program evidence wellFormed environments heaps (canonical_layout environments) execution
  simp only [Core.Expr.rename_id] at evaluated
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluated
  refine ⟨Core.infer_complete (tree.hasType_with_administrative wellFormed administrativeContext),
    result, finalStore, finalMapping, finalWorld, required, related, finalHeaps, maps, worlds, frame, completes, ?_⟩
  intro runtimeFuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) evaluated

theorem lowerFlowStatements_source_fault_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context finalContext : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasons)
      fuel source scope statements type reasonAt tailReturns selfReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (fault : ListFaults tailReturns program context evidence source environment heap statements finalContext reason after) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LocalLoop.resultType type) ∧
    ∃ word finalStore finalMapping finalWorld required,
      FaultRepresents program evidence source reasonAt reason word ∧ GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) =
        .done (.inLeft (Core.LocalLoop.controlType type) (.word word)) finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = .inLeft (Core.LocalLoop.controlType type) (.word word) ∧ actualStore = finalStore) := by
  have tree := tree_of_lowerFlowStatementsWithExpression aligned unique accepted
  obtain ⟨word, finalStore, finalMapping, finalWorld, related, evaluated, finalHeaps, maps, worlds, frame⟩ :=
    tree.source_fault unique program evidence wellFormed valid covers environments heaps (canonical_layout environments) fault
  simp only [Core.Expr.rename_id] at evaluated
  obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel evaluated
  refine ⟨Core.infer_complete (tree.hasType_with_administrative wellFormed administrativeContext),
    word, finalStore, finalMapping, finalWorld, required, related, finalHeaps, maps, worlds, frame, completes, ?_⟩
  intro runtimeFuel actual actualStore completed
  exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) evaluated

private theorem finish_success
    {type : Core.Ty} {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    {environment : Core.Environment} {before after : Core.Store} {code : Core.Expr}
    (related : ControlRepresents type outcome result)
    (evaluated : Core.Evaluates environment before code result after) (fellThrough escaped : Core.Word) :
    ∃ finished, FinishedControlRepresents type fellThrough escaped outcome finished ∧
      Core.Evaluates environment before
        (Core.LocalControl.finish type (Core.LocalLoop.toControl type code escaped) (fallback type fellThrough)) finished after := by
  cases related with
  | fallthrough sourceEnv =>
    refine ⟨_, .fallthrough sourceEnv, Core.LocalControl.finish_fallthrough type
      (Core.LocalLoop.toControl_normal type escaped evaluated) ?_⟩
    by_cases unit : type = .unit
    · simp [fallback, unit, Core.LanguageResult.success, Core.Expr.weakenAt]
      exact .inRight .unit
    · simp [fallback, unit, Core.LanguageResult.failure, Core.Expr.weakenAt]
      exact .inLeft .word
  | returned value typed =>
    exact ⟨_, .returned value typed, Core.LocalControl.finish_returned type
      (Core.LocalLoop.toControl_normal type escaped evaluated)⟩
  | breaking sourceEnv =>
    exact ⟨_, .breaking sourceEnv, Core.LocalControl.finish_failure type
      (Core.LocalLoop.toControl_transfer type escaped evaluated)⟩
  | continuing sourceEnv =>
    exact ⟨_, .continuing sourceEnv, Core.LocalControl.finish_failure type
      (Core.LocalLoop.toControl_transfer type escaped evaluated)⟩

private theorem finish_hasType
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty} {flow : Core.Expr}
    {reasonAt : ExpressionId → Core.Word} {escaped : Core.Word}
    (tree : Tree compilation source reasonAt escaped scope context (.statements true statements) type flow)
    (wellFormed : Core.Ty.WellFormed [] type) (admin : Core.Context) (fellThrough : Core.Word) :
    Core.HasType (SourceCoreLocalCell.coreContext scope ++ admin)
      (Core.LocalControl.finish type (Core.LocalLoop.toControl type flow escaped) (fallback type fellThrough))
      (Core.LanguageResult.resultType type) := by
  apply Core.LocalControl.finish_hasType wellFormed
    (Core.LocalLoop.toControl_hasType escaped wellFormed (tree.hasType_with_administrative wellFormed admin))
  by_cases unit : type = .unit
  · simpa [fallback, unit] using Core.LanguageResult.success_hasType (context := SourceCoreLocalCell.coreContext scope ++ admin) Core.HasType.unit
  · simpa [fallback, unit] using Core.LanguageResult.failure_hasType wellFormed (Core.HasType.word (value := fellThrough))

/-- Actual accepted function lowering preserves a supplied finite source
outcome. Fallthrough, return, escaped control and semantic faults retain their
separate boundary meanings. Fuel exhaustion is never a completed result. -/
theorem lowerStatements_source_run_preserves
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context finalContext : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason escapedReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerStatementsWithReasons fuel compilation source scope statements type reasonAt fellThroughReason escapedReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (execution : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap statements finalContext outcome after) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LanguageResult.resultType type) ∧
    ∃ result finalStore finalMapping finalWorld required,
      FinishedOutcomeRepresents program evidence source reasonAt type fellThroughReason escapedReason outcome result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
      GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore ∧
      (∀ runtimeFuel, required ≤ runtimeFuel → Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ∧
      (∀ runtimeFuel actual actualStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) := by
  obtain ⟨flow, same, tree⟩ := tree_of_lowerStatements aligned unique accepted
  change code = Core.LocalControl.finish type (Core.LocalLoop.toControl type flow escapedReason) (fallback type fellThroughReason) at same
  subst code
  refine ⟨Core.infer_complete (finish_hasType tree wellFormed administrativeContext fellThroughReason), ?_⟩
  cases execution with
  | control execution =>
    obtain ⟨result, finalStore, finalMapping, finalWorld, related, evaluated, finalHeaps, maps, worlds, frame⟩ :=
      tree.source_success unique program evidence wellFormed environments heaps (canonical_layout environments) execution
    simp only [Core.Expr.rename_id] at evaluated
    obtain ⟨finished, related, finishedEval⟩ := finish_success related evaluated fellThroughReason escapedReason
    obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel finishedEval
    refine ⟨finished, finalStore, finalMapping, finalWorld, required, .control related, finalHeaps, maps, worlds, frame, completes, ?_⟩
    intro runtimeFuel actual actualStore completed
    exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) finishedEval
  | fault fault =>
    obtain ⟨word, finalStore, finalMapping, finalWorld, related, evaluated, finalHeaps, maps, worlds, frame⟩ :=
      tree.source_fault unique program evidence wellFormed valid covers environments heaps (canonical_layout environments) fault
    simp only [Core.Expr.rename_id] at evaluated
    have finishedEval := Core.LocalControl.finish_failure (fallback := fallback type fellThroughReason) type
      (Core.LocalLoop.toControl_failure type escapedReason evaluated)
    obtain ⟨required, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel finishedEval
    refine ⟨_, finalStore, finalMapping, finalWorld, required, .fault related, finalHeaps, maps, worlds, frame, completes, ?_⟩
    intro runtimeFuel actual actualStore completed
    exact Core.evaluation_deterministic (Core.runStateful_evaluation_sound completed) finishedEval

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopBranchReflection
/-! Reconstruct scoped block and conditional heads from finite generated Core
executions. Child reflection contracts are structural induction hypotheses;
no independent source execution is supplied as an external premise. Lexical
environments are restored while heap, location-map and world extensions remain. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof

theorem reflects_block_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {id : StatementId} {node : StatementNode} {statements : List StatementId}
    {type : Core.Ty} {code : Core.Expr}
    (contains : ContainsStatement source id node) (form : node.form = .block statements)
    (bodyCorrect : Reflects compilation program evidence source reasonAt scope context false statements type code) :
    ScopedReflects compilation program evidence source reasonAt scope context id type code := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
    bodyCorrect wellFormed valid environments heaps layout evaluated
  refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps, worlds, frame⟩
  cases meaning with
  | control sourceBody related => exact .control (.block contains form sourceBody) related
  | fault sourceFault related => exact .fault (.block contains form sourceFault) related

theorem reflects_if_head
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {id : StatementId} {node : StatementNode} {type : Core.Ty}
    {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    {conditionCode thenCode elseCode : Core.Expr} {depth : Nat}
    (contains : ContainsStatement source id node) (form : node.form = .ifThen condition thenBody elseBody)
    (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
    (thenCorrect : Reflects compilation program evidence source reasonAt scope context false thenBody type thenCode)
    (elseCorrect : Reflects compilation program evidence source reasonAt scope context false (elseBody.getD []) type elseCode) :
    ScopedReflects compilation program evidence source reasonAt scope context id type
      (Core.LocalLoop.conditional type conditionCode thenCode elseCode) := by
  intro mapping world admin environment canonical actual actualContext ξ heap store finalStore result
    wellFormed valid environments heaps layout evaluated
  simp only [Core.LoopRenaming.conditional] at evaluated
  obtain ⟨conditionOutcome, conditionResult, sourceEvaluation, related, coreEvaluation⟩ :=
    expression_meaning conditionTree program context evidence valid environments heaps layout
  cases related with
  | uninitialized site location origin =>
    cases sourceEvaluation with
    | fault sourceFault =>
      obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated
        (Core.LocalControl.choose_failure (Core.LocalLoop.controlType type) coreEvaluation)
      exact ⟨_, heap, mapping, world, .fault (.ifCondition contains form sourceFault) (.uninitialized site location origin),
        heaps, .refl _, .refl _, .refl _ _⟩
  | value staged typed =>
    obtain ⟨boolean, rfl⟩ := PrimitiveExpressions.bool_of_type staged typed
    cases sourceEvaluation with
    | value sourceCondition =>
      obtain ⟨size, sized⟩ := evaluation_has_size evaluated
      cases boolean with
      | true =>
        obtain ⟨_, _, branch⟩ := sized.choose_true coreEvaluation
        obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
          thenCorrect wellFormed valid environments heaps (layout.insert Core.RuntimeValueHasType.bool)
            (by simpa only [rename_insert] using branch.sound)
        refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps, worlds, frame⟩
        cases meaning with
        | control sourceBody related => exact .control (.ifTrue contains form sourceCondition sourceBody) related
        | fault sourceFault related => exact .fault (.ifTrueBody contains form sourceCondition sourceFault) related
      | false =>
        obtain ⟨_, _, branch⟩ := sized.choose_false coreEvaluation
        obtain ⟨finalContext, outcome, after, finalMap, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
          elseCorrect wellFormed valid environments heaps (layout.insert Core.RuntimeValueHasType.bool)
            (by simpa only [rename_insert] using branch.sound)
        refine ⟨outcome, after, finalMap, finalWorld, ?_, finalHeaps, maps, worlds, frame⟩
        cases elseBody with
        | none =>
          cases meaning with
          | control sourceBody related =>
            cases sourceBody
            exact .control (.ifFalseWithoutElse contains form sourceCondition) related
          | fault sourceFault _ => cases sourceFault
        | some statements =>
          cases meaning with
          | control sourceBody related => exact .control (.ifFalseWithElse contains form sourceCondition sourceBody) related
          | fault sourceFault related => exact .fault (.ifFalseBody contains form sourceCondition sourceFault) related

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForStatementReflection
/-! Finite Core executions of the complete static default while/for profile
reconstruct independent finite source executions. Static-tree induction
closes all body/post/initializer contracts; repeated loop iterations use
strictly smaller finite Core derivations. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Reflection

def ReflectsPosition (compilation : SourceCorePrimitive.Context) (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (scope : SourceCoreLocalCell.Scope)
    (context : Context) (position : Position) (type : Core.Ty) (code : Core.Expr) : Prop :=
  match position with
  | .statements mode statements => Reflects compilation program evidence source reasonAt scope context mode statements type code
  | .initializers items condition post statements =>
      InitializersReflects compilation program evidence source reasonAt scope context items condition post statements type code

theorem Tree.reflects
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {position : Position} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context position type code)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    ReflectsPosition compilation program evidence source reasonAt scope context position type code := by
  induction tree with
  | nil => exact reflects_nil compilation program evidence source reasonAt _ _ _ _
  | breaking _ metadata form => exact reflects_breaking metadata.contains form
  | continuing _ metadata form => exact reflects_continuing metadata.contains form
  | returnUnit _ metadata form => exact reflects_returnUnit metadata.contains form
  | returnValue _ metadata form value => exact reflects_returnValue metadata.contains form value
  | tailExpression metadata form value => exact reflects_tailExpression metadata.contains form value
  | letUninitialized metadata form binding extension _ ih =>
      exact reflects_letUninitialized metadata.contains form binding extension ih
  | letInitialized metadata form binding extension value _ ih =>
      exact reflects_letInitialized metadata.contains form binding extension value ih
  | assign metadata form target value _ ih => exact reflects_assign metadata.contains form target value ih
  | discard metadata form notTail _ value _ ih => exact reflects_discard metadata.contains form notTail value ih
  | block metadata form _ _ bodyIH tailIH =>
      exact reflects_scoped metadata.contains (by intros; simp [form])
        (reflects_block_head metadata.contains form bodyIH) tailIH
  | ifThen metadata form condition _ _ _ thenIH elseIH tailIH =>
      exact reflects_scoped metadata.contains (by intros; simp [form])
        (reflects_if_head metadata.contains form condition thenIH elseIH) tailIH
  | whileLoop metadata form condition body _ bodyIH tailIH =>
      exact reflects_scoped metadata.contains (by intros; simp [form])
        (reflects_while_head metadata.contains form condition body.hasType bodyIH) tailIH

  | forLoop metadata form _ _ initialIH tailIH =>
      exact reflects_scoped metadata.contains (by intros; simp [form])
        (reflects_for_head metadata.contains form initialIH) tailIH
  | initializersDone condition body post bodyIH =>
      exact reflects_initializers_empty condition body.hasType bodyIH post
  | initializerUninitialized binding extension _ ih =>
      exact reflects_initializers_prepend (.letUninitialized binding extension (.nil ih))
  | initializerInitialized binding extension value _ ih =>
      exact reflects_initializers_prepend (.letInitialized binding extension value (.nil ih))
  | initializerAssign target value _ ih =>
      exact reflects_initializers_prepend (.assign target value (.nil ih))
  | initializerDiscard value _ ih =>
      exact reflects_initializers_prepend (.discard value (.nil ih))

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopFinishedReflection
/-! The function-boundary helper is inverted before reconstructing its source
flow. Fallthrough, returned values, escaped control and semantic faults retain
their distinct source outcomes. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection

open Frontend Frontend.SourceInference TypeSystem LocalCell Internal CoreProof Default

private theorem finish_success
    {type : Core.Ty} {outcome : Dynamic.ControlOutcome} {result : Core.Value}
    {environment : Core.Environment} {before after : Core.Store} {code : Core.Expr}
    (related : ControlRepresents type outcome result)
    (evaluated : Core.Evaluates environment before code result after) (fellThrough escaped : Core.Word) :
    ∃ finished, FinishedControlRepresents type fellThrough escaped outcome finished ∧
      Core.Evaluates environment before
        (Core.LocalControl.finish type (Core.LocalLoop.toControl type code escaped) (fallback type fellThrough)) finished after := by
  cases related with
  | fallthrough sourceEnv =>
    refine ⟨_, .fallthrough sourceEnv, Core.LocalControl.finish_fallthrough type
      (Core.LocalLoop.toControl_normal type escaped evaluated) ?_⟩
    by_cases unit : type = .unit
    · simp [fallback, unit, Core.LanguageResult.success, Core.Expr.weakenAt]
      exact .inRight .unit
    · simp [fallback, unit, Core.LanguageResult.failure, Core.Expr.weakenAt]
      exact .inLeft .word
  | returned value typed =>
    exact ⟨_, .returned value typed, Core.LocalControl.finish_returned type
      (Core.LocalLoop.toControl_normal type escaped evaluated)⟩
  | breaking sourceEnv =>
    exact ⟨_, .breaking sourceEnv, Core.LocalControl.finish_failure type
      (Core.LocalLoop.toControl_transfer type escaped evaluated)⟩
  | continuing sourceEnv =>
    exact ⟨_, .continuing sourceEnv, Core.LocalControl.finish_failure type
      (Core.LocalLoop.toControl_transfer type escaped evaluated)⟩


def FinishedResult (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (reasonAt : ExpressionId → Core.Word) (fellThrough escaped : Core.Word)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (statements : List StatementId) (type : Core.Ty)
    (mapping : GeneralHeap.LocationMap) (world : Core.StoreTyping) (store : Core.Store)
    (result : Core.Value) (finalStore : Core.Store) : Prop :=
  ∃ finalContext outcome after finalMapping finalWorld,
    Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before statements finalContext outcome after ∧
    FinishedOutcomeRepresents program evidence source reasonAt type fellThrough escaped outcome result ∧
    GeneralHeap.HeapRepresents finalMapping finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends mapping finalMapping ∧ Core.WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved mapping store finalMapping finalStore

/-- This wrapper requires only the structural flow induction hypothesis and
an actual finite finished Core evaluation, never a source trace. -/
theorem reflects_finished
    {compilation : SourceCorePrimitive.Context} {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {statements : List StatementId} {type : Core.Ty} {flow : Core.Expr}
    (correct : Reflects compilation program evidence source reasonAt scope context true statements type flow)
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {ξ : Core.Renaming} {heap : Dynamic.Heap} {store finalStore : Core.Store} {result : Core.Value}
    (wellFormed : Core.Ty.WellFormed [] type) (valid : PrimitiveExpressions.ContextValid compilation context)
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment canonical)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (layout : Layout world (SourceCoreLocalCell.coreContext scope) canonical actualContext actual ξ)
    (fellThrough escaped : Core.Word)
    (evaluated : Core.Evaluates actual store
      (Core.LocalControl.finish type (Core.LocalLoop.toControl type (flow.rename ξ) escaped) (fallback type fellThrough)) result finalStore) :
    FinishedResult program context evidence source reasonAt fellThrough escaped environment heap statements type mapping world store result finalStore := by
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨_, _, _, _, toControl⟩ := sized.bind_computation
  obtain ⟨_, flowStore, flowResult, _, flowEvaluation⟩ := toControl.bind_computation
  obtain ⟨finalContext, outcome, after, finalMapping, finalWorld, meaning, finalHeaps, maps, worlds, frame⟩ :=
    correct wellFormed valid environments heaps layout flowEvaluation.sound
  cases meaning with
  | control execution related =>
    obtain ⟨finished, finishedRelated, finishedEval⟩ := finish_success related flowEvaluation.sound fellThrough escaped
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated finishedEval
    exact ⟨finalContext, outcome, after, finalMapping, finalWorld, .control execution, .control finishedRelated,
      finalHeaps, maps, worlds, frame⟩
  | fault execution related =>
    have finishedEval := Core.LocalControl.finish_failure (fallback := fallback type fellThrough) type
      (Core.LocalLoop.toControl_failure type escaped flowEvaluation.sound)
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated finishedEval
    exact ⟨finalContext, _, after, finalMapping, finalWorld, .fault execution, .fault related,
      finalHeaps, maps, worlds, frame⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Reflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForStatementReflectionBridge
/-! Actual accepted default while/for lowering reflects every completed Core run
into independent source semantics. No finite source trace is assumed. Static
metadata/context validity and represented initial heap/environment delimit the
scalar/product default profile; source calls remain outside it. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference BasicStatements Reflection

theorem lowerFlowStatements_run_reflects
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasons)
      fuel source scope statements type reasonAt tailReturns selfReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store finalStore : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    {runtimeFuel : Nat} {result : Core.Value}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (completed : Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LocalLoop.resultType type) ∧
    Reflection.Result program context evidence source reasonAt tailReturns environment heap statements type mapping world store result finalStore := by
  have tree := tree_of_lowerFlowStatementsWithExpression aligned unique accepted
  have typed : Core.HasType (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code (Core.LocalLoop.resultType type) := by
    simpa only [Core.Expr.rename_id] using (tree.hasType wellFormed).rename (identity_respects scope administrativeContext)
  exact ⟨Core.infer_complete typed,
    tree.reflects program evidence wellFormed valid environments heaps (canonical_layout environments)
      (by simpa only [Core.Expr.rename_id] using Core.runStateful_evaluation_sound completed)⟩

/-- Every completed result of actual accepted function lowering constructs a
finite source function trace with matching result, mapped cells and untouched
administrative cells. The theorem does not accept fuel exhaustion as done. -/
theorem lowerStatements_run_reflects
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason escapedReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerStatementsWithReasons fuel compilation source scope statements type reasonAt fellThroughReason escapedReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store finalStore : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    {runtimeFuel : Nat} {result : Core.Value}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (completed : Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) :
    FinishedResult program context evidence source reasonAt fellThroughReason escapedReason environment heap statements type mapping world store result finalStore := by
  obtain ⟨flow, same, tree⟩ := tree_of_lowerStatements aligned unique accepted
  change code = Core.LocalControl.finish type (Core.LocalLoop.toControl type flow escapedReason) (Default.fallback type fellThroughReason) at same
  subst code
  apply reflects_finished (tree.reflects program evidence) wellFormed valid environments heaps
    (canonical_layout environments) fellThroughReason escapedReason
  simpa only [Core.Expr.rename_id] using Core.runStateful_evaluation_sound completed


end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ForStatementCorrespondence
/-! Finite completion equivalence for the actual accepted default while/for
compiler. Forward preservation retains all source outcomes and represented
state; reverse reflection constructs a source trace from Core completion only.
Fuel exhaustion remains a suspended computation, not a completed outcome. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference BasicStatements Reflection

/-- Finite completion is equivalent at the accepted function boundary. The
source side includes its specified semantic faults. Neither side treats a
fuel-exhausted checkpoint as a completed execution. -/
theorem lowerStatements_finite_iff
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason escapedReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLoops.lowerStatementsWithReasons fuel compilation source scope statements type reasonAt fellThroughReason escapedReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    (∃ runtimeFuel result finalStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ↔
    (∃ finalContext outcome after, Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap statements finalContext outcome after) := by
  constructor
  · rintro ⟨runtimeFuel, result, finalStore, completed⟩
    obtain ⟨finalContext, outcome, after, _, _, execution, _⟩ :=
      lowerStatements_run_reflects aligned unique accepted wellFormed valid environments heaps completed
    exact ⟨finalContext, outcome, after, execution⟩
  · rintro ⟨finalContext, outcome, after, execution⟩
    obtain ⟨_, result, finalStore, _, _, required, _, _, _, _, _, completes, _⟩ :=
      lowerStatements_source_run_preserves aligned unique accepted wellFormed valid covers environments heaps execution
    exact ⟨required, result, finalStore, completes required (Nat.le_refl _)⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopStatementReflection
/-! Finite Core executions of the complete static default while profile
reconstruct independent finite source executions. Static-tree induction
closes all body contracts; repeated while iterations use the strictly smaller
finite derivation established in `LoopFiniteReflection`. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Default

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements Reflection

theorem Tree.reflects
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {mode : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context mode statements type code)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) :
    Reflects compilation program evidence source reasonAt scope context mode statements type code := by
  induction tree with
  | nil => exact reflects_nil compilation program evidence source reasonAt _ _ _ _
  | breaking _ metadata form => exact reflects_breaking metadata.contains form
  | continuing _ metadata form => exact reflects_continuing metadata.contains form
  | returnUnit _ metadata form => exact reflects_returnUnit metadata.contains form
  | returnValue _ metadata form value => exact reflects_returnValue metadata.contains form value
  | tailExpression metadata form value => exact reflects_tailExpression metadata.contains form value
  | letUninitialized metadata form binding extension _ ih =>
      exact reflects_letUninitialized metadata.contains form binding extension ih
  | letInitialized metadata form binding extension value _ ih =>
      exact reflects_letInitialized metadata.contains form binding extension value ih
  | assign metadata form target value _ ih => exact reflects_assign metadata.contains form target value ih
  | discard metadata form notTail _ value _ ih => exact reflects_discard metadata.contains form notTail value ih
  | block metadata form _ _ bodyIH tailIH =>
      exact reflects_scoped metadata.contains (by intros; simp [form])
        (reflects_block_head metadata.contains form bodyIH) tailIH
  | ifThen metadata form condition _ _ _ thenIH elseIH tailIH =>
      exact reflects_scoped metadata.contains (by intros; simp [form])
        (reflects_if_head metadata.contains form condition thenIH elseIH) tailIH
  | whileLoop metadata form condition body _ bodyIH tailIH =>
      exact reflects_scoped metadata.contains (by intros; simp [form])
        (reflects_while_head metadata.contains form condition body.hasType bodyIH) tailIH

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Default
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopStatementReflectionBridge
/-! Actual accepted default while lowering reflects every completed Core run
into independent source semantics. No finite source trace is assumed. Static
metadata/context validity and represented initial heap/environment delimit the
scalar/product default profile; for-loops and source calls remain outside it. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Default

open Frontend Frontend.SourceInference BasicStatements Reflection

private theorem identity_respects (scope : SourceCoreLocalCell.Scope) (administrativeContext : Core.Context) :
    Core.Renaming.Respects Core.Renaming.id (SourceCoreLocalCell.coreContext scope)
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) := by
  intro index foundType found
  change (SourceCoreLocalCell.coreContext scope ++ administrativeContext)[index]? = some foundType
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem canonical_layout
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment) :
    Layout world (SourceCoreLocalCell.coreContext scope) coreEnvironment
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext) coreEnvironment Core.Renaming.id :=
  ⟨identity_respects scope administrativeContext, fun found => found, environments.runtime_hasTypes⟩


theorem lowerFlowStatements_run_reflects
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {tailReturns : Bool} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source) (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel compilation source scope id reasons)
      fuel source scope statements type reasonAt tailReturns selfReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store finalStore : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    {runtimeFuel : Nat} {result : Core.Value}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (completed : Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) :
    Core.infer? (SourceCoreLocalCell.coreContext scope ++ administrativeContext) code = some (Core.LocalLoop.resultType type) ∧
    Reflection.Result program context evidence source reasonAt tailReturns environment heap statements type mapping world store result finalStore := by
  have tree := tree_of_lowerFlowStatementsWithExpression aligned unique noFor accepted
  exact ⟨Core.infer_complete (tree.hasType_with_administrative wellFormed administrativeContext),
    tree.reflects program evidence wellFormed valid environments heaps (canonical_layout environments)
      (by simpa only [Core.Expr.rename_id] using Core.runStateful_evaluation_sound completed)⟩

/-- Every completed result of actual accepted function lowering constructs a
finite source function trace with matching result, mapped cells and untouched
administrative cells. The theorem does not accept fuel exhaustion as done. -/
theorem lowerStatements_run_reflects
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason escapedReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source) (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerStatementsWithReasons fuel compilation source scope statements type reasonAt fellThroughReason escapedReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store finalStore : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    {runtimeFuel : Nat} {result : Core.Value}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (completed : Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) :
    FinishedResult program context evidence source reasonAt fellThroughReason escapedReason environment heap statements type mapping world store result finalStore := by
  obtain ⟨flow, same, tree⟩ := tree_of_lowerStatements aligned unique noFor accepted
  change code = Core.LocalControl.finish type (Core.LocalLoop.toControl type flow escapedReason) (fallback type fellThroughReason) at same
  subst code
  apply reflects_finished (tree.reflects program evidence) wellFormed valid environments heaps
    (canonical_layout environments) fellThroughReason escapedReason
  simpa only [Core.Expr.rename_id] using Core.runStateful_evaluation_sound completed


/-- Finite completion is equivalent at the accepted function boundary. The
source side includes its specified semantic faults. Neither side treats a
fuel-exhausted checkpoint as a completed execution. -/
theorem lowerStatements_finite_iff
    {fuel : Nat} {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {statements : List StatementId} {type : Core.Ty}
    {reasonAt : ExpressionId → Core.Word} {fellThroughReason escapedReason : Core.Word} {code : Core.Expr}
    (aligned : ScopeContextAligned scope context) (unique : NodeOccurrencesUnique source) (noFor : NoForLoops source)
    (accepted : SourceCoreLoops.lowerStatementsWithReasons fuel compilation source scope statements type reasonAt fellThroughReason escapedReason = .ok code)
    (wellFormed : Core.Ty.WellFormed [] type) {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {coreEnvironment : Core.Environment} {store : Core.Store} {world : Core.StoreTyping}
    {mapping : GeneralHeap.LocationMap} {administrativeContext : Core.Context}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store) :
    (∃ runtimeFuel result finalStore, Core.runStateful runtimeFuel (.initial code coreEnvironment store) = .done result finalStore) ↔
    (∃ finalContext outcome after, Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment heap statements finalContext outcome after) := by
  constructor
  · rintro ⟨runtimeFuel, result, finalStore, completed⟩
    obtain ⟨finalContext, outcome, after, _, _, execution, _⟩ :=
      lowerStatements_run_reflects aligned unique noFor accepted wellFormed valid environments heaps completed
    exact ⟨finalContext, outcome, after, execution⟩
  · rintro ⟨finalContext, outcome, after, execution⟩
    obtain ⟨_, result, finalStore, _, _, required, _, _, _, _, _, completes, _⟩ :=
      lowerStatements_source_run_preserves aligned unique noFor accepted wellFormed valid covers environments heaps execution
    exact ⟨required, result, finalStore, completes required (Nat.le_refl _)⟩

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Default
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.LoopTerminalBodies
/-! Discharge the finite-loop body induction hypothesis for terminal bodies.
The code contains no generated closure, so its temporary lexical prefix can
be inserted exactly using the restricted expression-renaming theorem. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Internal

open Frontend Frontend.SourceInference TypeSystem LocalCell

private theorem shiftBody {code : Core.Expr} (restricted : Core.ReadOnly.Expression code)
    {environment : Core.Environment} {before after : Core.Store} {result : Core.Value}
    (evaluation : Core.Evaluates environment before code result after)
    (type : Core.Ty) (location : Core.Location) :
    Core.Evaluates (Core.LoopExecution.bodyEnvironment type location environment) before
      (Core.LoopExecution.bodyCode code) result after :=
  ((restricted.weakenAt 0).weakenAt 0).evaluation_weakenAt_zero
    ((restricted.weakenAt 0).evaluation_weakenAt_zero
      (restricted.evaluation_weakenAt_zero evaluation
        (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType type)) location)) .unit) (.bool true)

theorem breaking_body_preserves
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {type : Core.Ty} {location : Core.Location} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node) (form : node.form = .breakStmt) :
    BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
      type location (id :: rest) (Core.LocalLoop.breaking type) := by
  intro mapping world heap after store finalContext outcome environments heaps actualTyped selfTyped execution
  rcases ScalarStatementViews.cons_view false unique contains (by simp) execution with
    ⟨_, _, _, head, _⟩ | ⟨head, _⟩
  · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head
    cases impossible
  · obtain ⟨rfl, rfl, rfl⟩ := ScalarStatementViews.breaking unique contains form head
    refine ⟨_, store, mapping, world, .breaking environment, ?_, heaps, .refl _, .refl _, .refl _ _⟩
    exact shiftBody (.inRight (.inRight (.inLeft .unit)))
      (Core.LocalLoop.breaking_evaluates type actual store) type location

theorem breaking_body_fault_preserves
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Core.Environment} {actualContext : Core.Context}
    {type : Core.Ty} {location : Core.Location} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {reasonAt : ExpressionId → Core.Word}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node) (form : node.form = .breakStmt) :
    BodyFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
      type location (id :: rest) (Core.LocalLoop.breaking type) reasonAt := by
  intro mapping world heap after store finalContext reason environments heaps actualTyped selfTyped execution
  rcases ScalarStatementViews.cons_fault_view false unique contains (by simp) execution with
    ⟨_, head⟩ | ⟨_, _, _, head, _⟩
  · exact False.elim (ScalarStatementViews.breaking_cannot_fault unique contains form head)
  · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique contains form head
    cases impossible

private theorem return_readOnly {type : Core.Ty} {value : Core.Expr}
    (restricted : Core.ReadOnly.Expression value) : Core.ReadOnly.Expression (Core.LocalLoop.returnValue type value) :=
  .caseE restricted (.inLeft .var) (.inRight (.inLeft (.inRight .var)))

theorem return_body_preserves
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {administrativeContext : Core.Context} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
    {type : Core.Ty} {location : Core.Location} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {reasonAt : ExpressionId → Core.Word} {expression : ExpressionId} {valueCode : Core.Expr} {depth : Nat}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt (some expression))
    (value : PrimitiveExpressions.Tree compilation source scope reasonAt expression type valueCode depth)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual) :
    BodyPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
      type location (id :: rest) ((Core.LocalLoop.returnValue type valueCode).rename ξ) := by
  intro mapping world heap after store finalContext outcome environments heaps actualTyped selfTyped execution
  rcases ScalarStatementViews.cons_view false unique contains (by simp) execution with
    ⟨_, _, _, head, _⟩ | ⟨head, _⟩
  · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head
    cases impossible
  · obtain ⟨rfl, sourceValue, rfl, evaluated⟩ := ScalarStatementViews.returnValue unique contains form head
    obtain ⟨rfl, staged, rfl, typed, core⟩ := ScalarExpressionReflection.Primitive.source_success value unique environments heaps evaluated
    have restricted := return_readOnly (type := type) (GeneralExpressions.Primitive.readOnly value)
    have renamed := restricted.evaluation_rename (Core.LocalLoop.returnValue_success type core) agree
    exact ⟨_, store, mapping, world, .returned staged typed,
      shiftBody (restricted.rename ξ) renamed type location, heaps, .refl _, .refl _, .refl _ _⟩

theorem return_body_fault_preserves
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {administrativeContext : Core.Context} {environment : Dynamic.Environment}
    {canonical actual : Core.Environment} {actualContext : Core.Context} {ξ : Core.Renaming}
    {type : Core.Ty} {location : Core.Location} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {reasonAt : ExpressionId → Core.Word} {expression : ExpressionId} {valueCode : Core.Expr} {depth : Nat}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt (some expression))
    (value : PrimitiveExpressions.Tree compilation source scope reasonAt expression type valueCode depth)
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    (agree : Core.ReadOnly.EnvironmentsAgree ξ canonical actual) :
    BodyFaultPreserves program context evidence source scope administrativeContext environment canonical actual actualContext
      type location (id :: rest) ((Core.LocalLoop.returnValue type valueCode).rename ξ) reasonAt := by
  intro mapping world heap after store finalContext reason environments heaps actualTyped selfTyped execution
  rcases ScalarStatementViews.cons_fault_view false unique contains (by simp) execution with
    ⟨_, head⟩ | ⟨_, _, _, head, _⟩
  · have fault := ScalarStatementViews.returnValue_fault unique contains form head
    obtain ⟨rfl, site, sourceLocation, rfl, origin, core⟩ :=
      ScalarExpressionReflection.Primitive.source_fault value unique valid covers environments heaps fault
    have restricted := return_readOnly (type := type) (GeneralExpressions.Primitive.readOnly value)
    have renamed := restricted.evaluation_rename (Core.LocalLoop.returnValue_failure type core) agree
    exact ⟨_, store, mapping, world, .uninitialized site sourceLocation origin,
      shiftBody (restricted.rename ξ) renamed type location, heaps, .refl _, .refl _, .refl _ _⟩
  · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head
    cases impossible

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Internal
end

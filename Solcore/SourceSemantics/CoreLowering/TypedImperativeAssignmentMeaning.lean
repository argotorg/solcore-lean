import Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementHeadMeaning
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileComposition

/-! Ordinary assignment heads compose with transfer-aware continuations.
The continuation contracts are intermediate induction hypotheses; the public
recursive tree discharges them using its concrete children. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperative
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open TypedLexicalWhile (Preserves Reflects FlowRep)
open TypedScopedStatements (Executes source_view prepend head_fault)

variable {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations values.checked.catalog functions identities)

include extension uninitialized missing faithful observations in
theorem assignment_preserves {mode : Bool} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {body : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (head : CompatibleAssignmentStatements.Head readFuel values source context solved reasonAt scope administrative ambient.definitions assignment operator rhs)
    (headErrors : head.Errors registry faults)
    (unique : NodeOccurrencesUnique source)
    (continuationMeaning : Preserves (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode rest expected type body) :
    Preserves (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome resultContext environments heaps locals agrees actualTyped reference read unmapped trace
  have go {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
      (first : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough next) middle)
      (tail : Executes mode program middleContext evidence source next middle rest resultContext outcome after) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
        FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
        HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
          context scope environment resultContext after := by
    obtain ⟨rfl, same, updated, assigned⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
    cases same
    obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩ :=
      head.preserves_prefix functions extension program evidence valid unique uninitialized missing faithful observations
        environments heaps locals agrees actualTyped assigned
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
      continuationMeaning valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
        ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 tail
    exact ⟨value, finalStore, finalMap, finalWorld,
      (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
      represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) executed with
      ⟨_, _, _, first, tail⟩ | ⟨first, terminal⟩
    · exact go first (by cases mode <;> exact .control tail)
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
      cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) failed with
      ⟨rfl, first⟩ | ⟨_, _, _, first, tail⟩
    · have assigned := ScalarStatementViews.assignValue_fault unique (lookupStatement?_sound found) form first
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
        head.preserves_fault functions extension program evidence valid unique uninitialized missing faithful observations
          environments heaps locals agrees actualTyped headErrors assigned body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · exact go first (by cases mode <;> exact .fault tail)

include extension uninitialized missing faithful observations in
theorem assignment_reflects (functionTypes : FunctionRuntimeViews functions)
    {mode : Bool} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {body : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (head : CompatibleAssignmentStatements.Head readFuel values source context solved reasonAt scope administrative ambient.definitions assignment operator rhs)
    (headErrors : head.Errors registry faults)
    (unique : NodeOccurrencesUnique source)
    (continuationMeaning : Reflects (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode rest expected type body) :
    Reflects (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped evaluated
  rcases head.reflects functions extension program evidence valid unique uninitialized missing faithful observations
    environments heaps locals agrees actualTyped functionTypes headErrors evaluated with
    ⟨reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, frame, metadata⟩ |
    ⟨updated, middle, written, middleMap, middleWorld, slots, trace, middleHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
  · exact ⟨context, .fault reason, after, finalMap, finalWorld,
      head_fault mode rest (.assignValue (lookupStatement?_sound found) form trace), .fault matched,
      finalHeaps, maps, worlds, frame, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  · obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
      continuationMeaning valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
        ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
    exact ⟨resultContext, outcome, after, finalMap, finalWorld,
      prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignValue (lookupStatement?_sound found) form trace) tailTrace,
      represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩

end Solcore.SourceSemantics.CoreLowering.TypedImperative

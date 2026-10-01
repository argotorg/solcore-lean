import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementMeaning
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileComposition

/-! Bare unary heads compose with transfer-aware continuations.
The continuation contracts are intermediate induction hypotheses; the public
recursive tree discharges them using its concrete children. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open TypedLexicalWhile (Preserves Reflects FlowRep)
open TypedScopedStatements (Executes source_view prepend head_fault)

private theorem statement_shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

section Views
variable {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {outcome : Dynamic.ControlOutcome}
  (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
include unique contains

theorem bitNot_view {assignment : AssignmentResolution} (form : node.form = .assignBitNot assignment)
    (evaluated : Dynamic.StatementExecutes program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ outcome = .fallthrough environment ∧ ∃ updated,
      Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
        environment before assignment.target updated after := by
  have shape := statement_shape unique contains form
  clear contains form
  cases evaluated <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, by assumption⟩

theorem bitNot_fault {assignment : AssignmentResolution} {reason : Dynamic.SemanticFault}
    (form : node.form = .assignBitNot assignment)
    (fault : Dynamic.StatementFaults program context evidence source environment before id reason after) :
    Dynamic.SourcePlaceBitNotFaults program context evidence source environment before assignment.target reason after := by
  have shape := statement_shape unique contains form
  have present : ¬ Dynamic.StatementMissing source id := fun absent => Dynamic.StatementAbsentIn.excludes_contains absent contains
  clear contains form
  cases fault
  all_goals first
    | exact False.elim (present (by assumption))
    | have actualForm := shape _ (by assumption); simp_all
end Views

variable {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {solved : List SolvedRequirement}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop}
  (observations : FunctionObservations values.checked.catalog functions identities)

include observations in
theorem assignment_preserves {mode : Bool} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {body : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (head : Head context scope assignment)
    (headErrors : head.Errors faults)
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
    obtain ⟨rfl, same, updated, assigned⟩ := bitNot_view unique (lookupStatement?_sound found) form first
    cases same
    obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩ :=
      head.preserves_prefix functions program evidence observations
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
    · obtain ⟨_, rfl, _⟩ := bitNot_view unique (lookupStatement?_sound found) form first
      cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) failed with
      ⟨rfl, first⟩ | ⟨_, _, _, first, tail⟩
    · have assigned := bitNot_fault unique (lookupStatement?_sound found) form first
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
        head.preserves_fault functions program evidence observations
          environments heaps locals agrees headErrors assigned body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame, metadata,
        _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · exact go first (by cases mode <;> exact .fault tail)

include observations in
theorem assignment_reflects
    {mode : Bool} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution}
    {rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {body : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (head : Head context scope assignment)
    (headErrors : head.Errors faults)
    (_unique : NodeOccurrencesUnique source)
    (continuationMeaning : Reflects (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode rest expected type body) :
    Reflects (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) (source := source) (context := context) (registry := registry) functions program evidence (solved := solved) (faults := faults) mode (id :: rest) expected type (head.emit body (LocalLoop.controlType type)) := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped evaluated
  rcases head.reflects functions program evidence observations
    environments heaps locals agrees actualTyped headErrors evaluated with
    ⟨reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, frame, metadata⟩ |
    ⟨updated, middle, written, middleMap, middleWorld, slots, trace, middleHeaps, maps, worlds, frame, metadata, count, typed, continuation⟩
  · exact ⟨context, .fault reason, after, finalMap, finalWorld,
      head_fault mode rest (.assignBitNot (lookupStatement?_sound found) form trace), .fault matched,
      finalHeaps, maps, worlds, frame, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
  · obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
      continuationMeaning valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
        ((frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (frame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
    exact ⟨resultContext, outcome, after, finalMap, finalWorld,
      prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignBitNot (lookupStatement?_sound found) form trace) tailTrace,
      represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata, lexical⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatements

import Solcore.SourceSemantics.CoreLowering.GenericImperativeForEndpoint
import Solcore.SourceSemantics.CoreLowering.ForSourceViews

/-! Header effects precede the installed loop. These composition lemmas are
used inside concrete statement-tree induction: their endpoint propositions
are proved from the recursive body, never stored in the compiler certificate.
The outer lexical environment is restored without discarding header cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedImperativeFor (LoopPreserves LoopReflects)
open TypedLexicalWhile (Scope ValuesContext HeadPreserves HeadReflects restored restore_rep)

variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  {context : SourceSemantics.Context} {scope : Scope} {id : StatementId} {node : StatementNode}
  {items post : List ForItemForm} {condition : ExpressionId} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

abbrev PreservingHeader (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => LoopPreserves functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (administrative := administrative) condition post statements expected type code) context scope items code,
    GenericForHeader.Tree.Errors registry faults tree

abbrev ReflectingHeader (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => LoopReflects functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults) (solved := solved) (frameLayout := frameLayout)
      (globals := globals) (administrative := administrative) condition post statements expected type code) context scope items code,
    GenericForHeader.Tree.Errors registry faults tree

include definitions registered extension meaning faithful observations in
theorem header_preserves (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : PreservingHeader (certificates := certificates) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frameLayout := frameLayout) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
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
      header.preserves_prefix functions definitions registered extension program evidence meaning faithful observations
        valid environments heaps locals agrees actualTyped reference read unmapped initialization
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩ :=
      tail.certificate tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped (.control loop)
    exact ⟨rfl, restored environment loopOutcome, value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
      restore_rep represented environment, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
      frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2⟩
  | fault failed =>
    rcases ForSourceViews.fault unique (lookupStatement?_sound found) form failed with initialFailure | loopFailure
    · obtain ⟨_, fault⟩ := initialFailure
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, frame, metadata⟩ :=
        header.preserves_fault functions definitions registered extension program evidence meaning faithful observations errors
          valid environments heaps locals agrees actualTyped reference read unmapped fault
      exact ⟨rfl, (by intro next impossible; cases impossible), _, finalStore, finalMap, finalWorld,
        evaluated, .fault matched, heaps, maps, worlds, frame, metadata⟩
    · obtain ⟨loopContext, loopEnvironment, initialized, initialization, loop⟩ := loopFailure
      obtain ⟨tail, maps, worlds, frame, metadata, agreement⟩ :=
        header.preserves_prefix functions definitions registered extension program evidence meaning faithful observations
          valid environments heaps locals agrees actualTyped reference read unmapped initialization
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, progress⟩ :=
        tail.certificate tail.valid tail.environments tail.heaps tail.locals tail.agrees tail.actualTyped tail.reference tail.read tail.unmapped (.fault loop)
      exact ⟨rfl, (by intro next impossible; cases impossible), value, finalStore, finalMap, finalWorld, agreement.wrap evaluated,
        represented, progress.1, maps.trans progress.2.1, worlds.trans progress.2.2.1,
        frame.trans progress.2.2.2.1, metadata.trans progress.2.2.2.2⟩

include definitions registered extension meaning reflection faithful observations in
theorem header_reflects (functionTypes : FunctionRuntimeViews functions) (_unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (headers : ReflectingHeader (certificates := certificates) functions program evidence (layouts := layouts) (owner := owner) (active := active)
      (frameLayout := frameLayout) (globals := globals) (onError := onError)
      (source := source) (solved := solved) (administrative := administrative)
      (registry := registry) (faults := faults) context scope items condition post statements expected type code) :
    HeadReflects functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (solved := solved) (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) id expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped evaluated
  obtain ⟨header, errors⟩ := headers
  have result := header.reflects functions definitions registered extension program evidence meaning reflection faithful observations functionTypes errors
    valid environments heaps locals agrees actualTyped reference read unmapped evaluated
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

end Solcore.SourceSemantics.CoreLowering.GenericImperativeFor

import Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.Owned.mk
#check_failure Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.ViewStep.mk
#check_failure Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.Cache.mk

/-! Two reads with identical closed types, dictionaries and target descriptors
still retain different actual requirement IDs in a nested lambda's source.
The fixture uses actual checked/compiler-owned metadata. It proves no native
frame history or complete unbounded ancestry cache. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryMetadata
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
abbrev MetadataState := Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def w (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type WordFunction = function(Word) returns (Word);",
    "function keep<T>(item: T) returns (T) where T: Mark { return item; }",
    "function pair() returns (WordFunction, WordFunction) {",
    " let outer = lam(value) { keep(value);",
    "   let inner: WordFunction = lam(item: Word) -> Word { return item; }; return inner; };",
    " return (outer(1), outer(2)); }"
  ]}] }

private def artifact (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let signature ← match program.signatures.functions.filter (·.name == "pair") with
    | [signature] => pure signature
    | _ => throw (IO.userError "ancestry fixture missing pair")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"ancestry worklist failed: {reprStr result}")
  get "ancestry compatible artifact" (SourceCoreCompatibleFunctions.prepare program plan 512)

private def requiredState {checked : Checked} {base : Base checked} {owned : Owned base}
    {frame : ContextFrame} (result : {state : Option MetadataState // Authenticates owned frame state}) : IO MetadataState :=
  match result.val with | some state => pure state | none => throw (IO.userError "ancestry lost its source")

example (function : Solcore.SourceSemantics.Dynamic.GeneralizedClosure) (substitution : Substitution)
    (evidence : Solcore.SourceSemantics.Dynamic.EvidenceEnvironment) (witnesses : List Witness) :
    eraseRequirements (SourceTypedRuntime.rewriteLocalRequirements witnesses
      (function.source.applySubstitution substitution)) =
      eraseRequirements (function.instantiate substitution evidence).source :=
  dynamic_instantiate_erased function substitution evidence witnesses

example {checked : Checked} {base : Base checked} {owned : Owned base} {frame : ContextFrame}
    {state : MetadataState} (authenticated : Authenticates owned frame (some state)) :
    ∃ (id : Core.Word) (named : Named owned id), SourceRecipe named.state.source state.source := authenticated.recipe

example (canonical source : TypedSource) (alphabet : List RequirementId)
    (erased : eraseRequirements source = eraseRequirements canonical)
    (lengths : (requirementProfile source).map List.length = (requirementProfile canonical).map List.length)
    (bounded : ∀ spine ∈ requirementProfile source, ∀ id ∈ spine, id ∈ alphabet) :
    requirementProfile source ∈ FiniteProfiles.profiles alphabet ((requirementProfile canonical).map List.length) :=
  (FiniteProfiles.source_profile_bound canonical source alphabet erased lengths bounded).1

private def rejected {checked : Checked} {base : Base checked} (owned : Owned base) (frame : ContextFrame) : IO Unit :=
  match prepareFrame owned frame with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"forged ancestry metadata accepted: {reprStr frame}")

def run : IO Unit := do
  let program ← get "ancestry source checker" (checkProgram workspace)
  let artifact ← artifact program
  let base := artifact.prepared
  let owned ← get "ancestry owned tables" (prepare base)
  let reads := owned.views.entries.filter (·.view.principal.binder.name == "outer")
  let (left, right) ← match reads with
    | [left, right] => pure (left, right)
    | _ => throw (IO.userError "expected two exact outer reads")
  assertTrue (decide (left.view.ownSubstitution = right.view.ownSubstitution) &&
    decide (left.view.reference.original.rawType = right.view.reference.original.rawType))
    "fixture no longer uses two equal native/source types"
  let leftIds := left.view.ownWitnesses.map (·.actualRequirement)
  let rightIds := right.view.ownWitnesses.map (·.actualRequirement)
  assertTrue (!leftIds.isEmpty && decide (leftIds ≠ rightIds)) "fixture merged occurrence-specific requirement IDs"
  assertTrue (reprStr (left.view.ownWitnesses.map (·.evidence)) == reprStr (right.view.ownWitnesses.map (·.evidence)))
    "fixture should share dictionaries while retaining distinct requirement IDs"
  let owner := left.view.owner
  let named ← match owned.callable.table.idAt? (.named owner) with
    | some named => pure named | none => throw (IO.userError "owned named origin missing")
  let target ← match owned.callable.table.idAt? (.lambda owner left.view.principal.initializer left.view.cumulative) with
    | some target => pure target | none => throw (IO.userError "owned outer lambda target missing")
  let innerView ← match owned.views.entries.find? (·.view.principal.binder.name == "inner") with
    | some entry => pure entry | none => throw (IO.userError "owned inner lambda metadata missing")
  let inner ← match owned.callable.table.idAt? (.lambda owner innerView.view.principal.initializer left.view.cumulative) with
    | some inner => pure inner | none => throw (IO.userError "owned nested lambda target missing")
  let leftView : ContextFrame := .view left.id target (.named named)
  let rightView : ContextFrame := .view right.id target (.named named)
  let leftFrame : ContextFrame := .lambda inner (.lambda target leftView)
  let rightFrame : ContextFrame := .lambda inner (.lambda target rightView)
  let leftPrepared ← get "left nested ancestry" (prepareFrame owned leftFrame)
  let rightPrepared ← get "right nested ancestry" (prepareFrame owned rightFrame)
  let leftState ← requiredState leftPrepared
  let rightState ← requiredState rightPrepared
  assertTrue (decide (leftState.active = rightState.active) &&
    decide (eraseRequirements leftState.source = eraseRequirements rightState.source))
    "equal type contexts changed metadata beyond requirement IDs"
  assertTrue (decide (leftState.source ≠ rightState.source))
    "same-type read views collapsed the nested lambda's retained source"
  let leftPrincipal ← get "left dynamic principal" (preparePrincipal owned leftState innerView.view.binding.binder.id)
  let rightPrincipal ← get "right dynamic principal" (preparePrincipal owned rightState innerView.view.binding.binder.id)
  assertTrue (decide (leftPrincipal.entry.principal.declaration = rightPrincipal.entry.principal.declaration) &&
    decide (leftPrincipal.node.form = rightPrincipal.node.form)) "dynamic ancestry changed the cached principal declaration/header"
  let expectedLeft := SourceTypedRuntime.rewriteLocalRequirements left.view.ownWitnesses
    (left.view.principal.source.applySubstitution left.view.ownSubstitution)
  let expectedRight := SourceTypedRuntime.rewriteLocalRequirements right.view.ownWitnesses
    (right.view.principal.source.applySubstitution right.view.ownSubstitution)
  assertTrue (decide (leftState.source = expectedLeft) && decide (rightState.source = expectedRight))
    "transported ancestry did not retain the exact principal-source recipe"
  let differences := leftState.source.nodes.filterMap fun
    | .expression node => match rightState.source.lookupExpression? node.id with
      | some other => if node.requirements != other.requirements then some node.id else none
      | none => none
    | _ => none
  assertTrue (!differences.isEmpty) "fixture has no actual expression requirement difference"
  let alphabet := (requirementProfile left.view.principal.originalSource).flatten.eraseDups
  assertTrue ((requirementProfile leftState.source).map List.length ==
    (requirementProfile rightState.source).map List.length)
    "view transport changed requirement spine lengths"
  assertTrue ([leftState.source, rightState.source].all fun source =>
    (requirementProfile source).all fun spine => spine.all alphabet.contains)
    "view transport invented a requirement ID outside the original source alphabet"
  let cache ← get "finite ancestry cache" (prepareCache owned [.empty, leftFrame, rightFrame])
  for frame in [leftFrame, rightFrame] do
    assertTrue ((cache.lookup? frame).isSome) "cache lost a prepared source view"
  assertTrue ((cache.lookup? (.lambda target leftFrame)).isNone)
    "finite cache silently treated an unprepared history as prepared"
  rejected owned (.view left.id inner (.named named))
  rejected owned (.lambda target .empty)
  rejected owned (.named target)
  rejected owned (.view (w 999999) target (.named named))
  rejected owned (.lambda (w 999999) (.named named))
  IO.println "owned ancestry metadata: equal types/dictionaries, distinct read requirement IDs and cached nested sources GREEN"
end Tests.SourceCoreCallableAncestryMetadata

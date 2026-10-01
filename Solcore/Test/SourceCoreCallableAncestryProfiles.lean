import Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Universal factory/ancestry invariants and a checked qualified-local
fixture. Repeated lambda ancestry changes the finite frame, while retaining
the same occurrence profile. No cache-completeness assertion is made here. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryProfiles
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
open Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles

example {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceCompilationPlan.EvidenceEnvironment} {binder : TypedBinder} {node : ExpressionNode}
    {substitution : Substitution} {witnesses : List Witness}
    (accepted : SourceCompilationPlan.localRequirementWitnesses caller available binder node = .ok (substitution, witnesses)) :
    ∀ witness ∈ witnesses, witness.actualRequirement ∈ node.requirements := witnesses_actual_subset accepted

example {checked : Checked} {base : Base checked} {owned : Owned base}
    {frame : ContextFrame} {state : Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State}
    (authenticated : Authenticates owned frame (some state)) :
    ∃ (id : Core.Word) (named : Named owned id), state.owner = named.state.owner ∧
      Bounded (alphabet named.state.source) state.source ∧
      (requirementProfile state.source).map List.length = (requirementProfile named.state.source).map List.length :=
  Authenticates.original_bound authenticated

example {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target}
    {before : Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State}
    (step : ViewStep view before) {canonical : TypedSource}
    (beforeCanonical : eraseRequirements before.source = eraseRequirements canonical) :
    step.after.owner = view.entry.view.owner ∧ step.after.active = view.entry.view.cumulative ∧
      eraseRequirements step.after.source = eraseRequirements (canonical.applySubstitution view.entry.view.ownSubstitution) :=
  ViewStep.canonical step beforeCanonical

private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "function keep<T>(item: T) returns (T) where T: Mark { return item; }",
    "function main() returns (Word) {",
    " let f = lam(value) { keep(value); return value; }; return f(1); }"
  ]}] }

def run : IO Unit := do
  let program ← get "profile fixture checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "main") with
    | some signature => pure signature | none => throw (IO.userError "profile fixture main missing")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"profile worklist: {reprStr result}")
  let artifact ← get "profile artifact" (SourceCoreCompatibleFunctions.prepare program plan 512)
  let owned ← get "profile metadata" (prepare artifact.prepared)
  let view ← match owned.views.entries.find? (·.view.principal.binder.name == "f") with
    | some view => pure view | none => throw (IO.userError "profile view missing")
  let named ← match owned.callable.table.idAt? (.named view.view.owner) with
    | some id => pure id | none => throw (IO.userError "profile named descriptor missing")
  let target ← match owned.callable.table.idAt? (.lambda view.view.owner view.view.principal.initializer view.view.cumulative) with
    | some id => pure id | none => throw (IO.userError "profile lambda descriptor missing")
  let root : ContextFrame := .view view.id target (.named named)
  let deep := (List.range 200).foldl (fun (frame : ContextFrame) _ => .lambda target frame) root
  let first ← get "profile first view" (prepareFrame owned root)
  let repeated ← get "profile repeated ancestry" (prepareFrame owned deep)
  let (first, repeated) ← match first.val, repeated.val with
    | some first, some repeated => pure (first, repeated)
    | _, _ => throw (IO.userError "profile ancestry lost source")
  assertTrue (decide (first = repeated)) "lambda ancestry altered metadata state"
  let original := view.view.principal.originalSource
  assertTrue ((requirementProfile repeated.source).map List.length == (requirementProfile original).map List.length)
    "actual view changed spine lengths"
  assertTrue ((requirementProfile repeated.source).all fun spine => spine.all (alphabet original).contains)
    "actual view introduced an ID outside the owned original source"
  IO.println "ancestry profiles: actual witness factory and 200 nested frames retain the finite original ID alphabet GREEN"
end Tests.SourceCoreCallableAncestryProfiles

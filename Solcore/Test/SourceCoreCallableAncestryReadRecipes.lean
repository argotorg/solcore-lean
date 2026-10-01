import Solcore.Frontend.SourceCoreCallableAncestryReadRecipes
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableAncestryReadRecipes.Read.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryReadRecipes.Applied.mk

/-! Actual owned read factories distinguish read-caller metadata from the
principal source selected at creation. This test exercises preparation only;
native snapshot/capture provenance belongs to the paired runtime adapter. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryReadRecipes
open Solcore Solcore.Frontend SourceInference TypeSystem
open SourceCoreCallableAncestryReadRecipes
abbrev RecipeState := SourceCoreCallableAncestryReadRecipes.State
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function nested(seed: Word) returns (F, F) { let outer = lam(value) { keep(value); let inner = lam(item) { keep(item); return seed; }; return (inner, inner); }; return outer(1); }"
  ]}] }

def run : IO Unit := do
  let program ← get "read recipes checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "nested") with
    | some signature => pure signature | none => throw (IO.userError "missing recipe root")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"recipe plan failed: {reprStr other}")
  let automatic ← get "read recipes base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let inputs ← get "read recipes inventory" (SourceCoreCallableAncestryPreparation.prepareInputs automatic.prepared)
  let mut separated := 0
  for entry in inputs.views.entries do
    if entry.view.wrapsPrincipal then
      let target ← match inputs.callable.table.idAt?
          (.lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative) with
        | some target => pure target | none => throw (IO.userError "missing recipe target")
      let caller : RecipeState := ⟨⟨entry.view.owner, entry.view.parentActive, entry.view.principal.source⟩, entry.view.parentActive⟩
      let read ← get "actual read recipe" (prepareRead inputs caller entry.id target)
      let _ ← get "same-context lexical application" (applyRead read caller)
      if !entry.view.parentActive.isEmpty then
        let specialized ← get "recipe principal root" (SourceCompilationPlan.exactSpecialization plan entry.view.owner)
        let lexical : RecipeState := ⟨⟨entry.view.owner, [], specialized.function.typedBody⟩, []⟩
        let applied ← get "different-context lexical application" (applyRead read lexical)
        let after := read.after lexical
        assertTrue (after.nativeActive == entry.view.cumulative && after.metadata.active == read.substitution)
          "native full context replaced the source substitution"
        assertTrue (after.metadata.active != after.nativeActive) "caller and principal contexts collapsed"
        assertTrue (after.metadata.source == SourceTypedRuntime.rewriteLocalRequirements read.witnesses
          (lexical.metadata.source.applySubstitution read.substitution)) "transport targeted the caller source"
        match applied.sourceValue [] [] with
        | .instantiated own witnesses (.closure _ _ _ source owner captured evidence) =>
          assertTrue (own == read.substitution && reprStr witnesses == reprStr read.witnesses &&
            source == lexical.metadata.source && owner == lexical.metadata.owner &&
            captured.isEmpty && evidence.isEmpty) "instantiated export lost the original principal"
        | _ => throw (IO.userError "recipe export collapsed the instantiated wrapper")
        assertTrue (match prepareRead inputs {caller with nativeActive := []} entry.id target with
          | .error _ => true | .ok _ => false)
          "read accepted the wrong native caller context"
        separated := separated + 1
  assertTrue (separated == 2) "missing nested occurrence-specific recipes"
  IO.println "paired read recipes: caller witnesses, lexical source, separate native/source contexts and original instantiated header GREEN"

end Tests.SourceCoreCallableAncestryReadRecipes

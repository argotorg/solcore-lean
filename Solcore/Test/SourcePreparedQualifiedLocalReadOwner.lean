import Solcore.Frontend.SourceCoreExecution
import Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadOwner

/-! Public compilation supplies exact owner and template receipts for a real
nested qualified function while the outer function remains generalized. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourcePreparedQualifiedLocalReadOwner
open Solcore Frontend SourceInference SourceSemantics SourceSpecializationWorklist

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "return outer(1, flag); }"]}] }

private def inspect (compiled : SourceCoreCompiler.Compiled) : IO Unit := do
  let mut qualifiedCount := 0
  let mut outerCount := 0
  for caller in compiled.plan.specializations.attach do
    match discovered : localLambdaInstances caller.val.function.typedBody with
    | .error error => throw (IO.userError s!"discovery: {reprStr error}")
    | .ok instances =>
      for value in instances.attach do
        have _owner := SourcePreparedQualifiedLocalReadOwner.discovered_owner discovered value.property
        unless SourceCompilationPlan.directLambdaLetBinder? caller.val.function.typedBody
            value.val.binding.binder.id == some value.val.binding.binder do
          throw (IO.userError "complete owner mismatch")
        if value.val.binding.binder.name == "outer" then
          unless !value.val.binding.binder.scheme.quantified.isEmpty do
            throw (IO.userError "outer is no longer generalized")
          outerCount := outerCount + 1
        if qualified : value.val.binding.binder.schemeRequirements ≠ [] then
          have _receipt := SourcePreparedQualifiedLocalReadOwner.compiled_instance
            compiled caller.property discovered value.property qualified
          for template in value.val.binding.binder.schemeRequirements.attach do
            for metavariable in (TypedTraitResolution.predicateVariables template.val.predicate).attach do
              have _scoped := SourcePreparedQualifiedLocalReadOwner.compiled_instance_template_scoped
                compiled caller.property discovered value.property template.property metavariable.property
              unless value.val.binding.binder.scheme.quantified.contains metavariable.val do
                throw (IO.userError "template variable outside same inner scheme")
          qualifiedCount := qualifiedCount + 1
  unless qualifiedCount > 0 && outerCount > 0 do
    throw (IO.userError "empty nested owner connection")
  IO.println s!"PASS instances: qualified={qualifiedCount}, generalizedOuter={outerCount}"

def main : IO Unit := do
  let .ok program := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some signature := program.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError "missing run")
  let seeds := [SourceCoreCompiler.Seed.declaration signature.id]
  let options : SourceCoreCompiler.Options :=
    {checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128}
  match accepted : SourceCoreCompiler.compileChecked program seeds options with
  | .error error => throw (IO.userError s!"checked compiler: {reprStr error}")
  | .ok compiled =>
    for caller in compiled.plan.specializations.attach do
      have _public := SourcePreparedQualifiedLocalReadOwner.compileChecked_instance_templates
        accepted caller.property
      pure ()
    inspect compiled
    IO.println "PASS compileChecked"
  match accepted : SourceCoreCompiler.compile workspace seeds options with
  | .error error => throw (IO.userError s!"raw compiler: {reprStr error}")
  | .ok compiled =>
    for caller in compiled.plan.specializations.attach do
      have _public := SourcePreparedQualifiedLocalReadOwner.compile_instance_templates
        accepted caller.property
      pure ()
    inspect compiled
    IO.println "PASS compile"

end Tests.SourcePreparedQualifiedLocalReadOwner

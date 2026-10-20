import Solcore.SourceSemantics.SourceBodyTemplateScope
import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalCatalogOrigins

/-! Raw public compilation prepares a method containing nested generalized
lambdas and a nonempty qualified template. Both genuine catalog origins
supply their original checker body at the completed cache position. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceBodyTemplateScope
open Solcore Frontend SourceInference SourceSemantics TypeSystem
open SourceSemantics.CoreLowering

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, (Word, Bool)> { function coerce(flag: Bool) returns ((Word, Bool)) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, flag);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; } }",

    "function entry(flag: Bool) returns (Word, Bool) { return flag; }"]}] }

def main : IO Unit := do
  let checked ← match checkProgram workspace 4096 with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"checker: {reprStr error}")
  let some entry := checked.signatures.functions.find? (fun function => function.name == "entry")
    | throw (IO.userError "missing entry")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    match artifact : compiled.artifact? with
    | none => throw (IO.userError "missing completed artifact")
    | some cached =>
      let mut ordinary := 0
      let mut methods := 0
      let mut methodTemplates := 0
      let mut templates := 0
      let mut variables := 0
      for index in List.range cached.indexed.base.functions.length do
        match position : cached.indexed.base.functions[index]? with
        | none => throw (IO.userError "missing cache position")
        | some named =>
          have _actualScope := SourceBodyTemplateScope.cached_selection_scope artifact
            (SourceCoreCompiler.compile_checked_source compiledEq) position
          let original ← match compiled.program.functions.find?
              (fun function => function.declaration == named.specialized.function.declaration) with
            | some original =>
                ordinary := ordinary + 1
                pure original
            | none =>
                let some method := compiled.program.methods.find?
                    (fun method => method.checked.declaration == named.specialized.function.declaration)
                  | throw (IO.userError "cache body has no actual ordinary or method origin")
                methods := methods + 1
                methodTemplates := methodTemplates + (localSchemeTemplateOwners method.checked.typedBody).length
                pure method.checked
          for owner in localSchemeTemplateOwners original.typedBody do
            let free := TypedTraitResolution.predicateVariables owner.requirement.predicate
            unless free.all owner.binder.scheme.quantified.contains do
              throw (IO.userError "original body template escapes its complete owner")
            let some solved := original.solvedRequirements.find?
                (fun solved => solved.id == owner.requirement.templateRequirement)
              | throw (IO.userError "original body template has no solved row")
            unless solved.predicate == owner.requirement.predicate do
              throw (IO.userError "original body predicate changed in solved ledger")
            templates := templates + 1
            variables := variables + free.length
      unless compiled.plan.specializations.length == 1 && ordinary > 1 && methods > 0 && methodTemplates > 0 && templates > 0 && variables > 0 do
        throw (IO.userError s!"method coverage changed: initial={compiled.plan.specializations.length}, ordinary={ordinary}, methods={methods}, method templates={methodTemplates}, templates={templates}, variables={variables}")
      IO.println s!"PASS cached ordinary and method template scope: initial={compiled.plan.specializations.length}, ordinary={ordinary}, methods={methods}, method templates={methodTemplates}, templates={templates}, flexible variables={variables}"

end Tests.SourceBodyTemplateScope

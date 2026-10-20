import Solcore.SourceSemantics.SourceCachedTemplateScope
import Solcore.SourceSemantics.CoreLowering.CallablePreparedFinalCatalogOrigins

/-! Raw public compilation prepares an implementation method and its ordinary
helper after the initial worklist. The unchanged nested helper retains its
nonempty original template predicate at the actual completed cache position. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCachedTemplateScope
open Solcore Frontend SourceInference SourceSemantics TypeSystem
open SourceSemantics.CoreLowering

private theorem catalog_scope {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named) :
    (∃ original ∈ compiled.program.functions,
      named.specialized.function = SourceSpecialization.applyCheckedFunction named.specialized.parameterSubstitution original ∧
      (∀ owner, ContainsLocalSchemeTemplate original.typedBody owner →
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables owner.requirement.predicate,
          metavariable ∈ owner.binder.scheme.quantified)) ∨
    (∃ method : ExecutableImplMethods.CheckedMethod,
      Nonempty (CallableCoercionBodyProvenance.Selection cached.sourceProgram method) ∧
      named.specialized = method.specialized) := by
  have finalMember := RecursiveNamedPreparedFinalPlanOrigins.final_member cached position rfl
  have origin := CallablePreparedFinalCatalogOrigins.of_default_preparation
    (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached) _ finalMember
  generalize rowEq : named.specialized = row at origin
  cases origin with
  | ordinary ordinary =>
      rw [← rowEq] at ordinary
      apply Or.inl
      simpa only [← rowEq] using SourceCachedTemplateScope.cached_origin_scope artifact checked position ordinary
  | method selected => exact .inr ⟨_, ⟨selected⟩, rfl⟩

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, flag);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; }",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "impl Coerce<Bool, (Word, Bool)> { function coerce(value: Bool) returns ((Word, Bool)) { return run(value); } }",
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
      let mut late := 0
      let mut templates := 0
      let mut variables := 0
      for index in List.range cached.indexed.base.functions.length do
        match position : cached.indexed.base.functions[index]? with
        | none => throw (IO.userError "missing cache position")
        | some named =>
          have _actualScope := catalog_scope artifact
            (SourceCoreCompiler.compile_checked_source compiledEq) position
          match compiled.program.functions.find?
              (fun function => function.declaration == named.specialized.function.declaration) with
          | none => methods := methods + 1
          | some original =>
            ordinary := ordinary + 1
            if !(compiled.plan.specializations.map (·.key)).contains named.specialized.key then
              late := late + 1
              for owner in localSchemeTemplateOwners original.typedBody do
                let free := TypedTraitResolution.predicateVariables owner.requirement.predicate
                unless free.all owner.binder.scheme.quantified.contains do
                  throw (IO.userError "late original template escapes its complete owner")
                let some solved := original.solvedRequirements.find?
                    (fun solved => solved.id == owner.requirement.templateRequirement)
                  | throw (IO.userError "late original template has no solved row")
                unless solved.predicate == owner.requirement.predicate do
                  throw (IO.userError "late original predicate changed in solved ledger")
                templates := templates + 1
                variables := variables + free.length
      unless compiled.plan.specializations.length == 1 && ordinary > 1 && methods > 0 && late > 0 && templates > 0 && variables > 0 do
        throw (IO.userError s!"late coverage changed: initial={compiled.plan.specializations.length}, ordinary={ordinary}, methods={methods}, late={late}, templates={templates}, variables={variables}")
      IO.println s!"PASS cached ordinary template scope: initial={compiled.plan.specializations.length}, ordinary={ordinary}, methods={methods}, late={late}, templates={templates}, flexible variables={variables}"

end Tests.SourceCachedTemplateScope

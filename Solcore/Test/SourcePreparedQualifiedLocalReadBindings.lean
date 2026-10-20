import Solcore.Frontend.SourceCoreExecution
import Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadBindings

/-! Nonempty compilation checks for the original selected qualified-reference
receipt, including a nested owner which retains a separate type variable. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourcePreparedQualifiedLocalReadBindings
open Solcore Frontend SourceInference SourceSemantics

private def workspace (body : List String) : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" ([
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }"
  ] ++ body)}] }

private def references (compiled : SourceCoreCompiler.Compiled) : IO Nat := do
  let mut count := 0
  for caller in compiled.plan.specializations.attach do
    for item in caller.val.function.typedBody.nodes.attach do
      match itemEq : item.val with
      | .statement _ => pure ()
      | .expression node =>
        match form : node.form with
        | .reference name (.local localId) =>
          match found : SourceCompilationPlan.directLambdaLetBinder?
              caller.val.function.typedBody localId with
          | none => pure ()
          | some binder =>
            if qualified : binder.schemeRequirements ≠ [] then
              have present : .expression node ∈ caller.val.function.typedBody.nodes := by
                rw [← itemEq]; exact item.property
              have _certificate := SourcePreparedQualifiedLocalReadBindings.compiled_selected
                compiled caller.property present form found qualified
              let some owned := SourceCompilationPlan.ordinaryOwnedRequirements? node
                | throw (IO.userError "missing ordinary requirement spine")
              let ownNode := {node with type := node.rawType, requirements := owned, coercions := []}
              let .ok (substitution, bindings) :=
                  SourceCompilationPlan.localRequirementBindings caller.val binder ownNode
                | throw (IO.userError "qualified bindings rejected")
              unless bindings.map (fun binding => (binding.template, binding.actualRequirement)) ==
                  binder.schemeRequirements.zip owned do
                throw (IO.userError "template/actual pairing")
              for template in binder.schemeRequirements.attach do
                have _excludes := fun metavariable (outside : metavariable ∉ binder.scheme.quantified) =>
                  SourcePreparedQualifiedLocalReadBindings.compiled_template_excludes
                    compiled caller.property present form found qualified template.property outside
                for metavariable in TypedTraitResolution.predicateVariables template.val.predicate do
                  unless binder.scheme.quantified.contains metavariable do
                    throw (IO.userError "captured template variable")
              for binding in bindings do
                unless (TypedTraitResolution.predicateVariables binding.predicate).isEmpty do
                  throw (IO.userError "ungrounded instantiated predicate")
              IO.println s!"QUALIFIED {name} domain={reprStr substitution.domain} bindings={bindings.length}"
              count := count + 1
            else pure ()
        | _ => pure ()
  pure count

private def checkCase (label : String) (generalizedOuter : Bool) (body : List String) : IO Unit := do
  let .ok program := checkProgram (workspace body) 4096
    | throw (IO.userError s!"{label}: checker rejected")
  let some signature := program.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError s!"{label}: missing run")
  let .ok compiled := SourceCoreCompiler.compileChecked program [.declaration signature.id]
      {checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128}
    | throw (IO.userError s!"{label}: compiler rejected")
  let outerBinders := compiled.plan.specializations.flatMap fun caller =>
    caller.function.typedBody.nodes.filterMap fun
      | .statement {form := .letDecl binder (some _), ..} =>
          if binder.name == "outer" then some binder else none
      | _ => none
  let [outer] := outerBinders | throw (IO.userError s!"{label}: outer owner")
  unless (!outer.scheme.quantified.isEmpty) == generalizedOuter do
    throw (IO.userError s!"{label}: outer generalization")
  IO.println s!"OUTER quantified={reprStr outer.scheme.quantified}"
  let count ← references compiled
  unless count > 0 do throw (IO.userError s!"{label}: no qualified references")
  IO.println s!"PASS {label}: {count} qualified original references"

def main : IO Unit := do
  checkCase "used-inner" false [
    "function run(flag: Bool) returns (Word) {",
    "let outer = lam(value) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return value; };",
    "return outer(1); }"]
  checkCase "separate-outer-variable" true [
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "return outer(1, flag); }"]

end Tests.SourcePreparedQualifiedLocalReadBindings

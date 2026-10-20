import Solcore.SourceSemantics.SourceCompiledNestedInitializerPublicPrivacy

/-! Public compilation exercises a nonempty inner generalized template,
nonzero outer and inner positions, and later uses of both closures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCompiledNestedInitializerPrivacy
open Solcore Frontend SourceInference SourceSemantics TypeSystem

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let before = flag;",
    "let outer = lam(value, tag) { let prior = true; let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, before);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; }"]}] }

def main : IO Unit := do
  let .ok program := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some signature := program.signatures.functions.find? (fun signature => signature.name == "run")
    | throw (IO.userError "missing run")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match accepted : SourceCoreCompiler.compile workspace [.declaration signature.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    let mut connected := 0
    for row in compiled.plan.specializations.attach do
      have _continuation := SourceCompiledLocalFinalization.compile_nested_lambda_privacy
        accepted row.property
      connected := connected + 1
    let some original := compiled.program.functions.find? (fun function => function.declaration == signature.id)
      | throw (IO.userError "missing original selected checker body")
    let bindings := initializedLetBindings original.typedBody
    let some outer := bindings.find? (fun binding => binding.binder.name == "outer")
      | throw (IO.userError "missing outer initialized binder")
    let some inner := bindings.find? (fun binding => binding.binder.name == "inner")
      | throw (IO.userError "missing inner initialized binder")
    unless !inner.binder.scheme.quantified.isEmpty && !inner.binder.schemeRequirements.isEmpty do
      throw (IO.userError "inner quantified template coverage is empty")
    unless !outer.binder.scheme.quantified.isEmpty do
      throw (IO.userError "outer quantified coverage is empty")
    for q in inner.binder.scheme.quantified do
      if outer.binder.scheme.quantified.contains q then
        throw (IO.userError "inner quantifier entered the outer scheme")
    let some outerValue := original.typedBody.nodes.findSome? (fun node => match node with
        | .expression expression =>
            if NodeId.expression expression.id == outer.initializer then some expression else none
        | _ => none)
      | throw (IO.userError "missing actual outer initializer expression")
    for q in inner.binder.scheme.quantified do
      if outerValue.type.freeVariables.contains q then
        throw (IO.userError "inner quantifier escaped into the finalized outer lambda result")
    unless connected > 0 do throw (IO.userError "public selected row coverage is empty")
    IO.println s!"PASS nested initializer final privacy: selected rows={connected}, inner quantifiers={inner.binder.scheme.quantified.length}, outer quantifiers={outer.binder.scheme.quantified.length}, inner templates={inner.binder.schemeRequirements.length}"

end Tests.SourceCompiledNestedInitializerPrivacy

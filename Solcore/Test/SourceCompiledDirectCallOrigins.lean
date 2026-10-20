import Solcore.SourceSemantics.SourceCompiledDirectCallOrigins

/-! A complete nested qualified source program exercises actual direct
requirement issuance, final solving and selected public compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCompiledDirectCallOrigins
open Solcore Frontend SourceInference SourceSemantics TypeSystem DirectCallEvents

def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Rel<A, B> {}",
    "impl<A, B> Rel<A, B> {}",
    "function keep<A, B>(first: A, second: B) returns (B) where A: Rel<B> { return second; }",
    "function run(flag: Bool) returns (Word, Bool) {",
    "let outer = lam(value, tag) { let inner = lam(item) { return keep(value, item); }; let touched = inner(true); return (value, tag); };",
    "let result = outer(1, flag);",
    "if (flag) { let discarded = keep(2, true); } else { let discarded = keep(3, false); }",
    "return result; }"]}] }

private def hasEmitter (nodes : List Node) (requirement : RequirementId) : Bool :=
  nodes.any fun node => match node with
    | .expression expression => match expression.form with
      | .call _ _ (.declaration _) => expression.requirements.contains requirement
      | _ => false
    | _ => false

def main : IO Unit := do
  let .ok program := checkProgram workspace 4096 | throw (IO.userError "checker rejected")
  let some entry := program.signatures.functions.find? (fun function => function.name == "run")
    | throw (IO.userError "missing run")
  let options : SourceCoreCompiler.Options :=
    { checkingFuel := 4096, compilationFuel := 1000, specializationBudget := 128 }
  match compiledEq : SourceCoreCompiler.compile workspace [.declaration entry.id] options with
  | .error error => throw (IO.userError s!"public compile: {reprStr error}")
  | .ok compiled =>
    let mut emitted := 0
    let mut rows := 0
    for caller in compiled.plan.specializations.attach do
      have _public := SourceCompiledDirectCallOrigins.compile_direct_emitters compiledEq caller.property
      let some signature := compiled.program.signatures.functions.find?
          (fun signature => signature.id == caller.val.function.declaration)
        | throw (IO.userError "missing selected signature")
      let some declaration := compiled.program.environment.declaration? signature.id
        | throw (IO.userError "missing selected declaration")
      let context : SourceInference.Context := {
        environment := compiled.program.environment
        signatures := compiled.program.signatures
        scope := .ofDeclaration declaration
        typeParameters := signature.scheme.parameters
        assumptions := signature.scheme.predicates }
      let initial := State.initial declaration.id
        ((signature.parameterNames.zip signature.parameterTypes).map fun parameter =>
          (parameter.1, Scheme.mono parameter.2)) signature.parameterComptime
      match inferred : Detail.inferStatementsFuel options.checkingFuel context
          signature.source.value.body.value (Ty.productMany signature.returnTypes) initial with
      | .error error => throw (IO.userError s!"actual body inference: {reprStr error}")
      | .ok body =>
        have origins := initializedStatements_origins inferred
        for requirement in body.state.directCallRequirements.attach do
          have _emitter := origins requirement.val requirement.property
          unless hasEmitter body.state.nodes requirement.val do
            throw (IO.userError "issued requirement lost its original emitter")
          unless hasEmitter caller.val.function.typedBody.nodes requirement.val do
            throw (IO.userError "issued requirement lost its selected emitter")
          emitted := emitted + 1
        rows := rows + 1
    unless emitted >= 3 && rows > 0 do
      throw (IO.userError "empty direct emitter coverage")
    IO.println s!"PASS public compilation: rows={rows}, issued requirements={emitted}"

end Tests.SourceCompiledDirectCallOrigins

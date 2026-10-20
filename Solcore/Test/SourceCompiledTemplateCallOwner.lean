import Solcore.SourceSemantics.SourceCompiledTemplateCallOwner

/-! The unchanged full nested qualified program makes the actual prepared
open-call owner connection nonempty through raw public compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCompiledTemplateCallOwner
open Solcore Frontend SourceInference SourceSemantics TypeSystem CatalogedDirectCallEvents

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

private def hasEmitter (catalog : List Resolved.DeclarationId) (nodes : List Node) (requirement : RequirementId) : Bool :=
  nodes.any fun node => match node with
    | .expression expression => match expression.form with
      | .call _ _ (.declaration instantiation) => expression.requirements.contains requirement && catalog.contains instantiation.declaration
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
    let mut templates := 0
    let mut readyPositions := 0
    let mut rows := 0
    let mut openTemplates := 0
    let mut instances := 0
    for caller in compiled.plan.specializations.attach do
      have compiledEmitters := SourceCompiledCatalogedCallOrigins.compile_template_emitters compiledEq caller.property
      for template in (sourceLocalSchemeTemplateIds caller.val.function.typedBody).attach do
        have _emitter := compiledEmitters template.val template.property
        have _owner := SourceCompiledTemplateCallOwner.template_owner compiledEq caller.property template.property
        let openEmitter := caller.val.function.typedBody.nodes.any fun node => match node with
          | .expression expression => match expression.form with
            | .call _ _ (.declaration instantiation) =>
                expression.requirements.contains template.val &&
                  !SourcePreparedOpenCallEdges.InstantiationClosed instantiation
            | _ => false
          | _ => false
        if openEmitter then openTemplates := openTemplates + 1
        unless hasEmitter (compiled.program.signatures.functions.map (·.id)) caller.val.function.typedBody.nodes template.val do
          throw (IO.userError "finalized template lost its selected cataloged emitter")
        templates := templates + 1
      match SourceSpecializationWorklist.localLambdaInstances caller.val.function.typedBody with
      | .error error => throw (IO.userError s!"actual local discovery: {reprStr error}")
      | .ok discovered => instances := instances + discovered.length
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
        have classified := ClassifiedCallEvents.initializedStatements_classified inferred
        for template in body.state.localSchemeAssumptions.attach do
          have direct := classified template.property
          have _emitter := origins template.val direct
          unless body.state.directCallRequirements.contains template.val do
            throw (IO.userError "classified template is not a declaration-call requirement")
        match position : signature.source.value.body.value[0]? with
        | none => pure ()
        | some first =>
          match form : first.value with
          | .letDecl _name _annotation (some _initializer) =>
            have _ready := SourceInferenceDirectCallInitializerOrigins.initialized_statement_position
              inferred position form
            readyPositions := readyPositions + 1
          | _ => pure ()
        for requirement in body.state.directCallRequirements.attach do
          have _emitter := origins requirement.val requirement.property
          unless hasEmitter (compiled.program.signatures.functions.map (·.id)) body.state.nodes requirement.val do
            throw (IO.userError "issued requirement lost its original cataloged emitter")
          unless hasEmitter (compiled.program.signatures.functions.map (·.id)) caller.val.function.typedBody.nodes requirement.val do
            throw (IO.userError "issued requirement lost its selected cataloged emitter")
          emitted := emitted + 1
        rows := rows + 1
    unless emitted >= 3 && rows > 0 && templates > 0 && readyPositions > 0 && openTemplates > 0 && instances > 0 do
      throw (IO.userError "empty template or actual initializer coverage")
    IO.println s!"PASS prepared template owners: rows={rows}, issued requirements={emitted}, templates={templates}, actual ready positions={readyPositions}, open templates={openTemplates}, actual instances={instances}"

end Tests.SourceCompiledTemplateCallOwner

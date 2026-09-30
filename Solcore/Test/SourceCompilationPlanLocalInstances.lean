import Solcore.Frontend.SourceCompilationPlan.LocalInstances

/-! Catalog regressions use checked source programs. They test contextual
discovery and retained metadata, without executing either source or Core. -/

#check_failure Solcore.Frontend.SourceTypedRuntime.Value
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreDirectLinking.link

set_option autoImplicit false

namespace Tests.SourceCompilationPlanLocalInstances

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference Solcore.TypeSystem

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc"
  mainSources := [{
    path := "main.solc"
    content := String.intercalate "\n" [
      "trait Mark<T> {}",
      "impl Mark<Word> {}",
      "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function nested<T>(captured: T, flag: Bool) returns (Word) {",
      "  let outer = lam(value) {",
      "    let inner = lam(item) { return (captured, value, item); };",
      "    return inner(value);",
      "  };",
      "  outer(1);",
      "  outer(flag);",
      "  return 9;",
      "}",
      "function sameInnerType(flag: Bool) returns (Word, Word) {",
      "  let outer = lam(value) {",
      "    let inner = lam(item) { return item; };",
      "    return inner(1);",
      "  };",
      "  return (outer(1), outer(flag));",
      "}",
      "function sharedCapture(flag: Bool) returns (Word) {",
      "  let total: Word = 0;",
      "  let f = lam(item) { total += 1; return item; };",
      "  f(1);",
      "  f(flag);",
      "  f(2);",
      "  return total;",
      "}",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      "  let f = lam(item) { return keep(item); };",
      "  return (f(1), f(flag));",
      "}",
      "function unused() returns (Word) {",
      "  let outer = lam(value) {",
      "    let inner = lam(item) { return item; };",
      "    return inner(value);",
      "  };",
      "  return 9;",
      "}"
    ]
  }]
  externalLibraries := []
}

private def requestNamed (program : CheckedProgram) (name : String)
    (arguments : List Ty := []) : IO SourceSpecializationWorklist.Request := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"missing catalog fixture `{name}`")
  assertTrue (signature.scheme.parameters.length == arguments.length)
    s!"catalog fixture `{name}` parameter count changed"
  pure {
    declaration := signature.id
    parameterSubstitution := signature.scheme.parameters.zip arguments
  }

private def planFor (program : CheckedProgram)
    (requests : List SourceSpecializationWorklist.Request) :
    IO SourceSpecializationWorklist.Plan := do
  match SourceSpecializationWorklist.run program requests 16 with
  | .ok (.complete plan) => pure plan
  | result => throw (IO.userError s!"catalog worklist: {reprStr result}")

private def catalogFor (plan : SourceSpecializationWorklist.Plan) :
    IO (List SourceCompilationPlan.LocalLambdaCatalogEntry) := do
  match SourceCompilationPlan.localLambdaCatalog plan with
  | .ok entries => pure entries
  | .error error => throw (IO.userError s!"local catalog: {reprStr error}")

private def testNestedContexts (program : CheckedProgram) : IO Unit := do
  let wordRequest ← requestNamed program "nested" [.word]
  let boolRequest ← requestNamed program "nested" [.bool]
  let plan ← planFor program [wordRequest, boolRequest]
  let entries ← catalogFor plan
  let expected := ["outer", "outer", "inner", "inner"]
  assertTrue (entries.map (·.binder.name) == expected ++ expected)
    "nested local catalog lost plan/FIFO order"
  assertTrue (entries.map (·.caller.arguments) ==
      List.replicate 4 [Ty.word] ++ List.replicate 4 [Ty.bool])
    "same lambda identities collided across enclosing specializations"
  for entry in entries do
    assertTrue (entry.parameterSubstitution.map Prod.snd == entry.caller.arguments)
      "catalog lost the enclosing rigid parameter substitution"
    assertTrue ((entry.substitution.apply entry.binder.scheme.body).freeVariables.isEmpty)
      "catalog lost a cumulative local substitution"
    assertTrue (SourceSpecialization.isDirectLambdaInitializer entry.source entry.initializer)
      "catalog lost the initializer expression identity"
    if entry.binder.name == "inner" then
      assertTrue (entry.substitution.domain.length == 2)
        "nested context omitted an outer or inner flexible parameter"
      let captured ← match entry.source.inputs.find? (·.name == "captured") with
        | some binder => pure binder
        | none => throw (IO.userError "nested fixture lost its captured input")
      let uses := entry.instantiatedBodyNodes.filterMap fun
        | .expression node@{ form := .reference _ (.local id), .. } =>
            if id == captured.id then some node.type else none
        | _ => none
      assertTrue (uses == entry.caller.arguments)
        "contextual body lost the captured input identity or rigid type"
  let repeated ← catalogFor plan
  assertTrue (entries == repeated) "local catalog order is unstable"

private def testSameTypeDistinctContexts (program : CheckedProgram) : IO Unit := do
  let request ← requestNamed program "sameInnerType"
  let entries ← catalogFor (← planFor program [request])
  match entries.filter (·.binder.name == "inner") with
  | [first, second] =>
      assertTrue (first.initializer == second.initializer &&
          first.binder.id == second.binder.id &&
          first.substitution != second.substitution &&
          first.substitution.apply first.binder.scheme.body == Ty.function .word .word &&
          second.substitution.apply second.binder.scheme.body == Ty.function .word .word)
        "catalog incorrectly merged distinct contexts with the same function type"
  | entries => throw (IO.userError s!"expected two contextual inner instances, got {entries.length}")

private def testSharedCaptureAndBounds (program : CheckedProgram) : IO Unit := do
  let request ← requestNamed program "sharedCapture"
  let plan ← planFor program [request, request]
  let entries ← catalogFor plan
  assertTrue (plan.seedKeys.length == 2 && entries.length == 2)
    "duplicate roots or repeated Word uses duplicated local code contexts"
  assertTrue (entries.map (fun entry => entry.substitution.apply entry.binder.scheme.body) ==
      [Ty.function .word .word, Ty.function .bool .bool])
    "first-seen local instance order changed"
  let total ← match entries.head? with
    | none => throw (IO.userError "shared capture has no local instances")
    | some entry =>
        match entry.source.nodes.findSome? fun
            | .statement { form := .letDecl binder _, .. } =>
                if binder.name == "total" then some binder.id else none
            | _ => none with
        | some id => pure id
        | none => throw (IO.userError "shared capture lost its mutable binder")
  for entry in entries do
    let targets := entry.instantiatedBodyNodes.filterMap fun
      | .statement { form := .assignValue assignment _ _, .. } => some assignment.target.root
      | _ => none
    assertTrue (targets == [total])
      "local instantiation changed the shared captured mutation target"
  let specialized ← match plan.specializations with
    | [specialized] => pure specialized
    | _ => throw (IO.userError "shared capture fixture changed its specialization frontier")
  let source := specialized.function.typedBody
  match SourceSpecializationWorklist.localLambdaInstances source with
  | .ok instances =>
      assertTrue (instances == entries.map (·.localInstance))
        "preparation disagrees with worklist local instances"
  | .error error => throw (IO.userError s!"local discovery: {reprStr error}")
  match SourceCompilationPlan.localLambdaCatalog plan (some 0) with
  | .error (.localPolymorphicContextFuelExhausted 2) => pure ()
  | result => throw (IO.userError s!"zero context fuel changed: {reprStr result}")
  match SourceCompilationPlan.localLambdaCatalog plan (some 1) with
  | .error (.localPolymorphicContextFuelExhausted 1) => pure ()
  | result => throw (IO.userError s!"FIFO context fuel changed: {reprStr result}")
  match SourceCompilationPlan.localLambdaCatalog plan (some 2) with
  | .ok bounded => assertTrue (bounded == entries) "exact context bound changed catalog contents"
  | .error error => throw (IO.userError s!"sufficient context fuel failed: {reprStr error}")
  let duplicate := { plan with specializations := plan.specializations ++ plan.specializations }
  match SourceCompilationPlan.localLambdaCatalog duplicate with
  | .error (.duplicatePlanSpecializations key 2) =>
      assertTrue (key == specialized.key) "duplicate diagnosis lost the enclosing key"
  | result => throw (IO.userError s!"duplicate catalog key accepted: {reprStr result}")

private def testRequirementsAndUnusedTemplates (program : CheckedProgram) : IO Unit := do
  let request ← requestNamed program "qualified"
  let entries ← catalogFor (← planFor program [request])
  assertTrue (entries.length == 2) "qualified local instances were lost"
  for entry in entries do
    match entry.binder.schemeRequirements with
    | [template] =>
        let retained := entry.solvedRequirements.filter fun solved =>
          solved.id == template.templateRequirement
        assertTrue (retained.any fun solved =>
            solved.predicate == template.predicate &&
              match solved.evidence with
              | .assumption predicate => predicate == template.predicate
              | _ => false)
          "catalog consumed or resolved the retained template assumption"
        let uses := entry.source.nodes.filterMap fun
          | .expression node@{ form := .reference _ (.local id), .. } =>
              if id == entry.binder.id then some node.requirements else none
          | _ => none
        assertTrue (uses.length == 2 && uses.all (·.length == 1))
          "catalog discarded the original qualified local use requirements"
    | _ => throw (IO.userError "qualified fixture lost its template requirement")
  let unused ← requestNamed program "unused"
  let unusedEntries ← catalogFor (← planFor program [unused])
  assertTrue unusedEntries.isEmpty "unreachable local templates acquired catalog entries"

def testSourceCompilationPlanLocalInstances : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"local catalog fixture: {reprStr errors}")
  testNestedContexts program
  testSameTypeDistinctContexts program
  testSharedCaptureAndBounds program
  testRequirementsAndUnusedTemplates program

end Tests.SourceCompilationPlanLocalInstances

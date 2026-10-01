import Solcore.Frontend.SourceCoreAllocationContexts
import Solcore.Frontend.SourceCoreCompatibleDataMatches

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Checked source fixtures retain principal lambdas, contextual instances,
for binders and match-generated cells. Real common parameter/match allocation
helpers send requests through the discovered metadata inventory. -/
set_option autoImplicit false
namespace Tests.SourceCoreAllocationContexts
open Solcore Solcore.Core Solcore.Frontend SourceInference
open SourceCoreAllocationContexts

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function allBindings(flag: Bool) returns (Word, Bool) {",
    " let unused = lam(unusedArg) { return unusedArg; };",
    " let f = lam(value) { return value; };",
    " let total: Word = 0;",
    " for (let i: Word = 0; i < 1; i = i + 1) { total = total + i; }",
    " match ((f(1), f(flag))) { case (left, right) { return (left, right); } }",
    "}",
    "function nested(flag: Bool) returns (Word, Word) {",
    " let outer = lam(value) { let inner = lam(item) { return item; }; return inner(1); };",
    " return (outer(1), outer(flag)); }"
  ]}]
}

private def makePlan (program : CheckedProgram) : IO Plan := do
  let requests ← ["allBindings", "nested"].mapM fun name => do
    let signature ← match program.signatures.functions.filter (·.name == name) with
      | [signature] => pure signature
      | _ => throw (IO.userError s!"allocation context source function missing: {name}")
    pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program requests 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"allocation context worklist failed: {reprStr result}")
  get "executable plan" (SourceCompilationPlan.prepareExecutablePlanEvidence program plan)

private def basicError (error : SourceCoreAllocationDiscovery.Error) : SourceCoreBasic.Error :=
  match error with
  | .missingBinder _ id => .missingBinding id
  | .binderMismatch id => .duplicateBinding id
  | _ => .callPreparation .invalidPatternMetadata

private def matchRequests (program : CheckedProgram) (context : SourceCoreAllocationDiscovery.Context)
    (discovery : SourceCoreAllocationDiscovery.Prepared) : IO Unit := do
  let checked ← get "compatible match catalog"
    (SourceCoreCompatibleCatalog.prepare program.signatures 128 [.word, .bool, .product .word .bool])
  let allocator := discovery.allocatorAt context.owner context.active basicError
  let matchContext : SourceCoreCompatibleDataMatches.Context := {
    values := SourceCoreCompatibleValues.Context.initial checked
    solvedRequirements := []
    sourceCells := some allocator }
  let selected ← match context.source.nodes.findSome? fun
      | .statement statement@{form := .matchWith resolution, ..} => some (statement, resolution)
      | _ => none with
    | some selected => pure selected
    | none => throw (IO.userError "checked match statement missing")
  let (statement, resolution) := selected
  let resultType := Core.Ty.product .word .bool
  let lowerExpression : SourceCoreCompatibleDataMatches.ExpressionLowerer := fun _ _ _ _ _ =>
    pure ⟨resultType, LanguageResult.success (.pair (.word Word.zero) (.bool true))⟩
  let lowerBody : SourceCoreCompatibleDataMatches.BodyLowerer := fun _ _ _ _ type _ _ =>
    pure (Core.LocalLoop.fallthrough type)
  let expression ← get "actual match allocation requests"
    (SourceCoreCompatibleDataMatches.lowerWithReasons matchContext lowerExpression lowerBody 128 context.source []
      statement.id resolution resultType (fun _ => Word.zero) Word.zero)
  let found ← get "match request discovery" (SourceCoreAllocationDiscovery.discover discovery 512 expression)
  let names := found.sites.map (·.receipt.binding.binding.binder.name)
  assertTrue (names.contains "" && names.contains "left" && names.contains "right" && names.length == 3)
    "actual match helper lost hidden/arm allocations"
  let hidden ← match found.sites.find? (·.receipt.binding.binding.binder.name == "") with
    | some hidden => pure hidden
    | none => throw (IO.userError "match hidden receipt missing")
  let scrutinee ← match context.source.lookupExpression? resolution.scrutinee with
    | some node => pure node
    | none => throw (IO.userError "match scrutinee metadata missing")
  assertTrue (decide (hidden.receipt.binding.binding.binder = hiddenBinder statement resolution scrutinee))
    "hidden allocation did not retain exact runtime type/span/name metadata"
  assertTrue (found.sites.any (fun site => site.receipt.scope.any (fun entry => entry.1 == resolution.hiddenScrutinee)))
    "arm allocation did not capture the actual hidden source cell"

private def parameterRequests (context : SourceCoreAllocationDiscovery.Context)
    (discovery : SourceCoreAllocationDiscovery.Prepared) : IO Unit := do
  let parameters ← match context.source.nodes.findSome? fun
      | .expression {form := .lambda parameters _ _, ..} =>
          if parameters.all (fun parameter => parameter.scheme.body.freeVariables.isEmpty) then some parameters else none
      | _ => none with
    | some parameters => pure parameters
    | none => throw (IO.userError "closed contextual lambda parameters missing")
  let parameters ← parameters.mapM fun parameter => do
    let type ← get "scalar contextual parameter" (SourceCoreElaboration.lowerType (.binder parameter.id) parameter.scheme.body)
    pure (parameter, type)
  let expression ← get "actual parameter allocation requests"
    (SourceCoreSourceCells.bindParameters (discovery.allocatorAt context.owner context.active basicError)
      context.source [] parameters .unit SourceCoreFunctions.argumentProjection (LanguageResult.success .unit))
  let found ← get "parameter request discovery" (SourceCoreAllocationDiscovery.discover discovery 128 expression)
  assertTrue (found.sites.length == parameters.length)
    "contextual parameter allocator failed to preserve each actual binder"
  for site in found.sites do
    assertTrue (decide (site.receipt.context.inventory.active = context.active))
      "contextual parameter lost its full substitution"

def run : IO Unit := do
  let program ← get "checked allocation fixture" (checkProgram workspace)
  let plan ← makePlan program
  let checked ← get "local projection catalog" (SourceCoreDataCatalog.prepare program.signatures 128 [.word, .bool])
  let locals ← get "actual local instances" (SourceCoreLocalPolymorphism.prepare checked plan)
  let candidates := locals.bindings.flatMap (·.instances)
  let prepared ← get "actual canonical contexts" (prepare program plan candidates)
  let contexts := prepared.inventory.contexts
  assertTrue (contexts.length > plan.specializations.length)
    "generalized local instantiations were not inventoried"
  let roots := contexts.filter (·.active.isEmpty)
  assertTrue (roots.length == plan.specializations.length) "root contexts changed their empty substitution"
  let root ← match roots.find? (fun context => context.binders.any (·.name == "unused")) with
    | some root => pure root
    | none => throw (IO.userError "principal generic root metadata missing")
  for name in ["flag", "unused", "unusedArg", "f", "value", "total", "i", "left", "right", ""] do
    assertTrue (root.binders.any (·.name == name)) s!"declared/hidden binder missing: {name}"
  assertTrue (root.binders.any (fun binder => binder.name == "unusedArg" && !binder.scheme.body.freeVariables.isEmpty))
    "unreached principal generic lambda metadata was projected away"
  let repeated ← get "identical context reuse" (fromPrepared
    {plan with specializations := plan.specializations ++ plan.specializations}
    (prepared.parents ++ prepared.parents))
  assertTrue (decide (repeated.contexts = contexts)) "identical owner/context rows were not shared"
  let first ← match plan.specializations with
    | first :: _ => pure first
    | [] => throw (IO.userError "empty allocation fixture plan")
  let changedSource := {first.function.typedBody with
    inputs := first.function.typedBody.inputs.map (fun binder => {binder with name := binder.name ++ "changed"})}
  let changed := {first with function := {first.function with typedBody := changedSource}}
  match fromPrepared {plan with specializations := plan.specializations ++ [changed]} [] with
  | .error (.conflictingContext owner active) =>
      assertTrue (owner == first.key && active.isEmpty) "conflicting context diagnostic changed"
  | _ => throw (IO.userError "different original source reused an existing context key")
  let discovery ← get "metadata-only discovery prepare" (SourceCoreAllocationDiscovery.prepare [] contexts)
  matchRequests program root discovery
  for context in contexts.filter (fun context => !context.active.isEmpty) do
    parameterRequests context discovery
  let nestedContexts := contexts.filter (fun context => !context.active.isEmpty && context.binders.any (·.name == "inner"))
  assertTrue (nestedContexts.length >= 4) "nested contextual instances lost cumulative identities"
  assertTrue (nestedContexts.any (fun context => context.active.length >= 2))
    "nested contexts discarded their outer substitution"

example {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (row : Certified plan parents) {binder : TypedBinder} (member : binder ∈ row.context.binders) :
    BinderOrigin row.context.source binder := row.binder_origin member

example {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (row : Certified plan parents) {binder : TypedBinder}
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders row.context.source) :
    binder ∈ row.context.binders := row.declared_mem member

example {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (inventory : Inventory plan parents) :
    (inventory.contexts.map (fun context => (context.owner, context.active))).Nodup := inventory.contexts_unique

end Tests.SourceCoreAllocationContexts

import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewAllocations
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableIndexedAllocationFrames.Annotated.mk
set_option autoImplicit false
namespace Tests.SourceCoreCallableLambdaViewEdits
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableLambdaViewEdits

/-- Every complete child header in a disjoint footprint survives an actual raw
view. The freshness condition is supplied per occurrence, not inferred from
ownership or from an arbitrary graph being a tree. -/
theorem raw_body_lookups {source : TypedSource} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? node.id = some node)
    (ordinary : List RequirementId) (footprint : List ExpressionId)
    (fresh : ∀ id ∈ footprint, id ≠ node.id) :
    ∀ id ∈ footprint, source.lookupExpression? id =
      (SourceCoreEvidence.withNode source
        {node with type := node.rawType, requirements := ordinary, coercions := []}).lookupExpression? id := by
  exact (raw unique found ordinary).expressions (by simpa only [List.mem_singleton] using fresh)

theorem normalized_body_lookups {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : SourceCoreLocalPolymorphism.Binding} {parent : Option SourceCoreLocalEvidence.Prepared}
    {source view : TypedSource} {id : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent source id = .ok view)
    (footprint : List ExpressionId) (fresh : ∀ child ∈ footprint, child ≠ id) :
    ∀ child ∈ footprint, source.lookupExpression? child = view.lookupExpression? child := by
  exact (normalized unique accepted).expressions (by simpa only [List.mem_singleton] using fresh)

/-- The edit list composes for successive actual normalizations. -/
theorem successive_normalizations {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : SourceCoreLocalPolymorphism.Binding} {parent : Option SourceCoreLocalEvidence.Prepared}
    {source middle final : TypedSource} {first second child : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (left : SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent source first = .ok middle)
    (right : SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent middle second = .ok final)
    (freshFirst : child ≠ first) (freshSecond : child ≠ second) :
    source.lookupExpression? child = final.lookupExpression? child := by
  have before := normalized unique left
  have after := normalized (before.metadata.unique unique) right
  exact (before.trans after).unchanged child (by simp [freshFirst, freshSecond])

/-- An accepted actual allocator equation can be moved to the edited source;
no caller-provided allocation or evaluation relation is needed. -/
theorem accepted_allocation {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {view : TypedSource} {changed : List ExpressionId} {code : Expr}
    (edited : LocalView request.source view changed)
    (accepted : SourceCoreAllocationLayouts.allocate layouts owner active request = .ok code) :
    SourceCoreAllocationLayouts.allocate layouts owner active {request with source := view} = .ok code :=
  (CallableLambdaViewAllocations.allocate_eq (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata)).symm.trans accepted

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(item: Word) -> Word { return seed + item; }; }",
    "function qualified(flag: Bool) returns (Word, Bool) { let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
  ]}] }

private def checkOtherLookups (source view : TypedSource) (changed : ExpressionId) : IO Unit := do
  for node in source.nodes do
    match node with
    | .expression expression =>
      unless expression.id == changed do
        SourceCompilerFeatureSupport.require (source.lookupExpression? expression.id == view.lookupExpression? expression.id)
          "local edit changed complete metadata at a different expression"
    | .statement statement =>
      SourceCompilerFeatureSupport.require (source.lookupStatement? statement.id == view.lookupStatement? statement.id)
        "local edit changed a statement"

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "local edit checker" (checkProgram workspace)
  let roots ← ["make", "qualified"].mapM fun name => do
    match program.signatures.functions.find? (·.name == name) with
    | some signature => pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
    | none => throw (IO.userError s!"local edit signature missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program roots 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"local edit worklist {reprStr result}")
  let automatic ← SourceCompilerFeatureSupport.get "local edit base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "local edit indexed" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let lambda ← match prepared.ancestry.templates.lambdas.find? (fun row =>
      match row.node.form with | .lambda (binder :: _) _ _ => binder.name == "item" && binder.scheme.body == .word | _ => false) with
    | some lambda => pure lambda
    | none => throw (IO.userError "ordinary lambda template missing")
  let parameter ← match lambda.node.form with
    | .lambda (parameter :: _) _ _ => pure parameter
    | _ => throw (IO.userError "lambda parameter missing")
  let site ← match prepared.layouts.entries.find? (fun site => decide
      (site.key.owner = lambda.owner ∧ site.key.active = lambda.active ∧ site.key.binder = parameter ∧ site.key.initialized = true)) with
    | some site => pure site
    | none => throw (IO.userError "actual lambda allocation site missing")
  let source := lambda.context.inventory.source
  let originalNode ← match source.lookupExpression? lambda.node.id with
    | some node => pure node
    | none => throw (IO.userError "original lambda occurrence missing")
  let view := SourceCoreEvidence.withNode source {originalNode with type := .bool}
  SourceCompilerFeatureSupport.require (decide (source ≠ view)) "fixture did not change the parent metadata"
  checkOtherLookups source view originalNode.id
  SourceCompilerFeatureSupport.require (source.lookupExpression? originalNode.id != view.lookupExpression? originalNode.id)
    "changed parent was incorrectly included in the unchanged footprint"
  let request : SourceCoreSourceCells.Request :=
    ⟨source, site.key.scope, Renaming.insertion 2, parameter, site.key.payloadType, some (.var 1)⟩
  let allocate := prepared.layouts.allocatorAt lambda.owner lambda.active (fun error => .sourceAllocation (reprStr error))
  let old ← SourceCompilerFeatureSupport.get "original annotated allocation"
    (SourceCoreCallableIndexedAllocationFrames.annotateWithReceipt prepared.ancestry.layout.frame automatic.prepared.globals.length allocate request)
  let new ← SourceCompilerFeatureSupport.get "view annotated allocation"
    (SourceCoreCallableIndexedAllocationFrames.annotateWithReceipt prepared.ancestry.layout.frame automatic.prepared.globals.length allocate {request with source := view})
  SourceCompilerFeatureSupport.require (old.original == new.original && old.expression == new.expression)
    "local edit changed the real capture/payload/snapshot expression"
  let malformed := {request with payloadType := .unit}
  match allocate malformed, allocate {malformed with source := view} with
  | .error before, .error after =>
    SourceCompilerFeatureSupport.require (reprStr before == reprStr after) "metadata edit changed allocator rejection"
  | _, _ => throw (IO.userError "invalid payload type unexpectedly allocated")
  let changedForm := SourceCoreEvidence.withNode source {originalNode with form := .proxy .word}
  match allocate {request with source := changedForm} with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "altered source form bypassed allocation authentication")
  let binding ← match automatic.prepared.locals.bindings.find? (·.binder.name == "f") with
    | some binding => pure binding
    | none => throw (IO.userError "qualified local binding missing")
  let ids := binding.source.nodes.filterMap fun
    | .expression {id, form := .reference _ (.local binderId), ..} => if binderId == binding.binder.id then some id else none
    | _ => none
  SourceCompilerFeatureSupport.require (ids.length == 2) "qualified fixture lost either read occurrence"
  let mut accumulated := binding.source
  for id in ids do
    let view ← SourceCompilerFeatureSupport.get "qualified local normalization"
      (SourceCoreLocalEvidence.normalizeOccurrence program plan binding none binding.source id)
    checkOtherLookups binding.source view id
    SourceCompilerFeatureSupport.require (binding.source.lookupExpression? id != view.lookupExpression? id)
      "qualified normalization did not change its owned requirements"
    let repeated ← SourceCompilerFeatureSupport.get "repeated qualified normalization"
      (SourceCoreLocalEvidence.normalizeOccurrence program plan binding none view id)
    SourceCompilerFeatureSupport.require (view == repeated) "repeated normalization changed a stable source"
    let next ← SourceCompilerFeatureSupport.get "composed qualified normalization"
      (SourceCoreLocalEvidence.normalizeOccurrence program plan binding none accumulated id)
    checkOtherLookups accumulated next id
    accumulated := next
  for id in ids do
    let normalized ← SourceCompilerFeatureSupport.get "original reference authentication"
      (SourceCoreLocalEvidence.authenticateReference program plan binding none id)
    SourceCompilerFeatureSupport.require (accumulated.lookupExpression? id == some normalized.normalized)
      "successive normalizations failed to retain either read's authenticated metadata"
  IO.println "lambda local metadata edits: disjoint lookups, exact snapshot allocation and qualified normalization GREEN"
end Tests.SourceCoreCallableLambdaViewEdits

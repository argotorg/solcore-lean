import Solcore.Frontend.SourceCoreCallablePrincipals
import Solcore.Frontend.SourceCoreCompatibleMarkedFunctions
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallablePrincipals.Context.mk
#check_failure Solcore.Frontend.SourceCoreCallablePrincipals.Principal.mk
#check_failure Solcore.Frontend.SourceCoreCallablePrincipals.Entry.mk
#check_failure Solcore.Frontend.SourceCoreCallablePrincipals.Table.mk

/-! Actual checked artifacts retain unused direct lambda principals, including
empty native bundles, for-header lets and nested qualified contexts. This tests
compile-time metadata and allocation-key compatibility, not heap decoding,
emitted closure authentication, or dynamic view ancestry. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallablePrincipals
open Solcore Solcore.Frontend SourceInference TypeSystem
open SourceCoreCallablePrincipals

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "type WordFunction = function(Word) returns (Word);",
    "function keep<T>(item: T) returns (T) where T: Mark { return item; }",
    "function unusedMono() returns (Word) { let mono: WordFunction = lam(item: Word) -> Word { return item; }; return 1; }",
    "function unusedPoly() returns (Word) { let unused = lam(item) { return item; }; return 2; }",
    "function header() returns (Word) { for (let headerLambda: WordFunction = lam(item: Word) -> Word { return item; }; false; ) {} return 3; }",
    "function nested(flag: Bool) returns (Word, Word) {",
    " let outer = lam(value) { keep(value); let inner = lam(item) { return keep(item); };",
    " let untouched = lam(other) { return other; }; return inner(1); };",
    " return (outer(1), outer(flag)); }",
    "function enclosing<T>(value: T) returns (T) where T: Mark { let ignored = lam(item) { return item; }; return keep(value); }",
    "function reachable(flag: Bool) returns (Word, Bool) { return (enclosing(1), enclosing(flag)); }"
  ]}] }

private def prepareBase (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let requests ← ["unusedMono", "unusedPoly", "header", "nested", "reachable"].mapM fun name => do
    match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
    | _ => throw (IO.userError s!"principal fixture missing {name}")
  let plan ← match SourceSpecializationWorklist.run program requests 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"principal worklist failed: {reprStr result}")
  get "compatible principal artifact" (SourceCoreCompatibleFunctions.prepare program plan 512)

example {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    {context : Context program plan parents} (principal : Principal context) :
    SourceCoreAllocationContexts.BinderOrigin context.compilerSource principal.binder := principal.allocation_origin

example {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    (table : Table program plan parents) (origin : Origin plan parents)
    (member : origin ∈ origins plan parents) {declaration : Declaration}
    (declared : declaration ∈ directDeclarations (originKey origin).originalSource) :
    ∃ entry ∈ table.entries,
      entry.metadata.owner = origin.owner ∧ entry.metadata.active = origin.active ∧
      entry.metadata.originalSource = (originKey origin).originalSource ∧
      entry.metadata.inherited = (originKey origin).inherited ∧
      entry.metadata.originalDeclaration = declaration :=
  table.origin_declaration_retained origin member declared

example {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    (entry : Entry program plan parents) {key : SourceCoreAllocationLayouts.Key}
    (matching : entry.matchesLayout key) :
    SourceCoreAllocationContexts.BinderOrigin entry.context.compilerSource key.binder :=
  entry.layout_binder_origin matching

private def checkEntry {program : CheckedProgram} {plan : Plan} {parents : List Parent}
    (table : Table program plan parents) (entry : Entry program plan parents) : IO Unit := do
  let context := entry.context
  let principal := entry.principal
  assertTrue (decide (context.compilerSource = context.originalSource.applySubstitution context.active))
    "compiler source was replaced by the runtime requirement view"
  assertTrue (decide (context.source = SourceTypedRuntime.rewriteLocalRequirements context.inherited
    (context.originalSource.applySubstitution context.active))) "principal recipe changed"
  assertTrue (decide (principal.binder = principal.declaration.binder.applySubstitution context.active))
    "canonical allocation binder erased raw metadata"
  assertTrue (principal.binder.id.owner == context.owner.declaration && context.source.owner == context.owner.declaration)
    "principal owner metadata changed"
  assertTrue ((table.find? context.owner context.active principal.binder.id).isSome)
    "principal lookup lost a retained declaration"
  match insert [entry] entry with
  | .ok rows => assertTrue (rows.length == 1) "identical principal was duplicated"
  | .error error => throw (IO.userError s!"identical principal rejected: {reprStr error}")
  let wrongBinder := {principal.binder with name := principal.binder.name ++ "tampered"}
  let fakeKey : SourceCoreAllocationLayouts.Key :=
    ⟨context.owner, context.active, wrongBinder, [], .unit, true⟩
  assertTrue ((table.forLayout? fakeKey).isNone) "layout matched only a binder ID instead of full metadata"

private def checkLayouts {checked : Checked} (base : SourceCoreCompatibleFunctions.Prepared checked)
    (table : Table base.sourceProgram base.plan base.contexts) : IO Unit := do
  let marked ← get "marked principals" (SourceCoreCompatibleMarkedFunctions.prepare base 512)
  let relevant := marked.layouts.entries.filter fun layout =>
    ["mono", "unused", "outer", "inner", "untouched", "ignored", "headerLambda"].contains layout.key.binder.name
  assertTrue (!relevant.isEmpty) "no actual principal allocation layouts found"
  for layout in relevant do
    let entry ← match table.forLayout? layout.key with
      | some entry => pure entry
      | none => throw (IO.userError s!"real layout lost principal metadata: {reprStr layout.key}")
    assertTrue (decide (entry.principal.binder = layout.key.binder) &&
      decide (entry.context.active = layout.key.active) && decide (entry.context.owner = layout.key.owner))
      "actual layout matched a different principal context"
  let unused := relevant.filter (·.key.binder.name == "unused")
  assertTrue (unused.length == 1 && unused.all (fun layout => layout.key.payloadType == .unit))
    "unused generalized declaration did not keep its empty native bundle"

def run : IO Unit := do
  let program ← get "principal checker" (checkProgram workspace)
  let artifact ← prepareBase program
  let base := artifact.prepared
  let table ← get "principal inventory" (prepare base)
  for entry in table.entries do checkEntry table entry
  let named := fun name => table.entries.filter (·.principal.binder.name == name)
  assertTrue ((named "mono").length == 1 && (named "mono").all (fun entry => entry.principal.binder.scheme.quantified.isEmpty))
    "unused monomorphic principal was omitted"
  assertTrue ((named "unused").length == 1 && (named "unused").all (fun entry => !entry.principal.binder.scheme.quantified.isEmpty))
    "unused generalized principal was omitted"
  assertTrue ((named "headerLambda").length == 1) "for-header lambda declaration was omitted"
  let nested := (named "untouched").filter (fun entry => !entry.context.active.isEmpty)
  assertTrue (nested.length ≥ 2 && (nested.map (·.context.active)).eraseDups.length ≥ 2)
    "unused nested principal lost distinct full parent contexts"
  assertTrue (nested.any (fun entry => !entry.context.inherited.isEmpty))
    "qualified parent witnesses were not retained"
  assertTrue ((named "ignored").length == 2 && (named "ignored").all (fun entry => !entry.context.evidence.isEmpty))
    "actual specialized caller evidence was not retained"
  assertTrue ((table.entries.map (·.key)).length == (table.entries.map (·.key)).eraseDups.length)
    "principal keys were duplicated"
  checkLayouts base table
  IO.println "unused mono/poly/for principal metadata, parent contexts/evidence, exact allocation keys GREEN"
end Tests.SourceCoreCallablePrincipals

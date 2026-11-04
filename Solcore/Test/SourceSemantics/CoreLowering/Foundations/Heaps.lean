import Solcore.Frontend.SourceCoreAllocationCodebook
import Solcore.Core.BoundedSafety
import Solcore.Frontend.SourceCoreAllocationContexts
import Solcore.Frontend.SourceCoreCompatibleDataMatches
import Solcore.Frontend.SourceCoreAllocationDiscovery
import Solcore.Frontend.SourceCoreAllocationLayouts
import Solcore.Frontend.SourceCoreAllocationLedger
import Solcore.Frontend.SourceCoreHeapMarkers
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Test.SourceSemantics.CoreLowering.UnifiedCorpusSupport
import Solcore.Frontend.SourceCoreSession
import Solcore.Frontend.SourceCoreLocalCell
import Solcore.SourceSemantics.CoreLowering.LocalCell
import Solcore.Frontend.SourceCoreLocalEvidence
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAllocationReadiness
import Solcore.Test.SourceSemantics.CoreLowering.Closed.Owned
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodNestedEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedIndirectBodies
import Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSourceInversion
import Solcore.SourceSemantics.CoreLowering.SourceStagingHeapRelation

/-!
# Heap and allocation tests

Allocation layouts and ledgers, heap snapshots and markers, indexed sessions, local cells and owned
parameters.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreAllocationCodebook
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Allocation catalog fixtures exercise actual pure preparation/emission,
renaming, suffix installation and the final Core checker. The machine fixtures
only run the generated Core to check initializer/marker/payload order. They do
not use a source evaluator or claim a source-heap export theorem. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreAllocationCodebook
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreAllocationCodebook

private def check {α : Type} [DecidableEq α] [Repr α] (label : String)
    (actual expected : Except SourceCoreAllocationCodebook.Error α) : IO Unit :=
  match actual, expected with
  | .ok actual, .ok expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected result {repr actual}")
  | .error actual, .error expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected error {repr actual}")
  | _, _ => throw (IO.userError s!"{label}: {repr actual}")

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"allocation_codebook", by decide⟩], by decide⟩⟩, 0⟩
private def key : Key := ⟨owner, []⟩
private def active : TypeSystem.Substitution := [(⟨42⟩, .word)]
private def binder (index : Nat) (type : TypeSystem.Ty) : TypedBinder := {
  id := ⟨owner, index⟩, name := "local", scheme := .mono type }
private def a := binder 0 .bool
private def b := binder 1 .word
private def c := binder 2 .integer
private def source : TypedSource := { owner, inputs := [a, b], roots := [], nodes := [] }
private def inventory : ContextInventory := {
  owner := key, active, source, bindings := [⟨a, .bool⟩, ⟨b, .word⟩, ⟨c, .integer⟩] }
private def ambient : DataEnvironment := [⟨[.unit]⟩]
private def scope : SourceCoreLocalCell.Scope := [(b.id, .word), (a.id, .bool)]
private def context : Core.Context := [.integer, OptionalCell.referenceType .word, OptionalCell.referenceType .bool]
private def request : SourceCoreSourceCells.Request := {
  source, scope, references := fun index => index + 1, binder := c, payloadType := .integer
  payload := some (.letE (.newCell .integer (.integer 8)) (.integer 9)) }

private structure Observation where
  references : List Nat
  scopes : List SourceCoreLocalCell.Scope
  definitions : DataEnvironment
  expression : Expr
  deriving Repr, DecidableEq

private def compile (request : SourceCoreSourceCells.Request) (rename : Renaming := Renaming.id)
    (context : Core.Context := context) : Except SourceCoreAllocationCodebook.Error Observation := do
  let prepared ← prepare ambient [inventory]
  let raw ← emit prepared key active request
  let result ← finalize prepared 128 context (OptionalCell.referenceType .integer) (raw.rename rename)
  pure ⟨result.entries.flatMap (·.receipt.references), result.entries.map (·.receipt.scope), result.definitions, result.expression⟩

private def captureType : Core.Ty := .product (OptionalCell.referenceType .word) (OptionalCell.referenceType .bool)
private def layout : SourceCoreHeapMarkers.Layout := ⟨⟨1⟩, captureType⟩
private def captures : Expr := .pair (.var 1) (.var 2)
private def emitted : Expr := SourceCoreHeapMarkers.allocateInitialized layout .integer captures
  (.letE (.newCell .integer (.integer 8)) (.integer 9))


private def initial : Store := [.inRight .unit (.word Word.zero), .inRight .unit (.bool true)]
private def environment : Environment := [.integer 123,
  .cellRef (OptionalCell.cellType .word) 0, .cellRef (OptionalCell.cellType .bool) 1]
private def captured : Value := .pair (.cellRef (OptionalCell.cellType .word) 0)
  (.cellRef (OptionalCell.cellType .bool) 1)

private def malformed : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let _ ← finalize prepared 32 [] .unit (.construct ⟨prepared.sentinel, 0⟩ .unit)
  pure ()

private def escapedType : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let _ ← finalize prepared 32 [] (.function .unit .unit)
    (.lambda (.namedData prepared.sentinel) .unit .unit)
  pure ()

private def unknownKey : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let _ ← decode prepared (placeholder prepared (← wordKey 17) Word.zero [] .unit .bool .unit none)
  pure ()

private def ordinaryShape : Except SourceCoreAllocationCodebook.Error (Nat × Expr) := do
  let prepared ← prepare ambient [inventory]
  let expression := .pair (.word Word.zero) (.lambda .unit .unit .unit)
  let result ← finalize prepared 32 [] (.product .word (.function .unit .unit)) expression
  pure (result.entries.length, result.expression)

private def duplicateContexts : Except SourceCoreAllocationCodebook.Error Unit := do
  let _ ← prepare ambient [inventory, inventory]
  pure ()

private def duplicateBinders : Except SourceCoreAllocationCodebook.Error Unit := do
  let _ ← prepare ambient [{ inventory with bindings := [⟨a, .bool⟩, ⟨a, .bool⟩] }]
  pure ()



private def duplicateCaptures : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let _ ← emit prepared key active { request with references := fun _ => 1 }
  pure ()

private def forgedBinder : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let _ ← emit prepared key active { request with binder := { c with comptime := true } }
  pure ()

private def wrongSubstitution : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let _ ← emit prepared key [] request
  pure ()

/-- Final checker rejection catches ill-scoped real captures; nominal-marker
recognition alone cannot authenticate the caller's Core environment. -/
private def badEnvironment : Except SourceCoreAllocationCodebook.Error Unit := do
  let prepared ← prepare ambient [inventory]
  let raw ← emit prepared key active request
  let _ ← finalize prepared 128 [] (OptionalCell.referenceType .integer) raw
  pure ()

private def overflow : Except SourceCoreAllocationCodebook.Error Unit := do
  let _ ← prepare ambient [inventory] wordModulus
  pure ()

example : wordKey wordModulus = .error (.keyOverflow wordModulus) := by simp [wordKey, Word.ofNat?]

example : runStateful 200 (.initial emitted environment initial) =
    .done (.cellRef (OptionalCell.cellType .integer) 4)
      (initial ++ [.integer 8, SourceCoreHeapMarkers.markerValue layout captured, .inRight .unit (.integer 9)]) := by cbv

private def expressionNode : ExpressionNode := {
  id := ⟨⟨owner, 0⟩⟩, span := ⟨⟨.main, "allocation.solc"⟩, 0, 1⟩,
  type := .bool, form := .reference "true" (.builtinBoolean true) }

private def viewCheck (changeForm : Bool) : Except SourceCoreAllocationCodebook.Error Unit := do
  let canonical := { source with nodes := [.expression expressionNode] }
  let changedNode := { expressionNode with
    type := .word
    form := if changeForm then .reference "false" (.builtinBoolean false) else expressionNode.form }
  let changed := { source with nodes := [.expression changedNode] }
  let prepared ← prepare ambient [{ inventory with source := canonical }]
  let _ ← emit prepared key active { request with source := changed }
  pure ()

private def distinctContexts : Except SourceCoreAllocationCodebook.Error (Word × TypeSystem.Substitution) := do
  let otherActive := [(⟨42⟩, TypeSystem.Ty.bool)]
  let prepared ← prepare ambient [inventory, { inventory with active := otherActive }]
  let emission ← emitWithReceipt prepared key otherActive request
  pure (emission.receipt.context.key, emission.receipt.context.inventory.active)

private def twoSites : Except SourceCoreAllocationCodebook.Error (List Nat) := do
  let prepared ← prepare ambient [inventory]
  let raw ← emit prepared key active { request with payload := none }
  let result ← finalize prepared 128 context (OptionalCell.referenceType .integer) (.letE raw (raw.weakenAt 0))
  pure (result.entries.map (·.layout.dataType.index))

def run : IO Unit := do
  check "initialized metadata/captures/definitions" (compile request)
    (.ok ⟨[1, 2], [scope], ambient ++ [layout.definition], emitted⟩)
  check "renamed captures" (compile request (Renaming.insertion 0) (.bool :: context))
    (.ok ⟨[2, 3], [scope], ambient ++ [layout.definition],
      SourceCoreHeapMarkers.allocateInitialized layout .integer (.pair (.var 2) (.var 3))
        (.letE (.newCell .integer (.integer 8)) (.integer 9))⟩)
  check "uninitialized allocation" (compile { request with payload := none })
    (.ok ⟨[1, 2], [scope], ambient ++ [layout.definition], SourceCoreHeapMarkers.allocate layout .integer captures⟩)
  check "malformed reserved construct" malformed (.error .malformedPlaceholder)
  check "reserved type outside marker" escapedType (.error (.invalidType (.namedData ⟨1⟩)))
  check "unknown context key" unknownKey (.error (.unknownContextKey ⟨17, by decide⟩))
  check "ordinary Core shape preserved" ordinaryShape (.ok (0, .pair (.word Word.zero) (.lambda .unit .unit .unit)))
  check "duplicate contexts" duplicateContexts (.error .duplicateContexts)
  check "duplicate binders" duplicateBinders (.error (.invalidContext Word.zero))
  check "word overflow" overflow (.error (.keyOverflow wordModulus))
  check "duplicate capture slots" duplicateCaptures (.error .duplicateReferences)
  check "changed original binder" forgedBinder (.error (.binderMismatch c.id))
  check "complete substitution key" wrongSubstitution (.error (.missingContext key []))
  check "final checker" badEnvironment (.error (.finalBodyType (OptionalCell.referenceType .integer) none))
  check "raw metadata view accepted" (viewCheck false) (.ok ())
  check "changed source form rejected" (viewCheck true) (.error (.sourceViewMismatch Word.zero))
  check "full active contexts remain distinct" distinctContexts (.ok (⟨1, by decide⟩, [(⟨42⟩, .bool)]))
  check "each emitted site indexes its definition" twoSites (.ok [1, 2])

/-- An accepted emission retains exact source/capture/binder provenance. -/
example {prepared : Prepared} {owner : Key} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {expression : Expr}
    (accepted : emit prepared owner active request = .ok expression) :
    ∃ receipt : Receipt, decode prepared expression = .ok receipt ∧
      receipt.context.inventory.owner = owner ∧ receipt.context.inventory.active = active ∧
      receipt.binding.binding.binder = request.binder ∧ receipt.scope = request.scope ∧
      receipt.captures = SourceCoreSourceCells.captures request.references request.scope := by
  obtain ⟨emission, rfl⟩ := emit_receipt accepted
  exact ⟨emission.receipt, emission.decoded, emission.ownerExact, emission.activeExact,
    emission.binderExact, emission.scopeExact, emission.capturesExact⟩

end Tests.SourceCoreAllocationCodebook
end

section
-- leanmerge: from Solcore.Test.SourceCoreAllocationContexts
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreAllocationDiscovery
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Two-pass allocation discovery uses actual callback requests and preserved
capture layouts. Unused open metadata is accepted without projecting it; these
fixtures do not infer source semantics from a Core payload type. -/
set_option autoImplicit false
namespace Tests.SourceCoreAllocationDiscovery
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreAllocationDiscovery

private def check {α : Type} [DecidableEq α] [Repr α] (label : String)
    (actual expected : Except SourceCoreAllocationDiscovery.Error α) : IO Unit :=
  match actual, expected with
  | .ok actual, .ok expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected result {repr actual}")
  | .error actual, .error expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected error {repr actual}")
  | _, _ => throw (IO.userError s!"{label}: {repr actual}")

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"allocation_discovery", by decide⟩], by decide⟩⟩, 0⟩
private def key : Key := ⟨owner, []⟩
private def active : TypeSystem.Substitution := [(⟨99⟩, .bool)]
private def binder (index : Nat) (type : TypeSystem.Ty) : TypedBinder := {
  id := ⟨owner, index⟩, name := "allocated", scheme := .mono type }
private def outer := binder 0 (.function (.variable ⟨7⟩) (.variable ⟨7⟩))
private def unused := binder 1 (.variable ⟨88⟩)
private def allocated := binder 2 .bool
private def source : TypedSource := { owner, inputs := [outer], roots := [], nodes := [] }
private def canonical : SourceCoreAllocationDiscovery.Context := {
  owner := key, active, source, binders := [outer, unused, allocated] }
private def outerBundle : Core.Ty := .product (.function .word .word) (.function .bool .bool)
private def scope : Scope := [(outer.id, outerBundle)]
private def request : SourceCoreSourceCells.Request := {
  source, scope, references := fun index => index + 2, binder := allocated,
  payloadType := .bool, payload := some (.bool true) }
private def environment : Core.Context := [.word, .integer, OptionalCell.referenceType outerBundle]
private def layout : SourceCoreHeapMarkers.Layout := ⟨⟨0⟩, OptionalCell.referenceType outerBundle⟩
private def expectedInventory : SourceCoreAllocationCodebook.ContextInventory := {
  owner := key, active, source, bindings := [⟨outer, outerBundle⟩, ⟨allocated, .bool⟩] }

private structure Observation where
  inventories : List SourceCoreAllocationCodebook.ContextInventory
  references : List Nat
  definitions : DataEnvironment
  expression : Expr
  deriving Repr, DecidableEq

private def roundtrip : Except SourceCoreAllocationDiscovery.Error Observation := do
  let prepared ← prepare [] [canonical]
  let first ← emit prepared key active request
  let found ← discover prepared 128 first
  let second ← SourceCoreAllocationCodebook.emit found.codebook key active request
  let final ← SourceCoreAllocationCodebook.finalize found.codebook 128 environment
    (OptionalCell.referenceType .bool) second
  pure ⟨found.inventories, found.sites.flatMap (·.receipt.references), final.definitions, final.expression⟩

private def renamed : Except SourceCoreAllocationDiscovery.Error (List Nat × List Scope) := do
  let prepared ← prepare [] [canonical]
  let first ← emit prepared key active request
  let found ← discover prepared 128 (first.weakenAt 0)
  pure (found.sites.flatMap (·.receipt.references), found.sites.map (·.receipt.scope))

private def unusedMetadata : Except SourceCoreAllocationDiscovery.Error (List SourceCoreAllocationCodebook.ContextInventory) := do
  let prepared ← prepare [] [canonical]
  let found ← discover prepared 32 (.lambda .unit .unit .unit)
  pure found.inventories

private def repeated (changedPayload changedCapture : Bool) :
    Except SourceCoreAllocationDiscovery.Error (List SourceCoreAllocationCodebook.ContextInventory) := do
  let prepared ← prepare [] [canonical]
  let first ← emit prepared key active request
  let other := { request with
    payloadType := if changedPayload then .word else .bool
    scope := if changedCapture then [(outer.id, .word)] else scope
    payload := none }
  let second ← emit prepared key active other
  let found ← discover prepared 128 (.pair first second)
  pure found.inventories

private def contexts : Except SourceCoreAllocationDiscovery.Error (List SourceCoreAllocationCodebook.ContextInventory) := do
  let other := [(⟨99⟩, TypeSystem.Ty.word)]
  let prepared ← prepare [] [canonical, {canonical with active := other}]
  let first ← emit prepared key active request
  let second ← emit prepared key other { request with payloadType := .word, payload := none }
  let found ← discover prepared 128 (.pair first second)
  pure found.inventories

private def missingCapture : Except SourceCoreAllocationDiscovery.Error Unit := do
  let prepared ← prepare [] [canonical]
  let _ ← emit prepared key active { request with scope := [(⟨owner, 17⟩, .bool)] }
  pure ()

private def modifiedBinder : Except SourceCoreAllocationDiscovery.Error Unit := do
  let prepared ← prepare [] [canonical]
  let _ ← emit prepared key active { request with binder := {allocated with comptime := true} }
  pure ()

private def malformed : Except SourceCoreAllocationDiscovery.Error Unit := do
  let prepared ← prepare [] [canonical]
  let _ ← discover prepared 32 (.construct ⟨prepared.sentinel, 0⟩ .unit)
  pure ()

private def escaped : Except SourceCoreAllocationDiscovery.Error Unit := do
  let prepared ← prepare [] [canonical]
  let _ ← discover prepared 32 (.lambda (.namedData prepared.sentinel) .unit .unit)
  pure ()

private def unknownKey : Except SourceCoreAllocationDiscovery.Error Unit := do
  let prepared ← prepare [] [canonical]
  let _ ← discover prepared 32
    (placeholder prepared ⟨17, by decide⟩ Word.zero [] .unit .bool .unit none)
  pure ()

private def duplicateMetadata : Except SourceCoreAllocationDiscovery.Error Unit := do
  let _ ← prepare [] [{canonical with binders := [allocated, allocated]}]
  pure ()

private def overflow : Except SourceCoreAllocationDiscovery.Error Unit := do
  let _ ← prepare [] [canonical] wordModulus
  pure ()

private def exhausted : Except SourceCoreAllocationDiscovery.Error Unit := do
  let prepared ← prepare [] [canonical]
  let first ← emit prepared key active request
  let _ ← discover prepared 0 first
  pure ()

private def ordinary : Except SourceCoreAllocationDiscovery.Error Nat := do
  let prepared ← prepare [⟨[.unit]⟩] [canonical]
  let found ← discover prepared 32
    (.pair (.construct ⟨⟨0⟩, 0⟩ .unit) (.pair (.word Word.zero) (.lambda .unit .unit .unit)))
  pure found.sites.length

/-- Exercise the unchanged common allocation helper, then re-run that same
helper with the discovered checked allocator. Administrative result binders
are therefore introduced by the real helper rather than by the fixture. -/
private def commonHelper : Except SourceCoreAllocationDiscovery.Error (List Nat × Expr) := do
  let prepared ← prepare [] [canonical]
  let onError : SourceCoreAllocationDiscovery.Error → SourceCoreBasic.Error := fun _ =>
    .missingExpression ⟨⟨owner, 0⟩⟩
  let first ← (SourceCoreSourceCells.letInitialized (some (prepared.allocatorAt key active onError))
    source scope Renaming.id allocated .bool .bool (LanguageResult.success (.bool true))
    (LanguageResult.success (.bool false))).mapError (fun _ => .emissionMismatch)
  let found ← discover prepared 128 first
  let second ← (SourceCoreSourceCells.letInitialized (some (found.codebook.allocatorAt key active onError))
    source scope Renaming.id allocated .bool .bool (LanguageResult.success (.bool true))
    (LanguageResult.success (.bool false))).mapError (fun _ => .emissionMismatch)
  let final ← SourceCoreAllocationCodebook.finalize found.codebook 128
    [OptionalCell.referenceType outerBundle] (LanguageResult.resultType .bool) second
  pure (found.sites.flatMap (·.receipt.references), final.expression)

def run : IO Unit := do
  check "two-pass inventory and final checker" roundtrip
    (.ok ⟨[expectedInventory], [2], [layout.definition],
      SourceCoreHeapMarkers.allocateInitialized layout .bool (.var 2) (.bool true)⟩)
  check "renaming keeps actual captures" renamed (.ok ([3], [scope]))
  check "unused open metadata not projected" unusedMetadata (.ok [{expectedInventory with bindings := []}])
  check "same binder agrees across occurrences" (repeated false false) (.ok [expectedInventory])
  check "allocated payload disagreement" (repeated true false)
    (.error (.payloadMismatch allocated.id .bool .word))
  check "captured outer bundle disagreement" (repeated false true)
    (.error (.payloadMismatch outer.id outerBundle .word))
  check "full contexts have distinct discovered types" contexts
    (.ok [expectedInventory, {expectedInventory with
      active := [(⟨99⟩, .word)], bindings := [⟨outer, outerBundle⟩, ⟨allocated, .word⟩]}])
  check "unknown capture metadata" missingCapture (.error (.missingBinder Word.zero ⟨owner, 17⟩))
  check "original binder metadata exact" modifiedBinder (.error (.binderMismatch allocated.id))
  check "malformed reserved shape" malformed (.error .malformedPlaceholder)
  check "reserved type outside annotation" escaped (.error (.invalidType (.namedData ⟨0⟩)))
  check "unknown context key" unknownKey (.error (.unknownContextKey ⟨17, by decide⟩))
  check "duplicate original binder" duplicateMetadata (.error (.invalidContext Word.zero))
  check "Word key overflow" overflow (.error (.keyOverflow wordModulus))
  check "discovery exhaustion" exhausted (.error .traversalExhausted)
  check "ordinary nominal/lambda/word shape" ordinary (.ok 0)
  check "common source allocation helper" commonHelper
    (.ok ([1], LanguageResult.bind .bool (LanguageResult.success (.bool true))
      (.letE (SourceCoreHeapMarkers.allocateInitialized layout .bool (.var 1) (.var 0))
        ((LanguageResult.success (.bool false)).weakenAt 1))))

example {prepared : Prepared} {owner : Key} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {expression : Expr}
    (accepted : emit prepared owner active request = .ok expression) :
    ∃ emission : Emission prepared owner active request, emission.expression = expression :=
  emit_receipt accepted

example {prepared : Prepared} {fuel : Nat} {expression : Expr}
    (found : Discovered prepared fuel expression) :
    SourceCoreAllocationCodebook.prepare prepared.ambient found.inventories = .ok found.codebook :=
  found.checked

end Tests.SourceCoreAllocationDiscovery
end

section
-- leanmerge: from Solcore.Test.SourceCoreAllocationLayouts
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreAllocationLayouts.Prepared.mk

/-! Fixed artifact layouts survive different capture embeddings and initial
payload expressions. Syntactic clones share a nominal definition but generated
Core still appends distinct marker/payload pairs on every execution. -/
set_option autoImplicit false
namespace Tests.SourceCoreAllocationLayouts
open Solcore Solcore.Core Solcore.Frontend SourceInference
open SourceCoreAllocationLayouts

private def check {α : Type} [DecidableEq α] [Repr α] (label : String)
    (actual expected : Except SourceCoreAllocationLayouts.Error α) : IO Unit :=
  match actual, expected with
  | .ok actual, .ok expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected result {repr actual}")
  | .error actual, .error expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected error {repr actual}")
  | _, _ => throw (IO.userError s!"{label}: {repr actual}")

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"allocation_layouts", by decide⟩], by decide⟩⟩, 0⟩
private def key : SourceSpecialization.SpecializationKey := ⟨owner, []⟩
private def active : TypeSystem.Substitution := [(⟨42⟩, .bool)]
private def binder (index : Nat) (type : TypeSystem.Ty) : TypedBinder := {
  id := ⟨owner, index⟩, name := "local", scheme := .mono type }
private def capturedBinder := binder 0 .word
private def allocatedBinder := binder 1 .bool
private def source : TypedSource := { owner, inputs := [capturedBinder], roots := [], nodes := [] }
private def metadata : SourceCoreAllocationDiscovery.Context := {
  owner := key, active, source, binders := [capturedBinder, allocatedBinder] }
private def ambient : DataEnvironment := [⟨[.unit]⟩]
private def scope : SourceCoreLocalCell.Scope := [(capturedBinder.id, .word)]
private def request : SourceCoreSourceCells.Request := {
  source, scope, references := fun index => index + 1, binder := allocatedBinder,
  payloadType := .bool, payload := some (.bool true) }
private def layout : SourceCoreHeapMarkers.Layout := ⟨⟨1⟩, OptionalCell.referenceType .word⟩

private def fixture (includeUninitialized : Bool := false) : Except SourceCoreAllocationLayouts.Error Prepared := do
  let prepared ← (SourceCoreAllocationDiscovery.prepare ambient [metadata]).mapError Error.authentication
  let first ← (SourceCoreAllocationDiscovery.emit prepared key active request).mapError Error.authentication
  let repeated := .letE first (first.weakenAt 0)
  let expression ← if includeUninitialized then do
      let absent ← (SourceCoreAllocationDiscovery.emit prepared key active {request with payload := none})
        |>.mapError Error.authentication
      pure (.pair repeated absent)
    else pure repeated
  let discovered ← (SourceCoreAllocationDiscovery.discover prepared 128 expression).mapError Error.authentication
  prepare discovered

private def staticLayouts (includeUninitialized : Bool) :
    Except SourceCoreAllocationLayouts.Error (List Nat × DataEnvironment) := do
  let fixed ← fixture includeUninitialized
  pure (fixed.entries.map (·.layout.dataType.index), fixed.definitions)

private def differentEmbedding : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with references := fun index => index + 5, payload := some (.bool false)}

private def unobservedScope : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with scope := [], references := Renaming.id}

private def unobservedInitialization : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with payload := none}

private def initializedVariant : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture true
  allocate fixed key active {request with payload := none}

private def missingBinder : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with binder := binder 17 .bool}

private def mismatchPayload : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with payloadType := .word, payload := none}

private def duplicateCapture : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with scope := scope ++ scope}

private def mismatchMetadata : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key active {request with binder := {allocatedBinder with comptime := true}}

private def wrongContext : Except SourceCoreAllocationLayouts.Error Expr := do
  let fixed ← fixture
  allocate fixed key [] request

private structure RunObservation where
  value : Value
  store : Store
  definitions : DataEnvironment
  deriving Repr, DecidableEq

private def runTwice : Except SourceCoreAllocationLayouts.Error RunObservation := do
  let fixed ← fixture
  let first ← allocate fixed key active request
  let second ← allocate fixed key active {request with
    references := fun index => index + 2
    payload := some (.bool false)}
  let code := .letE first second
  unless Core.infer? [.integer, OptionalCell.referenceType .word] code fixed.definitions =
      some (OptionalCell.referenceType .bool) do throw .invalidDefinitions
  match Core.runStateful 200 (.initial code
      [.integer 123, .cellRef (OptionalCell.cellType .word) 0]
      [.inRight .unit (.word (Word.ofNatModulo 9))]) with
  | .done value store => pure ⟨value, store, fixed.definitions⟩
  | _ => throw .invalidDefinitions

private def emptyCatalog : Except SourceCoreAllocationLayouts.Error (List Nat × DataEnvironment) := do
  let prepared ← (SourceCoreAllocationDiscovery.prepare ambient [metadata]).mapError Error.authentication
  let discovered ← (SourceCoreAllocationDiscovery.discover prepared 32 (.lambda .unit .unit .unit)).mapError Error.authentication
  let fixed ← prepare discovered
  pure (fixed.entries.map (·.layout.dataType.index), fixed.definitions)

private def contextSpecific : Except SourceCoreAllocationLayouts.Error (List Nat) := do
  let other := [(⟨42⟩, TypeSystem.Ty.word)]
  let prepared ← (SourceCoreAllocationDiscovery.prepare ambient [metadata, {metadata with active := other}])
    |>.mapError Error.authentication
  let first ← (SourceCoreAllocationDiscovery.emit prepared key active request).mapError Error.authentication
  let second ← (SourceCoreAllocationDiscovery.emit prepared key other request).mapError Error.authentication
  let discovered ← (SourceCoreAllocationDiscovery.discover prepared 128 (.pair first second)).mapError Error.authentication
  let fixed ← prepare discovered
  pure (fixed.entries.map (·.layout.dataType.index))

private def malformed : Except SourceCoreAllocationLayouts.Error Unit := do
  let prepared ← (SourceCoreAllocationDiscovery.prepare ambient [metadata]).mapError Error.authentication
  let discovered ← (SourceCoreAllocationDiscovery.discover prepared 32 (.construct ⟨prepared.sentinel, 1⟩ .unit))
    |>.mapError Error.authentication
  let _ ← prepare discovered
  pure ()

private def overflow : Except SourceCoreAllocationLayouts.Error Unit := do
  let _ ← (SourceCoreAllocationDiscovery.prepare ambient [metadata] wordModulus).mapError Error.authentication
  pure ()

def run : IO Unit := do
  check "cloned site shares one fixed definition" (staticLayouts false) (.ok ([1], ambient ++ [layout.definition]))
  check "initialized form is part of static key" (staticLayouts true)
    (.ok ([1, 2], ambient ++ [layout.definition, layout.definition]))
  check "actual captures and initializer are request-specific" differentEmbedding
    (.ok (SourceCoreHeapMarkers.allocateInitialized layout .bool (.var 5) (.bool false)))
  check "unobserved lexical scope rejected" unobservedScope
    (.error (.unobservedLayout (Key.ofRequest key active {request with scope := [], references := Renaming.id})))
  check "unobserved initialized form rejected" unobservedInitialization
    (.error (.unobservedLayout (Key.ofRequest key active {request with payload := none})))
  check "registered uninitialized variant" initializedVariant
    (.ok (SourceCoreHeapMarkers.allocate ⟨⟨2⟩, OptionalCell.referenceType .word⟩ .bool (.var 1)))
  check "unknown original binder rejected before selection" missingBinder
    (.error (.authentication (.missingBinder Word.zero (binder 17 .bool).id)))
  check "payload type reauthenticated" mismatchPayload
    (.error (.authentication (.payloadMismatch allocatedBinder.id .bool .word)))
  check "duplicate source capture rejected" duplicateCapture (.error (.authentication .duplicateScope))
  check "binder flags reauthenticated" mismatchMetadata (.error (.authentication (.binderMismatch allocatedBinder.id)))
  check "full context reauthenticated" wrongContext (.error (.authentication (.missingContext key [])))
  let captured := .cellRef (OptionalCell.cellType .word) 0
  check "shared layout still allocates two distinct runtime pairs" runTwice
    (.ok ⟨.cellRef (OptionalCell.cellType .bool) 4,
      [.inRight .unit (.word (Word.ofNatModulo 9)), SourceCoreHeapMarkers.markerValue layout captured,
        .inRight .unit (.bool true), SourceCoreHeapMarkers.markerValue layout captured, .inRight .unit (.bool false)],
      ambient ++ [layout.definition]⟩)
  check "no sites preserves only ambient catalog" emptyCatalog (.ok ([], ambient))
  check "full contextual identities never share layout" contextSpecific (.ok [1, 2])
  check "malformed initial discovery refused" malformed (.error (.authentication .malformedPlaceholder))
  check "metadata Word overflow never wraps" overflow (.error (.authentication (.keyOverflow wordModulus)))

example {prepared : Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    (receipt : Allocation prepared owner active request) :
    ∃ site ∈ prepared.origin.discovered.sites, Key.ofReceipt site.receipt = Key.ofRequest owner active request :=
  receipt.observed

example {prepared : Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    (receipt : Allocation prepared owner active request) : receipt.entry.layout.Registered prepared.definitions :=
  receipt.registered

end Tests.SourceCoreAllocationLayouts
end

section
-- leanmerge: from Solcore.Test.SourceCoreAllocationLedger
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreAllocationLedger.Ledger.mk

/-! Actual fixed discovery layouts are scanned with opaque initial source
cells, administrative cells, aliases, pending allocations and cyclic payloads.
These tests certify the ledger boundary, not arbitrary store provenance or a
source execution corresponding to each hand-constructed native store. -/
set_option autoImplicit false
namespace Tests.SourceCoreAllocationLedger
open Solcore Solcore.Core Solcore.Frontend SourceInference
open SourceCoreAllocationLedger

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"allocation_ledger", by decide⟩], by decide⟩⟩, 0⟩
private def key : SourceSpecialization.SpecializationKey := ⟨owner, []⟩
private def active : TypeSystem.Substitution := [(⟨42⟩, .word)]
private def binder (index : Nat) (type : TypeSystem.Ty) : TypedBinder := {
  id := ⟨owner, index⟩, name := "local", scheme := .mono type }
private def a := binder 0 .word
private def b := binder 1 .word
private def c := binder 2 .bool
private def f := binder 3 (.function .unit .unit)
private def d := binder 4 .word
private def source : TypedSource := { owner, inputs := [], roots := [], nodes := [] }
private def metadata : SourceCoreAllocationDiscovery.Context := {
  owner := key, active, source, binders := [a, b, c, f, d] }
private def ambient : DataEnvironment := [⟨[.unit]⟩]
private def wordScope : Scope := [(a.id, .word)]
private def aliasScope : Scope := [(a.id, .word), (b.id, .word)]
private def functionType : Ty := .function .unit .unit
private def functionScope : Scope := [(f.id, functionType)]
private def request (allocated : TypedBinder) (type : Ty) (scope : Scope) : SourceCoreSourceCells.Request := {
  source, scope, references := Renaming.id, binder := allocated, payloadType := type, payload := none }
private def requests : List SourceCoreSourceCells.Request :=
  [request a .word [], request b .word wordScope, request c .bool aliasScope,
   request f functionType [], request d .word functionScope]

private def fixture : Except String Layouts := do
  let prepared ← (SourceCoreAllocationDiscovery.prepare ambient [metadata]).mapError reprStr
  let emitted ← requests.mapM (fun request =>
    (SourceCoreAllocationDiscovery.emit prepared key active request).mapError reprStr)
  let discovered ← (SourceCoreAllocationDiscovery.discover prepared 512
    (emitted.foldr Expr.pair .unit)).mapError reprStr
  (SourceCoreAllocationLayouts.prepare discovered).mapError reprStr

private def layout (id : Nat) (scope : Scope) : SourceCoreHeapMarkers.Layout :=
  ⟨⟨id⟩, SourceCoreSourceCells.captureType scope⟩
private def marker (id : Nat) (scope : Scope) (captures : Value) : Value :=
  SourceCoreHeapMarkers.markerValue (layout id scope) captures
private def reference (type : Ty) (index : Nat) : Value := .cellRef (OptionalCell.cellType type) index
private def word (value : Nat) : Value := .word (Word.ofNatModulo value)
private def present (value : Value) : Value := .inRight .unit value

/-- Deliberately invalid and unreachable legacy cells are retained verbatim.
The scan must not inspect their type, body, capture references or metadata. -/
private def initial : SourceHeap := [
  { type := .error, value := some (.closure [] .unit [] source key [(a.id, ⟨999⟩)] []) },
  { type := .word, value := some (.proxy (.comptime .bool)) }]

private def store : Store := [word 99,
  marker 1 [] .unit, present (word 9),
  marker 2 wordScope (reference .word 2), present (word 10),
  marker 3 aliasScope (.pair (reference .word 2) (reference .word 2)), present (.bool true),
  .closure .unit .unit .unit [], .constructed ⟨⟨0⟩, 0⟩ .unit]

private structure Observation where
  locations : List LocationEntry
  environments : List SourceEnvironment
  payloads : List (Option Value)
  pending : Bool
  next : SourceLocation
  deriving Repr, DecidableEq

private def observe (layouts : Layouts) (initial : SourceHeap) (store : Store) : Except SourceCoreAllocationLedger.Error Observation := do
  let ledger ← scan layouts initial store
  pure ⟨ledger.locations, ledger.rows.map (·.environment), ledger.rows.map (·.payload),
    ledger.pending.isSome, ledger.nextSourceLocation⟩

private def check {α : Type} [DecidableEq α] [Repr α] (label : String)
    (actual expected : Except SourceCoreAllocationLedger.Error α) : IO Unit :=
  match actual, expected with
  | .ok actual, .ok expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected result {repr actual}")
  | .error actual, .error expected =>
      unless actual = expected do throw (IO.userError s!"{label}: unexpected error {repr actual}")
  | _, _ => throw (IO.userError s!"{label}: {repr actual}")

private def expected : Observation := ⟨
  [⟨2, ⟨2⟩, .word⟩, ⟨4, ⟨3⟩, .word⟩, ⟨6, ⟨4⟩, .bool⟩],
  [[], [(a.id, ⟨2⟩)], [(a.id, ⟨2⟩), (b.id, ⟨2⟩)]],
  [some (word 9), some (word 10), some (.bool true)], false, ⟨5⟩⟩

private def prefixExport (layouts : Layouts) : Except SourceCoreAllocationLedger.Error (String × String × Nat) := do
  let ledger ← scan layouts initial store
  let exported ← ledger.exportHeap (fun _ => Except.ok ({type := .unit, value := some .unit} : SourceTypedRuntime.Cell))
  pure (reprStr ledger.initialHeap, reprStr (exported.take initial.length), exported.length)

private def recursiveValue : Value :=
  .closure .unit .unit .unit [reference functionType 1]
private def recursiveStore : Store := [marker 4 [] .unit, present recursiveValue,
  marker 5 functionScope (reference functionType 1), present (word 7)]

private def recursiveWorld : StoreTyping :=
  [.namedData ⟨4⟩, OptionalCell.cellType functionType, .namedData ⟨5⟩, OptionalCell.cellType .word]

/-- A closure may capture the very optional cell which contains it. Runtime
typing checks the finite world, without recursively unfolding the heap. -/
private theorem recursiveValue_typed {definitions : DataEnvironment} {world : StoreTyping}
    (self : world[1]? = some (OptionalCell.cellType functionType)) :
    RuntimeValueHasType world recursiveValue functionType definitions :=
  .closure (.cons (.cellRef self) .nil) .unit

private theorem recursiveStore_typed {definitions : DataEnvironment}
    (first : (layout 4 []).Registered definitions)
    (second : (layout 5 functionScope).Registered definitions) :
    RuntimeStoreHasTypes recursiveWorld recursiveStore definitions := by
  have contents : RuntimeEnvironmentHasTypes recursiveWorld recursiveStore recursiveWorld definitions :=
    .cons (.constructed first.payloadLookup .unit)
      (.cons (.inRight (recursiveValue_typed rfl))
        (.cons (.constructed second.payloadLookup (.cellRef rfl))
          (.cons (.inRight .word) .nil)))
  exact ⟨rfl, fun found => contents.lookup found⟩

private def typedCyclic (layouts : Layouts) : Except SourceCoreAllocationLedger.Error (List LocationEntry) := do
  if first : layouts.definitions[4]? = some (layout 4 []).definition then
    if second : layouts.definitions[5]? = some (layout 5 functionScope).definition then
      let firstRegistered : (layout 4 []).Registered layouts.definitions := ⟨.unit, first⟩
      let secondRegistered : (layout 5 functionScope).Registered layouts.definitions :=
        ⟨.cell (.sum .unit (.function .unit .unit)), second⟩
      let certified ← scanTyped layouts [] recursiveWorld recursiveStore
        (recursiveStore_typed firstRegistered secondRegistered)
      pure certified.ledger.locations
    else throw .invalidLedgerOrder
  else throw .invalidLedgerOrder

def run : IO Unit := do
  let layouts ← match fixture with
    | .ok layouts => pure layouts
    | .error error => throw (IO.userError error)
  check "opaque prefix, admin cells and aliased captured source locations"
    (observe layouts initial store) (.ok expected)
  check "opaque prefix is never decoded or validated" (prefixExport layouts)
    (.ok (reprStr initial, reprStr initial, 5))
  let pending := store.take 4
  check "marker-only tail reserves no source location" (observe layouts initial pending)
    (.ok ⟨[⟨2, ⟨2⟩, .word⟩], [[]], [some (word 9)], true, ⟨3⟩⟩)
  check "resume completes payload with stable earlier locations" (observe layouts initial (store.take 5))
    (.ok ⟨[⟨2, ⟨2⟩, .word⟩, ⟨4, ⟨3⟩, .word⟩], [[], [(a.id, ⟨2⟩)]],
      [some (word 9), some (word 10)], false, ⟨4⟩⟩)
  check "initialization flag describes allocation, not later payload contents"
    (observe layouts [] [marker 1 [] .unit, .inLeft .word .unit])
    (.ok ⟨[⟨1, ⟨0⟩, .word⟩], [[]], [none], false, ⟨1⟩⟩)
  check "pending first marker with opaque prefix" (observe layouts initial [marker 1 [] .unit])
    (.ok ⟨[], [], [], true, ⟨2⟩⟩)
  check "unrelated store append preserves completed ledger" (observe layouts initial
      (store ++ [.integer 100, .cellRef .integer 77, .inRight .unit (word 4)])) (.ok expected)
  check "admin frame changes do not affect source mapping" (observe layouts initial
      ([.integer (-123)] ++ store.drop 1)) (.ok expected)
  check "recursive payload is finite and capture references share completed cells"
    (observe layouts [] recursiveStore)
    (.ok ⟨[⟨1, ⟨0⟩, functionType⟩, ⟨3, ⟨1⟩, .word⟩], [[], [(f.id, ⟨0⟩)]],
      [some recursiveValue, some (word 7)], false, ⟨2⟩⟩)
  check "finite runtime world types the whole cyclic store and typed scan"
    (typedCyclic layouts) (.ok [⟨1, ⟨0⟩, functionType⟩, ⟨3, ⟨1⟩, .word⟩])
  let first := store.take 3
  check "capture must reference a completed source cell" (observe layouts []
    (first ++ [marker 2 wordScope (reference .word 0), present (word 1)]))
    (.error (.unknownCaptureLocation 0))
  check "capture cannot reference the future payload" (observe layouts []
    [marker 2 wordScope (reference .word 1), present (word 1)])
    (.error (.unknownCaptureLocation 1))
  check "capture annotation is checked" (observe layouts []
    (first ++ [marker 2 wordScope (.cellRef .word 2), present (word 1)]))
    (.error (.invalidReferenceType .word (OptionalCell.cellType .word)))
  check "actual captured cell payload type is checked" (observe layouts []
    (first ++ [marker 5 functionScope (reference functionType 2), present (word 1)]))
    (.error (.capturePayloadMismatch 2 .word functionType))
  check "capture product pack must match the exact scope" (observe layouts []
    (first ++ [marker 3 aliasScope (reference .word 2), present (.bool true)]))
    (.error .invalidCaptureShape)
  check "empty scope still requires unit capture" (observe layouts []
    [marker 1 [] (.bool false), present (word 1)]) (.error .invalidCaptureShape)
  check "known owner with wrong constructor is rejected" (observe layouts []
    [.constructed ⟨⟨1⟩, 1⟩ .unit, present (word 1)])
    (.error (.invalidKnownConstructor 0 ⟨⟨1⟩, 1⟩ ⟨⟨1⟩, 0⟩))
  check "interleaved known marker cannot stand in for payload" (observe layouts []
    [marker 1 [] .unit, marker 1 [] .unit]) (.error (.invalidOptionalPayload 1 .word))
  check "absent payload annotation must match native payload type" (observe layouts []
    [marker 1 [] .unit, .inLeft .bool .unit]) (.error (.invalidOptionalPayload 1 .word))
  check "present payload must match native payload type" (observe layouts []
    [marker 1 [] .unit, present (.bool true)]) (.error (.invalidOptionalPayload 1 .word))
  check "empty native store preserves opaque source prefix" (observe layouts initial [])
    (.ok ⟨[], [], [], false, ⟨2⟩⟩)

example {layouts : Layouts} {store : Store} (row : Row layouts store) {world : StoreTyping}
    (typed : RuntimeStoreHasTypes world store layouts.definitions) :
    RuntimeValueHasType world row.captures row.entry.layout.captureType layouts.definitions :=
  row.captures_typed typed

example {layouts : Layouts} {initial : SourceHeap} {store : Store} (ledger : Ledger layouts initial store)
    (index : Fin ledger.rows.length) :
    (ledger.rows[index]).environment.map Prod.fst = (ledger.rows[index]).entry.key.scope.map Prod.fst :=
  (ledger.capture_prior_exact index).binders_exact

example {layouts : Layouts} {initial : SourceHeap} {store : Store} (ledger : Ledger layouts initial store)
    (decode : Row layouts store → Except SourceCoreAllocationLedger.Error SourceTypedRuntime.Cell) {heap : SourceHeap}
    (exported : ledger.exportHeap decode = .ok heap) : heap.take initial.length = initial :=
  ledger.exportHeap_prefix decode exported

end Tests.SourceCoreAllocationLedger
end

section
-- leanmerge: from Solcore.Test.SourceCoreHeapMarkers
/-! Source payload references retain their caller scope when hidden marker
cells precede them. Native checkpoints can stop between the two allocations;
the marker alone does not decode as a completed source cell. -/

set_option autoImplicit false
namespace Tests.SourceCoreHeapMarkers
open Solcore Solcore.Core
open Solcore.Frontend.SourceCoreHeapMarkers

private def word (value : Nat) : Word := Word.ofNatModulo value
private def layout : Layout := ⟨⟨0⟩, .cell .word⟩
private def definitions : DataEnvironment := [layout.definition]
private def functionType : Ty := .function .word .word
private def functionBody : Expr := .binary .wordAdd (.loadCell (.var 1)) (.var 0)
private def initialized : Program := ⟨.word,
  .letE (.newCell .word (.word (word 7)))
    (.letE (allocateInitialized layout functionType (.var 0)
      (.lambda .word .word functionBody))
      (.letE (.storeCell (.var 1) (.word (word 9)))
        (.caseE (.loadCell (.var 1)) (.word Word.zero) (.apply (.var 0) (.word (word 3)))))),
  definitions⟩
private def uninitialized : Program := ⟨LanguageResult.resultType functionType,
  .letE (.newCell .word (.word (word 7)))
    (.letE (allocate layout functionType (.var 0))
      (OptionalCell.read functionType (.var 0) (word 61))), definitions⟩
private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

example : layout.Registered definitions := ⟨.cell .word, rfl⟩

/-- The uninitialized function needs no dummy closure, even with metadata. -/
example : HasType [.cell .word] (allocate layout functionType (.var 0))
    (OptionalCell.referenceType functionType) definitions :=
  allocate_hasType ⟨.cell .word, rfl⟩ (.var rfl) (.function .word .word)

def run : IO Unit := do
  assertTrue initialized.check "marked function allocation failed Core checking"
  match initialized.runStateful 10000 with
  | .done value store =>
      assertTrue (value == .word (word 12)) "marker binding changed the actual closure capture"
      assertTrue (store.length == 3 && store[0]? == some (.word (word 9))) "marked allocation changed its store prefix"
      match completedPair layout store 1 with
      | some (.cellRef .word 0, .inRight .unit (.closure .word .word body captured)) =>
          assertTrue (body == functionBody && captured == [.cellRef .word 0])
            "marker or initializer temporary escaped into closure captures"
      | _ => throw (IO.userError "marked function payload or capture metadata changed")
  | other => throw (IO.userError s!"marked function did not complete: {reprStr other}")
  assertTrue uninitialized.check "marked uninitialized function failed Core checking"
  match uninitialized.runStateful 10000 with
  | .done (.inLeft type (.word reason)) store =>
      assertTrue (type == functionType && reason == word 61) "marked uninitialized read changed its source fault"
      assertTrue (completedPair layout store 1 == some (.cellRef .word 0, .inLeft functionType .unit))
        "uninitialized source cell was lost during marker observation"
  | other => throw (IO.userError s!"marked uninitialized function changed: {reprStr other}")
  let mut sawPartial := false
  for fuel in List.range 96 do
    match initialized.runStateful fuel with
    | .outOfFuel checkpoint =>
        if checkpoint.store.length == 2 then
          sawPartial := true
          assertTrue ((completedPair layout checkpoint.store 1).isNone)
            "marker-only checkpoint exported an unfinished source cell"
        match runStateful 10000 checkpoint with
        | .done value _ => assertTrue (value == .word (word 12)) "marked source cell resume changed"
        | other => throw (IO.userError s!"marked source cell resume failed: {reprStr other}")
    | .done value _ => assertTrue (value == .word (word 12)) "marked source cell finite result changed"
    | .fault error _ => throw (IO.userError s!"marked source cell machine fault: {reprStr error}")
  assertTrue sawPartial "native checkpoints did not cover a marker without its payload"
  IO.println "ordinary Core source allocation markers and native checkpoints GREEN"

end Tests.SourceCoreHeapMarkers
end

section
-- leanmerge: from Solcore.Test.SourceCoreHeapSnapshot
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Snapshot.mk
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Snapshot.saved
#check_failure Solcore.Frontend.SourceCoreIndexedSession.PrefixSnapshot.sourcePrefix
#check_failure Solcore.Frontend.SourceCoreHeapSnapshot.ObservedValue.source
#check_failure Solcore.Frontend.SourceCoreHeapSnapshot.Principal.mk
#check_failure Solcore.Frontend.SourceCoreHeapSnapshot.Principal.source
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Value.closure
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false
namespace Tests.SourceCoreHeapSnapshot
open Solcore Solcore.Frontend SourceCoreIndexedSession
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α := SourceCoreUnifiedCorpusSupport.get label
private def require (condition : Bool) (message : String) : IO Unit := SourceCoreUnifiedCorpusSupport.assertTrue condition message
private def word (value : Nat) : Value := .word (Core.Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "function inc(n: Word) returns (Word) { return n + 1; }",
  "function sum(a: Word, b: Word) returns (Word) { return a + b; }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { let f: function(Word) returns (Word) = lam(step: Word) { seed += step; return seed; }; return f; }",
  "function use(f: function(Word) returns (Word), n: Word) returns (Word) { return f(n); }",
  "function unused(captured: Word) returns (Word) { let unused = lam(item) { return (item, captured); }; return captured; }",
  "function stored(seed: Word) returns (Word) { let f: function(Word) returns (Word) = lam(step: Word) { seed += step; return seed; }; return seed; }",
  "function views(seed: Word) returns (Word) { let f = lam(item) { seed += 1; return item; }; f(true); return f(4); }",
  "function echo(table: mapping(Word => @Word)) returns (mapping(Word => @Word)) { return table; }",
  "function sourceClosure() returns (function() returns (Word)) { let captured: Word = 7; return lam() -> Word { return captured; }; }",
  "function sourceView(seed: Word) returns (function(Word) returns (Word)) { let f = lam(item) { return item; }; return f; }",
  "function failure(seed: Word) returns (Word) { let f = lam() -> Word { seed += 2; let absent: Word; return absent; }; return f(); }",
  "function spin() returns (Word) { while (true) {} return 0; }"
]
private def names : List String := ["inc", "sum", "make", "use", "unused", "stored", "views", "echo", "sourceClosure", "sourceView", "failure", "spin"]

private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (args : List Value) : IO (Completion artifact) := do
  match ← session.run key args 300000 with
  | .ok (.succeeded completion) => pure completion
  | .ok (.failed reason _) => throw (IO.userError s!"snapshot language failure: {reprStr reason}")
  | .ok (.exportError error _) => throw (IO.userError s!"snapshot export: {reprStr error}")
  | .ok (.outOfFuel _) => throw (IO.userError "snapshot execution exhausted")
  | .error error => throw (IO.userError s!"snapshot call rejected: {reprStr error}")

private def ready {artifact : Artifact} (snapshot : Snapshot artifact) : IO (Session artifact) :=
  match snapshot.restore with
  | .ready session => pure session
  | .suspended _ => throw (IO.userError "ready snapshot restored a checkpoint")

example {artifact : Artifact} (snapshot : Snapshot artifact) := snapshot.source_length
example {artifact : Artifact} (snapshot : Snapshot artifact) := snapshot.prefix_length
example {artifact : Artifact} (snapshot : Snapshot artifact) := snapshot.restore_native_size
example {artifact : Artifact} (snapshot : Snapshot artifact) := snapshot.restore_world
example {artifact : Artifact} (snapshot : Snapshot artifact) := snapshot.restore_authority
example {artifact : Artifact} (snapshot : Snapshot artifact) := snapshot.restore_typed

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "opaque heap snapshots" content names
  let recipe ← get "snapshot recipe" (Recipe.prepare compiled)
  let artifact ← recipe.open
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  -- This migration-only initial state was produced by the same cached Core
  -- artifact. Its source closure and captured indices never become Core refs.
  let (rawReturned, previous) ← match compiled.run (← key "sourceClosure") [] 1024 300000 with
    | .ok result => match result.observation with
      | .done value final => pure (value, final)
      | other => throw (IO.userError s!"prefix native fixture failed: {reprStr other}")
    | .error error => throw (IO.userError s!"prefix fixture rejected: {reprStr error}")
  let (rawView, rawPrefix) ← match compiled.run (← key "sourceView") [.word (Core.Word.ofNatModulo 5)] 1024 300000 previous with
    | .ok result => match result.observation with
      | .done value final => pure (value, final)
      | other => throw (IO.userError s!"prefix view native fixture failed: {reprStr other}")
    | .error error => throw (IO.userError s!"prefix view fixture rejected: {reprStr error}")
  let initialState : SourceTypedRuntime.RuntimeState := {heap := rawPrefix.heap ++ [
      ⟨.function .unit .word, some rawReturned⟩,
      ⟨.function .word .word, some rawView⟩,
      ⟨.comptime (.proxy .word), some (.proxy (.comptime .word))⟩,
      ⟨.mapping .word (.proxy .word), some (.mapping (.comptime .word) (.proxy (.comptime .word)) [
        (.word (Core.Word.ofNatModulo 1), .proxy (.comptime .word)),
        (.word (Core.Word.ofNatModulo 1), .proxy (.comptime .word))])⟩,
      ⟨.parameter ⟨(← key "unused").declaration, 999⟩, none⟩]}
  let inert ← match Legacy.preparePrefix artifact initialState 1024 with
    | some acceptedPrefix => pure acceptedPrefix | none => throw (IO.userError "accepted opaque closure/raw prefix rejected")
  let initial ← match (← artifact.bootstrapFromPrefix inert).resume 300000 with
    | .ready session => pure session
    | _ => throw (IO.userError "snapshot bootstrap failed")
  let original ← get "initial snapshot" (← initial.snapshot)
  require (original.prefixSize == initialState.heap.length && original.heapSize == initialState.heap.length)
    "source prefix changed or administrative globals leaked into observation"
  require (original.cells.map (·.type) == initialState.heap.map (·.type)) "raw source prefix types changed"
  require (original.cellAt? (initialState.heap.length - 1) |>.any fun cell => cell.value.isNone)
    "open uninitialized prefix was lost"
  match (original.cellAt? (initialState.heap.length - 2)).bind (·.value) with
  | some (.legacy observed) => match observed.view with
    | .mapping (.comptime _) (.proxy (.comptime _)) entries =>
      require (entries.length == 2) "ordered duplicate raw prefix mapping changed"
    | _ => throw (IO.userError "raw mapping header was canonicalized")
  | _ => throw (IO.userError "inert mapping observation was not opaque legacy data")
  match (original.cellAt? (rawPrefix.heap.length + 1)).bind (·.value) with
  | some (.legacy observed) => match observed.view with
    | .instantiated _ requirements principal =>
      require requirements.isEmpty "unqualified view invented witnesses"
      match principal.view with
      | .closure parameters _ _ environment _ =>
        require (parameters.length == 1 && !environment.isEmpty) "raw principal header/captures were lost"
      | _ => throw (IO.userError "instantiated observation lost original principal")
    | _ => throw (IO.userError "prefix observation erased instantiated wrapper")
  | _ => throw (IO.userError "prefix instantiated cell unavailable")
  let importedAgain ← match (← artifact.bootstrapFromPrefix original.prefix).resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "opaque prefix rebootstrap failed")
  let reimported ← get "reimported prefix view" (← importedAgain.snapshot)
  require (reimported.cells.map (·.type) == original.cells.map (·.type) &&
      reimported.prefixSize == original.prefixSize && importedAgain.installedGlobalsPresent)
    "opaque prefix reuse changed raw types or active native global layout"
  match importedAgain.restoreSnapshot original with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "prefix reuse transferred the original native snapshot issuer")
  let restoredInitial ← ready original
  let maker ← execute restoredInitial (← key "make") [word 10]
  let kept ← get "captured snapshot" (← maker.session.snapshot)
  let before ← ready kept
  let changed ← execute before (← key "use") [maker.value, word 2]
  require (changed.value == word 12) "restored capture lost its native shared cell"
  let rolledBack ← match changed.session.restoreSnapshot kept with
    | .ok (.ready session) => pure session
    | _ => throw (IO.userError "same-session snapshot rejected")
  let replayed ← execute rolledBack (← key "use") [maker.value, word 3]
  require (replayed.value == word 13) "snapshot kept the newer store rather than its captured store"
  let replayedAgain ← execute (← ready kept) (← key "use") [maker.value, word 3]
  require (replayedAgain.value == word 13) "duplicate restore changed handle ownership or captured state"
  -- Snapshot-created function capabilities belong to the returned registry.
  let retainedHandles := kept.cells.filterMap fun cell => match cell.value with
    | some (.data (.function handle)) => some handle | _ => none
  require (!retainedHandles.isEmpty) "source lambda parameter/cell did not export a capability"
  for handle in retainedHandles do
    discard <| get "snapshot handle exact registry" ((← ready kept).authenticate 1024 handle.sourceType (.function handle))
  let unexported ← execute replayed.session (← key "stored") [word 70]
  let branchA ← get "new heap capability branch A" (← unexported.session.snapshot)
  let branchB ← get "new heap capability branch B" (← unexported.session.snapshot)
  let newlyIssued := branchA.cells.drop kept.heapSize |>.filterMap fun cell => match cell.value with
    | some (.data (.function handle)) => some handle | _ => none
  let newHandle ← match newlyIssued.getLast? with
    | some handle => pure handle | none => throw (IO.userError "unexported stored lambda did not issue snapshot handle")
  match unexported.session.authenticate 1024 newHandle.sourceType (.function newHandle) with
  | .error {code := .unknownHandle, ..} => pure ()
  | _ => throw (IO.userError "snapshot silently changed the original registry")
  discard <| get "new snapshot registry" ((← ready branchA).authenticate 1024 newHandle.sourceType (.function newHandle))
  match (← ready branchB).authenticate 1024 newHandle.sourceType (.function newHandle) with
  | .error {code := .unknownHandle, ..} => pure ()
  | _ => throw (IO.userError "branched snapshots collided at the same registry slot")
  let invoked ← match ← (← ready branchA).invokePacked newHandle (word 2) 300000 with
    | .ok (.succeeded completion) => pure completion
    | _ => throw (IO.userError "stored snapshot-issued capability failed native invocation")
  require (invoked.value == word 72) "stored capability lost its actual mutable capture"
  let foreign ← match (← artifact.bootstrapFresh).resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "foreign bootstrap failed")
  match foreign.restoreSnapshot kept with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "snapshot transferred store/registry into a foreign session")
  match foreign.authenticate 1024 (.function .word .word) maker.value with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "restored handle changed its issuer")
  -- Empty native Unit bundles retain the open original source principal.
  let unused ← execute replayed.session (← key "unused") [word 21]
  let unusedAgain ← execute unused.session (← key "unused") [word 22]
  let unusedSnapshot ← get "unused generic principal snapshot" (← unusedAgain.session.snapshot)
  let principals := unusedSnapshot.cells.filterMap fun cell => match cell.value with
    | some (.principal principal) => some (cell, principal) | _ => none
  require (principals.length == 2) "unused Unit principals were dropped or treated as ground handles"
  let mut captures : List Nat := []
  for (cell, principal) in principals do
    require (!principal.scheme.quantified.isEmpty && cell.type == principal.type && principal.type != .unit)
      "generic principal lost its raw open type/scheme"
    match principal.observation.view with
    | .closure parameters _ _ environment _ =>
      require (parameters.length == 1 && environment.length == 1) "unused principal signature or capture order changed"
      let location ← match environment with
        | (_, location) :: _ => pure location
        | [] => throw (IO.userError "principal capture missing")
      require (location >= initialState.heap.length && location < cell.location) "principal capture bypassed source prefix offset"
      captures := captures ++ [location]
    | _ => throw (IO.userError "principal exposed a substituted view instead of original closure metadata")
  require (captures[0]? != captures[1]?) "reused binder ID confused captures from distinct invocations"
  let viewed ← execute unusedAgain.session (← key "views") [word 30]
  let viewsSnapshot ← get "used generic principal snapshot" (← viewed.session.snapshot)
  require (viewsSnapshot.cells.any fun cell => match cell.value with
    | some (.principal principal) => !principal.scheme.quantified.isEmpty | _ => false)
    "used generalized bundle lost principal metadata"
  let mapping : Value := .mapping (.comptime .word) (.proxy (.comptime .word)) [
    (word 1, .proxy (.comptime .word)), (word 1, .proxy (.comptime .word))]
  let echoed ← execute viewed.session (← key "echo") [mapping]
  let rawSnapshot ← get "native raw data snapshot" (← echoed.session.snapshot)
  require (rawSnapshot.cells.any fun cell => match cell.value with | some (.data value) => value == mapping | _ => false)
    "native cell snapshot changed raw mapping/proxy metadata or duplicate order"
  let start ← get "snapshot checkpoint" (echoed.session.start (← key "unused") [word 40])
  let suspended ← match ← start.resume 37 with
    | .outOfFuel checkpoint => pure checkpoint | _ => throw (IO.userError "expected real suspended allocation")
  let saved ← get "checkpoint heap snapshot" (← suspended.snapshot)
  require (saved.nativeHeapSize == suspended.heapSize) "checkpoint snapshot observed original session store"
  let resumed ← match saved.restore with
    | .suspended checkpoint => checkpoint.resume 300000
    | .ready _ => throw (IO.userError "snapshot dropped real native continuation")
  match resumed with
  | .succeeded completion => require (completion.value == word 40) "snapshot continuation resumed from wrong state"
  | _ => throw (IO.userError "snapshot continuation did not finish")
  match ← echoed.session.run (← key "failure") [word 50] 300000 with
  | .ok (.failed _ session) =>
    let faultSnapshot ← get "fault heap snapshot" (← session.snapshot)
    require (faultSnapshot.cells.any fun cell => match cell.value with | some (.data value) => value == word 52 | _ => false)
      "language-fault snapshot lost captured write"
    require (faultSnapshot.cells.any fun cell => cell.value.isNone && cell.location >= initialState.heap.length)
      "language-fault snapshot lost uninitialized source allocation"
  | _ => throw (IO.userError "failure fixture classification changed")
  match echoed.session.start (← key "sum") [word 1] 0 with
  | .error {code := .argumentCountMismatch 2 1, ..} => pure ()
  | _ => throw (IO.userError "root arity diagnostic lost original counts or ran encoding first")
  IO.println "opaque source heap/session snapshots GREEN"

end Tests.SourceCoreHeapSnapshot
end

section
-- leanmerge: from Solcore.Test.SourceCoreIndexedSessionFactories
#check_failure Solcore.Frontend.SourceCoreIndexedSession.CallableFactory
#check_failure Solcore.Frontend.SourceCoreIndexedSession.prepareCallable
#check_failure Solcore.Frontend.SourceCoreIndexedSession.issueCallable
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Recipe.named
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Session.register

set_option autoImplicit false
namespace Tests.SourceCoreIndexedSessionFactories
open Solcore Solcore.Frontend SourceCoreIndexedSession
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α := SourceCoreUnifiedCorpusSupport.get label
private def require (condition : Bool) (message : String) : IO Unit := SourceCoreUnifiedCorpusSupport.assertTrue condition message
private def word (value : Nat) : Value := .word (Core.Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "enum Functions { Put(function(Word) returns (Word)) }",
  "function inc(n: Word) returns (Word) { return n + 1; }",
  "function use(f: function(Word) returns (Word), n: Word) returns (Word) { return f(n); }",
  "function named() returns (function(Word) returns (Word)) { return inc; }",
  "function boxed(f: function(Word) returns (Word)) returns (Functions) { return .Put(f); }",
  "function unbox(v: Functions) returns (function(Word) returns (Word)) { match (v) { case .Put(f) { return f; } } }",
  "function maps(v: mapping(Word => function(Word) returns (Word))) returns (mapping(Word => function(Word) returns (Word))) { return v; }",
  "function tuples(v: (function(Word) returns (Word), Word)) returns ((function(Word) returns (Word), Word)) { return v; }",
  "function builtin(f: function(Word) returns (integer), n: Word) returns (integer) { return f(n); }",
  "function builtinMap(v: mapping(Word => function(Word) returns (integer)), n: Word) returns (integer) { return v[1](n); }",
  "function missing(v: mapping(Word => function(Word) returns (Word)), n: Word) returns (Word) { return v[n](0); }"
]
private def names : List String := ["inc", "use", "named", "boxed", "unbox", "maps", "tuples", "builtin", "builtinMap", "missing"]
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (args : List Value) : IO (Completion artifact) := do
  match ← session.run key args 300000 with
  | .ok (.succeeded result) => pure result
  | .ok (.failed reason _) => throw (IO.userError s!"factory language failure: {reprStr reason}")
  | .ok (.exportError error _) => throw (IO.userError s!"factory export: {reprStr error}")
  | .ok (.outOfFuel _) => throw (IO.userError "factory call exhausted")
  | .error error => throw (IO.userError s!"factory call rejected: {reprStr error}")

example {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (accepted : Recipe.prepare compiled = .ok recipe) : recipe.compiled = compiled :=
  Recipe.prepare_compiled accepted

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "owned callable factories" content names
  let recipe ← get "callable recipe" (Recipe.prepare compiled)
  let artifact ← recipe.open
  let boot ← artifact.bootstrapFresh
  let pending ← match boot.resume 0 with
    | .outOfFuel pending => pure pending | _ => throw (IO.userError "fresh bootstrap did not save checkpoint")
  let initial ← match pending.resume 300000 with
    | .ready session => pure session
    | .error error => throw (IO.userError s!"fresh bootstrap: {reprStr error}")
    | .outOfFuel _ => throw (IO.userError "fresh bootstrap exhausted")
  require (initial.inertPrefix.heap.isEmpty && initial.installedGlobalsPresent) "fresh bootstrap changed source boundary"
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  let inc ← get "named factory" (← initial.named (← key "inc"))
  require (inc.session.heapSize == initial.heapSize && inc.session.functionCount == 1) "named factory allocated/reinstalled native cells"
  let incAgain ← get "stable named factory" (← inc.session.named (← key "inc"))
  require (inc.value == incAgain.value && incAgain.session.functionCount == 1) "factory changed named handle identity"
  let returned ← execute incAgain.session (← key "named") []
  require (returned.value == inc.value) "factory differs from actual source named export"
  let called ← execute returned.session (← key "use") [inc.value, word 40]
  require (called.value == word 41) "named factory value was not callable"
  let box ← execute called.session (← key "boxed") [inc.value]
  let unboxed ← execute box.session (← key "unbox") [box.value]
  require (unboxed.value == inc.value) "deep nominal named input lost owned handle"
  let fn : TypeSystem.Ty := .function .word .word
  let raw : Value := .mapping (.comptime .word) fn [(word 1, inc.value), (word 1, inc.value)]
  let mapping ← execute unboxed.session (← key "maps") [raw]
  require (mapping.value == raw) "deep mapping factory input changed raw header/order"
  let tuple ← execute mapping.session (← key "tuples") [.product inc.value (word 7)]
  require (tuple.value == .product inc.value (word 7)) "deep product factory input changed handle"
  let converted ← get "builtin factory" (← tuple.session.builtin .wordToInteger)
  require (converted.session.heapSize == tuple.session.heapSize) "builtin factory allocated native cells"
  let integer ← execute converted.session (← key "builtin") [converted.value, word 19]
  require (integer.value == .integer 19) "owned builtin template returned wrong integer"
  let intFn : TypeSystem.Ty := .function .word .integer
  let intMapping : Value := .mapping .word intFn [(word 1, converted.value), (word 1, converted.value)]
  let mappedInteger ← execute integer.session (← key "builtinMap") [intMapping, word 23]
  require (mappedInteger.value == .integer 23) "builtin input inside ordered mapping was not callable"
  let mut allBuiltins := mappedInteger.session
  for function in BuiltinFunctionId.all do
    let imported ← get "complete builtin factory inventory" (← allBuiltins.builtin function)
    discard <| get "builtin type certificate" (imported.session.authenticate 1024 function.type imported.value)
    require (imported.session.heapSize == allBuiltins.heapSize) "builtin inventory changed persistent heap"
    allBuiltins := imported.session
  let rawMissingType : TypeSystem.Ty := .comptime fn
  let missingKey ← key "missing"
  let missingStart ← get "missing-default request" (allBuiltins.start missingKey
    [.mapping (.comptime .word) rawMissingType [], word 1])
  let missingPending ← match ← missingStart.resume 0 with
    | .outOfFuel checkpoint => pure checkpoint
    | _ => throw (IO.userError "missing request did not preserve checkpoint")
  match ← missingPending.resume 300000 with
  | .failed reason session =>
      let after ← get "retained raw diagnostic" (session.diagnostic missingKey reason)
      let before ← get "pending raw diagnostic" (missingPending.diagnostic reason)
      require (decide (before = after)) "checkpoint lost newly interned raw mapping header"
      match after with
      | some diagnostic =>
          require (decide (diagnostic.error = .typeMismatch rawMissingType none) && diagnostic.span.isSome)
            "missing default diagnostic changed raw type or source site"
      | none => throw (IO.userError "missing default reason was not decoded")
      require ((← get "unknown reason" (session.diagnostic missingKey (Core.Word.ofNatModulo (Core.wordModulus - 1)))).isNone)
        "unknown language reason was silently accepted"
  | _ => throw (IO.userError "missing default changed result classification")
  let freshBoot ← artifact.bootstrapFresh
  let fresh ← match freshBoot.resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "fresh foreign session bootstrap failed")
  match fresh.authenticate 1024 intFn converted.value with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "factory capability accepted by foreign session")
  let branchA ← get "branch A builtin" (← initial.builtin .wordToInteger)
  let branchB ← get "branch B builtin" (← initial.builtin .wordToInteger)
  match branchB.session.authenticate 1024 intFn branchA.value with
  | .error {code := .unknownHandle, ..} => pure ()
  | _ => throw (IO.userError "builtin export generations collided")
  let missing := { (← key "inc") with arguments := [.bool] }
  match ← mappedInteger.session.named missing with
  | .error {code := .missingEntry _, ..} => pure ()
  | _ => throw (IO.userError "factory accepted unowned specialization")
  IO.println "owned indexed named/builtin factories GREEN"

end Tests.SourceCoreIndexedSessionFactories
end

section
-- leanmerge: from Solcore.Test.SourceCoreIndexedSessionInvocation
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Request
#check_failure Solcore.Frontend.SourceCoreIndexedSession.selectCallable
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Checkpoint.request
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Value.closure

set_option autoImplicit false
namespace Tests.SourceCoreIndexedSessionInvocation
open Solcore Solcore.Frontend SourceCoreIndexedSession
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α := SourceCoreUnifiedCorpusSupport.get label
private def require (condition : Bool) (message : String) : IO Unit := SourceCoreUnifiedCorpusSupport.assertTrue condition message
private def word (value : Nat) : Value := .word (Core.Word.ofNatModulo value)
private def content : String := String.intercalate "\n" [
  "function add(left: Word, right: Word) returns (Word) { return left + right; }",
  "function tuple(value: (Word, Word)) returns (Word) { return 33; }",
  "function zero() returns (Word) { return 4; }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(step: Word) { seed += step; return seed; }; }",
  "function twins(seed: Word) returns (function(Word) returns (Word), function(Word) returns (Word)) {",
  " let left = lam(step: Word) -> Word { seed += step; return seed; };",
  " let right = lam(step: Word) -> Word { seed += step; return seed; }; return (left, right); }",
  "function failurePair(seed: Word) returns (function(Word) returns (Word), function() returns (Word)) {",
  " let fails = lam(step: Word) -> Word { seed += step; let absent: Word; return absent; };",
  " let observes = lam() -> Word { return seed; }; return (fails, observes); }",
  "function spin() returns (function() returns (Word)) { return lam() -> Word { while (true) {} return 0; }; }",
  "function marked() returns (function(Word) returns (Word)) { return lam(comptime value: Word) -> Word { return value; }; }",
  "function markedGlobal(comptime value: Word) returns (Word) { return value; }",
  "function markedResult() returns (comptime<Word>) { return 5; }",
  "function stagedSource() returns (Word) { let f = markedGlobal; return f(21); }"
]
private def names : List String := ["add", "tuple", "zero", "make", "twins", "failurePair", "spin", "marked", "markedGlobal", "markedResult", "stagedSource"]
private def handle : Value → IO Handle
  | .function handle => pure handle
  | _ => throw (IO.userError "function export was not an opaque handle")
private def success {artifact : Artifact} (label : String) : Except Error (Outcome artifact) → IO (Completion artifact)
  | .ok (.succeeded completion) => pure completion
  | .ok (.failed reason _) => throw (IO.userError s!"{label}: language failure {reprStr reason}")
  | .ok (.exportError error _) => throw (IO.userError s!"{label}: export {reprStr error}")
  | .ok (.outOfFuel _) => throw (IO.userError s!"{label}: exhausted")
  | .error error => throw (IO.userError s!"{label}: rejected {reprStr error}")
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (args : List Value) : IO (Completion artifact) := do
  success "cached source root" (← session.run key args 300000)
private def invoke {artifact : Artifact} (session : Session artifact) (value : Value) (argument : Value) : IO (Completion artifact) := do
  success "direct packed handle" (← session.invokePacked (← handle value) argument 300000)

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "direct packed invocation" content names
  let recipe ← get "direct recipe" (Recipe.prepare compiled)
  let artifact ← recipe.open
  let bootstrap ← artifact.bootstrapFresh
  let initial ← match bootstrap.resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "direct bootstrap failed")
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  let add ← get "two-parameter named handle" (← initial.named (← key "add"))
  let tuple ← get "tuple-parameter named handle" (← add.session.named (← key "tuple"))
  require (add.sourceType == tuple.sourceType) "fixture did not preserve the grouped source function type"
  let grouped : Value := .product (word 8) (word 9)
  let added ← invoke tuple.session add.value grouped
  require (added.value == word 17 && added.session.heapSize == tuple.session.heapSize + 6)
    "two scalar parameters lost values or source allocation count"
  let tupled ← invoke added.session tuple.value grouped
  require (tupled.value == word 33 && tupled.session.heapSize == added.session.heapSize + 3)
    "one tuple parameter was flattened into two parameter allocations"
  let zero ← get "zero-parameter named handle" (← tupled.session.named (← key "zero"))
  let zeroed ← invoke zero.session zero.value .unit
  require (zeroed.value == word 4 && zeroed.session.heapSize == zero.session.heapSize)
    "Unit parameter bundle added source parameter cells"
  let made ← execute zeroed.session (← key "make") [word 10]
  let first ← invoke made.session made.value (word 4)
  let next ← get "direct native checkpoint" (first.session.startHandlePacked (← handle made.value) (word 5))
  let saved ← match ← next.resume 0 with
    | .outOfFuel checkpoint => pure checkpoint | _ => throw (IO.userError "direct call did not preserve zero-fuel checkpoint")
  let progressed ← match ← saved.resume 37 with
    | .outOfFuel checkpoint => pure checkpoint | _ => throw (IO.userError "direct call did not preserve partial checkpoint")
  let resumed ← success "direct resume" (.ok (← progressed.resume 300000))
  require (first.value == word 14 && resumed.value == word 15 && resumed.session.installedGlobalsPresent)
    "direct closure call did not restart from its captured value or native resume lost the retained world"
  let pair ← execute resumed.session (← key "twins") [word 30]
  let (left, right) ← match pair.value with
    | .product left right => pure (left, right) | _ => throw (IO.userError "twin direct closures missing")
  let leftCall ← invoke pair.session left (word 3)
  let rightCall ← invoke leftCall.session right (word 4)
  require (leftCall.value == word 33 && rightCall.value == word 34) "direct handles shared a captured cell instead of each keeping its own value"
  let failedPair ← execute rightCall.session (← key "failurePair") [word 70]
  let (fails, observes) ← match failedPair.value with
    | .product fails observes => pure (fails, observes) | _ => throw (IO.userError "direct failure closures missing")
  let failsHandle ← handle fails
  let failureStart ← get "direct fault checkpoint" (failedPair.session.startHandlePacked failsHandle (word 4))
  let faulted ← match ← failureStart.resume 300000 with
    | .failed reason session =>
        let before ← get "direct checkpoint diagnostic" (failureStart.diagnostic reason)
        let after ← get "direct retained handle diagnostic" (session.handleDiagnostic failsHandle reason)
        require (decide (before = after)) "direct fault lost request origin or metadata"
        match after with
        | some {error := .uninitializedLocal _, span := some _, ..} => pure session
        | _ => throw (IO.userError "direct fault lost exact source read diagnostic")
    | _ => throw (IO.userError "direct fault changed classification")
  let observed ← invoke faulted observes .unit
  require (observed.value == word 70) "a write before a direct language failure reached another closure's captured value"
  let builtin ← get "direct builtin" (← observed.session.builtin .integerAdd)
  let integer ← invoke builtin.session builtin.value (.product (.integer 900000000000000000000000000000000000) (.integer 7))
  require (integer.value == .integer 900000000000000000000000000000000007) "packed builtin lost native Integer arithmetic"
  let marked ← execute integer.session (← key "marked") []
  let markedGlobal ← get "marked named handle" (← marked.session.named (← key "markedGlobal"))
  let markedResult ← get "marked result handle" (← markedGlobal.session.named (← key "markedResult"))
  for function in [marked.value, markedGlobal.value, markedResult.value] do
    let before := markedResult.session.heapSize
    match markedResult.session.startHandlePacked (← handle function) (.proxy (.comptime .word)) 0 with
    | .error {code := .stagedInvocationRequired _, ..} => pure ()
    | _ => throw (IO.userError "direct host stage rejection did not precede invalid packed input")
    require (markedResult.session.heapSize == before) "staged host rejection mutated source/native cells"
  let staged ← execute markedResult.session (← key "stagedSource") []
  require (staged.value == word 21) "legitimate staged source call no longer executes through its compiled guard"
  let spinning ← execute staged.session (← key "spin") []
  let spinningHandle ← handle spinning.value
  let pending ← match ← spinning.session.invokePacked spinningHandle .unit 200 with
    | .ok (.outOfFuel checkpoint) => pure checkpoint | _ => throw (IO.userError "direct spin completed")
  match ← pending.resume 300 with
  | .outOfFuel _ => pure () | _ => throw (IO.userError "resumed direct spin completed")
  let foreignBootstrap ← artifact.bootstrapFresh
  let foreign ← match foreignBootstrap.resume 300000 with
    | .ready session => pure session | _ => throw (IO.userError "foreign direct bootstrap failed")
  match foreign.startHandlePacked spinningHandle .unit with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "direct invocation accepted a foreign session handle")
  IO.println "direct owned packed invocation, source arity, stage guards, by-value captures and native resume GREEN"

end Tests.SourceCoreIndexedSessionInvocation
end

section
-- leanmerge: from Solcore.Test.SourceCoreIndexedSession
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCorePublicValues.Handle.mk
#check_failure Solcore.Frontend.SourceCorePublicValues.Handle.artifact
#check_failure Solcore.Frontend.SourceCorePublicValues.Handle.slot
#check_failure Solcore.Frontend.SourceCorePublicValues.ArtifactAuthority.mk
#check_failure Solcore.Frontend.SourceCorePublicValues.SessionAuthority.artifact
#check_failure Solcore.Frontend.SourceCoreIndexedSession.register
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Session.store
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Checkpoint.state
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Value.closure
#check_failure Solcore.Frontend.SourceCoreIndexedSession.Value.cellRef

set_option autoImplicit false
namespace Tests.SourceCoreIndexedSession
open Solcore Solcore.Frontend SourceCoreIndexedSession
private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α := SourceCoreUnifiedCorpusSupport.get label
private def require (condition : Bool) (message : String) : IO Unit := SourceCoreUnifiedCorpusSupport.assertTrue condition message
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def word (n : Nat) : Value := .word (w n)
private def content : String := String.intercalate "\n" [
  "enum Holder { Put(function(Word) returns (Word)) }",
  "function inc(n: Word) returns (Word) { return n + 1; }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { return lam(step: Word) { seed += step; return inc(seed); }; }",
  "function use(f: function(Word) returns (Word), n: Word) returns (Word) { return f(n); }",
  "function twins(seed: Word) returns (function(Word) returns (Word), function(Word) returns (Word)) {",
  " let f: function(Word) returns (Word) = lam(step: Word) { seed += step; return seed; };",
  " let g: function(Word) returns (Word) = lam(step: Word) { seed += step; return seed; }; return (f, g); }",
  "function named() returns (function(Word) returns (Word)) { return inc; }",
  "function mirror(f: function(Word) returns (Word)) returns (function(Word) returns (Word)) { return f; }",
  "function boxed(f: function(Word) returns (Word)) returns (Holder) { return .Put(f); }",
  "function unbox(v: Holder) returns (function(Word) returns (Word)) { match (v) { case .Put(f) { return f; } } }",
  "function mapEcho(v: mapping(Word => function(Word) returns (Word))) returns (mapping(Word => function(Word) returns (Word))) { return v; }",
  "function mapGet(v: mapping(Word => function(Word) returns (Word)), k: Word) returns (function(Word) returns (Word)) { return v[k]; }",
  "function wordMap(v: mapping(Word => Word)) returns (mapping(Word => Word)) { return v; }",
  "function proxy(v: @Word) returns (@Word) { return v; }",
  "function failurePair(seed: Word) returns (function(Word) returns (Word), function() returns (Word)) {",
  " let f: function(Word) returns (Word) = lam(step: Word) { seed += step; let absent: Word; return absent; };",
  " let g: function() returns (Word) = lam() { return seed; }; return (f, g); }",
  "function get(f: function() returns (Word)) returns (Word) { return f(); }",
  "function spin() returns (Word) { while (true) {} return 0; }"
]
private def names : List String := ["inc", "make", "use", "twins", "named", "mirror", "boxed", "unbox", "mapEcho", "mapGet", "wordMap", "proxy", "failurePair", "get", "spin"]
private def execute {artifact : Artifact} (session : Session artifact) (key : Key) (args : List Value)
    (fuel : Nat := 300000) : IO (Completion artifact) := do
  match ← session.run key args fuel with
  | .ok (.succeeded result) => pure result
  | .ok (.exportError error _) => throw (IO.userError s!"session export: {reprStr error}")
  | .ok (.failed reason _) => throw (IO.userError s!"session language failure: {reprStr reason}")
  | .ok (.outOfFuel _) => throw (IO.userError "session exhausted")
  | .error error => throw (IO.userError s!"session rejected: {reprStr error}")

-- The certificate retains the private world's exact frame location.
example {artifact : Artifact} (session : Session artifact) := session.frame_location_zero
example {artifact : Artifact} (completion : Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value := completion.typed
example {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat) := checkpoint.native_safe fuel
example : SourceCoreSession.Value = SourceCorePublicValues.Value := rfl

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "persistent indexed session" content names
  let recipe ← get "session recipe" (Recipe.prepare compiled)
  let artifact ← recipe.open
  let key := SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram
  let sentinel : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, none⟩]}
  let sourcePrefix ← match InertPrefix.prepare artifact sentinel 500 with
    | some accepted => pure accepted | none => throw (IO.userError "inert prefix rejected")
  let bootstrap ← artifact.bootstrap sourcePrefix
  let suspended ← match bootstrap.resume 1 with
    | .outOfFuel next => pure next | _ => throw (IO.userError "bootstrap did not suspend")
  let initial ← match suspended.resume 300000 with
    | .ready initial => pure initial
    | .error error => throw (IO.userError s!"bootstrap: {reprStr error}")
    | .outOfFuel _ => throw (IO.userError "bootstrap exhausted")
  require (initial.heapSize == compiled.indexed.base.globals.length + 1) "bootstrap installed unexpected source/input cells"
  require initial.installedGlobalsPresent "bootstrap did not authenticate globals"
  require (reprStr initial.inertPrefix == reprStr sentinel) "bootstrap imported/changed the inert source prefix"
  let made ← execute initial (← key "make") [word 10]
  let used ← execute made.session (← key "use") [made.value, word 2]
  require (used.value == word 13) "returned native capture/global call failed"
  let reused ← execute used.session (← key "use") [made.value, word 3]
  require (reused.value == word 14) "reused closure did not restart from its captured value"
  require (reused.session.installedGlobalsPresent && reprStr reused.session.inertPrefix == reprStr sentinel) "later invocation replaced globals or prefix"
  let mirrored ← execute reused.session (← key "mirror") [made.value]
  require (mirrored.value == made.value && mirrored.session.functionCount == 1) "handle registry did not retain exact native closure"
  let pair ← execute mirrored.session (← key "twins") [word 20]
  let (left, right) ← match pair.value with
    | .product left right => pure (left, right) | _ => throw (IO.userError "twins did not return two handles")
  let first ← execute pair.session (← key "use") [left, word 2]
  let second ← execute first.session (← key "use") [right, word 3]
  require (first.value == word 22 && second.value == word 23) "two handles shared a captured cell instead of each keeping its own value"
  let box ← execute second.session (← key "boxed") [left]
  let unboxed ← execute box.session (← key "unbox") [box.value]
  require (unboxed.value == left) "nominal payload function did not preserve the handle"
  let functionType : TypeSystem.Ty := .function .word .word
  let rawMapping : Value := .mapping (.comptime .word) functionType [(word 1, left), (word 1, right)]
  let mapped ← execute unboxed.session (← key "mapEcho") [rawMapping]
  require (mapped.value == rawMapping) "mapping raw header, duplicate order or function leaves changed"
  let fromMap ← execute mapped.session (← key "mapGet") [mapped.value, word 1]
  require (fromMap.value == left) "ordered mapping selected wrong duplicate"
  let rawWords : Value := .mapping (.comptime .word) (.comptime .word) [(word 1, word 7), (word 1, word 9)]
  let echoed ← execute fromMap.session (← key "wordMap") [rawWords]
  require (echoed.value == rawWords) "raw mapping metadata/default was canonicalized"
  let proxy ← execute echoed.session (← key "proxy") [.proxy (.comptime .word)]
  require (proxy.value == .proxy (.comptime .word)) "raw proxy metadata was canonicalized"
  let named ← execute proxy.session (← key "named") []
  let called ← execute named.session (← key "use") [named.value, word 40]
  require (called.value == word 41) "owned global handle was not callable"
  let pending ← get "start captured call" (called.session.start (← key "use") [made.value, word 1])
  let next ← match ← pending.resume 37 with
    | .outOfFuel next => pure next | _ => throw (IO.userError "partial call did not suspend")
  let resumed ← match ← next.resume 300000 with
    | .succeeded result => pure result | _ => throw (IO.userError "native checkpoint did not complete")
  require (resumed.value == word 12 && resumed.session.installedGlobalsPresent) "resume lost capture/global authority"
  let branchedA ← execute initial (← key "make") [word 50]
  let branchedB ← execute initial (← key "make") [word 50]
  match branchedB.session.authenticate 1024 functionType branchedA.value with
  | .error {code := .unknownHandle, ..} => pure ()
  | _ => throw (IO.userError "branched export slot collision accepted")
  let freshBootstrap ← artifact.bootstrap sourcePrefix
  let fresh ← match freshBootstrap.resume 300000 with
    | .ready fresh => pure fresh | _ => throw (IO.userError "second bootstrap failed")
  match fresh.authenticate 1024 functionType made.value with
  | .error {code := .foreignSession, ..} => pure ()
  | _ => throw (IO.userError "foreign session accepted handle")
  let otherArtifact ← recipe.open
  let otherPrefix ← match InertPrefix.prepare otherArtifact {} 500 with
    | some accepted => pure accepted | none => throw (IO.userError "empty prefix rejected")
  let otherBootstrap ← otherArtifact.bootstrap otherPrefix
  let other ← match otherBootstrap.resume 300000 with
    | .ready other => pure other | _ => throw (IO.userError "foreign artifact bootstrap failed")
  match other.authenticate 1024 functionType made.value with
  | .error {code := .foreignArtifact, ..} => pure ()
  | _ => throw (IO.userError "foreign artifact accepted handle")
  let failedPair ← execute resumed.session (← key "failurePair") [word 70]
  let (fails, observes) ← match failedPair.value with
    | .product left right => pure (left, right) | _ => throw (IO.userError "failure pair missing")
  let afterFault ← match ← failedPair.session.run (← key "use") [fails, word 4] 300000 with
    | .ok (.failed _ session) => pure session | _ => throw (IO.userError "language failure changed category")
  let observed ← execute afterFault (← key "get") [observes]
  require (observed.value == word 70) "a write before a language fault reached another closure's captured value"
  let spinning ← get "spin" (observed.session.start (← key "spin") [])
  let spinningNext ← match ← spinning.resume 200 with
    | .outOfFuel next => pure next | _ => throw (IO.userError "spin completed")
  match ← spinningNext.resume 300 with
  | .outOfFuel _ => pure () | _ => throw (IO.userError "resumed spin completed")

end Tests.SourceCoreIndexedSession
end

section
-- leanmerge: from Solcore.Test.SourceCoreLocalCell
/-! Local-read lowering coverage: occurrence metadata, first-match source
identity lookup, checked Core execution, and retained exhaustion checkpoints.
The parsed fixture exercises a local read, not a whole-function compiler. -/

set_option autoImplicit false

namespace Tests.SourceCoreLocalCell

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"local_cell", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : Resolved.LocalId := ⟨owner, 0⟩
private def otherBinder : Resolved.LocalId := ⟨owner, 1⟩
private def foreignBinder : Resolved.LocalId := ⟨⟨ownerModule, 1⟩, 0⟩
private def expressionId : ExpressionId := ⟨⟨owner, 0⟩⟩
private def missingId : ExpressionId := ⟨⟨owner, 99⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "local_cell.solc" }
  startByte := 0
  endByte := 1
}

private def node (type : TypeSystem.Ty := .word) : ExpressionNode := {
  id := expressionId
  span
  type
  form := .reference "value" (.local binder)
}

private def sourceWith (expression : ExpressionNode) : TypedSource := {
  owner
  inputs := [{ id := binder, name := "value", scheme := .mono expression.type }]
  roots := [.expression expressionId]
  nodes := [.expression expression]
}

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)
private def scalar (value : Nat) : Core.Value := .word (word value)
private def reason : Core.Word := word 71

private def scalarScope : Frontend.SourceCoreLocalCell.Scope :=
  [(otherBinder, .bool), (binder, .word), (binder, .bool)]

private def scalarRead : Core.Expr := Core.OptionalCell.read .word (.var 1) reason

private theorem scalar_lowered :
    Frontend.SourceCoreLocalCell.lowerRead (sourceWith (node .word)) scalarScope expressionId reason =
      .ok scalarRead := by rfl

example : Frontend.SourceCoreLocalCell.lookup? scalarScope binder = some (1, .word) := by rfl
example : Frontend.SourceCoreLocalCell.lookup? scalarScope otherBinder = some (0, .bool) := by rfl
example : Frontend.SourceCoreLocalCell.lookup? scalarScope foreignBinder = none := by rfl
example : (Frontend.SourceCoreLocalCell.coreContext scalarScope)[1]? =
    some (Core.OptionalCell.referenceType .word) :=
  Frontend.SourceCoreLocalCell.lookup?_context (id := binder) (by rfl)

private def scalarProgram (read : Core.Expr := scalarRead) : Core.Program := {
  resultType := Core.LanguageResult.resultType .word
  body :=
    .letE (Core.OptionalCell.allocateInitialized .bool (.bool true)) <|
    .letE (Core.OptionalCell.allocateInitialized .word (literal 42)) <|
    .letE (Core.OptionalCell.allocateInitialized .bool (.bool false)) read
}

private def scalarStore : Core.Store :=
  [.inRight .unit (.bool true), .inRight .unit (scalar 42), .inRight .unit (.bool false)]

private def productType : Core.Ty := .product .word .bool
private def productScope : Frontend.SourceCoreLocalCell.Scope := [(binder, productType)]
private def productRead : Core.Expr := Core.OptionalCell.read productType (.var 0) reason
private def productValue : Core.Value := .pair (scalar 8) (.bool true)
private def productProgram (read : Core.Expr := productRead) : Core.Program := {
  resultType := Core.LanguageResult.resultType productType
  body := .letE
    (Core.OptionalCell.allocateInitialized productType (.pair (literal 8) (.bool true))) read
}

private theorem product_lowered :
    Frontend.SourceCoreLocalCell.lowerRead (sourceWith (node (.product .word .bool)))
      productScope expressionId reason = .ok productRead := by rfl

private def uninitializedRead : Core.Expr := Core.OptionalCell.read .word (.var 0) reason
private def uninitializedProgram (read : Core.Expr := uninitializedRead) : Core.Program := {
  resultType := Core.LanguageResult.resultType .word
  body := .letE (Core.OptionalCell.allocate .word) read
}

private theorem uninitialized_lowered :
    Frontend.SourceCoreLocalCell.lowerRead (sourceWith (node .word))
      [(binder, .word)] expressionId reason = .ok uninitializedRead := by rfl

private theorem scalar_checked : (scalarProgram).check = true := by decide
private theorem product_checked : (productProgram).check = true := by decide
private theorem uninitialized_checked : (uninitializedProgram).check = true := by decide

private theorem scalar_completed :
    (scalarProgram).runStateful 80 = .done (.inRight .word (scalar 42)) scalarStore := by rfl
private theorem product_completed :
    (productProgram).runStateful 80 =
      .done (.inRight .word productValue) [.inRight .unit productValue] := by rfl
private theorem uninitialized_completed :
    (uninitializedProgram).runStateful 80 =
      .done (.inLeft .word (.word reason)) [.inLeft .word .unit] := by rfl

private theorem scalar_exhausted :
    ∃ checkpoint, (scalarProgram).runStateful 24 = .outOfFuel checkpoint := by
  exact ⟨_, rfl⟩

private theorem uninitialized_exhausted :
    ∃ checkpoint, (uninitializedProgram).runStateful 10 = .outOfFuel checkpoint := by
  exact ⟨_, rfl⟩

example : ∃ checkpoint,
    (scalarProgram).runStateful 24 = .outOfFuel checkpoint ∧
    Core.StateHasType checkpoint (Core.LanguageResult.resultType .word) ∧
    Core.runStateful 56 checkpoint = .done (.inRight .word (scalar 42)) scalarStore := by
  obtain ⟨checkpoint, exhausted⟩ := scalar_exhausted
  have typed := Core.initial_state_has_type (Core.Program.check_full_sound scalar_checked).bodyHasType
  exact ⟨checkpoint, exhausted,
    Core.well_typed_runStateful_preserves_checkpoint_type typed exhausted,
    (Core.runStateful_resume exhausted 56).trans scalar_completed⟩

example : ∃ checkpoint,
    (uninitializedProgram).runStateful 10 = .outOfFuel checkpoint ∧
    Core.StateHasType checkpoint (Core.LanguageResult.resultType .word) ∧
    Core.runStateful 70 checkpoint =
      .done (.inLeft .word (.word reason)) [.inLeft .word .unit] := by
  obtain ⟨checkpoint, exhausted⟩ := uninitialized_exhausted
  have typed := Core.initial_state_has_type
    (Core.Program.check_full_sound uninitialized_checked).bodyHasType
  exact ⟨checkpoint, exhausted,
    Core.well_typed_runStateful_preserves_checkpoint_type typed exhausted,
    (Core.runStateful_resume exhausted 70).trans uninitialized_completed⟩

private def wordReadSite : SourceSemantics.CoreLowering.LocalCell.ReadSite
    (sourceWith (node .word)) [(binder, .word)] expressionId .word := {
  node := node .word
  binder
  name := "value"
  index := 0
  contains := ⟨List.Mem.head _, rfl⟩
  form := rfl
  owner := rfl
  requirements := rfl
  coercions := rfl
  slot := rfl
  types := .word
}

private theorem wordSource_unique :
    SourceSemantics.NodeOccurrencesUnique (sourceWith (node .word)) := by
  simp [SourceSemantics.NodeOccurrencesUnique, SourceSemantics.nodeOccurrenceIds, sourceWith]

/-- A concrete proof consumer includes actual lowering, an independent source
outcome, a finite completion bound, and reflection of every completed run. -/
private def ReadCorrespondence (program : SourceSemantics.Program)
    (context : SourceSemantics.Context) (evidence : SourceSemantics.Dynamic.EvidenceEnvironment)
    (heap : SourceSemantics.Dynamic.Heap) (store : Core.Store) : Prop :=
  Core.RuntimeStoreHasTypes [Core.OptionalCell.cellType .word] store ∧
  ∃ expression sourceOutcome coreValue required,
    Frontend.SourceCoreLocalCell.lowerRead (sourceWith (node .word)) [(binder, .word)]
      expressionId reason = .ok expression ∧
    SourceSemantics.Dynamic.ExpressionEvaluatesOutcome program context evidence
      (sourceWith (node .word)) [(binder, ⟨0⟩)] heap expressionId sourceOutcome heap ∧
    SourceSemantics.CoreLowering.LocalCell.OutcomeRepresents ⟨0⟩ reason sourceOutcome coreValue ∧
    (∀ fuel, required ≤ fuel → Core.runStateful fuel
      (.initial expression [.cellRef (Core.OptionalCell.cellType .word) 0] store) =
        .done coreValue store) ∧
    (∀ fuel result finalStore, Core.runStateful fuel
      (.initial expression [.cellRef (Core.OptionalCell.cellType .word) 0] store) =
        .done result finalStore → result = coreValue ∧ finalStore = store)

private def initializedCell : SourceSemantics.Dynamic.Cell := {
  type := .word
  value := some (.word (word 42))
}

private def absentCell : SourceSemantics.Dynamic.Cell := {
  type := .word
  value := none
}

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : SourceSemantics.Dynamic.EvidenceEnvironment) :
    ReadCorrespondence program context evidence ⟨[initializedCell]⟩
      [.inRight .unit (scalar 42)] := by
  have heaps : SourceSemantics.CoreLowering.LocalCell.HeapRepresents [initializedCell]
      [.inRight .unit (scalar 42)] [Core.OptionalCell.cellType .word] :=
    .cons (.initialized (.word (word 42))) .nil
  exact ⟨heaps.runtime_hasTypes [],
    wordReadSite.lower_run_preserves wordSource_unique program context evidence
      [(binder, ⟨0⟩)] ⟨[initializedCell]⟩ [.cellRef (Core.OptionalCell.cellType .word) 0]
      [.inRight .unit (scalar 42)] [Core.OptionalCell.cellType .word] ⟨0⟩ initializedCell
      heaps .head (.intro .head) rfl rfl reason⟩

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : SourceSemantics.Dynamic.EvidenceEnvironment) :
    ReadCorrespondence program context evidence ⟨[absentCell]⟩ [.inLeft .word .unit] := by
  have heaps : SourceSemantics.CoreLowering.LocalCell.HeapRepresents [absentCell]
      [.inLeft .word .unit] [Core.OptionalCell.cellType .word] :=
    .cons (.uninitialized .word) .nil
  exact ⟨heaps.runtime_hasTypes [],
    wordReadSite.lower_run_preserves wordSource_unique program context evidence
      [(binder, ⟨0⟩)] ⟨[absentCell]⟩ [.cellRef (Core.OptionalCell.cellType .word) 0]
      [.inLeft .word .unit] [Core.OptionalCell.cellType .word] ⟨0⟩ absentCell
      heaps .head (.intro .head) rfl rfl reason⟩

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def lower (source : TypedSource) (scope : Frontend.SourceCoreLocalCell.Scope)
    (id : ExpressionId) : IO Core.Expr := do
  match Frontend.SourceCoreLocalCell.lowerRead source scope id reason with
  | .ok expression => pure expression
  | .error error => throw (IO.userError s!"local read failed to lower: {reprStr error}")

private def expectError (label : String) (source : TypedSource)
    (scope : Frontend.SourceCoreLocalCell.Scope) (id : ExpressionId)
    (accept : Frontend.SourceCoreLocalCell.Error → Bool) : IO Unit := do
  match Frontend.SourceCoreLocalCell.lowerRead source scope id reason with
  | .ok _ => throw (IO.userError s!"{label}: invalid local read lowered")
  | .error error => assertTrue (accept error) s!"{label}: wrong error {reprStr error}"

private def testRejections : IO Unit := do
  let source := sourceWith (node .word)
  expectError "missing occurrence" source scalarScope missingId
    fun error => match error with | .missingExpression id => id == missingId | _ => false
  expectError "non-reference expression" (sourceWith { node .word with form := .literal (.decimal "1") })
    scalarScope expressionId fun error => error matches .expectedLocalReference _
  expectError "nonlocal reference"
    (sourceWith { node .word with form := .reference "true" (.builtinBoolean true) })
    scalarScope expressionId fun error => error matches .expectedLocalReference _
  expectError "foreign owner before missing binding"
    (sourceWith { node .word with form := .reference "value" (.local foreignBinder) })
    [] expressionId fun error => match error with
      | .ownerMismatch id => decide (id = foreignBinder)
      | _ => false
  expectError "missing binding" source [] expressionId fun error => match error with
    | .missingBinding id => decide (id = binder)
    | _ => false
  let coercion : CoercionStep := { requirement := ⟨3⟩, source := .word, target := .word }
  expectError "requirements before coercions and missing binding"
    (sourceWith { node .word with requirements := [⟨3⟩], coercions := [coercion] })
    [] expressionId fun error => error matches .requirementsPresent _
  expectError "coercions before missing binding"
    (sourceWith { node .word with coercions := [coercion] })
    [] expressionId fun error => error matches .coercionsPresent _
  expectError "unsupported projected type" (sourceWith (node (.function .word .word)))
    scalarScope expressionId fun error => match error with
      | .typeProjection failure =>
          failure.site == .occurrence expressionId.occurrence &&
            (failure.reason matches .unsupportedType _)
      | _ => false
  expectError "slot type mismatch" source [(binder, .bool)] expressionId fun error =>
    error matches .slotTypeMismatch .word .bool

private def checkResume (label : String) (program : Core.Program) (spent : Nat)
    (value : Core.Value) (store : Core.Store) : IO Unit := do
  match program.runStateful spent with
  | .outOfFuel checkpoint =>
      assertTrue (Core.runStateful (80 - spent) checkpoint == .done value store)
        s!"{label}: resumption lost the local reference or optional payload"
  | _ => throw (IO.userError s!"{label}: expected a retained checkpoint")

private def testLoweredExecution : IO Unit := do
  let scalarExpr ← lower (sourceWith (node .word)) scalarScope expressionId
  assertTrue (scalarExpr == scalarRead) "source identity lookup lost the first matching slot"
  let scalarCore := scalarProgram scalarExpr
  assertTrue scalarCore.check "lowered scalar read did not pass the Core checker"
  assertTrue (scalarCore.runStateful 80 == .done (.inRight .word (scalar 42)) scalarStore)
    "lowered scalar read chose the wrong slot or changed the store"
  checkResume "scalar read" scalarCore 24 (.inRight .word (scalar 42)) scalarStore
  let productExpr ← lower (sourceWith (node (.product .word .bool))) productScope expressionId
  let product := productProgram productExpr
  assertTrue product.check "lowered product read did not pass the Core checker"
  assertTrue (product.runStateful 80 ==
      .done (.inRight .word productValue) [.inRight .unit productValue])
    "lowered product read lost its structural payload"
  let absentExpr ← lower (sourceWith (node .word)) [(binder, .word)] expressionId
  let absent := uninitializedProgram absentExpr
  assertTrue absent.check "lowered uninitialized read did not pass the Core checker"
  assertTrue (Core.LanguageResult.run absent 80 == .failed reason [.inLeft .word .unit])
    "lowered uninitialized read must return the supplied reason and unchanged marker"
  checkResume "uninitialized read" absent 10 (.inLeft .word (.word reason)) [.inLeft .word .unit]

private def testParsedCheckedLocalRead : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc"
    mainSources := [{ path := "main.solc", content :=
      "function read(value: Word) returns (Word) { return value; }" }]
    externalLibraries := []
  }
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"local read fixture failed checking: {reprStr errors}")
  let function ← match program.functions with
    | [function] => pure function
    | _ => throw (IO.userError "local read fixture expected one checked function")
  let occurrence ← match function.typedBody.nodes.find? (fun
      | .expression { form := .reference _ (.local _), .. } => true
      | _ => false) with
    | some (.expression node) => pure node
    | _ => throw (IO.userError "checked local occurrence is missing")
  let localId ← match occurrence.form with
    | .reference _ (.local localId) => pure localId
    | _ => throw (IO.userError "checked occurrence is not a local reference")
  let expression ← lower function.typedBody [(localId, .word)] occurrence.id
  let core : Core.Program := {
    resultType := Core.LanguageResult.resultType .word
    body := .letE (Core.OptionalCell.allocateInitialized .word (literal 17)) expression
  }
  assertTrue core.check "the actual checked occurrence did not lower to checked Core"
  assertTrue (Core.LanguageResult.run core 80 == .succeeded (scalar 17) [.inRight .unit (scalar 17)])
    "the actual checked occurrence lost its local value"

def run : IO Unit := do
  testRejections
  testLoweredExecution
  testParsedCheckedLocalRead

end Tests.SourceCoreLocalCell
end

section
-- leanmerge: from Solcore.Test.SourceCoreLocalEvidence
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreLocalEvidence.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreLocalEvidence.Reference.mk
#check_failure fun (prepared : Solcore.Frontend.SourceCoreLocalEvidence.Prepared) => { prepared with witnesses := [] }
#check_failure fun (reference : Solcore.Frontend.SourceCoreLocalEvidence.Reference) => { reference with owned := [] }

/-! Qualified template assumptions remain at their original body requirement
IDs after contextual authentication. These are static compiler receipts; the
public compiler's executable routing is tested by its owning module. -/

set_option autoImplicit false

namespace Tests.SourceCoreLocalEvidence

open Solcore Solcore.Frontend SourceInference TypeSystem SourceCoreLocalEvidence
abbrev Catalog := SourceCoreLocalPolymorphism.Catalog

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "trait Coerce<From, To> { function coerce(value: From) returns (To); }",
    "type WordFunction = function(Word) returns (Word);",
    "impl Coerce<WordFunction, Word> { function coerce(value: WordFunction) returns (Word) { return value(5); } }",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function qualified(flag: Bool) returns (Word, Bool) {",
    " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }",
    "function coerced() returns (Word) { let f: WordFunction = lam(item: Word) -> Word { return keep(item); }; return f; }",
    "function nested(flag: Bool) returns (Word, Word) {",
    " let outer = lam(value) { keep(value);",
    "   let inner = lam(item) { return keep(item); }; return inner(1); };",
    " return (outer(1), outer(flag)); }"
  ] }] }

private def plan (program : CheckedProgram) (name : String) : IO SourceSpecializationWorklist.Plan := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"local evidence fixture missing: {name}")
  match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 64 with
  | .ok (.complete plan) => pure plan
  | other => throw (IO.userError s!"local evidence worklist failed: {reprStr other}")

private def catalog (checked : SourceCoreDataCatalog.Checked) (plan : SourceSpecializationWorklist.Plan) : IO Catalog :=
  match SourceCoreLocalPolymorphism.prepare checked plan with
  | .ok catalog => pure catalog
  | .error error => throw (IO.userError s!"local evidence catalog failed: {reprStr error}")

private def binding (catalog : Catalog) (name : String) : IO Binding :=
  match catalog.bindings.filter (·.binder.name == name) with
  | [binding] => pure binding
  | _ => throw (IO.userError s!"local evidence binding missing: {name}")

private def prepared (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (candidate : Instance) (parent : Option Prepared := none) : IO Prepared :=
  match prepare program plan candidate parent with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"local evidence receipt failed: {reprStr error}")

private def checkCalls (prepared : Prepared) : IO Unit := do
  let calls := prepared.source.nodes.filterMap fun
    | .expression node@{ form := .call _ _ (.declaration instantiation), .. } =>
        if instantiation.predicates.all (fun predicate => (TypedTraitResolution.predicateVariables predicate).isEmpty) then
          some (node, instantiation)
        else none
    | _ => none
  for (node, instantiation) in calls do
    match SourceCompilationPlan.exactDirectCallRuntimeEvidence prepared.caller node [] instantiation with
    | .ok evidence =>
        assertTrue (evidence.length == instantiation.predicates.length)
          "contextual direct-call evidence lost a source obligation"
    | .error error => throw (IO.userError s!"contextual call ledger rejected: {reprStr error}")

example (substitution : Substitution) (witnesses : List Witness) (rows : List SolvedRequirement) :
    (rewriteLedger substitution witnesses rows).map (·.id) = rows.map (·.id) :=
  rewriteLedger_ids substitution witnesses rows

example (reference : Reference) : reference.normalized.coercions = reference.original.coercions :=
  reference.normalized_coercions

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"local evidence source failed: {reprStr error}")
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 128 [.word, .bool] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"local evidence catalog failed: {reprStr error}")
  let qualifiedPlan ← plan program "qualified"
  let qualifiedCatalog ← catalog checked qualifiedPlan
  let f ← binding qualifiedCatalog "f"
  assertTrue (f.instances.length == 2 && f.binder.schemeRequirements.length == 1)
    "qualified fixture lost Word/Bool instances or its template"
  for candidate in f.instances do
    let child ← prepared program qualifiedPlan candidate
    assertTrue (child.caller.key == candidate.origin.caller && child.substitution == candidate.origin.substitution &&
      child.caller.function.type == (qualifiedPlan.specializations.find? (·.key == candidate.origin.caller) |>.map
        (·.function.type) |>.getD .error)) "qualified child changed its global signature or contextual key"
    assertTrue (child.caller.function.solvedRequirements.map (·.id) == candidate.origin.solvedRequirements.map (·.id))
      "qualified child erased or re-numbered a body requirement"
    assertTrue (child.witnesses.length == 1) "qualified child failed to discharge one template assumption"
    for witness in child.witnesses do
      let row ← match child.caller.function.solvedRequirements.filter (·.id == witness.templateRequirement) with
        | [row] => pure row
        | _ => throw (IO.userError "qualified template row disappeared")
      match row.evidence with
      | .implementation evidence =>
          assertTrue (evidence == witness.evidence && row.predicate == witness.predicate)
            "qualified child substituted an unauthenticated implementation"
      | _ => throw (IO.userError "qualified template assumption remained unresolved")
    checkCalls child
  let readIds := f.source.nodes.filterMap fun
    | .expression { id, form := .reference _ (.local binder), .. } => if binder == f.binder.id then some id else none
    | _ => none
  for id in readIds do
    match authenticateReference program qualifiedPlan f none id with
    | .ok reference =>
        assertTrue (!reference.original.requirements.isEmpty && reference.normalized.requirements.isEmpty)
          "qualified reference silently dropped an unbound obligation or kept its bound scheme obligation"
        assertTrue (reference.normalized.form == reference.original.form &&
          reference.normalized.coercions == reference.original.coercions &&
          reference.normalized.span == reference.original.span &&
          reference.normalized.type == reference.original.type) "reference normalization changed source metadata"
        match normalizeOccurrence program qualifiedPlan f none f.source id with
        | .ok source =>
            assertTrue (source.lookupExpression? id == some reference.normalized)
              "policy metadata traversal did not remove its authenticated qualified requirement"
        | .error error => throw (IO.userError s!"qualified policy metadata normalization failed: {reprStr error}")
    | .error error => throw (IO.userError s!"qualified local read authentication failed: {reprStr error}")

  let coercedPlan ← plan program "coerced"
  let coercedF ← match coercedPlan.specializations.find? (·.function.typedBody.nodes.any fun
      | .statement { form := .letDecl binder _, .. } => binder.name == "f"
      | _ => false) with
    | none => throw (IO.userError "coerced local caller disappeared")
    | some caller =>
        match caller.function.typedBody.nodes.findSome? fun
          | .statement { form := .letDecl binder (some initializer), .. } =>
              if binder.name == "f" then some (binder, initializer) else none
          | _ => none with
        | none => throw (IO.userError "coerced local binder disappeared")
        | some (binder, initializer) => pure ({
            caller := caller.key
            source := caller.function.typedBody
            binder
            initializer
            instances := [] } : Binding)
  let coercedId ← match coercedF.source.nodes.findSome? fun
      | .expression node@{ form := .reference _ (.local binder), .. } =>
          if binder == coercedF.binder.id then some node.id else none
      | _ => none with
    | some id => pure id
    | none => throw (IO.userError "coerced local reference disappeared")
  let receipt ← match authenticateReference program coercedPlan coercedF none coercedId with
    | .ok receipt => pure receipt
    | .error error => throw (IO.userError s!"coerced local authentication failed: {reprStr error}")
  assertTrue (!receipt.original.coercions.isEmpty && !receipt.normalized.requirements.isEmpty &&
    receipt.normalized.coercions == receipt.original.coercions)
    "qualified normalization removed the distinct output-coercion obligation"
  let normalizedSource ← match normalizeOccurrence program coercedPlan coercedF none coercedF.source coercedId with
    | .ok source => pure source
    | .error error => throw (IO.userError s!"policy local normalization failed: {reprStr error}")
  assertTrue (normalizedSource.lookupExpression? coercedId == some receipt.normalized)
    "policy metadata read retained scheme-instance requirements"
  match normalizeOccurrence program coercedPlan coercedF none normalizedSource coercedId with
  | .ok repeated => assertTrue (repeated == normalizedSource) "local normalization was not idempotent"
  | .error error => throw (IO.userError s!"normalized metadata was rejected: {reprStr error}")
  let rawRequirements ← match SourceCompilationPlan.ordinaryOwnedRequirements? receipt.normalized with
    | some requirements => pure requirements
    | none => throw (IO.userError "normalized coercion requirement inventory is invalid")
  let raw := { receipt.normalized with
    type := receipt.normalized.rawType
    requirements := rawRequirements
    coercions := [] }
  let rawSource := { normalizedSource with nodes := normalizedSource.nodes.map fun
    | .expression node => .expression (if node.id == coercedId then raw else node)
    | .statement node => .statement node }
  match normalizeOccurrence program coercedPlan coercedF none rawSource coercedId with
  | .ok unchanged => assertTrue (unchanged == rawSource) "coercion-child raw metadata was replaced by post-coercion metadata"
  | .error error => throw (IO.userError s!"authentic raw local view rejected: {reprStr error}")
  let erasedSource := { normalizedSource with nodes := normalizedSource.nodes.map fun
    | .expression node => .expression (if node.id == coercedId then { node with requirements := [] } else node)
    | .statement node => .statement node }
  match normalizeOccurrence program coercedPlan coercedF none erasedSource coercedId with
  | .error (.occurrenceMismatch _) => pure ()
  | _ => throw (IO.userError "a forged erased coercion obligation was accepted")

  let nestedPlan ← plan program "nested"
  let nestedCatalog ← catalog checked nestedPlan
  let outer ← binding nestedCatalog "outer"
  let inner ← binding nestedCatalog "inner"
  assertTrue (outer.instances.length == 2 && inner.instances.length == 2) "nested qualified contexts disappeared"
  for outerInstance in outer.instances do
    let outerPrepared ← prepared program nestedPlan outerInstance
    assertTrue (outerPrepared.witnesses.length == 1) "outer local evidence was not retained"
    let innerInstance ← match inner.atContext outerPrepared.substitution with
      | [candidate] => pure candidate
      | _ => throw (IO.userError "nested qualified bundle matched another outer context")
    let innerPrepared ← prepared program nestedPlan innerInstance (some outerPrepared)
    assertTrue (innerPrepared.witnesses.length == 2 && innerPrepared.substitution == innerInstance.origin.substitution)
      "nested receipt lost the inherited dictionary or full cumulative context"
    checkCalls innerPrepared
    assertTrue (innerPrepared.caller.function.solvedRequirements.map (·.id) == innerInstance.origin.solvedRequirements.map (·.id))
      "nested evidence rebinding changed ledger identities"

  let first ← match f.instances with
    | first :: _ => pure first
    | [] => throw (IO.userError "qualified instances disappeared")
  let forgedLedger := { first with origin := { first.origin with solvedRequirements := [] } }
  match prepare program qualifiedPlan forgedLedger with
  | .error (.originMismatch _) => pure ()
  | _ => throw (IO.userError "a caller erased the original qualified ledger")
  let forgedSource := { first with origin := { first.origin with source := { first.origin.source with nodes := [] } } }
  match prepare program qualifiedPlan forgedSource with
  | .error (.originMismatch _) => pure ()
  | _ => throw (IO.userError "a fabricated local source obtained an evidence receipt")
  let forgedContext := { first with origin := { first.origin with localInstance :=
    { first.origin.localInstance with substitution := [] } } }
  match prepare program qualifiedPlan forgedContext with
  | .error (.instanceMismatch _) => pure ()
  | _ => throw (IO.userError "an undiscovered local substitution obtained an evidence receipt")
  let foreignParent ← prepared program nestedPlan (← match outer.instances with
    | first :: _ => pure first
    | [] => throw (IO.userError "outer instances disappeared"))
  match prepare program qualifiedPlan first (some foreignParent) with
  | .error (.parentMismatch _) => pure ()
  | _ => throw (IO.userError "an unrelated caller's dictionary entered a local instance")
  IO.println "qualified local evidence, nested dictionaries and retained obligation identities GREEN"

end Tests.SourceCoreLocalEvidence
end

section
-- leanmerge: from Solcore.Test.SourceCoreLocalPolymorphicExecution
/-! Actual checked local polymorphic lambdas run through Core. A generalized
local copies its lexical cells once, every concrete instance shares that
snapshot, and each call starts again from it; nested choices retain their full
cumulative contexts. -/
set_option autoImplicit false
namespace Tests.SourceCoreLocalPolymorphicExecution
open Solcore Solcore.Frontend SourceCoreExecution
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [],
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function qualified(flag: Bool) returns (Word, Bool) { let f = lam(item) { return keep(item); }; return (f(19), f(flag)); }",
    "function qualifiedNested(flag: Bool) returns (Word, Word) { let outer = lam(value) { keep(value); let inner = lam(item) { return keep(item); }; return inner(1); }; return (outer(1), outer(flag)); }",
    "function qualifiedCapture(flag: Bool) returns (Word) { let count: Word = 0; let f = lam(item) { count += 1; return keep(item); }; f(1); f(flag); return count; }",
    "type WordFunction = function(Word) returns (Word);",
    "function qualifiedMaker(seed: Word) returns (WordFunction) { let count: Word = seed; let f = lam(item) { keep(item); count += 1; return count; }; return f; }",
    "function useFunction(f: WordFunction, value: Word) returns (Word) { return f(value); }",
    "function identity<T>(value: T) returns (T) { return value; }",
    "function local(flag: Bool) returns (Word, Bool) { let f = lam(item) { return identity(item); }; return (f(11), f(flag)); }",
    "function nested(flag: Bool) returns (Word, Bool) { let outer = lam(item) { let inner = lam(value) { return identity(value); }; return inner(item); }; return (outer(13), outer(flag)); }",
    "function recursiveContext(flag: Bool) returns (Word, Bool) { let outer = lam(value) { let middle = lam(item) { let inner = lam(innerValue) { return identity(innerValue); }; return inner(item); }; return middle(value); }; return (outer(15), outer(flag)); }",
    "function sameInnerType(flag: Bool) returns (Word, Word) { let outer = lam(value) { let inner = lam(item) { return item; }; return inner(1); }; return (outer(1), outer(flag)); }",
    "function dependentInner(flag: Bool) returns ((Word, Word), (Bool, Bool)) { let outer = lam(value) { let inner = lam(item) { return (value, item); }; return inner(value); }; return (outer(1), outer(flag)); }",
    "function repeatedCapture(flag: Bool) returns (Word) { let total: Word = 0; let f = lam(item) { total += 1; return item; }; f(1); f(flag); f(2); return total; }",
    "function unused() returns (Word) { let outer = lam(value) { let inner = lam(item) { return item; }; return inner(value); }; return 9; }",
    "enum Box<T> { Full(T) }",
    "function intermediate(flag: Bool) returns (Word, Bool) { let f = lam(item) { let box = Box.Full(item); match (box) { case .Full(value) { return value; } } }; return (f(17), f(flag)); }"
  ]}]
}
private def check (program : CheckedProgram) (name : String) (arguments : List Value) (expected : Value) : IO Unit := do
  let compiled ← SourceCompilerFeatureSupport.compileNamed program name []
    {specializationBudget := 32, compilationFuel := 1000}
  for _ in [0, 1] do
    unless (← compiled.run arguments) == expected do
      throw (IO.userError s!"{name} changed the specialized result")
  compiled.checkResume arguments expected 0

def run : IO Unit := do
  let program ← match checkProgram workspace 4096 with
    | .ok result => pure result
    | .error error => throw (IO.userError s!"local runtime source rejected: {reprStr error}")
  for flag in [true, false] do
    check program "qualified" [.bool flag] (.product (.word (w 19)) (.bool flag))
    check program "qualifiedNested" [.bool flag] (.product (.word (w 1)) (.word (w 1)))
    -- Each instance call assigns only its own copy of the captured counter.
    check program "qualifiedCapture" [.bool flag] (.word (w 0))
    check program "local" [.bool flag] (.product (.word (w 11)) (.bool flag))
    check program "nested" [.bool flag] (.product (.word (w 13)) (.bool flag))
    check program "recursiveContext" [.bool flag] (.product (.word (w 15)) (.bool flag))
    check program "sameInnerType" [.bool flag] (.product (.word (w 1)) (.word (w 1)))
    check program "dependentInner" [.bool flag] (.product (.product (.word (w 1)) (.word (w 1))) (.product (.bool flag) (.bool flag)))
    check program "repeatedCapture" [.bool flag] (.word (w 0))
    check program "intermediate" [.bool flag] (.product (.word (w 17)) (.bool flag))
  check program "unused" [] (.word (w 9))
  let seeds ← ["qualifiedMaker", "useFunction"].mapM fun name => do
    match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure (SourceCoreCompiler.Seed.declaration signature.id)
    | _ => throw (IO.userError s!"qualified function root missing: {name}")
  let shared ← match SourceCoreExecution.compileChecked program seeds {compilationFuel := 128, specializationBudget := 32} with
    | .ok shared => pure shared
    | .error error => throw (IO.userError s!"qualified function session failed: {reprStr error}")
  let artifact ← shared.open
  let session ← SourceCompilerFeatureSupport.boot artifact
  let producer ← match shared.keys[0]? with | some key => pure key | none => throw (IO.userError "qualified producer missing")
  let consumer ← match shared.keys[1]? with | some key => pure key | none => throw (IO.userError "qualified consumer missing")
  match ← session.run producer [.word (w 10)] {executionFuel := 300000} with
  | .ok (.succeeded made) =>
      match ← made.session.run consumer [made.value, .word (w 1)] {executionFuel := 300000} with
      | .ok (.succeeded first) =>
          unless first.value == .word (w 11) do throw (IO.userError "qualified closure lost its capture or globals")
          match ← first.session.run consumer [made.value, .word (w 2)] {executionFuel := 300000} with
          | .ok (.succeeded second) =>
              unless second.value == .word (w 11) do throw (IO.userError "qualified closure call did not restart from its captured seed")
          | _ => throw (IO.userError "qualified closure second invocation failed")
      | _ => throw (IO.userError "qualified closure invocation failed")
  | _ => throw (IO.userError "qualified closure export failed")
  IO.println "actual Core local polymorphism and qualified by-value captures GREEN"
end Tests.SourceCoreLocalPolymorphicExecution
end

section
-- leanmerge: from Solcore.Test.SourceCoreOwnedAllocationReadiness
/-! Formal consumers of actual allocation readiness and the same registered
post-pool through lexical binder removal. The reached ghost is projected from
the actual pool; the stable origin seed is never substituted for it. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreOwnedAllocationReadiness
open Core Frontend SourceInference
open Solcore.SourceSemantics
open Solcore.SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedAllocationProducer

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)

include model in
theorem ready_acquires_the_reached_rows_ghost {index : ProtectedStateTransition.Index}
    (reached : State headers keys index) {location : Location} {native : NativeFrame}
    (seed : StableOwner keys location native)
    (read : index.store.read? location = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native)) :
    ∃ selected : Fin keys.length, ∃ metadata,
      keys[selected.val].frameLocation = location ∧
      (reached.rows selected).authority.current = native ∧
      Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        native (reached.rows selected).authority.ghost metadata := by
  obtain ⟨selected, metadata, physicalOwner, current, carried⟩ :=
    readyAt_of_stableOwner model seed reached read
  refine ⟨selected, metadata, physicalOwner, current, ?_⟩
  simpa only [current] using carried

theorem retained_actual_read_supplies_next_allocation {initial reached : ProtectedStateTransition.Index}
    (state : State headers keys reached) {location : Location} {native : NativeFrame}
    (seed : StableOwner keys location native)
    (read : initial.store.read? location = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : location ∉ initial.mapping)
    (preserved : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    (producer headers keys model).Ready state location native :=
  ProtectedStateTransition.OrdinaryAllocation.ReadyAt.after_administrative
    (readyAt_of_stableOwner model seed) state read unmapped preserved

theorem transient_view_cannot_produce_a_stable_snapshot {index : ProtectedStateTransition.Index}
    (state : State headers keys index) (location : Location) (id target : Word) (caller : Int) :
    ¬ (producer headers keys model).Ready state location (.view id target caller) :=
  not_ready_view state location id target caller

theorem transient_view_is_not_a_body_seed (location : Location) (id target : Word) (caller : Int) :
    ¬ StableOwner keys location (.view id target caller) := by
  intro seed
  obtain ⟨selected, ghost, metadata, _physicalOwner, carried⟩ := seed
  cases carried

section CompletedAllocation
variable {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {request : SourceCoreSourceCells.Request} {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
  (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts owner active request)
  (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame globals allocate request)
  (same : annotation.original = allocation.expression)
  (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {before after : Dynamic.Heap} {store : Store}
  (initial : State headers keys ⟨request.scope, mapping, world, before, store, canonical⟩)
  (selected : Fin keys.length) {metadata : Option MetadataState}
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (initial.rows selected).authority.current (initial.rows selected).authority.ghost metadata)
  {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree request.references canonical actual)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type keys[selected.val].frameLocation))
  (payloadAt : CallableIndexedAllocationCompletion.PayloadAt request actual payload)
  (cell : GenericHeap.CellRepresents model mapping world
    ⟨request.binder.scheme.body, sourceValue, none⟩
    (CallableIndexedAllocationCompletion.optionalValue request.payloadType payload) request.payloadType)
  (allocated : Dynamic.Heap.Allocates before request.binder.scheme.body sourceValue sourceLocation after)

include same registered history environments agrees heaps reference payloadAt cell allocated in
/-- The real owned completion supplies one post-witness for the generic
bound transition and the exact append receipt. Binder restoration consumes
that same post-witness and retains every ordered row's complete list. -/
theorem actual_completion_restores_the_registered_post :
    ∃ captured,
      CallableIndexedAllocationCompletion.Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope) compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType])
        after (store ++ [SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload]) ∧
      ∃ final : State headers keys
        ⟨(request.binder.id, request.payloadType) :: request.scope, mapping ++ [store.length + 2],
          world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType], after,
          store ++ [SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
            SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
            CallableIndexedAllocationCompletion.optionalValue request.payloadType payload],
          .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical⟩,
        Relates initial final ∧
        records final selected = records initial selected ++
          [⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩] ∧
        (∀ i, i ≠ selected → records final i = records initial i) ∧
        records ((CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore
          (index := ⟨request.scope, mapping ++ [store.length + 2],
            world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType], after,
            store ++ [SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
              SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
              CallableIndexedAllocationCompletion.optionalValue request.payloadType payload], canonical⟩)
          (id := request.binder.id) (type := request.payloadType)
          (value := .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)) final) = records final ∧
        ProtectedStateTransition.Transition (protocol headers keys) initial
          ⟨request.scope, mapping ++ [store.length + 2],
            world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type, OptionalCell.cellType request.payloadType], after,
            store ++ [SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
              SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
              CallableIndexedAllocationCompletion.optionalValue request.payloadType payload], canonical⟩ := by
  obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, _reference, _boundEnvironment, _frame,
    final, related, selectedRecords, otherRecords⟩ :=
    CallableIndexedOwnedOrdinaryAllocation.completed_bind allocation annotation same registered initial selected
      history environments agrees heaps reference payloadAt cell allocated
  refine ⟨captured, captures, capturedTyped, evaluated, finalHeaps, final, related, selectedRecords, otherRecords, rfl, ?_⟩
  exact ProtectedStateTransition.Bindings.restore_reached
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys) initial ⟨final, related⟩

end CompletedAllocation
end Solcore.Test.SourceCoreOwnedAllocationReadiness
end

section
-- leanmerge: from Solcore.Test.SourceCoreOwnedMethodPrincipalParameters
/-! A genuine method selector and typed bootstrap drive a real Boolean marked
parameter allocation. The actual parameter pool enters a principal packet with
its own complete Source seed. Native completion keeps its original strict child
and the same parameter post. No body meaning or lambda support is assumed. -/
set_option autoImplicit false
namespace Tests.SourceCoreOwnedMethodPrincipalParameters
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning
open CallableIndexedOwnedMethodPrincipal
open Tests.SourceCoreClosedOwnedMethodBootstrap

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (principal : Principal compiled method)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profileFlag : compiled.compatible.checked.catalog.callableContracts = true)

/-- Whole preparation and the full method selector construct the native and
Source bootstrap together; the test requires no external initial heap law. -/
theorem typed_bootstrap {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      principal.cached principal.dictionary profileFlag) :=
  typed_capture_of_selected principal.cached principal.dictionary profileFlag accepted principal.selected wellFormed

variable
  (bootstrap : TypedCapture (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    principal.cached principal.dictionary profileFlag)
  (profile : Profile principal.cached.compilation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) principal.sourceBody principal.dictionary
    bootstrap.capture.administrative registry faults)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (physical : owner.key.frameLocation = 0)
  (locations : ∀ header, header ∈ headers → owner.key.locations header =
    RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
  (initial : State headers keys ⟨[], [], bootstrap.world, ⟨[]⟩,
    RecursiveNamedCatalogPreparedInitialization.store compiled,
    RecursiveNamedCatalogPreparedInitialization.environment compiled⟩)
  {binder : TypedBinder}
  (bindings : principal.named.inputs = [(binder, .bool)])
  (binderType : binder.scheme.body = .bool)
  (boolean : Bool)

include bindings binderType in
private theorem boolean_arguments : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag))
    [] bootstrap.world principal.named.inputs [.bool boolean] [.bool boolean] := by
  rw [bindings]
  apply CallableIndexedParameterMeaning.Arguments.cons _ .nil
  change ValueRep compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    [] bootstrap.world binder.scheme.body (.bool boolean) (.bool boolean) .bool
  rw [binderType]
  exact .bool boolean

include profile bindings binderType in
private theorem boolean_source_types :
    Dynamic.ValuesHaveTypes principal.sourceBody.context ⟨[]⟩ [.bool boolean] profile.types := by
  have rawTypes : profile.types = [.bool] := by
    rw [← Dynamic.MonoBindersExtend.bodyTypes_eq profile.extended, profile.parameters, bindings]
    simp only [List.map_cons, List.map_nil, binderType]
  rw [rawTypes]
  exact .cons (.bool boolean) .nil

include profile physical locations bindings binderType in
/-- The actual marked allocation supplies both original Source admission and
the selected row's own authenticated method seed at the same reached pool. -/
theorem boolean_source_packet
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ environment heap canonical store mapping world,
      Dynamic.BindersAllocate [] ⟨[]⟩ principal.sourceFunction.parameters
        [.bool boolean] environment heap ∧
      Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) profile.context principal.sourceBody.source ∧
      principal.dictionary.Covers profile.context ∧ Dynamic.HeapWellTyped profile.context heap ∧
      Dynamic.EnvironmentAgrees heap profile.context.locals environment ∧
      ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named).State
        ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, heap, store, canonical⟩,
        Relates initial reached.val ∧
        (CallableIndexedOwnedOriginCanonicalState.protocol owner principal.named).records reached = records reached.val ∧
        (∀ row record, record ∈ records reached.val row → CallableIndexedSnapshots.Holds
          compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame mapping store record) := by
  have arguments := boolean_arguments principal profileFlag bootstrap bindings binderType boolean
  have rawTyped := boolean_source_types principal profileFlag bootstrap profile bindings binderType boolean
  have sameFrame := bootstrap.capture.frame_eq.trans physical.symm
  obtain ⟨_origin, _index, _metadata, selected, history, _emitted, entry, added, length, spine, reached, related⟩ :=
    CallableIndexedOwnedMethodInvocationBounds.parameters_with_state principal.cached.compilation
      (CallablePreparedMethodCatalogHookMeaning.of_builtin principal.cached.compilation profile)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) bootstrap.capture.installed
      arguments owner initial sameFrame bootstrap.heaps
  have observed := CallableIndexedOwnedMethodCaptureReceipts.BootstrapCapture.globals_for_owner
    principal.cached principal.dictionary (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    bootstrap.capture owner locations
  have packet := CallableIndexedOwnedMethodNestedEntries.source_packet principal
    (CallablePreparedMethodCatalogHookMeaning.of_builtin principal.cached.compilation profile)
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    bootstrap.capture.installed owner observed selected history entry added length spine reached
  have emptyTyped : Dynamic.HeapWellTyped principal.sourceBody.context ⟨[]⟩ := by
    intro cell impossible; simp at impossible
  obtain ⟨runtime, covers, typed, locals, _facts, _finalContext, _bodyTyped, _completes⟩ :=
    CallableIndexedOwnedBodySourceAdmission.admission_at_selected_method_parameters profile.extended entry.allocation
      emptyTyped rawTyped wellFormed principal.selected bootstrap.capture.sourceFrame
  exact ⟨entry.environment, entry.heap, entry.canonical, entry.store, entry.mapping, entry.world,
    entry.allocation, runtime, covers, typed, locals, ⟨reached, packet⟩, related, rfl,
    fun row record member => record_snapshot reached row member⟩

include profile physical locations bindings binderType in
/-- Original native hook inversion retains its measured body child and real
parameter pool. The packet observes that pool's actual ghost and every record. -/
theorem boolean_native_packet {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues [Value.bool boolean] :: bootstrap.capture.installed.captured)
      (RecursiveNamedCatalogPreparedInitialization.store compiled)
      (principal.cached.compilation.output.rename bootstrap.capture.installed.embedding.lift) value finalStore) :
    ∃ prefixSize childSize environment heap canonical store mapping world actualBody embedding bodyStore,
      prefixSize < size ∧ childSize < prefixSize ∧
      EvaluationSize childSize actualBody store (principal.cached.compilation.body.rename embedding) value bodyStore ∧
      Dynamic.BindersAllocate [] ⟨[]⟩ principal.sourceFunction.parameters [.bool boolean] environment heap ∧
      finalStore = bodyStore.set owner.key.frameLocation
        (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
          (initial.rows owner.position).authority.current) ∧
      ∃ reached : (CallableIndexedOwnedOriginCanonicalState.protocol (headers := headers) owner principal.named).State
        ⟨principal.named.inputs.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, heap, store, canonical⟩,
        Relates initial reached.val ∧
        (CallableIndexedOwnedOriginCanonicalState.protocol owner principal.named).records reached = records reached.val ∧
        (∀ row record, record ∈ records reached.val row → CallableIndexedSnapshots.Holds
          compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame mapping store record) := by
  have arguments := boolean_arguments principal profileFlag bootstrap bindings binderType boolean
  have sameFrame := bootstrap.capture.frame_eq.trans physical.symm
  obtain ⟨_origin, _index, _metadata, prefixSize, bodyStore, selected, history, strict, restored,
      entry, added, length, spine, reached, related⟩ :=
    CallableIndexedOwnedMethodInvocationBounds.body_prefix_with_state principal.cached.compilation
      (CallablePreparedMethodCatalogHookMeaning.of_builtin principal.cached.compilation profile)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag) bootstrap.capture.installed
      arguments owner initial sameFrame bootstrap.heaps completed
  have observed := CallableIndexedOwnedMethodCaptureReceipts.BootstrapCapture.globals_for_owner
    principal.cached principal.dictionary (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    bootstrap.capture owner locations
  have packet := CallableIndexedOwnedMethodNestedEntries.native_packet principal
    (CallablePreparedMethodCatalogHookMeaning.of_builtin principal.cached.compilation profile)
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profileFlag)
    bootstrap.capture.installed owner observed selected history entry added length spine reached
  have nonempty : principal.named.inputs ≠ [] := by rw [bindings]; simp
  exact ⟨prefixSize, entry.childSize, entry.environment, entry.heap, entry.canonical, entry.store, entry.mapping,
    entry.world, entry.actualBody, entry.embedding, bodyStore, strict, entry.strict nonempty, entry.completed,
    entry.allocation, restored, ⟨reached, packet⟩, related, rfl,
    fun row record member => record_snapshot reached row member⟩

end Tests.SourceCoreOwnedMethodPrincipalParameters
end

section
-- leanmerge: from Solcore.Test.SourceCoreOwnedParametersRestoration
/-! Concrete parameter prefixes produce their reached pool with real marked
allocation receipts. Restoring that same post preserves its exact ordered
rows, the original protected records, and the captured callable read. -/
set_option autoImplicit false
namespace Tests.SourceCoreOwnedParametersRestoration
open Solcore Core Frontend SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedParameterMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}

/-- Exact reached-row restoration and prefix retention are separate facts. -/
def ReturnedObservations {caller body : ProtectedStateTransition.Index}
    (saved : State headers keys caller) (reached : State headers keys body) (selected : Fin keys.length) : Prop :=
  let final := CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected
  let returned := CallableIndexedOwnedBodyRestoration.returned saved reached selected
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    body.mapping body.world body.heap final.store ∧
  AdministrativePreserved caller.mapping caller.store body.mapping final.store ∧
  CellState compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    compiled.indexed.ancestry.layout.frame keys[selected.val].frameLocation
    (saved.rows selected).authority.current (saved.rows selected).authority.ghost final.store ∧
  records returned = records reached ∧ Relates saved returned ∧
  (∀ row, RecordPrefix (records saved row) (records returned row)) ∧
  (∀ row record, record ∈ records saved row → record ∈ records returned row) ∧
  (∀ row record, record ∈ records reached row →
    CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame body.mapping final.store record) ∧
  (∀ row : Fin keys.length, keys[row.val].frameLocation = keys[selected.val].frameLocation →
    (returned.rows row).authority.current = (saved.rows selected).authority.current ∧
    (returned.rows row).authority.ghost = (saved.rows selected).authority.ghost) ∧
  (∀ row : Fin keys.length, keys[row.val].frameLocation ≠ keys[selected.val].frameLocation →
    (returned.rows row).authority.current = (reached.rows row).authority.current ∧
    (returned.rows row).authority.ghost = (reached.rows row).authority.ghost) ∧
  ProtectedStateTransition.Transition (protocol headers keys) saved final

private theorem set_of_read {store : Store} {location : Location} {value : Value}
    (read : store.read? location = some value) : store.set location value = store := by
  obtain ⟨bound, same⟩ := List.getElem_of_getElem? read
  rw [← same]
  exact List.set_getElem_self bound

private theorem restore_actual_prefix {caller body : ProtectedStateTransition.Index}
    (saved : State headers keys caller) (reached : State headers keys body) (selected : Fin keys.length)
    (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      body.mapping body.world body.heap body.store)
    (worlds : WorldExtends caller.world body.world)
    (frame : AdministrativePreserved caller.mapping caller.store body.mapping body.store)
    (related : Relates saved reached) : ReturnedObservations (functions := functions) (registry := registry) saved reached selected := by
  have read := (saved.rows selected).authority.frame.read
  rw [(saved.rows selected).frame_eq] at read
  have same := set_of_read read
  have installedFrame : AdministrativePreserved caller.mapping
      (caller.store.set keys[selected.val].frameLocation
        (encode compiled.indexed.ancestry.layout.frame (saved.rows selected).authority.current)) body.mapping body.store := by
    exact Eq.mp (congrArg (fun original => AdministrativePreserved caller.mapping original body.mapping body.store) same.symm) frame
  obtain ⟨finalHeaps, finalFrame, cell, _fromReached, fromSaved, exactRecords, transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return saved reached selected registered heaps worlds installedFrame related
  refine ⟨finalHeaps, finalFrame, cell, exactRecords, fromSaved, fromSaved, ?_, ?_, ?_, ?_, transition⟩
  · intro row record member
    obtain ⟨suffix, appended⟩ := fromSaved row
    rw [appended]
    exact List.mem_append_left _ member
  · exact CallableIndexedOwnedBodyRestoration.returned_snapshot saved reached selected
  · exact CallableIndexedOwnedBodyRestoration.returned_same_frame saved reached selected
  · exact CallableIndexedOwnedBodyRestoration.returned_other_frame saved reached selected

private theorem readyAt_layout
    {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

section Parameters
variable {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (saved : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (selected : Fin keys.length)
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  (sameLayouts : header.layouts = compiled.indexed.layouts)
  (capture : Capture (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers keys[selected.val].locations keys[selected.val].capturePrefix
    (saved.rows selected).authority.frameLocation header mapping world heap store)
  {metadata : Option MetadataState}
  (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (saved.rows selected).authority.current (saved.rows selected).authority.ghost metadata)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
  {actual : Environment} {actualContext : Core.Context} {ξ : Renaming}
  (agrees : EnvironmentsAgree ξ (DataPatternValues.packValues payloads :: capture.canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)

private def concreteProducer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
    header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

include history in
private theorem concreteReady : ProtectedStateTransition.OrdinaryAllocation.ReadyAt
    (concreteProducer (headers := headers) (keys := keys) (functions := functions) (registry := registry) sameLayouts).toOrdinary
    (saved.rows selected).authority.frameLocation (saved.rows selected).authority.current := by
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys
      (saved.rows selected).authority.frameLocation (saved.rows selected).authority.current :=
    ⟨selected, (saved.rows selected).authority.ghost, metadata, (saved.rows selected).frame_eq.symm, history⟩
  intro index reached read
  exact (readyAt_layout (headers := headers) (keys := keys) sameLayouts
    (CallableIndexedOwnedMarkedAllocation.producer headers keys
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) seed)) reached read

include sameLayouts capture represented heaps agrees actualTyped history in
/-- This source prefix needs no body execution or body meaning premise. -/
theorem parameters_restore_actual_pool :
    ∃ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys[selected.val].locations keys[selected.val].capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual ξ (saved.rows selected).authority.frameLocation
      (saved.rows selected).authority.current (saved.rows selected).authority.ghost,
    ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
      Relates saved reached ∧
      ContinuationAgreement actual store (header.parameterCode.rename ξ) entry.actualBody entry.store (header.body.rename entry.embedding) ∧
      ReturnedObservations (functions := functions) (registry := registry) saved reached selected ∧
      (CallableIndexedOwnedBodyRestoration.finalIndex
        (body := ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
        saved selected).store.read? (keys[selected.val].locations header) = some (.inRight .unit
          (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
            (header.code.rename capture.embedding.lift) capture.captured)) := by
  let initial : State headers keys ⟨[], mapping, world, heap, store, capture.canonical⟩ := saved
  obtain ⟨entry, transition, agreement⟩ := CallableIndexedOwnedInvocationBounds.parameters_with_state
    (saved.rows selected).authority capture.environments capture.locals capture.reference capture.coherent represented heaps agrees actualTyped
    (concreteProducer sameLayouts) initial (concreteReady saved selected sameLayouts history)
  obtain ⟨reached, related⟩ := transition
  have observations := restore_actual_prefix saved reached selected (CallableIndexedAmbient.frame_registered compiled.indexed)
    entry.heaps entry.worlds entry.frame related
  refine ⟨entry, reached, related, agreement, observations, ?_⟩
  exact (observations.2.1 _ capture.unmapped (List.getElem?_eq_some_iff.mp capture.read).1).2.trans capture.read

include sameLayouts capture represented heaps agrees actualTyped history in
/-- Native prefix inversion supplies its original body grade and the same real
parameter post. Source and native grades remain independent. -/
theorem parameters_native_restore_actual_pool (member : header ∈ headers)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (header.parameterCode.rename ξ) result afterStore) :
    ∃ entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys[selected.val].locations keys[selected.val].capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual ξ (saved.rows selected).authority.frameLocation
      (saved.rows selected).authority.current (saved.rows selected).authority.ghost,
    ∃ child, EvaluationSize child entry.actualBody entry.store (header.body.rename entry.embedding) result afterStore ∧
      child ≤ size ∧ (header.bindings ≠ [] → child < size) ∧
    ∃ reached : State headers keys ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
      entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
      Relates saved reached ∧ ReturnedObservations (functions := functions) (registry := registry) saved reached selected ∧
      (CallableIndexedOwnedBodyRestoration.finalIndex
        (body := ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
        saved selected).store.read? (keys[selected.val].locations header) = some (.inRight .unit
          (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
            (header.code.rename capture.embedding.lift) capture.captured)) := by
  let initial : State headers keys ⟨[], mapping, world, heap, store, capture.canonical⟩ := saved
  obtain ⟨entry, child, bodyCompletion, childLe, childStrict, transition⟩ := CallableIndexedOwnedInvocationBounds.parameters_sized_with_state
    (saved.rows selected).authority member capture represented heaps agrees actualTyped completed
    (concreteProducer sameLayouts) initial (concreteReady saved selected sameLayouts history)
  obtain ⟨reached, related⟩ := transition
  have observations := restore_actual_prefix saved reached selected (CallableIndexedAmbient.frame_registered compiled.indexed)
    entry.heaps entry.worlds entry.frame related
  refine ⟨entry, child, bodyCompletion, childLe, childStrict, reached, related, observations, ?_⟩
  exact (observations.2.1 _ capture.unmapped (List.getElem?_eq_some_iff.mp capture.read).1).2.trans capture.read

end Parameters
end Tests.SourceCoreOwnedParametersRestoration
end

section
-- leanmerge: from Solcore.Test.SourceCoreOwnedSelectedLiteralCall
/-! A literal lambda call uses its authentic formation receipt and caller packet.
The lambda-only child family and selected anonymous body continuations are closed
here from static receipts. The formation and the call each copy the captured
cells; empty arguments, empty parameters and a nil Unit body then construct the
complete Source parent; native reflection retains its own Source grade and the
exact actual returned pool. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
namespace Tests.SourceCoreOwnedSelectedLiteralCall
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedLambdaNestedRuntimeBodyMeaning
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open SourceCoreCallableIndexedFrames
open Tests.SourceCoreClosedOwnedLexicalBody (reached_pool_observations)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
variable
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (ranks : CallableIndexedOwnedFunctionValues.Header compiled program → Nat)
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}

variable (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame},
      (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) entry →
      MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
        (CallableIndexedOwnedNestedNamedFamilyClosure.certificates (headers := headers) (registry := registry) (faults := faults) ranks header)
        diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
  (callerGlobals : caller.globals = compiled.indexed.base.globals.length)
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)

/-- Every child receipt is a genuine original lambda occurrence. -/
def lambdaChildren : GenericExpressionMeaning.Certificate := fun scope id lowered =>
  ∃ rank, Nonempty (LambdaAt (values := .initial compiled.compatible.checked)
    headers caller registry faults rank source context evidence scope id lowered)

include prefixZero complete callerGlobals slots sameSource in
/-- The lambda child family is proved by the real formation leaf producer. -/
private theorem children_preserve (size : Nat) (unique : NodeOccurrencesUnique source) :
    ProtectedStateTransition.PreservesAt
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source (lambdaChildren (headers := headers) (registry := registry) (faults := faults) (source := source) (context := context) (evidence := evidence) caller) faults size := by
  intro scope id lowered certified
  obtain ⟨rank, child⟩ := certified
  exact CallableIndexedOwnedNestedCanonicalState.formation_preserves_at owner caller prefixZero profile complete
    callerGlobals slots sameSource size unique child

include prefixZero complete callerGlobals slots sameSource in
/-- Native lambda completion retains the same reached packet and Source grade. -/
private theorem children_reflect (size : Nat) :
    ProtectedStateTransition.ReflectsAt
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source (lambdaChildren (headers := headers) (registry := registry) (faults := faults) (source := source) (context := context) (evidence := evidence) caller) faults size := by
  intro scope id lowered certified
  obtain ⟨rank, child⟩ := certified
  exact CallableIndexedOwnedNestedCanonicalState.formation_reflects_at owner caller prefixZero profile complete
    callerGlobals slots sameSource size child

section Parent
variable {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : CallableIndexedOwnedSelectedIndirectHeads.Receipt (headers := headers)
    (registry := registry) (faults := faults) (source := source) (context := context) (evidence := evidence)
    caller (lambdaChildren (headers := headers) (registry := registry) (faults := faults) (source := source) (context := context) (evidence := evidence) caller) scope id lowered)
  (noArguments : head.ids = []) (noParameters : head.formation.parameters = [])
  (emptyBody : head.formation.statements = []) (unitResult : head.formation.result = .unit)
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}
  (initial : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
    ⟨scope, mapping, world, heap, store, canonical⟩)
  (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)

private def bridge := CallableIndexedOwnedIndirectCallerProtocol.forget_slots
  (CallableIndexedOwnedNestedCallerProtocol.carrier (headers := headers) owner caller)

local notation "Record" => CallableIndexedOwnedSelectedIndirectHeads.CalleeRecord owner caller prefixZero profile complete
  callerGlobals head (bridge owner caller) initial initial.property related agrees typed

private def selectedClosure (formedRecord : Record) :=
  CallableIndexedOwnedSelectedIndirectHeads.formedReceipt owner caller prefixZero profile complete callerGlobals slots head
    (bridge owner caller) initial initial.property related agrees typed heaps formedRecord


variable (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) ((actualCode head.formation environment).reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) (((actualCode head.formation environment).reasonAt id).add tag))

include prefixZero profile initial complete globals slots sameLayouts extension faithful observations functionTypes owners
  uninitialized missing escaped profiles callerGlobals related agrees typed heaps bodyUninitialized bodyMissing in
/-- The exact argument post selects the internally closed authentic body. -/
private theorem closed_source (formedRecord : Record)
    (reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨scope, formedRecord.finalMap, formedRecord.finalWorld, formedRecord.finalHeap, formedRecord.finalStore, canonical⟩)
    (budget : Nat) :
    SourceContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := head.ids) profile
      (selectedClosure owner prefixZero profile complete slots caller callerGlobals head initial related agrees typed heaps formedRecord)
      (head.selected environment).escaped (bridge owner caller) reached budget := by
  exact CallableIndexedOwnedSelectedIndirectBodies.source_continuations owner prefixZero profile complete globals slots sameLayouts
    extension faithful observations functionTypes owners uninitialized missing escaped ranks profiles
    (selectedClosure owner prefixZero profile complete slots caller callerGlobals head initial related agrees typed heaps formedRecord) rfl rfl
    callerGlobals bodyUninitialized bodyMissing (head.selected environment).escaped (bridge owner caller) reached budget

include prefixZero profile initial complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles callerGlobals related agrees typed heaps bodyUninitialized bodyMissing in
private theorem closed_native (formedRecord : Record)
    (reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State
      ⟨scope, formedRecord.finalMap, formedRecord.finalWorld, formedRecord.finalHeap, formedRecord.finalStore, canonical⟩)
    (budget : Nat) :
    NativeContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := head.ids) profile
      (selectedClosure owner prefixZero profile complete slots caller callerGlobals head initial related agrees typed heaps formedRecord)
      (head.selected environment).escaped (bridge owner caller) reached budget := by
  exact CallableIndexedOwnedSelectedIndirectBodies.native_continuations owner prefixZero profile complete globals slots sameLayouts
    extension faithful observations functionTypes uninitialized missing escaped ranks profiles
    (selectedClosure owner prefixZero profile complete slots caller callerGlobals head initial related agrees typed heaps formedRecord) rfl rfl
    callerGlobals bodyUninitialized bodyMissing (head.selected environment).escaped (bridge owner caller) reached budget


variable
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (heapTyped : Dynamic.HeapWellTyped context heap)
  (stable : StableRows initial.val)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)
  (unique : NodeOccurrencesUnique source)

include prefixZero profile complete callerGlobals slots initial related agrees typed heaps wellFormed runtime covers locals heapTyped noArguments noParameters emptyBody unitResult in
/-- The complete original Source parent is constructed from genuine formation,
which copies the captured cells, empty ordered arguments, the call's own copies,
actual empty parameters and the nil Unit body. -/
theorem actual_source :
    ∃ size after, RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment heap id
      (.value .unit) after := by
  obtain ⟨formedRecord⟩ := CallableIndexedOwnedLambdaFormationReceipts.formation_exists head.formation complete
    callerGlobals slots ((bridge owner caller).pool initial) owner prefixZero initial.property.observed
    initial.property.carried initial.property.bundle related agrees typed heaps
  let closure := (selectedClosure owner prefixZero profile complete slots caller callerGlobals head initial related agrees typed heaps formedRecord)
  obtain ⟨calleeSource, _copy, _native⟩ := CallableIndexedOwnedSelectedIndirectHeads.formed_receipts owner caller prefixZero
    profile complete callerGlobals slots head (bridge owner caller) initial initial.property related agrees typed heaps
    formedRecord
  obtain ⟨calleeSize, calleeTrace⟩ := SourceExecutionSize.ExpressionEvaluates.has_size calleeSource
  let function := formed head.formation formedRecord.captured
  have noArgumentsAt : ∀ heap', SourceExecutionSize.ExpressionsEvaluate program (SourceExecutionSize.stepSize [])
      context evidence source environment heap' head.ids [] heap' := by
    intro heap'; rw [noArguments]; exact .nil
  have arguments := noArgumentsAt formedRecord.finalHeap
  have capturesValid : Dynamic.EnvironmentAgrees formedRecord.finalHeap function.context.locals function.captured :=
    formedRecord.copy.agrees locals
  obtain ⟨copies, after, callCopy⟩ := CellAwareGeneralizedSourceInversion.copies_exist function.source capturesValid
  have parameters : function.parameters = [] := noParameters
  have body : function.body = [] := emptyBody
  have result : function.resultType = .unit := unitResult
  have allocated : Dynamic.BindersAllocate copies after function.parameters [] copies after := by
    rw [parameters]; exact .nil _ _
  have executed : SourceExecutionSize.FunctionStatementsExecute program (SourceExecutionSize.stepSize [])
      closure.inputs.context function.evidence function.source copies after function.body closure.inputs.context
      (.fallthrough copies) after := by
    have nilTrace : SourceExecutionSize.FunctionStatementsExecute program (SourceExecutionSize.stepSize [])
        closure.inputs.context function.evidence function.source copies after [] closure.inputs.context
        (.fallthrough copies) after := .nil
    exact Eq.mp (congrArg (fun statements => SourceExecutionSize.FunctionStatementsExecute program (SourceExecutionSize.stepSize [])
      closure.inputs.context function.evidence function.source copies after statements closure.inputs.context
      (.fallthrough copies) after) body.symm) nilTrace
  have called : RecursiveNamedCallBounds.CallOutcome program
      (SourceExecutionSize.stepSize [SourceExecutionSize.stepSize []]) context evidence
      function.evidence formedRecord.finalHeap (.closure function) [] (.value .unit) after :=
    .value (.closureUnit rfl (closure.bodyOrigin (head.selected environment).escaped).frame result
      closure.inputs.extended callCopy allocated executed ⟨_, rfl⟩)
  obtain ⟨size, sourceTrace⟩ := SourceSuffix.to_expression head.compiler.found head.compiler.originalForm
    head.parent.requirements head.parent.coercions head.compiler.argumentCoercions head.parent.arity wellFormed runtime
    covers (locals.mono formedRecord.copy.metadata_extends) (heapTyped.copy formedRecord.copy)
    head.sourceArguments head.sourceCount calleeTrace (SourceSuffix.of_call arguments called)
  exact ⟨size, after, sourceTrace⟩


/-- Observations refer to every real reached row, retaining duplicate records. -/
def observationsAt {firstIndex reachedIndex : ProtectedStateTransition.Index}
    (first : State headers keys firstIndex) (reached : State headers keys reachedIndex) : Prop :=
  (∀ row, RecordPrefix (records first row) (records reached row)) ∧
  (∀ row record, record ∈ records reached row → CallableIndexedSnapshots.Holds
    compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    compiled.indexed.ancestry.layout.frame reachedIndex.mapping reachedIndex.store record) ∧
  (∀ row record, record ∈ records first row → record ∈ records reached row)


/-- The same transition witness supplies every row's ordered prefix and real
snapshot interpretation at its own final map and store. -/
theorem observe_transition {firstIndex finalIndex : ProtectedStateTransition.Index}
    (first : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State firstIndex)
    (transition : ProtectedStateTransition.Transition
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) first finalIndex) :
    ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).State finalIndex,
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller).Relates first reached ∧
      observationsAt (compiled := compiled) (program := program) (headers := headers) (keys := keys) first.val reached.val := by
  obtain ⟨reached, related⟩ := transition
  exact ⟨reached, related,
    reached_pool_observations (compiled := compiled) (program := program) (headers := headers) (keys := keys)
      (initial := first.val) (final := reached.val) related⟩

include prefixZero profile initial complete globals slots sameLayouts extension faithful observations functionTypes owners
  uninitialized missing escaped profiles callerGlobals sameSource related agrees typed heaps locals heapTyped stable
  wellFormed runtime covers unique bodyUninitialized bodyMissing noArguments noParameters emptyBody unitResult in
/-- This whole literal call has no expression or body execution law as input.
The same actual callee, argument and body posts supply the restored caller pool. -/
theorem literal_call_source_post :
    ∃ sourceSize after,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id
        (.value .unit) after ∧
      ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld head.compiler.original.type lowered.type faults (.value .unit) value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
        initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, after, sourceTrace⟩ := actual_source
    (owner := owner) (prefixZero := prefixZero) (profile := profile) (complete := complete)
    (slots := slots) (caller := caller) (callerGlobals := callerGlobals) (head := head)
    (initial := initial) (related := related) (agrees := agrees) (typed := typed) (heaps := heaps)
    (wellFormed := wellFormed) (runtime := runtime) (covers := covers) (locals := locals) (heapTyped := heapTyped)
    (noArguments := noArguments) (noParameters := noParameters) (emptyBody := emptyBody) (unitResult := unitResult)
  refine ⟨sourceSize, after, sourceTrace, ?_⟩
  exact CallableIndexedOwnedSelectedIndirectHeads.preserves_bounded
      (owner := owner) (caller := caller) (prefixZero := prefixZero) (profile := profile) (complete := complete)
      (globals := callerGlobals) (slots := slots) (head := head) (bridge := bridge owner caller) (initial := initial)
      (packet := initial.property) (related := related) (agrees := agrees) (typed := typed)
      (heaps := heaps) (locals := locals) (heapTyped := heapTyped) (stable := stable) (wellFormed := wellFormed)
      (runtime := runtime) (covers := covers) (unique := unique) (budget := sourceSize)
      (arguments := fun child _ => children_preserve (owner := owner) (prefixZero := prefixZero) (profile := profile)
        (complete := complete) (caller := caller) (callerGlobals := callerGlobals) (slots := slots)
        (sameSource := sameSource) child unique)
      (bodies := fun formedRecord reached _ => closed_source (owner := owner) (prefixZero := prefixZero) (profile := profile)
        (complete := complete) (globals := globals) (slots := slots) (sameLayouts := sameLayouts) (extension := extension)
        (faithful := faithful) (observations := observations) (functionTypes := functionTypes) (owners := owners)
        (uninitialized := uninitialized) (missing := missing) (escaped := escaped) (ranks := ranks) (profiles := profiles)
        (caller := caller) (callerGlobals := callerGlobals) (head := head) (initial := initial) (related := related)
        (agrees := agrees) (typed := typed) (heaps := heaps) (bodyUninitialized := bodyUninitialized)
        (bodyMissing := bodyMissing) formedRecord reached sourceSize) sourceTrace (Nat.le_refl _)

include prefixZero profile initial complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles callerGlobals sameSource related agrees typed heaps locals heapTyped stable
  wellFormed runtime covers bodyUninitialized bodyMissing in
/-- Native completion follows the same actual selection and body family and
returns a genuine independently graded whole Source parent at the real post. -/
theorem literal_call_native_post {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld head.compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
        initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact CallableIndexedOwnedSelectedIndirectHeads.reflects_bounded
      (owner := owner) (caller := caller) (prefixZero := prefixZero) (profile := profile) (complete := complete)
      (globals := callerGlobals) (slots := slots) (head := head) (bridge := bridge owner caller) (initial := initial)
      (packet := initial.property) (related := related) (agrees := agrees) (typed := typed)
      (heaps := heaps) (locals := locals) (heapTyped := heapTyped) (stable := stable) (wellFormed := wellFormed)
      (runtime := runtime) (covers := covers) (budget := size)
      (arguments := fun child _ => children_reflect (owner := owner) (prefixZero := prefixZero) (profile := profile)
        (complete := complete) (caller := caller) (callerGlobals := callerGlobals) (slots := slots)
        (sameSource := sameSource) child)
      (bodies := fun formedRecord reached _ => closed_native (owner := owner) (prefixZero := prefixZero) (profile := profile)
        (complete := complete) (globals := globals) (slots := slots) (sameLayouts := sameLayouts) (extension := extension)
        (faithful := faithful) (observations := observations) (functionTypes := functionTypes)
        (uninitialized := uninitialized) (missing := missing) (escaped := escaped) (ranks := ranks) (profiles := profiles)
        (caller := caller) (callerGlobals := callerGlobals) (head := head) (initial := initial) (related := related)
        (agrees := agrees) (typed := typed) (heaps := heaps) (bodyUninitialized := bodyUninitialized)
        (bodyMissing := bodyMissing) formedRecord reached size) completed (Nat.le_refl _)

end Parent
end Tests.SourceCoreOwnedSelectedLiteralCall
end

section
-- leanmerge: from Solcore.Test.SourceCoreStagingHeapRelation
/-! The function consumer retains its actual acceptance, full ledger and source
trace. These tests do not claim a compiler has erased the whole call. -/

set_option autoImplicit false
namespace Tests.SourceCoreStagingHeapRelation
open Solcore Solcore.SourceSemantics Solcore.SourceSemantics.Dynamic TypeSystem
open Solcore.SourceSemantics.CoreLowering.SourceStagingHeapRelation

abbrev actual_function := @integer_function_suffix
abbrev actual_integer_allocation := @HeapRel.erase_allocated
abbrev retained_allocation := @HeapRel.keep_allocated

theorem full_initial_heap {context : Context} {heap : Heap}
    (typed : HeapWellTyped context heap) : HeapRel (identityMap heap.cells.length) heap heap :=
  HeapRel.identity typed

theorem selected_integer_suffix {context : Context} {before : Heap}
    (typed : HeapWellTyped context before) (first second : Int) :
    HeapRel (identityMap before.cells.length ++ [none, none])
      ⟨before.cells ++ [integerCell first, integerCell second]⟩ before := by
  simpa using (HeapRel.identity typed).erase_suffix [first, second]

theorem full_initial_read {before after : Heap} {values : List Int}
    (cells : after.cells = before.cells ++ values.map integerCell)
    {location : Location} {cell : Cell} (read : Heap.Reads before location cell) :
    Heap.Reads after location cell := initial_read cells read

theorem capture_before_suffix {context : Context} {before : Heap} {location : Location}
    (typed : HeapWellTyped context before) (capture : Capture.HeapCaptures before location)
    (offset : Nat) : location.index ≠ before.cells.length + offset := by
  have bound := Capture.heap_bounded typed capture
  omega

theorem integer_result_has_no_capture (value : Int) (location : Location) :
    ¬ Capture.ValueCaptures (.integer value) location := by
  intro captured
  cases captured

section Negative

theorem generalized_cannot_drop (function : GeneralizedClosure) :
    ¬ EligibleDrop ({type := .integer, value := some (.integer 3), generalized := some function} : Cell) :=
  generalized_not_eligible rfl

theorem uninitialized_cannot_drop (type : Ty) :
    ¬ EligibleDrop ({type, value := none} : Cell) := by
  intro eligible
  obtain ⟨value, valueEq⟩ := eligible.fields.2.2
  cases valueEq

theorem captured_drop_impossible {mapping : LocationMap} {function : Closure} {target : Value}
    {id : Resolved.LocalId} {location : Location} (member : (id, location) ∈ function.captured)
    (dropped : mapping[location.index]? = some none) :
    ¬ ValueRel mapping (.closure function) target := by
  intro related
  cases related with
  | closure captured => exact captured.not_dropped member dropped

theorem unused_shadowed_capture_impossible (function : Closure) (id : Resolved.LocalId) :
    ¬ ValueRel [some ⟨0⟩, none]
      (.closure {function with captured := [(id, ⟨0⟩), (id, ⟨1⟩)]}) (.closure function) := by
  apply captured_drop_impossible (id := id) (location := ⟨1⟩)
  · simp
  · rfl

theorem nested_product_capture_impossible (function : Closure) (id : Resolved.LocalId)
    (left right : Value) :
    ¬ ValueRel [none]
      (.product .unit (.closure {function with captured := [(id, ⟨0⟩)]})) (.product left right) := by
  intro related
  cases related with
  | product _ captured =>
      exact captured_drop_impossible (id := id) (location := ⟨0⟩) (by simp) rfl captured

theorem future_capture_cannot_be_typed {context : Context} {heap : Heap} {function : Closure}
    {id : Resolved.LocalId} {location : Location} {type : Ty}
    (member : (id, location) ∈ function.captured) (future : heap.cells.length ≤ location.index) :
    ¬ ValueHasType context heap (.closure function) type := by
  intro typed
  have bound := Capture.value_bounded typed location (.closure member)
  omega

end Negative

section Sharing

/-- The middle source cell is omitted. Both occurrences of the last source
location map to the same residual cell, and the older unused tail remains. -/
theorem ordered_shared_environment (id older : Resolved.LocalId) :
    EnvironmentRel [some ⟨0⟩, none, some ⟨1⟩]
      [(id, ⟨2⟩), (id, ⟨2⟩), (older, ⟨0⟩)]
      [(id, ⟨1⟩), (id, ⟨1⟩), (older, ⟨0⟩)] :=
  .cons rfl (.cons rfl (.cons rfl .nil))

theorem ordered_shared_closure (function : Closure) (id older : Resolved.LocalId) :
    ValueRel [some ⟨0⟩, none, some ⟨1⟩]
      (.closure {function with captured := [(id, ⟨2⟩), (id, ⟨2⟩), (older, ⟨0⟩)]})
      (.closure {function with captured := [(id, ⟨1⟩), (id, ⟨1⟩), (older, ⟨0⟩)]}) :=
  .closure (ordered_shared_environment id older)

theorem original_first_match (id older : Resolved.LocalId) :
    ∃ target, Environment.LooksUp [(id, ⟨1⟩), (id, ⟨1⟩), (older, ⟨0⟩)] id target ∧
      Maps [some ⟨0⟩, none, some ⟨1⟩] ⟨2⟩ target :=
  (ordered_shared_environment id older).lookup .head

theorem distinct_retained_cells {mapping : LocationMap} {length : Nat}
    (ordered : Ordered mapping length) {left right target : Location}
    (first : Maps mapping left target) (second : Maps mapping right target) : left = right :=
  ordered.injective first second

def boolCell (value : Bool) : Cell := {type := .bool, value := some (.bool value)}

theorem retain_drop_retain (erased : Int) :
    HeapRel [some ⟨0⟩, none, some ⟨1⟩]
      ⟨[boolCell false, integerCell erased, boolCell true]⟩
      ⟨[boolCell false, boolCell true]⟩ := by
  have empty : HeapRel [] ⟨[]⟩ ⟨[]⟩ := by
    refine ⟨rfl, .nil, ?_, ?_⟩
    · intro index target cell mapped
      simp at mapped
    · intro index dropped
      simp at dropped
  have first := empty.keep (sourceCell := boolCell false) (residualCell := boolCell false)
    ⟨rfl, .some (.bool false), .none⟩
  have dropped := first.erase_integer erased
  exact dropped.keep ⟨rfl, .some (.bool true), .none⟩

end Sharing
end Tests.SourceCoreStagingHeapRelation
end

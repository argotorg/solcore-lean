import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTypedMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualTyped
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceCoreCallableIndexedFrames

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual production contextual receipts close every semantic child obligation
in the typed recursive grammar. Runtime cases combine index, constructor,
member, proxy, primitive, conditional and product syntax under captured hidden slots. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleTypedExpressions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionTyped CompatiblePayload GeneralHeap ReadOnly

variable {values : ValuesContext} {readFuel : Nat} {source : TypedSource} {sourceContext : SourceSemantics.Context}
  {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
  {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
  {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {compilation : SourceCoreFunctions.Context} {native : Option SourceCoreGeneralFunctions.CallableContext}
  {parent : Option SourceCoreLocalEvidence.Prepared} {skip : Option ExpressionId}
  {fuel : Nat} {reasonAt : ExpressionId → Word}
  (ordinary : Ordinary source locals compilation.owner) (unique : NodeOccurrencesUnique source)
  (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
  (signatures : sourceContext.signatures = values.checked.signatures)
  (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
  (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
  (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)

/-- The complete static receipt is extracted from real contextual compilation.
No child lowering result or child execution is supplied by the caller. -/
def Accepted : GenericExpressionMeaning.Certificate := fun scope id code => ∃ node,
  CompatibleExpressionReads.ScopeDeclarations source scope sourceContext ∧
  Syntax source id ∧ source.lookupExpression? id = some node ∧
  ExpressionHasType source sourceContext id node.type ∧
  SourceCoreGeneralFunctions.lowerContextualExpression program representation values.checked.signatures locals parents
    assignments diagnostics compilation native parent skip fuel source scope id reasonAt = .ok code

include ordinary unique closed residual signatures readPolicy lowerPolicy leafPolicy in
theorem actual_tree {scope id code}
    (accepted : Accepted (sourceContext := sourceContext) (values := values)
      (source := source) (program := program) (representation := representation) (locals := locals) (parents := parents)
      (assignments := assignments) (diagnostics := diagnostics) (compilation := compilation) (native := native)
      (parent := parent) (skip := skip) (fuel := fuel) (reasonAt := reasonAt) scope id code) :
    Tree readFuel values source sourceContext compilation.solvedRequirements reasonAt scope id code := by
  obtain ⟨node, declarations, syntaxTree, found, typed, generated⟩ := accepted
  exact tree_of_contextual ordinary unique closed residual declarations signatures syntaxTree found typed
    readPolicy lowerPolicy leafPolicy generated

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (semantics : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements sourceContext evidence)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include ordinary unique closed residual signatures readPolicy lowerPolicy leafPolicy extension valid uninitialized missing in
theorem accepted_preserves :
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      semantics sourceContext evidence source
      (Accepted (sourceContext := sourceContext) (values := values)
        (source := source) (program := program) (representation := representation) (locals := locals) (parents := parents)
        (assignments := assignments) (diagnostics := diagnostics) (compilation := compilation) (native := native)
        (parent := parent) (skip := skip) (fuel := fuel) (reasonAt := reasonAt)) faults := by
  intro scope id code accepted node found mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps lexical agrees actualTyped trace
  have tree := actual_tree ordinary unique closed residual signatures readPolicy lowerPolicy leafPolicy accepted
  exact preserves functions extension semantics evidence valid unique uninitialized missing tree
    found environments heaps lexical agrees actualTyped trace

include ordinary unique closed residual signatures readPolicy lowerPolicy leafPolicy extension valid uninitialized missing in
theorem accepted_reflects :
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      semantics sourceContext evidence source
      (Accepted (sourceContext := sourceContext) (values := values)
        (source := source) (program := program) (representation := representation) (locals := locals) (parents := parents)
        (assignments := assignments) (diagnostics := diagnostics) (compilation := compilation) (native := native)
        (parent := parent) (skip := skip) (fuel := fuel) (reasonAt := reasonAt)) faults := by
  intro scope id code accepted node found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps lexical agrees actualTyped completed
  have tree := actual_tree ordinary unique closed residual signatures readPolicy lowerPolicy leafPolicy accepted
  exact reflects functions extension semantics evidence valid uninitialized missing tree
    found environments heaps lexical agrees actualTyped completed

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "function build_box() returns (Box<Bool>) { let m: mapping(Bool => Bool); let n: mapping(Bool => Bool); return .Box(!m[true] || n[false]); }",
    "function conditional() returns (Box<Bool>) { let m: mapping(Bool => Bool); let n: mapping(Bool => Bool); return m[true] ? .Box(n[true]) : .Box(!m[false]); }",
    "function paired() returns ((Box<Bool>, Bool)) { let m: mapping(Bool => Bool); let n: mapping(Bool => Bool); let box: Box<Bool> = .Box(!m[true]); return (box, n[m[false]]); }",
    "function member_base() returns (Box<mapping(Bool => Bool)>) { let m: mapping(Bool => Bool); return .Box(m); }",
    "function child_fault() returns (Box<Bool>) { let m: mapping(Bool => Bool); let missing: Bool; let n: mapping(Bool => Bool); return .Box(m[true] || missing || n[true]); }",
    "function skipped() returns (Box<Bool>) { let m: mapping(Bool => Bool); return .Box(false && m[true]); }",
    "function proxy_box() returns (Box<@Word>) { return .Box(@Word); }",
    "function proxy_choice(flag: Bool) returns (@Word) { return flag ? @Word : @Word; }",
    "function proxy_pair() returns ((@Word, @Bool)) { return (@Word, @Bool); }",
    "function proxy_nested() returns ((Box<@Word>, @Bool)) { let boxed: Box<@Word> = .Box(@Word); return (boxed, @Bool); }",
    "function proxy_parent() returns (Box<@Word>) { let make = lam(value) -> Box<@Word> { return .Box(@Word); }; return make(true); }",
    "function parent(seed: Bool) returns (Box<Bool>) { let f = lam(item) -> Box<Bool> { let m: mapping(Bool => Bool); return .Box(m[seed] ? m[false] : !m[true]); }; return f(true); }"]}] }
private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | budget + 1, source, id => match source.lookupExpression? id with
    | none => []
    | some node => node :: (match node.form with
      | .index base key => reached budget source base ++ reached budget source key
      | .group inner | .unary _ inner | .member inner _ _ => reached budget source inner
      | .binary left _ right => reached budget source left ++ reached budget source right
      | .conditional condition first second => reached budget source condition ++ reached budget source first ++ reached budget source second
      | .tuple ids | .constructor _ ids => ids.flatMap (reached budget source)
      | _ => [])

private def inspect {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked) (original : TypedSource)
    (owner : SourceSpecialization.SpecializationKey) (parent : Option SourceCoreLocalEvidence.Prepared)
    (solved : List SolvedRequirement) (name : String) (expression : ExpressionId) : IO Unit := do
  let originalNode ← match original.lookupExpression? expression with
    | some node => pure node | none => throw (IO.userError "typed recursive original expression missing")
  let original ← if name == "paired" || name == "proxy_nested" then do
      let constructor ← match original.nodes.findSome? fun
        | .expression node => match node.form with | .constructor _ _ => some node.id | _ => none
        | _ => none with
        | some id => pure id | none => throw (IO.userError "typed recursive paired constructor missing")
      let .tuple [_, right] := originalNode.form | throw (IO.userError "typed recursive pair shape changed")
      -- The checked initializer is used as the tuple child in retained typed IR.
      pure { original with nodes := original.nodes.map fun
        | .expression node => if node.id == expression then .expression {node with form := .tuple [constructor, right]} else .expression node
        | other => other }
    else pure original
  let (source, expression) := if name == "member_base" then
      let nextId := fun index => (⟨⟨original.owner, 100000 + index⟩⟩ : ExpressionId)
      let selected : ExpressionNode := { id := nextId 0, span := originalNode.span, type := .mapping .bool .bool, form := .member expression "0" 0 }
      let key : ExpressionNode := { id := nextId 1, span := originalNode.span, type := .bool, form := .reference "true" (.builtinBoolean true) }
      let indexed : ExpressionNode := { id := nextId 2, span := originalNode.span, type := .bool, form := .index selected.id key.id }
      ({ original with roots := [.expression indexed.id], nodes := original.nodes ++
        [.expression selected, .expression key, .expression indexed] }, indexed.id)
    else if name == "proxy_raw" then
      -- Retained typed IR changes only raw proxy metadata; the native identity
      -- is deliberately shared with canonical @Word. This is not new source admission.
      let raw := TypeSystem.Ty.comptime .word
      ({ original with nodes := original.nodes.map fun
        | .expression node => match node.form with
          | .proxy .word => .expression {node with type := .proxy raw, form := .proxy raw}
          | .tuple _ => if node.id == expression then
              .expression {node with type := .product (.proxy raw) (.proxy .bool)} else .expression node
          | _ => .expression node
        | other => other }, expression)
    else (original, expression)
  let nodes := reached 100 source expression
  let ids := (nodes.filterMap fun node => match node.form with | .reference _ (.local binder) => some binder | _ => none).eraseDups
  let mut values := SourceCoreCompatibleValues.Context.initial checked
  if name == "proxy_raw" then
    let raw := TypeSystem.Ty.comptime .word
    let encoded ← get "typed raw proxy registry" (SourceCoreCompatibleValues.encode 100 values (.proxy raw) (.proxy raw))
    values := encoded.context
    assertTrue ((checked.catalog.project (.proxy raw)).toOption == (checked.catalog.project (.proxy .word)).toOption)
      "raw proxy fixture no longer shares native type"
    assertTrue (values.registry.id? (.proxy raw) != values.registry.id? (.proxy .word))
      "raw proxy inner metadata collapsed to canonical header"
  let mut bindings : List (TypedBinder × Ty × Expr × Option Value) := []
  for id in ids do
    let binder ← get "typed recursive binder" (SourceCoreDataPlaces.rootBinder source id)
    let native ← get "typed recursive binder projection" (checked.catalog.project binder.scheme.body)
    let (initializer, expected) ← match binder.scheme.body with
      | .mapping key result => do
        let encoded ← get "typed recursive expected mapping" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key result []))
        values := encoded.context
        pure (OptionalCell.allocate native, some encoded.value)
      | .bool => pure (if binder.name == "missing" then (OptionalCell.allocate native, none)
          else (OptionalCell.allocateInitialized native (.bool true), some (.bool true)))
      | other => throw (IO.userError s!"typed recursive unexpected binder {reprStr other}")
    bindings := bindings ++ [(binder, native, initializer, expected)]
  let diagnostics ← match prepared.diagnostics with
    | some diagnostics => pure diagnostics.program | none => throw (IO.userError "typed recursive diagnostics missing")
  let own ← match diagnostics.base.find? owner with
    | some own => pure own | none => throw (IO.userError "typed recursive owner diagnostics missing")
  let compilation : SourceCoreFunctions.Context := {
    plan := prepared.plan, owner, globals := prepared.globals, administrativePrefix := 1,
    solvedRequirements := solved, internalReason := Word.zero }
  let scope := bindings.map fun (binder, type, _, _) => (binder.id, type)
  let representation := SourceCoreCompatibleFunctions.representation values 150
  let lowered ← get "typed recursive actual contextual compiler" (
    SourceCoreGeneralFunctions.lowerContextualExpression prepared.sourceProgram representation checked.signatures prepared.locals
      prepared.contexts own.assignments diagnostics compilation prepared.callableContext parent none 150 source scope expression (diagnostics.reasonAt owner))
  let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
  let adminType := Ty.function .unit frame.type
  let adminExpr := Expr.lambda .unit frame.type (SourceCoreCallableIndexedFrames.empty frame)
  let body := bindings.foldl (fun body (_, _, initializer, _) => Expr.letE initializer body)
    (.letE (.integer 99) (lowered.expression.weakenAt 0))
  let native : Core.Program := ⟨LanguageResult.resultType lowered.type,
    .letE (.newCell adminType adminExpr) body, checked.catalog.definitions ++ [frame.definition]⟩
  assertTrue native.check s!"typed recursive {name} failed Core checker"
  for fuel in [0, 5, 50, 1000] do
    let completed := match native.runStateful fuel with
      | .outOfFuel checkpoint => Core.runStateful 30000 checkpoint
      | other => other
    match completed with
    | .done result store =>
      assertTrue (store[0]? == some (.closure .unit frame.type (SourceCoreCallableIndexedFrames.empty frame) []))
        "typed recursive comparator changed ambient closure"
      if name == "child_fault" then
        let failed ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
          | some node => pure node | none => throw (IO.userError "typed recursive first fault absent")
        assertTrue (result == .inLeft lowered.type (.word (diagnostics.reasonAt owner failed.id))) "typed recursive fault changed"
      else
        let payload ← match result with
          | .inRight .word value => pure value
          | other => throw (IO.userError s!"typed recursive failed: {reprStr other}")
        let node ← match source.lookupExpression? expression with
          | some node => pure node | none => throw (IO.userError "typed recursive root metadata missing")
        let decoded ← get "typed recursive decode" (SourceCoreCompatibleValues.decode 150 values node.type payload)
        match name, decoded with
        | "build_box", .constructed _ [.bool true] | "conditional", .constructed _ [.bool true]
        | "parent", .constructed _ [.bool true] | "skipped", .constructed _ [.bool false]
        | "member_base", .bool false | "paired", .product (.constructed _ [.bool true]) (.bool false)
        | "proxy_box", .constructed _ [.proxy .word] | "proxy_parent", .constructed _ [.proxy .word]
        | "proxy_choice", .proxy .word | "proxy_pair", .product (.proxy .word) (.proxy .bool)
        | "proxy_raw", .product (.proxy (.comptime .word)) (.proxy .bool)
        | "proxy_nested", .product (.constructed _ [.proxy .word]) (.proxy .bool) => pure ()
        | _, other => throw (IO.userError s!"typed recursive {name} unexpected result: {reprStr other}")
      for ((binder, type, _, expected), position) in bindings.zipIdx do
        if let some expected := expected then
          let skipped := name == "skipped" || (name == "build_box" && binder.name == "n") ||
            (name == "conditional" && binder.name == "n") || (name == "child_fault" && binder.name == "n")
          let expectedCell := if skipped then Value.inLeft type .unit else Value.inRight .unit expected
          assertTrue (store[bindings.length - position]? == some expectedCell)
            s!"typed recursive {name} changed lazy initialization/skip at {binder.name}"
    | other => throw (IO.userError s!"typed recursive {name} failed to finish: {reprStr other}")

def run : IO Unit := do
  let program ← get "typed recursive checker" (checkProgram workspace)
  let roots := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program roots 500 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"typed recursive specialization: {reprStr other}")
  let prepared ← get "typed recursive actual factory" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let mut count := 0
  for function in prepared.prepared.functions do
    let name := (program.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    if name != "parent" && name != "proxy_parent" then
      let source := function.specialized.function.typedBody
      let returnId ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
        | _ => none with
        | some id => pure id | none => throw (IO.userError "typed recursive return missing")
      inspect prepared.prepared source function.signature.key none function.specialized.function.solvedRequirements name returnId
      if name == "proxy_pair" then
        inspect prepared.prepared source function.signature.key none function.specialized.function.solvedRequirements "proxy_raw" returnId
      count := count + 1
  let mut parentsSeen := 0
  let mut proxyParentsSeen := 0
  for parent in prepared.prepared.contexts do
    if !parent.substitution.isEmpty then
      for entry in parent.source.nodes do
        match entry with
        | .expression node => match node.form with
          | .constructor _ _ =>
            let name := (program.signatures.functions.find? (·.id == parent.caller.key.declaration)).map (·.name) |>.getD ""
            let fixture := if name == "proxy_parent" then "proxy_parent" else "parent"
            inspect prepared.prepared parent.source parent.caller.key (some parent) parent.caller.function.solvedRequirements fixture node.id
            if fixture == "proxy_parent" then proxyParentsSeen := proxyParentsSeen + 1
            else parentsSeen := parentsSeen + 1
          | _ => pure ()
        | _ => pure ()
  assertTrue (count == 10) s!"typed recursive cases missing: {count}"
  assertTrue (parentsSeen > 0) "typed recursive specialized parent case missing"
  assertTrue (proxyParentsSeen > 0) "typed recursive specialized proxy parent missing"
  IO.println "typed recursive expressions: proxy raw headers, nested proxies, constructor/control/index/key/member/product, typed captures, lazy effects, skipped/failing child, parent and resume GREEN"

end Tests.SourceCoreCompatibleTypedExpressions

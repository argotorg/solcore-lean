import Solcore.SourceSemantics.CoreLowering.TypedDataExpressionSequence
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualIndices
import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceCoreCallableIndexedFrames

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Argument-vector meanings use actual accepted scalar-key expression code.
The final theorems discharge every child semantic obligation with Index.Tree;
no child execution or externally supplied child meaning is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreTypedDataExpressionSequence
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionIndices CompatiblePayload GeneralHeap ReadOnly DataExpressionSequence

variable {values : ValuesContext} {readFuel fuel : Nat} {source : TypedSource} {scope : Scope}
  {context : SourceSemantics.Context} {compilation : SourceCoreFunctions.Context}
  {body : SourceCoreFunctions.BodyLowerer} {reasonAt : ExpressionId → Word}
private abbrev compile := SourceCoreFunctions.lowerExpressionWithPolicy
  (SourceCoreCompatibleDataExpressions.functionPolicy readFuel values) body fuel compilation source scope

/-- A real successful compiler traversal supplies every static child receipt;
source syntax and typing are independent of the compiler and of execution. -/
theorem accepted_sequence {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (coercions : ∀ id node, CompatibleExpressionIndices.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (inputs : ∀ id, id ∈ ids → ∃ node, source.lookupExpression? id = some node ∧
      CompatibleExpressionIndices.Syntax source id ∧ ExpressionHasType source context id node.type)
    (accepted : ids.mapM (fun id => compile (values := values) (readFuel := readFuel) (fuel := fuel)
      (body := body) (compilation := compilation) (source := source) (scope := scope) id reasonAt) = .ok codes) :
    ∃ types, DataExpressionSequence.Tree source (CompatibleExpressionIndices.Tree readFuel values source context compilation.solvedRequirements reasonAt)
      scope ids types codes := by
  apply DataExpressionSequence.Tree.of_children
  induction ids generalizing codes with
  | nil => simp at accepted; subst codes; exact .nil
  | cons id ids ih =>
    let lower := fun id => compile (values := values) (readFuel := readFuel) (fuel := fuel)
      (body := body) (compilation := compilation) (source := source) (scope := scope) id reasonAt
    change (id :: ids).mapM lower = .ok codes at accepted
    cases head : lower id with
    | error reason => simp [List.mapM_cons, head, bind, Except.bind] at accepted
    | ok code =>
      cases tail : ids.mapM lower with
      | error reason => simp [List.mapM_cons, head, tail, bind, Except.bind] at accepted
      | ok rest =>
        simp only [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
        subst codes
        obtain ⟨node, found, syntaxTree, typed⟩ := inputs id (by simp)
        have certificate := CompatibleExpressionIndices.tree_of_functions unique declarations signatures closed residual
          (show CompatibleExpressionIndices.PolicyFor (SourceCoreCompatibleDataExpressions.functionPolicy readFuel values)
            compilation readFuel values source scope reasonAt from ⟨by intros; rfl, by intros; rfl, rfl, rfl⟩)
          coercions syntaxTree found typed head
        exact .cons ⟨node, found, certificate⟩ (ih (fun child member => inputs child (by simp [member])) tail)

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid compilation.solvedRequirements context evidence)
  (unique : NodeOccurrencesUnique source)
  (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
  (signatures : context.signatures = values.checked.signatures)
  (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
  (coercions : ∀ id node, CompatibleExpressionIndices.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag → faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension valid unique declarations signatures closed residual coercions uninitialized missing in
theorem accepted_sufficient_fuel {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
    (inputs : ∀ id, id ∈ ids → ∃ node, source.lookupExpression? id = some node ∧
      CompatibleExpressionIndices.Syntax source id ∧ ExpressionHasType source context id node.type)
    (accepted : ids.mapM (fun id => compile (values := values) (readFuel := readFuel) (fuel := fuel)
      (body := body) (compilation := compilation) (source := source) (scope := scope) id reasonAt) = .ok codes)
    {mapping world administrative actualContext environment canonical actual before after store ξ outcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (trace : DataExpressionSequence.Trace program context evidence source environment before ids outcome after) :
    ∃ types value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) ∧
      DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld types codes faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨types, tree⟩ := accepted_sequence unique declarations signatures closed residual coercions inputs accepted
  obtain ⟨value, finalStore, finalMap, finalWorld, required, result⟩ :=
    TypedDataExpressionSequence.preserves_sufficient_fuel tree
      (CompatibleExpressionIndices.preserves functions extension program evidence valid unique uninitialized missing)
      environments heaps locals agrees actualTyped trace
  exact ⟨types, value, finalStore, finalMap, finalWorld, required, result⟩

include extension valid unique declarations signatures closed residual coercions uninitialized missing in
theorem accepted_reflects_done {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
    (inputs : ∀ id, id ∈ ids → ∃ node, source.lookupExpression? id = some node ∧
      CompatibleExpressionIndices.Syntax source id ∧ ExpressionHasType source context id node.type)
    (accepted : ids.mapM (fun id => compile (values := values) (readFuel := readFuel) (fuel := fuel)
      (body := body) (compilation := compilation) (source := source) (scope := scope) id reasonAt) = .ok codes)
    {mapping world administrative actualContext environment canonical actual before store finalStore ξ value runtimeFuel}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (completed : runStateful runtimeFuel (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) :
    ∃ types outcome after finalMap finalWorld,
      DataExpressionSequence.Trace program context evidence source environment before ids outcome after ∧
      DataExpressionSequence.Result (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld types codes faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨types, tree⟩ := accepted_sequence unique declarations signatures closed residual coercions inputs accepted
  obtain ⟨outcome, after, finalMap, finalWorld, result⟩ :=
    TypedDataExpressionSequence.reflects_done tree
      (CompatibleExpressionIndices.reflects functions extension program evidence valid uninitialized missing)
      environments heaps locals agrees actualTyped completed
  exact ⟨types, outcome, after, finalMap, finalWorld, result⟩

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function twice() returns ((Bool, Bool)) { let m: mapping(Bool => Bool); return (m[true], m[false]); }",
    "function fault() returns ((Bool, Bool, Bool)) { let m: mapping(Bool => Bool); let missing: Bool; let other: mapping(Bool => Bool); return (m[true], missing, other[false]); }",
    "function payload() returns ((mapping(Bool => Bool), Bool)) { let m: mapping(Bool => mapping(Bool => Bool)); let n: mapping(Bool => Bool); return (m[true], n[false]); }",
    "function key_fault() returns ((Bool, Bool)) { let m: mapping(Bool => Bool); let missing: Bool; return (m[true], m[missing]); }"
  ]}] }
private def reached : Nat → TypedSource → ExpressionId → List ExpressionNode
  | 0, _, _ => []
  | budget + 1, source, id => match source.lookupExpression? id with
    | none => []
    | some node => node :: (match node.form with
      | .index base key => reached budget source base ++ reached budget source key
      | .group inner => reached budget source inner
      | _ => [])

def run : IO Unit := do
  let program ← get "typed sequence checker" (checkProgram workspace)
  let roots := program.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program roots 300 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"typed sequence specialization: {reprStr other}")
  let prepared ← get "typed sequence real compiler" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let checked := prepared.checked
  let mut count := 0
  for function in prepared.prepared.functions do
    let name := (program.signatures.functions.find? (·.id == function.signature.key.declaration)).map (·.name) |>.getD ""
    let source := function.specialized.function.typedBody
    let returnId : ExpressionId ← match source.nodes.findSome? fun
      | .statement node => match node.form with | .returnStmt (some id) => some id | _ => none
      | _ => none with
      | some id => pure id | none => throw (IO.userError "typed sequence return missing")
    let returnNode : ExpressionNode ← match source.lookupExpression? returnId with
      | some node => pure node | none => throw (IO.userError "typed sequence return metadata missing")
    let ids : List ExpressionId ← match returnNode.form with
      | .tuple ids => pure ids | other => throw (IO.userError s!"typed sequence tuple missing: {reprStr other}")
    let nodes := ids.flatMap (reached 20 source)
    let binderIds := (nodes.filterMap fun node => match node.form with | .reference _ (.local id) => some id | _ => none).eraseDups
    let mut values := SourceCoreCompatibleValues.Context.initial checked
    let mut bindings : List (TypedBinder × Ty × Option Value) := []
    for id in binderIds do
      let binder ← get "typed sequence binder" (SourceCoreDataPlaces.rootBinder source id)
      let native ← get "typed sequence binder projection" (checked.catalog.project binder.scheme.body)
      let expected ← match binder.scheme.body with
        | .mapping key result => do
          let encoded ← get "typed sequence expected mapping" (SourceCoreCompatibleValues.encode 100 values binder.scheme.body (.mapping key result []))
          values := encoded.context
          pure (some encoded.value)
        | _ => pure none
      bindings := bindings ++ [(binder, native, expected)]
    let diagnostics ← match prepared.prepared.diagnostics with
      | some diagnostics => pure diagnostics.program | none => throw (IO.userError "typed sequence diagnostics missing")
    let owner := function.signature.key
    let own ← match diagnostics.base.find? owner with
      | some own => pure own | none => throw (IO.userError "typed sequence owner missing")
    let compilation : SourceCoreFunctions.Context := {
      plan := prepared.prepared.plan, owner, globals := prepared.prepared.globals, administrativePrefix := 1,
      solvedRequirements := function.specialized.function.solvedRequirements, internalReason := Word.zero }
    let scope := bindings.map fun (binder, type, _) => (binder.id, type)
    let representation := SourceCoreCompatibleFunctions.representation values 150
    let codes ← get "typed sequence actual child traversal" (ids.mapM fun id =>
      SourceCoreGeneralFunctions.lowerContextualExpression program representation checked.signatures prepared.prepared.locals
        prepared.prepared.contexts own.assignments diagnostics compilation prepared.prepared.callableContext none none 150 source scope id (diagnostics.reasonAt owner))
    let packed := SourceCoreCalls.packArguments codes
    let frame : SourceCoreCallableIndexedFrames.Layout := ⟨⟨checked.catalog.definitions.length⟩⟩
    let adminType := Ty.function .unit frame.type
    let adminExpr := Expr.lambda .unit frame.type (SourceCoreCallableIndexedFrames.empty frame)
    let body := bindings.foldl (fun body (_, type, _) => Expr.letE (OptionalCell.allocate type) body)
      (.letE (.integer 99) (packed.expression.weakenAt 0))
    let native : Core.Program := ⟨LanguageResult.resultType packed.type,
      .letE (.newCell adminType adminExpr) body, checked.catalog.definitions ++ [frame.definition]⟩
    assertTrue native.check s!"typed sequence {name} failed Core checker"
    let expectedFirst ← match bindings.find? (fun (binder, _, _) => binder.name == "m") with
      | some (_, _, some value) => pure value | _ => throw (IO.userError "typed sequence first mapping missing")
    let prefixStore : Option Core.Store ← if name == "fault" || name == "key_fault" then do
      let first ← match codes.head? with
        | some code => pure code | none => throw (IO.userError "typed sequence first code missing")
      let prefixBody := bindings.foldl (fun body (_, type, _) => Expr.letE (OptionalCell.allocate type) body)
        (.letE (.integer 99) (first.expression.weakenAt 0))
      let prefixProgram : Core.Program := ⟨LanguageResult.resultType first.type,
        .letE (.newCell adminType adminExpr) prefixBody, checked.catalog.definitions ++ [frame.definition]⟩
      match prefixProgram.runStateful 30000 with
      | .done (.inRight .word _) store => pure (some store)
      | other => throw (IO.userError s!"typed sequence successful prefix failed: {reprStr other}")
    else pure none
    for fuel in [0, 5, 50, 1000] do
      let completed := match native.runStateful fuel with
        | .outOfFuel checkpoint => Core.runStateful 30000 checkpoint
        | other => other
      match completed with
      | .done result store =>
        assertTrue (store[0]? == some (.closure .unit frame.type (SourceCoreCallableIndexedFrames.empty frame) []))
          "typed sequence changed administrative closure"
        assertTrue (store.length > bindings.length + 1) "typed sequence helper allocated no comparator cells"
        if name == "fault" || name == "key_fault" then
          let missing ← match nodes.find? (fun node => match node.form with | .reference "missing" (.local _) => true | _ => false) with
            | some node => pure node | none => throw (IO.userError "typed sequence failure node missing")
          assertTrue (result == .inLeft packed.type (.word (diagnostics.reasonAt owner missing.id))) "typed sequence changed first fault"
          assertTrue (prefixStore == some store) "typed sequence evaluated past the first fault or changed prefix effects"
        else if name == "twice" then
          assertTrue (result == .inRight .word (.pair (.bool false) (.bool false))) "typed sequence repeated-index results differ"
        else
          let nested ← get "typed sequence nested default" (SourceCoreCompatibleValues.encode 100 values (.mapping .bool .bool) (.mapping .bool .bool []))
          assertTrue (result == .inRight .word (.pair nested.value (.bool false))) "typed sequence captured payload changed"
        for ((binder, type, expected), position) in bindings.zipIdx do
          let expectedCell := if binder.name == "other" || binder.name == "missing" then Value.inLeft type .unit
            else match expected with | some value => .inRight .unit value | none => .inLeft type .unit
          assertTrue (store[bindings.length - position]? == some expectedCell) "typed sequence lost prefix or evaluated skipped tail"
        assertTrue (store.any (fun cell => cell == .inRight .unit expectedFirst)) "typed sequence first mapping effect missing"
      | other => throw (IO.userError s!"typed sequence {name} failed: {reprStr other}")
    count := count + 1
  assertTrue (count == 4) "typed sequence cases missing"
  IO.println "typed argument sequence: real index child receipts, typed hidden slots, comparator allocation, captured mapping payload, fault prefix, skipped tail and resume GREEN"

end Tests.SourceCoreTypedDataExpressionSequence
